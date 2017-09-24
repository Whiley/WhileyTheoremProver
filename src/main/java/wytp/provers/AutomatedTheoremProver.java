// Copyright 2011 The Whiley Project Developers
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//    http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.
package wytp.provers;

import java.util.BitSet;

import wyal.heap.StructurallyEquivalentHeap;
import wyal.heap.SyntacticHeaps;
import wyal.lang.WyalFile;
import wybs.lang.NameResolver;
import wybs.lang.SyntacticHeap;
import wybs.lang.SyntacticItem;
import wybs.lang.SyntaxError;
import wybs.lang.NameResolver.AmbiguousNameError;
import wybs.lang.NameResolver.NameNotFoundError;
import wybs.lang.NameResolver.ResolutionError;
import wyfs.lang.Path;
import wytp.proof.Formula;
import wytp.proof.Proof;
import wytp.proof.Proof.State;
import wytp.proof.io.ProofPrinter;
import wytp.proof.rules.CongruenceClosure;
import wytp.proof.rules.EqualityCaseAnalysis;
import wytp.proof.rules.Simplification;
import wytp.proof.rules.arithmetic.InequalityIntroduction;
import wytp.proof.rules.array.ArrayEqualityCaseAnalysis;
import wytp.proof.rules.array.ArrayIndexAxiom;
import wytp.proof.rules.array.ArrayIndexCaseAnalysis;
import wytp.proof.rules.array.ArrayLengthAxiom;
import wytp.proof.rules.function.FunctionCallAxiom;
import wytp.proof.rules.function.MacroExpansion;
import wytp.proof.rules.logic.AndElimination;
import wytp.proof.rules.logic.OrElimination;
import wytp.proof.rules.quantifier.ExhaustiveQuantifierInstantiation;
import wytp.proof.rules.quantifier.ExistentialElimination;
import wytp.proof.rules.record.RecordEqualityCaseAnalysis;
import wytp.proof.rules.type.TypeTestClosure;
import wytp.proof.rules.type.TypeTestNormalisation;
import wytp.proof.util.DeltaProof;
import wytp.proof.util.FastDelta;
import wytp.proof.util.Formulae;
import wytp.proof.util.FastDelta.Set;
import wytp.types.TypeSystem;

public class AutomatedTheoremProver {

	/**
	 * The type system encapsulates the core algorithms for type simplification
	 * and subtyping testing.
	 */
	private final TypeSystem types;

	/**
	 * Determines the maximum size of a proof.
	 */
	private int maxProofSize = 5000;

	/**
	 * Debugging option which prints the proof to the console. This should
	 * eventually be deprecated in favour of a more formal mechanism for
	 * extracting and examining the proof.
	 */
	private boolean printProof = false;

	/**
	 * Set the width for displaying proofs
	 */
	private int proofWidth = 80;

	/**
	 * The list of proof rules which can be applied by this theorem prover.
	 */
	private Proof.Rule[] rules;

	public void setPrintProof(boolean flag) {
		this.printProof = flag;
	}

	public void setProofLimit(int size) {
		this.maxProofSize = size;
	}

	public void setProofWidth(int width) {
		this.proofWidth= width;
	}

	public AutomatedTheoremProver(TypeSystem typeSystem) {
		this.types = typeSystem;
		//
		Simplification simplify = new Simplification(types);
		//
		this.rules = new Proof.Rule[] {
				simplify,
				new CongruenceClosure(simplify,types),
				new InequalityIntroduction(simplify,types),
				new AndElimination(simplify,types),
				new ExistentialElimination(simplify,types),
				new MacroExpansion(simplify,types),
				new TypeTestNormalisation(simplify,types),
				new TypeTestClosure(simplify,types),
				new ArrayLengthAxiom(simplify,types),
				new ArrayIndexAxiom(simplify,types),
				new ArrayIndexCaseAnalysis(simplify,types),
				new FunctionCallAxiom(simplify,types),
				new EqualityCaseAnalysis(simplify,types),
				new RecordEqualityCaseAnalysis(simplify,types),
				new ArrayEqualityCaseAnalysis(simplify,types),
				new OrElimination(),
				new ExhaustiveQuantifierInstantiation(simplify,types) };
	}

	public void check(WyalFile source, Path.Entry<?> originalSource) {
		for (int i = 0; i != source.size(); ++i) {
			SyntacticItem item = source.getSyntacticItem(i);
			if (item instanceof WyalFile.Declaration.Assert) {
				WyalFile.Declaration.Assert ast = (WyalFile.Declaration.Assert) item;
				try {
					if (!check(ast)) {
						String msg = ast.getMessage();
						msg = msg != null ? msg : "assertion failure";
						throw new SyntaxError(msg, originalSource, item);
					}
				} catch (NameResolver.ResolutionError e) {
					throw new SyntaxError(e.getMessage(), originalSource, item, e);
				}
			}
		}
	}

	private boolean check(WyalFile.Declaration.Assert decl) throws ResolutionError {
		// Convert the body of the assertion into "expression form". That is,
		// where every node is an expression.
		Formula root = Formulae.toFormula(decl.getBody(), types);
		// Check whether or not this formula is valid.
		return checkValidity(decl, root);
		//
	}

	/**
	 * Check whether a given formula is unsatisfiable or not. That is, whether
	 * or not it can be reduces to false.
	 *
	 * @param axiom
	 * @return
	 * @throws AmbiguousNameError
	 * @throws NameNotFoundError
	 */
	private boolean checkValidity(WyalFile.Declaration.Assert decl, Formula axiom) throws ResolutionError {
		SyntacticHeap heap = new StructurallyEquivalentHeap(decl.getHeap());
		Formula.Truth FALSE = heap.allocate(new Formula.Truth(false));
		// Invert the body of the assertion in order to perform a
		// "proof-by-contradiction".
		axiom = Formulae.invert(axiom);
		// Simplify the formula, since inversion does not do this.
		// Allocate initial formula to the heap
		axiom = heap.allocate(axiom);
		// Create initial state
		DeltaProof proof = new DeltaProof(null, heap, axiom);
		Proof.State head = proof.getState(0);
		//
		boolean r = checkUnsat(head, head, FALSE);
		//
		simplifyProof(head, FALSE);
		//
		if (printProof) {
			print(proof);
		}
		// Stash the proof so others can access it later.
		decl.attributes().add(new WyalFile.Attribute.Proof(proof));
		//
		return r;
	}

	/**
	 * Check whether a given state is unsatisfiable or not. That is, whether or
	 * not we can reach a contradiction from this state. One or more new truths
	 * are carried forward to be investigated. If there are no more new truths
	 * to investigate, then we are done. This method will apply all known rules
	 * to this set of truths and generate a set of new truths, to be used in any
	 * subsequent calls to this method.
	 *
	 * @param current
	 *            The current state being investigated to see whether or not it
	 *            leads to a contradiction.
	 * @param head
	 *            The current tip of the proof branch. This maybe some
	 *            distance in the future from the current state, and
	 *            identifies truths which have yet to be processed.
	 * @param FALSE
	 * @return
	 */
	private boolean checkUnsat(Proof.State current, Proof.State head, Formula.Truth FALSE) throws ResolutionError {
		// Sanity check whether we have reached the hard limit on the amount of
		// computation permitted.
		if (head.getProof().size() > maxProofSize) {
			// throw new IllegalArgumentException("Maximum proof size reached");
			return false;
		} else if (head.isKnown(FALSE)) {
			// We established a contradiction at some point during this round,
			// therefore we're done.
			return true;
		}
		// Apply all rules one after the other
		for (int j = 0; j != rules.length; ++j) {
			Proof.Rule rule = rules[j];
			// Apply the rule
			if (rule instanceof Proof.LinearRule) {
				Proof.LinearRule linearRule = (Proof.LinearRule) rule;
				// Linear rules are the easy case as they can only
				// produce one follow on case.
				head = linearRule.apply(current, head);
			} else {
				Proof.NonLinearRule nonLinearRule = (Proof.NonLinearRule) rule;
				// Non-linear rules are more complex as they can result
				// in multiple branches being taken.
				Proof.State[] heads = nonLinearRule.apply(current, head);
				if (heads.length > 1) {
					// Yes, we have multiple branches so handle that.
					return applySplit(current, heads, FALSE);
				} else {
					// In this case, either the rule did not apply or
					// there was only one child anyway.
					head = heads[0];
				}
			}
		}
		if(current == head) {
			// We're out of options, therefore we're failing to find a
			// contradiction and we give up on the whole thing.
			return false;
		} else {
			return checkUnsat(next(current, head), head, FALSE);
		}
	}

	/**
	 * Determine whether a given state is an "ancestor" of a given "descendant"
	 * or not. This is done by traversing from the ancestor on the assumption
	 * that they are unlikely to be far apart at any given moment.
	 *
	 * @param ancestor
	 * @param descendant
	 * @return
	 */
	private boolean isAncestor(Proof.State ancestor, Proof.State descendant) {
		if (ancestor == descendant) {
			return true;
		} else {
			for (int i = 0; i != ancestor.numberOfChildren(); ++i) {
				Proof.State child = ancestor.getChild(i);
				if (isAncestor(child, descendant)) {
					return true;
				}
			}
			return false;
		}
	}

	private boolean applySplit(Proof.State current, Proof.State[] heads, Formula.Truth FALSE) throws ResolutionError {
		// Now, try to find a contradiction for each case
		for (int j = 0; j != heads.length; ++j) {
			Proof.State head = heads[j];
			Proof.State next = next(current,head);
			//
			if (!checkUnsat(next, head, FALSE)) {
				// Unable to find a proof down this branch, therefore done.
				return false;
			} else {
				// We did find a proof for this branch. At this point, we need
				// to analyse the proof and see whether or not this disjunct
				// actually had a part to play or not. If not, then we can
				// terminate this disjunct early (which can lead to significant
				// reductions in the state space).
				BitSet cone = computeDependencyCone(head, FALSE);
				//
				if (stateNotRequired(current, cone)) {
					// Bypass the split where one of the clauses was assumed
					head.getParent().applyBypass(head);
					break;
				}
			}
		}
		return true;
	}

	private boolean stateNotRequired(Proof.State current, BitSet cone) {
		Proof.Delta.Set additions = current.getDelta().getAdditions();
		for(int i=0;i!=additions.size();++i) {
			if(cone.get(additions.get(i).getIndex())) {
				// Yes, it is required
				return false;
			}
		}
		// No, it's not required
		return true;
	}

	/**
	 * Determine the next state along a given branch. This is a little tricky
	 * when there are multiple children as, using the head only, we need to
	 * determine which child we should follow.
	 *
	 * @param current
	 *            The state which we want to advance to the next successor
	 * @param head
	 *            The tip of the branch we are following
	 * @return
	 */
	private Proof.State next(Proof.State current, Proof.State head) {
		for(int i=0;i!=current.numberOfChildren();++i) {
			Proof.State child = current.getChild(i);
			if(isAncestor(child,head)) {
				return child;
			}
		}
		return current;
	}

	/**
	 * Determine the "dependency cone" for a give state. That is, the set of
	 * truths on which the final contradiction depends. This is likely to be a
	 * subset of the actual active truths. In particular, at the point of a
	 * disjunction it is possible that the disjunct itself does not contribute
	 * torwards finding the contradiction. In such case, we can apply a "bypass"
	 * to avoid checking all of the other branches for that disjunct.
	 *
	 * @param state
	 * @return
	 */
	private BitSet computeDependencyCone(Proof.State state, Formula.Truth FALSE) {
		Proof.Delta delta = state.getDelta();
		if (delta.isAddition(FALSE)) {
			// This is the leaf case
			BitSet dependencies = new BitSet();
			for (Formula dep : state.getDependencies()) {
				dependencies.set(dep.getIndex());
			}
			return dependencies;
		} else {
			BitSet dependencies = new BitSet();
			// Determine recursive dependencies
			for (int i = 0; i != state.numberOfChildren(); ++i) {
				Proof.State child = state.getChild(i);
				dependencies.or(computeDependencyCone(child, FALSE));
			}
			//
			Proof.Delta.Set additions = delta.getAdditions();
			for (int i = 0; i != additions.size(); ++i) {
				Formula addition = additions.get(i);
				if (dependencies.get(addition.getIndex())) {
					// One of the additions for this state contributed to the
					// contradiction. Therefore, include our dependencies.
					for (Formula dep : state.getDependencies()) {
						dependencies.set(dep.getIndex());
					}
					break;
				}
			}
			//
			return dependencies;
		}
	}

	private boolean simplifyProof(Proof.State state, Formula.Truth FALSE) {
		Proof.Delta delta = state.getDelta();
		Proof.Delta.Set additions = delta.getAdditions();
		// First, simplify children
		for (int i = 0; i < state.numberOfChildren(); ++i) {
			Proof.State child = state.getChild(i);
			if (!simplifyProof(child, FALSE) && !additions.contains(FALSE)) {
				return false;
			} else if (child.getParent() != state) {
				// This indicates the given child has been bypassed. Therefore,
				// all remaining children would have been moved down and
				// therefore, we want to rewind one step.
				i = i - 1;
			}
		}
		// Now, see whether we can bypass this state or not
		if (additions.contains(FALSE)) {
			state.applyBypass(null);
			return true;
		} else if (state.numberOfChildren() == 0) {
			return false;
		} else {
			BitSet cone = computeDependencyCone(state, FALSE);
			for (int i = 0; i != additions.size(); ++i) {
				Formula addition = additions.get(i);
				if (cone.get(addition.getIndex())) {
					// This indicates a dependency that we introduced was
					// required for the final contradiction. Therefore, we don't
					// want to bypass this state.
					return true;
				}
			}
		}
		// If we get here, then we didn't fine anything in this state which
		// was actually required for the final proof. Therefore, we can
		// eliminate this state
		Proof.State parent = state.getParent();
		if (parent.numberOfChildren() == 1) {
			parent.applyBypass(state);
		}
		return true;
	}

	// Useful for debugging
	public void print(Proof proof) {
		ProofPrinter printer = new ProofPrinter(System.out).setWidth(proofWidth);
		for(int i=0;i!=proofWidth;++i) {
			System.out.print("=");
		}
		System.out.println();
		printer.print(proof);
		printer.flush();
	}
}
