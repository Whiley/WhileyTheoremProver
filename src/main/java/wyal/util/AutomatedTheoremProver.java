package wyal.util;

import java.util.BitSet;

import wyal.heap.StructurallyEquivalentHeap;
import wyal.heap.SyntacticHeaps;
import wyal.lang.Formula;
import wyal.lang.Proof;
import wyal.lang.SyntacticHeap;
import wyal.lang.SyntacticItem;
import wyal.lang.WyalFile;
import wyal.lang.Proof.State;
import wyal.rules.*;
import wybs.lang.SyntaxError;
import wyfs.lang.Path;

public class AutomatedTheoremProver {

	/**
	 * The type system encapsulates the core algorithms for type simplification
	 * and subtyping testing.
	 */
	private final TypeSystem types;
	/**
	 * The enclosing WyAL file being checked.
	 */
	private final WyalFile parent;

	/**
	 * Determines the maximum size of a proof.
	 */
	private final int maxProofSize = 500;

	/**
	 * The list of proof rules which can be applied by this theorem prover.
	 */
	private Proof.Rule[] rules;

	public AutomatedTheoremProver(final WyalFile parent) {
		this.parent = parent;
		// FIXME: this should be shared between different compilation stages
		this.types = new TypeSystem(parent);
		//
		this.rules = new Proof.Rule[] {
				new CongruenceClosure(types),
				new InequalityIntroduction(types),
				new AndElimination(),
				new ExistentialElimination(types),
				new MacroExpansion(types),
				new ExpandTypeTest(types),
				new TypeTestClosure(types),
				new ArrayLengthAxiom(types),
				new ArrayIndexAxiom(types),
				new ArrayIndexCaseAnalysis(types),
				new EqualityCaseAnalysis(types),
				new OrElimination(),
				new ExhaustiveQuantifierInstantiation(types)
				};
	}

	public void check(Path.Entry<?> originalSource) {
		for (int i = 0; i != parent.size(); ++i) {
			SyntacticItem item = parent.getSyntacticItem(i);
			if (item instanceof WyalFile.Declaration.Assert) {
				WyalFile.Declaration.Assert ast = (WyalFile.Declaration.Assert) item;
				if (!check(ast)) {
					throw new SyntaxError(ast.getMessage(), originalSource, item);
				}
			}
		}
	}

	private boolean check(WyalFile.Declaration.Assert decl) {
		// Convert the body of the assertion into "expression form". That is,
		// where every node is an expression.
		Formula root = Formulae.toFormula(decl.getBody(), types);
		// Check whether or not this formula is valid.
		return checkValidity(decl.getParent(), root);
		//
	}

	/**
	 * Check whether a given formula is unsatisfiable or not. That is, whether
	 * or not it can be reduces to false.
	 *
	 * @param formula
	 * @return
	 */
	private boolean checkValidity(SyntacticHeap parent, Formula formula) {
		SyntacticHeap heap = new StructurallyEquivalentHeap(parent);
		Formula.Truth FALSE = heap.allocate(new Formula.Truth(false));
		// Invert the body of the assertion in order to perform a
		// "proof-by-contradiction".
		formula = Formulae.invert(formula);
		// Simplify the formula, since inversion does not do this.
		formula = Formulae.simplifyFormula(formula, types);
		// Allocate initial formula to the heap
		formula = heap.allocate(SyntacticHeaps.clone(formula));
		// Create initial state
		DeltaProof proof = new DeltaProof(null, heap, formula);
		Proof.State state = proof.getState(0);
		//
		boolean r = checkUnsat(state, new FastDelta.Set(formula), FALSE);
		//
		simplifyProof(state,FALSE);
		//
		System.out.println("******************* PROOF (" + proof.size() + ") ******************");
		OldAutomatedTheoremProver.print(proof);
		return r;
	}

	private boolean checkUnsat(Proof.State state, FastDelta.Set additions, Formula.Truth FALSE) {
		// Sanity check whether we have reached the hard limit on the amount of
		// computation permitted.
		if(state.getProof().size() > maxProofSize) {
			//throw new IllegalArgumentException("Maximum proof size reached");
			return false;
		}
		// Hard limit not reached, therefore continue exploring!
		FastDelta delta = new FastDelta(additions,FastDelta.EMPTY_SET);
		// Infer information from current state and delta
		for (int i = 0; i != additions.size() && !state.isKnown(FALSE); ++i) {
			Formula truth = additions.get(i);
			for (int j = 0; j != rules.length; ++j) {
				// Check whether the given truth is actually active or not. If not,
				// it has been subsumed at some point, and must be ignored.
				if (delta.isRemoval(truth)) {
					break;
				} else {
					// Truth remains active, therefore try to process it with
					// the given rule.
					Proof.Rule rule = rules[j];
					Proof.State before = state;
					// Apply the rule
					if (rule instanceof Proof.LinearRule) {
						// Linear rules are the easy case as they can only
						// produce one follow on case.
						Proof.LinearRule linearRule = (Proof.LinearRule) rule;
						state = linearRule.apply(state, truth);
					} else {
						// Non-linear rules are more complex as they can result
						// in multiple branches being taken.
						Proof.NonLinearRule nonLinearRule = (Proof.NonLinearRule) rule;
						Proof.State[] splits = nonLinearRule.apply(state, truth);
						if (splits.length > 1) {
							// Yes, we have multiple branches so handle that.
							return applySplit(state, splits, delta, truth, FALSE);
						} else {
							// In this case, either the rule did not apply or
							// there was only one child anyway.
							state = splits[0];
						}
					}
					if(state != before) {
						// Given our current delta as processed thus far, we now
						// need to include the delta for the step that was just
						// taken (if any).
						delta = delta.apply(state.getDelta(before));
					}
				}
			}
			// At this point, we have now processed this truth
			// completely against all known rules. Therefore, it will
			// not be considered again.
			delta = delta.remove(truth);
		}
		if (state.isKnown(FALSE)) {
			// We established a contradiction at some point during this round,
			// therefore we're done.
			return true;
		} else if (delta.getAdditions().size() > 0) {
			// We still have unprocessed truths. Therefore, continue for another
			// round.
			return checkUnsat(state, delta.getAdditions(), FALSE);
		} else {
			// We're out of options, therefore we're failing to find a
			// contradiction and we give up on the whole thing.
			return false;
		}
	}

	private boolean applySplit(Proof.State state, Proof.State[] splits, FastDelta delta, Formula truth, Formula.Truth FALSE) {
		State parent = state.getParent();
		// Now, try to find a contradiction for each case
		for (int j = 0; j != splits.length; ++j) {
			Proof.State split = splits[j];
			FastDelta splitDelta = delta.apply(split.getDelta());
			//
			if (!checkUnsat(split, splitDelta.getAdditions(), FALSE)) {
				// Unable to find a proof down this branch, therefore done.
				return false;
			} else {
				// We did find a proof for this branch. At this point, we need
				// to analyse the proof and see whether or not this disjunct
				// actually had a part to play or not. If not, then we can
				// terminate this disjunct early (which can lead to significant
				// reductions in the state space).
				BitSet cone = computeDependencyCone(split, FALSE);
				//
				if (cone.get(truth.getIndex()) == false && parent != null) {
					// First, bypass the split where one of the clauses was
					// assumed
					state.applyBypass(split);
					break;
				}
			}
		}
		return true;
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
		if(delta.isAddition(FALSE)) {
			// This is the leaf case
			BitSet dependencies = new BitSet();
			for(Formula dep : state.getDependencies()) {
				dependencies.set(dep.getIndex());
			}
			return dependencies;
		} else {
			BitSet dependencies = new BitSet();
			// Determine recurisve dependencies
			for(int i=0;i!=state.numberOfChildren();++i) {
				Proof.State child = state.getChild(i);
				dependencies.or(computeDependencyCone(child,FALSE));
			}
			//
			Proof.Delta.Set additions = delta.getAdditions();
			for(int i=0;i!=additions.size();++i) {
				Formula addition = additions.get(i);
				if(dependencies.get(addition.getIndex())) {
					// One of the additions for this state contributed to the
					// contradiction. Therefore, include our dependencies.
					for(Formula dep : state.getDependencies()) {
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
		for(int i=0;i<state.numberOfChildren();++i) {
			Proof.State child = state.getChild(i);
			if(!simplifyProof(child,FALSE) && !additions.contains(FALSE)) {
				return false;
			} else if(child.getParent() != state) {
				// This indicates the given child has been bypassed. Therefore,
				// all remaining children would have been moved down and
				// therefore, we want to rewind one step.
				i = i - 1;
			}
		}
		// Now, see whether we can bypass this state or not
		if(additions.contains(FALSE)) {
			state.applyBypass(null);
			return true;
		} else if(state.numberOfChildren() == 0) {
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
		if(parent.numberOfChildren() == 1) {
			parent.applyBypass(state);
		}
		return true;
	}
}
