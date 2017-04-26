// Copyright 2017 David J. Pearce
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
package wytp.proof.rules;

import java.math.BigInteger;
import java.util.Arrays;

import wyal.lang.SyntacticItem;
import wyal.lang.WyalFile;
import wyal.lang.NameResolver.ResolutionError;
import wyal.lang.WyalFile.Expr;
import wyal.lang.WyalFile.Tuple;
import wyal.lang.WyalFile.Type;
import wytp.proof.Formula;
import wytp.proof.Proof;
import wytp.proof.Proof.State;
import wytp.proof.util.AbstractProofRule;
import wytp.proof.util.Arithmetic;
import wytp.proof.util.Arithmetic.Polynomial;
import wytp.types.TypeSystem;

/**
 * <p>
 * Responsible for implementing <i>congruence closure</i>. That is, applying
 * equalities to eliminate variables through substitution and simplify the
 * overall proof. As an example, consider this assertion:
 * </p>
 *
 * <pre>
 * assert:
 *   forall(int i, int j):
 *      if:
 *          i == 0
 *      then:
 *          i >= 0
 * </pre>
 *
 * <p>
 * This is a simple assertion that should be easily proved. To do this by
 * contradiction, we end up with the (skolemised) formula
 * <code>(i == 0) && (i < 0)</code>. To establish the contradiction, we
 * substitute <code>i == 0</code> through the formula <code>i &lt; 0</code> to
 * generate <code>0 < 0</code> (which immediately reduces to false). Such
 * substitutions are the responsibility of this rule.
 * </p>
 * <p>
 * Upon seeing a new equality (e.g. <code>i == 0</code> above), this rule
 * searches back through the history of active truths for any opportunities to
 * apply the substitution. If/when a successful substitution occurs, then the
 * truth in question is <i>subsumed</i> and the substituted version asserted
 * instead. To reduce overhead, this rule employs a lexicographic ordering of
 * terms and always substitutes through the lowest available candidate in any
 * given equality.
 * </p>
 * <p>
 * <b>NOTE:</b> The problem of <i>counting</i> is a surprising issue with
 * congruence closure. This is possible, for example, when you have recursive
 * function or predicate applications. For example, consider a formula
 * <code>x == f(x) && x < 0</code>. Upon first substitution, we end up with
 * <code>x == f(x) && f(x) < 0</code>. Then, upon second substitution, we end up
 * with <code>x == f(x) && f(f(x)) < 0</code>, and so on. Therefore, care must
 * be taken in any such rule to ensure such looping does not occur.
 * </p>
 *
 * @author David J. Pearce
 *
 */
public class CongruenceClosure extends AbstractProofRule implements Proof.LinearRule {

	public CongruenceClosure(TypeSystem types) {
		super(types);
	}

	@Override
	public String getName() {
		return "Eq-S";
	}

	@Override
	public State apply(Proof.State state, Formula newTruth) throws ResolutionError {
		//
		Formula constructed = (Formula) construct(state, newTruth, newTruth);

		if(constructed != newTruth) {
			state = state.subsume(this, newTruth, constructed);
		} else if (newTruth instanceof Formula.Equality && ((Formula.Equality) newTruth).getSign()) {
			state = substituteAgainstEquality(state, (Formula.Equality) newTruth);
		}
		//
		return state;
	}

	private Proof.State substituteAgainstEquality(Proof.State state, Formula.Equality newTruth) throws ResolutionError {
		//
		if (newTruth.getSign()) {
			state = applyEqualityTypeAxiom(state, newTruth);
			//
			Assignment assignment = rearrangeToAssignment(newTruth);
			if (assignment != null) {
				return applyAssignment(assignment,state);
			}
		}
		return state;
	}

	private State applyEqualityTypeAxiom(Proof.State state, Formula.Equality newTruth) throws ResolutionError {
		Expr lhs = newTruth.getOperand(0);
		Expr rhs = newTruth.getOperand(1);
		Type lhsT = types.inferType(lhs);
		Type rhsT = types.inferType(rhs);
		if(lhsT == null || rhsT == null) {
			// Defer processing of this equality
			return state;
		} else {
			Type intersection = new Type.Intersection(lhsT,rhsT);
			//
			boolean left = types.isRawSubtype(lhsT, rhsT);
			boolean right = types.isRawSubtype(rhsT, lhsT);
			Formula axiom;
			if (left && right) {
				// In this case, the types are equivalent so we don't need to do
				// anything.
				return state;
			} else if (left) {
				// In this case, the type of rhs is contained within that of lhs.
				// Therefore, that type must be the type for lhs.
				axiom = new Formula.Is(lhs, rhsT);
			} else if (right) {
				// In this case, the type of lhs is contained within that of rhs.
				// Therefore, that type must be the type for rhs.
				axiom = new Formula.Is(rhs, lhsT);
			} else if (types.isRawSubtype(new Type.Void(), intersection)) {
				// In this case, no possible intersection exists between the lhs and
				// rhs. Therefore, we're done as this equality cannot ever be true.
				return state.subsume(this, newTruth, new Formula.Truth(false));
			} else {
				// In this case, neither type is contained within the other.
				// Therefore, their intersection must be the type for both.
				axiom = new Formula.Conjunct(new Formula.Is(lhs, intersection), new Formula.Is(rhs, intersection));
			}
			// FIXME: I think it makes sense here to try and propagate the type
			// information upwards. Otherwise, we can get stuck with a non-variable
			// on the left-hand side.
			return state.subsume(this, newTruth, axiom);
		}
	}

	private State applyAssignment(Assignment assignment, Proof.State state) throws ResolutionError {
		Formula newTruth = assignment.getDependency();
		Proof.Delta history = state.getDelta(null);
		Proof.Delta.Set additions = history.getAdditions();
		//
		for (int i = 0; i != additions.size(); ++i) {
			Formula existingTruth = additions.get(i);
			if(existingTruth != newTruth) {
				Formula updatedTruth = (Formula) substitute(assignment.getLeftHandSide(), assignment.getRightHandSide(),
						existingTruth);
				if (existingTruth != updatedTruth) {
					// The following is needed because substitution can
					// produce a different looking term which, after
					// simplification, is the same. To avoid this, we
					// need to avoid "recursive substitutions" somehow.
					if (!existingTruth.equals(updatedTruth)) {
						state = state.subsume(this, existingTruth, updatedTruth, newTruth);
					}
				}
			}
		}
		//
		return state;
	}

	/**
	 * Rearrange an equality into two parts. The left-hand side (lhs)
	 * substituted through existing truths and replaced by the right-hand side
	 * (rhs). For example, in the equality <code>x+1 == y</code>, we may
	 * determine the lhs as <code>x</code> and the rhs as <code>y - 1</code>. A
	 * lexicographic ordering of terms is used to select the candidate for
	 * substitution, versus the rest.
	 *
	 * @param equality
	 *            --- The equality being rearranged
	 * @return
	 */
	public static Assignment rearrangeToAssignment(Formula.Equality equality) {
		if (equality instanceof Formula.ArithmeticEquality) {
			// Arithmetic equalities are a special case because we can actually
			// rearrange them.
			Formula.ArithmeticEquality e = (Formula.ArithmeticEquality) equality;
			Arithmetic.Polynomial lhs = Arithmetic.asPolynomial(e.getOperand(0));
			Arithmetic.Polynomial rhs = Arithmetic.asPolynomial(e.getOperand(1));
			Arithmetic.Polynomial diff = lhs.subtract(rhs);
			Polynomial.Term candidate = selectCandidateForSubstitution(diff);
			if(candidate == null) {
				return null;
			}
			Arithmetic.Polynomial bound = diff.subtract(candidate);
			if(candidate.getCoefficient().compareTo(BigInteger.ZERO) < 0) {
				candidate = candidate.negate();
			} else {
				bound = bound.negate();
			}
			if(candidate.getAtoms().length > 1) {
				throw new RuntimeException("Need support for non-linear arithmetic");
			} else if(candidate.getCoefficient().compareTo(BigInteger.ONE) != 0) {
				throw new RuntimeException("Need to fix this prexisting bug: " + candidate.getCoefficient());
			}
			return new Assignment(candidate.toExpression(),bound.toExpression(),equality);
		} else {
			// For non-arithmetic equalities, we can't rearrange them.
			// Therefore, there are relatively few options.
			Expr lhs = equality.getOperand(0);
			Expr rhs = equality.getOperand(1);
			//
			Expr candidate = min(lhs,rhs);
			Expr bound;
			if(candidate == null) {
				return null;
			} else {
				bound = max(lhs,rhs);
			}
			return new Assignment(candidate,bound,equality);
		}
	}

	/**
	 * Examine all terms in a polynomial to see whether any is a candidate for
	 * substitution or not. If one or more are found, then the least candidate
	 * is returned.
	 *
	 * @param p
	 * @return
	 */
	public static Polynomial.Term selectCandidateForSubstitution(Polynomial p) {
		Polynomial.Term candidate = null;
		for (int i = 0; i != p.size(); ++i) {
			Polynomial.Term term = p.getTerm(i);
			if (term.getAtoms().length > 0 && !hasRecursiveReference(term, p)) {
				candidate = selectCandidate(candidate,term);
			}
		}
		return candidate;
	}

	/**
	 * Given two candidate terms, select the best option.
	 *
	 * @param lhs
	 * @param rhs
	 * @return
	 */
	private static Polynomial.Term selectCandidate(Polynomial.Term lhs, Polynomial.Term rhs) {
		if (lhs == null) {
			return rhs;
		} else if (rhs == null) {
			return lhs;
		} else if (lessThan(lhs, rhs)) {
			return lhs;
		} else {
			return rhs;
		}
	}

	private static boolean lessThan(Polynomial.Term lhs, Polynomial.Term rhs) {
		Expr[] lhs_atoms = lhs.getAtoms();
		Expr[] rhs_atoms = rhs.getAtoms();
		//
		int lengthDifference = lhs_atoms.length - rhs_atoms.length;
		if (lengthDifference < 0) {
			return true;
		} else if (lengthDifference > 0) {
			return false;
		} else {
			for (int i = 0; i != lhs_atoms.length; ++i) {
				if (lessThan(lhs_atoms[i], rhs_atoms[i])) {
					return true;
				}
			}
			return false;
		}
	}

	private static boolean lessThan(Expr lhs, Expr rhs) {
		return lhs.getIndex() < rhs.getIndex();
	}

	public static Expr min(Expr lhs, Expr rhs) {
		if(isVariable(lhs) && isVariable(rhs)) {
			if(lessThan(lhs,rhs)) {
				return lhs;
			} else {
				return rhs;
			}
		} else if(isVariable(lhs)) {
			return lhs;
		} else if(isVariable(rhs)) {
			return rhs;
		} else {
			return null;
		}
	}

	public static Expr max(Expr lhs, Expr rhs) {
		Expr r = min(lhs,rhs);
		//
		if(r == lhs) {
			return rhs;
		} else if(r == rhs) {
			return lhs;
		} else {
			return null;
		}
	}

	private static boolean isVariable(Expr e) {
		switch(e.getOpcode()) {
		case EXPR_var:
		case EXPR_arridx:
		case EXPR_recfield:
		case EXPR_invoke:
		case EXPR_arrlen:
			return true;
		default:
			return false;
		}
	}

	/**
	 * Check whether a given polynomial contains a recursive reference to a
	 * given term. A recursive reference is simply an occurrence of the term as
	 * some component of a constructor contained within. For example, in
	 * <code>x</code> has a recursive reference in <code>x + y + f(x)</code>,
	 * whereas <code>y</code> does not.
	 *
	 * @param term
	 *            --- The term which we are checking to see whether it has a
	 *            recursive reference or not.
	 * @param poly
	 *            --- The polynomial within which we are looking for the
	 *            recursive reference.
	 * @return
	 */
	private static boolean hasRecursiveReference(Polynomial.Term term, Polynomial poly) {
		Expr[] atoms = term.getAtoms();
		//
		for (int i = 0; i != poly.size(); ++i) {
			Polynomial.Term t = poly.getTerm(i);
			// The polynomial is expected to contain the given term we're
			// looking for and, obviously, we don't want to use that when
			// looking for a recursive reference (since that would always be
			// true).
			if (t != term) {
				Expr[] t_atoms = t.getAtoms();
				for (int j = 0; j != atoms.length; ++j) {
					Expr atom = atoms[j];
					for (int k = 0; k != t_atoms.length; ++k) {
						if (isParentOf(t_atoms[k], atom)) {
							return true;
						}
					}
				}
			}
		}
		//
		return false;
	}

	/**
	 * Check whether a given expression is a parent of a given child. Or, put
	 * another way, whether the given parent contains the given child.
	 *
	 * @param parent
	 * @param child
	 * @return
	 */
	private static boolean isParentOf(Expr parent, Expr child) {
		if (parent.equals(child)) {
			return true;
		} else {
			for (int i = 0; i != parent.size(); ++i) {
				SyntacticItem pChild = parent.getOperand(i);
				if (pChild instanceof Expr && isParentOf((Expr) pChild, child)) {
					return true;
				}
			}
			return false;
		}
	}

	public static class Assignment {
		private final Expr lhs;
		private final Expr rhs;
		private final Formula dependency;

		public Assignment(Expr lhs, Expr rhs, Formula dep) {
			this.lhs = lhs;
			this.rhs = rhs;
			this.dependency = dep;
		}

		public Expr getLeftHandSide() {
			return lhs;
		}

		public Expr getRightHandSide() {
			return rhs;
		}

		public Formula getDependency() {
			return dependency;
		}
	}


	/**
	 * When generating an entirely new term within a given rule (i.e. one
	 * that has not been previously seen in the proof), we need to check
	 * whether it is the subject of some existing assignment or not.
	 *
	 * @param newTerm
	 * @return
	 */
	public SyntacticItem construct(Proof.State state, SyntacticItem term, Formula truth) {
		SyntacticItem[] children = term.getOperands();
		SyntacticItem[] nChildren = children;
		if(children != null) {
			for (int i = 0; i != children.length; ++i) {
				SyntacticItem child = children[i];
				SyntacticItem nChild;
				if (child instanceof Expr) {
					nChild = construct(state, (Expr) child, truth);
				} else if (child instanceof Tuple) {
					nChild = construct(state, (Tuple) child, truth);
				} else {
					nChild = child;
				}
				if (child != nChild && nChildren == children) {
					// Clone the new children array to avoid interfering
					// with original item.
					nChildren = Arrays.copyOf(children, children.length);
				}
				nChildren[i] = nChild;
			}
		}
		if (nChildren != children) {
			// At least one child was changed, therefore clone the original
			// item with the new children.
			term = (SyntacticItem) term.clone(nChildren);
		}
		if(term instanceof Expr) {
			return localConstruct(state,(Expr) term, truth);
		} else {
			return term;
		}
	}

	public Expr localConstruct(Proof.State state, Expr term, Formula truth) {
		Assignment assignment = lookupAssignment(state,term,truth);
		if (assignment != null) {
			return assignment.getRightHandSide();
		} else {
			return term;
		}
	}


	private Assignment lookupAssignment(Proof.State state, Expr term, Formula truth) {
		Proof.State parent = state.getParent();
		Proof.Delta.Set additions = state.getDelta().getAdditions();
		//
		for (int i = additions.size()-1; i >= 0; --i) {
			Formula f = additions.get(i);
			if (f instanceof Formula.Equality && f != truth) {
				Formula.Equality eq = (Formula.Equality) f;
				if(eq.getSign()) {
					CongruenceClosure.Assignment assign = CongruenceClosure.rearrangeToAssignment(eq);
					// FIXME: this is essentially pretty broken. Need to find a
					// much better way to handle congruence closure.
					if (assign != null && assign.getLeftHandSide().equals(term)) {
						return assign;
					}
				}
			}
		}
		if (parent == null) {
			return null;
		} else {
			return lookupAssignment(parent,term,truth);
		}
	}

}
