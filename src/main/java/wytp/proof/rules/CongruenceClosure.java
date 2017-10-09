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
package wytp.proof.rules;

import java.util.List;

import wyal.heap.StructurallyEquivalentHeap;
import wyal.lang.WyalFile;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Arrays;

import static wyal.lang.WyalFile.*;
import wybs.lang.SyntacticItem;
import wybs.lang.SyntaxError;
import wybs.lang.NameResolver.ResolutionError;
import wybs.lang.SyntacticHeap;
import wytp.proof.Formula;
import wytp.proof.Proof;
import wytp.proof.Proof.State;
import wytp.proof.util.AbstractClosureRule;
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
public class CongruenceClosure extends AbstractClosureRule implements Proof.LinearRule {

	public CongruenceClosure(Simplification simplify,TypeSystem types) {
		super(simplify,types);
	}

	@Override
	public String getName() {
		return "Eq-S";
	}

	@Override
	public State apply(Proof.Delta.Set existingTruths, Proof.State head, Formula newTruth) throws ResolutionError {
		//
		ArrayList<Formula> dependencies = new ArrayList<>();
		Formula constructed = (Formula) construct(existingTruths, head, newTruth, newTruth, dependencies);
		if(constructed != newTruth && !constructed.equals(newTruth)) {
			Formula[] deps = dependencies.toArray(new Formula[dependencies.size()]);
			// NOTE: we need to allocated the constructed item here so that we
			// can use it within the substituteAgainstEquality() function below
			// if it's an equality.
			constructed = head.allocate(constructed);
			head = head.subsume(this, newTruth, constructed, deps);
		}
		// If the construct truth is still an equality then we need to apply
		// that through all existing terms.
		if (constructed instanceof Formula.Equality && ((Formula.Equality) constructed).getSign()) {
			head = substituteAgainstEquality(existingTruths, head, (Formula.Equality) constructed);
		}
		//
		return head;
	}

	private Proof.State substituteAgainstEquality(Proof.Delta.Set existingTruths, Proof.State head, Formula.Equality newTruth) throws ResolutionError {
		//
		if (newTruth.getSign()) {
			head = applyEqualityTypeAxiom(head, newTruth);
			//
			Assignment assignment = rearrangeToAssignment(newTruth);
			if (assignment != null) {
				return applyAssignment(assignment,existingTruths,head);
			}
		}
		return head;
	}

	private State applyEqualityTypeAxiom(Proof.State state, Formula.Equality newTruth) throws ResolutionError {
		Expr lhs = newTruth.get(0);
		Expr rhs = newTruth.get(1);
		Type lhsT = types.inferType(state.getTypeEnvironment(),lhs);
		Type rhsT = types.inferType(state.getTypeEnvironment(),rhs);
		if(lhsT == null || rhsT == null) {
			// Defer processing of this equality
			return state;
		} else {
			Type intersection = new Type.Intersection(new Type[]{lhsT,rhsT});
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
			return state.infer(this,simp.simplify(axiom),newTruth);
		}
	}

	private State applyAssignment(Assignment assignment, Proof.Delta.Set existingTruths, Proof.State head) throws ResolutionError {
		Formula newTruth = assignment.getDependency();
		//
		for (int i = 0; i != existingTruths.size(); ++i) {
			Formula existingTruth = existingTruths.get(i);
			//
			Formula updatedTruth = (Formula) substitute(assignment.getLeftHandSide(), assignment.getRightHandSide(),
					existingTruth);
			//
			if (existingTruth != updatedTruth) {
				// The following is needed because substitution can
				// produce a different looking term which, after
				// simplification, is the same. To avoid this, we
				// need to avoid "recursive substitutions" somehow.
				if (!existingTruth.equals(updatedTruth)) {
					head = head.subsume(this, existingTruth, updatedTruth, newTruth);
				}
			}
		}
		//
		return head;
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
			Arithmetic.Polynomial lhs = Arithmetic.asPolynomial(e.get(0));
			Arithmetic.Polynomial rhs = Arithmetic.asPolynomial(e.get(1));
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
				syntaxError("Need support for non-linear arithmetic", equality);
			} else if(candidate.getCoefficient().compareTo(BigInteger.ONE) != 0) {
				syntaxError("Need support for reasoning about rationals", equality);
			}
			return new Assignment(candidate.toExpression(),bound.toExpression(),equality);
		} else {
			// For non-arithmetic equalities, we can't rearrange them.
			// Therefore, there are relatively few options.
			Expr lhs = equality.get(0);
			Expr rhs = equality.get(1);
			//
			Expr candidate = min(lhs,rhs);
			Expr bound;
			if(candidate == null || hasRecursiveReference(lhs,rhs)) {
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
		// FIXME: this is *clearly* a hack
		long lhs_coeff = Math.abs(lhs.getCoefficient().longValue());
		long rhs_coeff = Math.abs(rhs.getCoefficient().longValue());
		//
		int lengthDifference = lhs_atoms.length - rhs_atoms.length;
		if (lengthDifference < 0) {
			return true;
		} else if (lengthDifference > 0) {
			return false;
		} else if(lhs_coeff == 1 && rhs_coeff != 1) {
			return true;
		} else if(lhs_coeff != 1 && rhs_coeff == 1) {
			return false;
		} else if(lhs_coeff != rhs_coeff) {
			return lhs_coeff < rhs_coeff;
		} else {
			for (int i = 0; i != lhs_atoms.length; ++i) {
				if (lessThan(lhs_atoms[i], rhs_atoms[i])) {
					return true;
				}
			}
			return false;
		}
	}

//	private static boolean lessThan(Expr lhs, Expr rhs) {
//		return lhs.getIndex() < rhs.getIndex();
//	}

	public static boolean lessThan(Expr lhs, Expr rhs) {
		int lhsOpcode = lhs.getOpcode();
		int rhsOpcode = rhs.getOpcode();
		if(lhsOpcode < rhsOpcode) {
			return true;
		} else if(lhsOpcode > rhsOpcode) {
			return false;
		} else {
			switch(lhsOpcode) {
			case EXPR_const:
				return lessThan((Expr.Constant) lhs, (Expr.Constant) rhs);
			case EXPR_varcopy:
				return lessThan((Expr.VariableAccess) lhs, (Expr.VariableAccess) rhs);
			case EXPR_recinit:
				return lessThan((Expr.RecordInitialiser) lhs, (Expr.RecordInitialiser) rhs);
			case EXPR_recfield:
				return lessThan((Expr.RecordAccess) lhs, (Expr.RecordAccess) rhs);
			case EXPR_recupdt:
				return lessThan((Expr.RecordUpdate) lhs, (Expr.RecordUpdate) rhs);
			case EXPR_invoke:
				return lessThan((Expr.Invoke) lhs, (Expr.Invoke) rhs);
			case EXPR_arridx:
				return lessThan((Expr.ArrayAccess) lhs, (Expr.ArrayAccess) rhs);
			case EXPR_arrlen:
				return lessThan((Expr.ArrayLength) lhs, (Expr.ArrayLength) rhs);
			case EXPR_arrinit:
				return lessThan((Expr.ArrayInitialiser) lhs, (Expr.ArrayInitialiser) rhs);
			case EXPR_arrupdt:
				return lessThan((Expr.ArrayUpdate) lhs, (Expr.ArrayUpdate) rhs);
			default:
//				return syntaxError("unknown expression encountered during congruence closure (" + lhs.getClass().getName() + ")", lhs);
				return lhs.getIndex() < rhs.getIndex();
			}
		}
	}

	public static boolean lessThan(Expr.Constant lhs, Expr.Constant rhs) {
		return lhs.getValue().compareTo(rhs.getValue()) < 0;
	}

	public static boolean lessThan(Expr.VariableAccess lhs, Expr.VariableAccess rhs) {
		// FIXME: could do this based on string as well?
		return lhs.getVariableDeclaration().getIndex() < rhs.getVariableDeclaration().getIndex();
	}

	public static boolean lessThan(Expr.ArrayAccess lhs, Expr.ArrayAccess rhs) {
		if(lessThan(lhs.getSource(),rhs.getSource())) {
			return true;
		} else if(lessThan(rhs.getSource(),lhs.getSource())) {
			return false;
		} else {
			return lessThan(lhs.getSubscript(),rhs.getSubscript());
		}
	}

	public static boolean lessThan(Expr.ArrayUpdate lhs, Expr.ArrayUpdate rhs) {
		if(lessThan(lhs.getSource(),rhs.getSource())) {
			return true;
		} else if(lessThan(rhs.getSource(),lhs.getSource())) {
			return false;
		} else if(lessThan(lhs.getSubscript(),rhs.getSubscript())){
			return true;
		} else if(lessThan(rhs.getSubscript(),lhs.getSubscript())) {
			return false;
		} else {
			return lessThan(lhs.getValue(),rhs.getValue());
		}
	}

	public static boolean lessThan(Expr.ArrayLength lhs, Expr.ArrayLength rhs) {
		return lessThan(lhs.getSource(),rhs.getSource());
	}

	public static boolean lessThan(Expr.ArrayInitialiser lhs, Expr.ArrayInitialiser rhs) {
		if (lhs.size() != rhs.size()) {
			return lhs.size() < rhs.size();
		} else {
			for (int i = 0; i != lhs.size(); ++i) {
				Expr larg = lhs.get(i);
				Expr rarg = rhs.get(i);
				if (lessThan(larg, rarg)) {
					return true;
				} else if (lessThan(rarg, larg)) {
					return false;
				}
			}
			return false;
		}
	}

	public static boolean lessThan(Expr.RecordAccess lhs, Expr.RecordAccess rhs) {
		if(lessThan(lhs.getSource(),rhs.getSource())) {
			return true;
		} else if(lessThan(rhs.getSource(),lhs.getSource())) {
			return false;
		} else {
			return lhs.getField().compareTo(rhs.getField()) < 0;
		}
	}

	public static boolean lessThan(Expr.RecordInitialiser lhs, Expr.RecordInitialiser rhs) {
		Pair<Identifier, Expr>[] lhsArgs = lhs.getFields();
		Pair<Identifier, Expr>[] rhsArgs = rhs.getFields();
		if (lhsArgs.length != rhsArgs.length) {
			return lhsArgs.length < rhsArgs.length;
		} else {
			for (int i = 0; i != lhsArgs.length; ++i) {
				Pair<Identifier, Expr> lp = lhsArgs[i];
				Pair<Identifier, Expr> rp = rhsArgs[i];
				int c = lp.getFirst().compareTo(rp.getSecond());
				if (c != 0) {
					return c < 0;
				}
				Expr larg = lp.getSecond();
				Expr rarg = rp.getSecond();
				if (lessThan(larg, rarg)) {
					return true;
				} else if (lessThan(rarg, larg)) {
					return false;
				}
			}
			return false;
		}
	}

	public static boolean lessThan(Expr.RecordUpdate lhs, Expr.RecordUpdate rhs) {
		if(lessThan(lhs.getSource(),rhs.getSource())) {
			return true;
		} else if(lessThan(rhs.getSource(),lhs.getSource())) {
			return false;
		} else if(lessThan(lhs.getValue(),rhs.getValue())){
			return true;
		} else if(lessThan(rhs.getValue(),lhs.getValue())) {
			return false;
		} else {
			return lhs.getField().compareTo(rhs.getField()) < 0;
		}
	}
	public static boolean lessThan(Expr.Invoke lhs, Expr.Invoke rhs) {
		Tuple<Expr> lhsArgs = lhs.getArguments();
		Tuple<Expr> rhsArgs = rhs.getArguments();
		int c = lhs.getName().compareTo(rhs.getName());
		if (c != 0) {
			return c < 0;
		} else if (lhsArgs.size() != rhsArgs.size()) {
			return lhsArgs.size() < rhsArgs.size();
		} else {
			for (int i = 0; i != lhsArgs.size(); ++i) {
				Expr larg = lhsArgs.get(i);
				Expr rarg = rhsArgs.get(i);
				if (lessThan(larg, rarg)) {
					return true;
				} else if (lessThan(rarg, larg)) {
					return false;
				}
			}
			return false;
		}
	}



	public static Expr min(Expr lhs, Expr rhs) {
		// First, prefer variables as these are always more useful.
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
		}
		// Second, take whatever has lowest index
		if(lessThan(lhs,rhs)) {
			return lhs;
		} else {
			return rhs;
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
		case EXPR_varcopy:
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
	 * Check whether the rhs contains a recursive reference to the lhs.
	 * @param lhs
	 * @param rhs
	 * @return
	 */
	private static boolean hasRecursiveReference(Expr lhs, Expr rhs) {
		return isParentOf(rhs,lhs);
	}

	/**
	 * Check whether a given expression is a parent of a given child. Or, put
	 * another way, whether the given parent contains the given child.
	 *
	 * @param parent
	 * @param child
	 * @return
	 */
	private static boolean isParentOf(SyntacticItem parent, Expr child) {
		if (parent.equals(child)) {
			return true;
		} else {
			for (int i = 0; i != parent.size(); ++i) {
				SyntacticItem pChild = parent.get(i);
				if (pChild != null && isParentOf(pChild, child)) {
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
	public SyntacticItem construct(Proof.Delta.Set existingTruths, Proof.State head, SyntacticItem term, Formula newTruth, List<Formula> dependencies) {
		SyntacticItem[] children = term.getAll();
		SyntacticItem[] nChildren = children;
		if(children != null) {
			for (int i = 0; i != children.length; ++i) {
				SyntacticItem child = children[i];
				SyntacticItem nChild;
				if (child instanceof Expr) {
					nChild = construct(existingTruths, head, (Expr) child, newTruth, dependencies);
				} else if (child instanceof Tuple) {
					nChild = construct(existingTruths, head, (Tuple) child, newTruth, dependencies);
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
			return localConstruct(existingTruths, head,(Expr) term, newTruth, dependencies);
		} else {
			return term;
		}
	}

	public Expr localConstruct(Proof.Delta.Set existingTruths, Proof.State head, Expr term, Formula newTruth, List<Formula> dependencies) {
		Assignment assignment = lookupAssignment(existingTruths, head, term, newTruth);
		if (assignment != null) {
			dependencies.add(assignment.dependency);
			return assignment.getRightHandSide();
		} else {
			return term;
		}
	}

	private Assignment lookupAssignment(Proof.Delta.Set existingTruths, Proof.State head, Expr term, Formula newTruth) {
		//
		for (int i = existingTruths.size() - 1; i >= 0; --i) {
			Formula existingTruth = existingTruths.get(i);
			//
			if (existingTruth instanceof Formula.Equality) {
				Formula.Equality eq = (Formula.Equality) existingTruth;
				if (eq.getSign()) {
					CongruenceClosure.Assignment assign = rearrangeToAssignment(eq);
					// FIXME: this is essentially pretty broken. Need to find a
					// much better way to handle congruence closure.
					if (assign != null && assign.getLeftHandSide().equals(term)) {
						return assign;
					}
				}
			}
		}
		return null;
	}
}
