package wyal.rules;

import wyal.lang.Formula;
import wyal.lang.Proof;
import wyal.lang.SyntacticItem;
import wyal.lang.Proof.State;
import wyal.lang.WyalFile.Expr;
import wyal.lang.WyalFile.Pair;
import wyal.lang.WyalFile.Expr.Polynomial;
import wyal.util.Formulae;
import wyal.util.TypeSystem;

public class EqualityCongruence implements Proof.LinearRule {
	private final TypeSystem types;

	public EqualityCongruence(TypeSystem types) {
		this.types = types;
	}

	@Override
	public String getName() {
		return "Eq-S";
	}

	@Override
	public State apply(Proof.State state, Formula newTruth) {

		if(newTruth instanceof Formula.Equality) {
			Formula.Equality equality = (Formula.Equality) newTruth;
			// COUNTING. this is possible in congruence closure when you have
			// recursive predicates. For example, x == f(x) can ultimately give rise
			// to a sequence of applications end up with f(f(f(f(x)))), etc.
			Pair<Expr, Expr> substitution = rearrangeForSubstitution(equality);
			if(equality.getSign() && substitution != null) {
				// At this point, we have an equality which potentially could be
				// used to subsume one or more existing facts. Therefore, we need to
				// look back through the history to determine any cases where this
				// can be applied.
				Proof.Delta history = state.getDelta(null);
				Proof.Delta.Set additions = history.getAdditions();
				for(int i=0;i!=additions.size();++i) {
					Formula existingTruth = additions.get(i);
					if(existingTruth != newTruth) {
						Formula updatedTruth = (Formula) Formulae.substitute(substitution.getFirst(),
								substitution.getSecond(), existingTruth);
						if (existingTruth != updatedTruth) {
							updatedTruth = Formulae.simplifyFormula(updatedTruth, types);
							// The following is needed because substitution can
							// produce a different looking term which, after
							// simplification, is the same. To avoid this, we need
							// to avoid "recursive substitutions" somehow.
							if (!existingTruth.equals(updatedTruth)) {
								updatedTruth = state.allocate(updatedTruth);
								state = state.subsume(this, existingTruth, updatedTruth, equality);
							}
						}
					}
				}
			}
		}
		// No change in the normal case
		return state;
	}

	public static Pair<Expr, Expr> rearrangeForSubstitution(Formula.Equality f) {
		Expr candidate;
		Expr bound;
		if (f instanceof Formula.ArithmeticEquality) {
			// Arithmetic equalities are a special case because we can actually
			// rearrange them.
			Formula.ArithmeticEquality e = (Formula.ArithmeticEquality) f;
			Polynomial lhs = e.getOperand(0);
			Polynomial rhs = e.getOperand(1);
			Polynomial.Term lhsCandidate = selectCandidateForSubstitution(lhs,rhs);
			Polynomial.Term rhsCandidate = selectCandidateForSubstitution(rhs,lhs);
			if (lhsCandidate != null && rhsCandidate != null) {
				if (lhsCandidate.compareTo(rhsCandidate) < 0) {
					candidate = extractCandidate(lhsCandidate);
					bound = rhs.subtract(lhs.subtract(lhsCandidate));
				} else {
					candidate = extractCandidate(rhsCandidate);
					bound = lhs.subtract(rhs.subtract(rhsCandidate));
				}
			} else if (lhsCandidate != null) {
				candidate = extractCandidate(lhsCandidate);
				bound = rhs.subtract(lhs.subtract(lhsCandidate));
			} else if (rhsCandidate != null) {
				candidate = extractCandidate(rhsCandidate);
				bound = lhs.subtract(rhs.subtract(rhsCandidate));
			} else {
				return null;
			}
		} else {
			// For non-arithmetic equalities, we can't rearrange them.
			// Therefore, there are relatively few options.
			Expr lhs = f.getOperand(0);
			Expr rhs = f.getOperand(1);
			//
			if(lhs instanceof Expr.Constant && rhs instanceof Expr.Constant) {
				return null;
			} else if(lhs instanceof Expr.Constant) {
				candidate = rhs;
				bound = lhs;
			} else if(rhs instanceof Expr.Constant) {
				candidate = lhs;
				bound = rhs;
			} else if (lhs.compareTo(rhs) < 0) {
				candidate = lhs;
				bound = rhs;
			} else {
				candidate = rhs;
				bound = lhs;
			}
		}

		return new Pair<>(candidate, bound);
	}

	private static Expr extractCandidate(Polynomial.Term term) {
		return term.getAtoms()[0];
	}

	/**
	 * Examine all terms in a polynomial to see whether any is a candidate for
	 * substitution or not. If one or more are found, then the least candidate
	 * is returned.
	 *
	 * @param p
	 * @return
	 */
	public static Polynomial.Term selectCandidateForSubstitution(Polynomial p, Polynomial other) {
		Expr candidateAtom = null;
		Polynomial.Term candidate = null;
		for (int i = 0; i != p.size(); ++i) {
			Polynomial.Term term = p.getOperand(i);
			Expr[] atoms = term.getAtoms();
			if (term.getAtoms().length == 1) {
				Expr atom = atoms[0];
				// FIXME: the problem here is thatthe given polynomial is not
				// taking into account the other side of the equation, which may
				// contain a recursive reference.
				if ((candidate == null || atom.compareTo(candidateAtom) < 0) && !recursive(atom, i, p) && !recursive(atom, -1, other)) {
					candidate = term;
					candidateAtom = atom;
				}
			}
		}
		return candidate;
	}

	private static boolean recursive(Expr atom, int i, Polynomial p) {
		for (int j = 0; j != p.size(); ++j) {
			if (i != j) {
				Polynomial.Term term = p.getOperand(j);
				if (isParentOf(term,atom)) {
					return true;
				}
			}
		}
		return false;
	}

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
}
