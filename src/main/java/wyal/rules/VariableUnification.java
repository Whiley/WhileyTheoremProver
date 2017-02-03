package wyal.rules;

import java.math.BigInteger;
import java.util.Arrays;
import java.util.HashMap;

import wyal.lang.Formula;
import wyal.lang.Formula.Conjunct;
import wyal.lang.SyntacticItem;
import wyal.lang.WyalFile.Expr;
import wyal.lang.Formula.Polynomial;
import wyal.lang.WyalFile.Identifier;
import wyal.lang.WyalFile.Pair;
import wyal.lang.WyalFile.Tuple;
import wyal.util.AutomatedTheoremProver;
import wyal.util.Formulae;
import wyal.util.AutomatedTheoremProver.RewriteRule;

/**
 *
 * @author David J. Pearce
 *
 */
public class VariableUnification implements RewriteRule {

	@Override
	public Formula rewrite(Formula item) {
		if (item instanceof Conjunct) {
			return rewrite((Conjunct) item);
		} else {
			return item;
		}
	}

	private Formula rewrite(Conjunct item) {
		Formula[] children = item.getOperands();
		Formula[] nChildren = children;
		//
		for (int i = 0; i != children.length; ++i) {
			Formula f = children[i];
			if (f instanceof Formula.Equality) {
				Formula.Equality eq = (Formula.Equality) f;
				if (eq.getSign()) {
					Pair<Identifier, Formula.Atom> substitution = rearrangeForSubstitution(eq);
					nChildren = applySubstitution(substitution, i, nChildren, children == nChildren);
				}
			}
		}
		//
		if (children != nChildren) {
			// Something changed
			return Formulae.and(nChildren);
		} else {
			return item;
		}
	}

	private Formula[] applySubstitution(Pair<Identifier, Formula.Atom> substitution, int ignored, Formula[] children,
			boolean shared) {
		if (substitution != null) {
			// We've found a suitable substitution
			for (int j = 0; j != children.length; ++j) {
				if (j != ignored) {
					Formula before = children[j];
					Formula after = substituteFormula(substitution, before);
					if(before != after) {
						System.out.print("REWROTE: ");
						AutomatedTheoremProver.print(before);
						System.out.print(" -----> ");
						AutomatedTheoremProver.print(after);
					}
					if (before != after && shared) {
						children = Arrays.copyOf(children, children.length);
					}
					children[j] = after;
				}
			}
		}
		return children;
	}

	private Pair<Identifier, Formula.Atom> rearrangeForSubstitution(Formula.Equality f) {
		Identifier var;
		Formula.Atom bound;
		if (f instanceof Formula.ArithmeticEquality) {
			// Arithmetic equalities are a special case because we can actually
			// rearrange them.
			Formula.ArithmeticEquality e = (Formula.ArithmeticEquality) f;
			Polynomial lhs = e.getOperand(0);
			Polynomial rhs = e.getOperand(1);
			Polynomial.Term lhsCandidate = selectCandidateForSubstitution(lhs);
			Polynomial.Term rhsCandidate = selectCandidateForSubstitution(rhs);
			if (lhsCandidate != null && rhsCandidate != null) {
				Identifier var1 = extractCandidateName(lhsCandidate);
				Identifier var2 = extractCandidateName(rhsCandidate);
				if (var1.compareTo(var2) <= 0) {
					var = var1;
					bound = rhs.subtract(lhs.subtract(lhsCandidate));
				} else {
					var = var2;
					bound = lhs.subtract(rhs.subtract(lhsCandidate));
				}
			} else if (lhsCandidate != null) {
				var = extractCandidateName(lhsCandidate);
				bound = rhs.subtract(lhs.subtract(lhsCandidate));
			} else if (rhsCandidate != null) {
				var = extractCandidateName(rhsCandidate);
				bound = lhs.subtract(rhs.subtract(rhsCandidate));
			} else {
				return null;
			}
		} else {
			// For non-arithmetic equalities, we can't rearrange them.
			// Therefore, there are relatively few options.
			Formula.Atom lhs = f.getOperand(0);
			Formula.Atom rhs = f.getOperand(1);
			//
			if (lhs instanceof Expr.VariableAccess && rhs instanceof Expr.VariableAccess) {
				Identifier v1 = ((Expr.VariableAccess) lhs).getVariableDeclaration().getVariableName();
				Identifier v2 = ((Expr.VariableAccess) rhs).getVariableDeclaration().getVariableName();
				if (v1.compareTo(v2) <= 0) {
					var = v1;
					bound = rhs;
				} else {
					var = v2;
					bound = lhs;
				}
			} else if (lhs instanceof Expr.VariableAccess) {
				Expr.VariableAccess v = (Expr.VariableAccess) lhs;
				var = v.getVariableDeclaration().getVariableName();
				bound = rhs;
			} else if (rhs instanceof Expr.VariableAccess) {
				Expr.VariableAccess v = (Expr.VariableAccess) rhs;
				var = v.getVariableDeclaration().getVariableName();
				bound = lhs;
			} else {
				// no option here
				return null;
			}
		}

		System.out.print("FOUND SUBSTITUTION: " + var + " ==> ");
		AutomatedTheoremProver.println(bound);
		return new Pair<>(var, bound);
	}

	/**
	 * Examine all terms in a polynomial to see whether any is a candidate for
	 * substitution or not. If one or more are found, then the least candidate
	 * is returned.
	 *
	 * @param p
	 * @return
	 */
	private Polynomial.Term selectCandidateForSubstitution(Polynomial p) {
		Polynomial.Term candidate = null;
		Identifier candidateVar = null;
		for (int i = 0; i != p.size(); ++i) {
			Polynomial.Term term = p.getOperand(0);
			if (isCandidate(term)) {
				Identifier var = extractCandidateName(term);
				if (candidateVar == null || var.compareTo(candidateVar) < 0) {
					candidateVar = var;
					candidate = term;
				}
			}
		}
		return candidate;
	}

	/**
	 * Determine whether a given polynomial term is a candidate for
	 * substitution. A candidate must be a single atom with a trivial
	 * coefficient (i.e. 1). At this time, a candidate must also be a variable
	 * access (though this may be later relaxed).
	 *
	 * @param term
	 * @return
	 */
	public boolean isCandidate(Polynomial.Term term) {
		Tuple<Formula.Atom> atoms = term.getAtoms();
		BigInteger coefficient = term.getCoefficient().get();
		if (atoms.size() == 1 && coefficient.equals(BigInteger.ONE)) {
			// FIXME: can we substitute for things other than a variable access?
			// I think perhapds we should be able to.
			return atoms.getOperand(0) instanceof Expr.VariableAccess;
		} else {
			return false;
		}
	}

	/**
	 * Extract the name of a candidate. That is, the variable which is being
	 * rearranged for. This is necessary to determine whether a given candidate
	 * is the <i>least</i> candidate or not.
	 *
	 * @param term
	 * @return
	 */
	private Identifier extractCandidateName(Polynomial.Term term) {
		Expr.VariableAccess va = (Expr.VariableAccess) term.getAtoms().getOperand(0);
		return va.getVariableDeclaration().getVariableName();
	}

	private Formula.Atom substitute(Pair<Identifier, Formula.Atom> substitution, Formula.Atom item) {
		switch (item.getOpcode()) {
		case EXPR_const:
			return item;
		case EXPR_var: {
			// In this case, we might be able to make a substitution.
			Expr.VariableAccess v = (Expr.VariableAccess) item;
			Identifier name = v.getVariableDeclaration().getVariableName();
			if (name.equals(substitution.getFirst())) {
				// Yes, we made a substitution!
				return substitution.getSecond();
			}
			return item;
		}
		case EXPR_add: {
			return substitutePolynomial(substitution, (Polynomial) item);
		}
		case EXPR_mul: {
			return substitutePolynomialTerm(substitution, (Polynomial.Term) item);
		}
		default:
			throw new IllegalArgumentException("invalid expression opcode: " + item.getOpcode());
		}
	}

	private Formula substituteFormula(Pair<Identifier, Formula.Atom> substitution, Formula item) {
		switch (item.getOpcode()) {
		case EXPR_or: {
			Formula.Disjunct disjunct = (Formula.Disjunct) item;
			Formula[] children = disjunct.getOperands();
			Formula[] nChildren = substitute(substitution, children);
			if (children != nChildren) {
				return Formulae.or(nChildren);
			} else {
				return item;
			}
		}
		case EXPR_and: {
			Formula.Conjunct conjunct = (Formula.Conjunct) item;
			Formula[] children = conjunct.getOperands();
			Formula[] nChildren = substitute(substitution, children);
			if (children != nChildren) {
				return Formulae.and(nChildren);
			} else {
				return item;
			}
		}
		case EXPR_forall:
		case EXPR_exists: {
			Formula.Quantifier quantifier = (Formula.Quantifier) item;
			Formula body = quantifier.getBody();
			Formula nBody = substituteFormula(substitution, body);
			if (body == nBody) {
				return item;
			} else if (quantifier.getSign()) {
				return Formula.forall(quantifier.getParameters(), nBody);
			} else {
				return Formula.exists(quantifier.getParameters(), nBody);
			}
		}
		case EXPR_eq:
		case EXPR_neq: {
			Formula.Equality equality = (Formula.Equality) item;
			Formula.Atom[] children = equality.getOperands();
			Formula.Atom[] nChildren = substitute(substitution, children);
			if (children == nChildren) {
				return item;
			} else if(equality.getSign()){
				return Formulae.equal(nChildren[0], nChildren[1]);
			} else {
				return Formulae.notEqual(nChildren[0], nChildren[1]);
			}
		}
		case EXPR_lt:
		case EXPR_gteq: {
			Formula.Inequality inequality = (Formula.Inequality) item;
			Formula.Atom[] children = inequality.getOperands();
			Formula.Atom[] nChildren = substitute(substitution, children);
			if (children == nChildren) {
				return item;
			} else if (inequality.getSign()) {
				return Formulae.lessThan((Polynomial) nChildren[0], (Polynomial) nChildren[1]);
			} else {
				return Formulae.greaterThanOrEqual((Polynomial) nChildren[0], (Polynomial) nChildren[1]);
			}
		}
		default:
			throw new IllegalArgumentException("invalid formual opcode");
		}
	}

	private Polynomial substitutePolynomial(Pair<Identifier, Formula.Atom> substitution, Polynomial p) {
		Polynomial.Term[] children = p.getOperands();
		Expr[] nChildren = children;
		for (int i = 0; i != children.length; ++i) {
			Polynomial.Term before = children[i];
			Formula.Atom after = substitutePolynomialTerm(substitution, before);
			if (before != after && nChildren == children) {
				// Cannot use Arrays.copyOf here as this introduces a bug.
				nChildren = new Expr[children.length];
				System.arraycopy(children, 0, nChildren, 0, children.length);
			}
			nChildren[i] = after;
		}
		if (nChildren == children) {
			return p;
		} else {
			return flatternPolynomial(nChildren);
		}
	}

	private Formula.Atom substitutePolynomialTerm(Pair<Identifier, Formula.Atom> substitution, Polynomial.Term p) {
		Formula.Atom[] children = p.getOperands();
		Formula.Atom[] nChildren = substitute(substitution, children);
		if (children == nChildren) {
			return p;
		} else {
			for (int i = 0; i != nChildren.length; ++i) {
				if (nChildren[i] instanceof Polynomial) {
					return evaluatePolynomialTerm(nChildren);
				}
			}
			return p.clone(nChildren);
		}
	}

	private Polynomial evaluatePolynomialTerm(Formula.Atom[] children) {
		Polynomial p = new Polynomial(BigInteger.ONE);
		for (int i = 0; i != children.length; ++i) {
			Expr child = children[i];
			if (child instanceof Polynomial) {
				p = p.multiply((Polynomial) child);
			} else {
				p = p.multiply(Polynomials.toPolynomial(child));
			}
		}
		return p;
	}

	private Polynomial flatternPolynomial(Formula.Atom[] children) {
		int count = 0;
		for (int i = 0; i != children.length; ++i) {
			Expr child = children[i];
			if (child instanceof Polynomial) {
				count++;
			}
		}
		if (count == 0) {
			return Formula.sum((Polynomial.Term[]) children);
		} else {
			Polynomial p = new Polynomial(BigInteger.ZERO);
			for (int i = 0; i != children.length; ++i) {
				Expr child = children[i];
				if (child instanceof Polynomial) {
					p = p.add((Polynomial) child);
				} else {
					p = Formulae.add(p, (Polynomial.Term) child);
				}
			}
			return p;
		}
	}

	public static Polynomial sum(Polynomial.Term... terms) {
		Polynomial.Term[] nTerms = Arrays.copyOf(terms, terms.length);
		// FIXME: this is not the ideal way to do this.
		return Formulae.toNormalForm(nTerms);
	}

	/**
	 * Substitute through an array of syntactic formulae.
	 *
	 * @param substitution
	 * @param children
	 * @return
	 */
	private Formula[] substitute(Pair<Identifier, Formula.Atom> substitution, Formula[] children) {
		Formula[] nChildren = children;
		for (int i = 0; i != children.length; ++i) {
			Formula before = children[i];
			Formula after = substituteFormula(substitution, before);
			if (before != after && nChildren == children) {
				nChildren = Arrays.copyOf(children, children.length);
			}
			nChildren[i] = after;
		}
		return nChildren;
	}

	/**
	 * Substitute through an array of syntactic atom.
	 *
	 * @param substitution
	 * @param children
	 * @return
	 */
	private Formula.Atom[] substitute(Pair<Identifier, Formula.Atom> substitution, Formula.Atom[] children) {
		Formula.Atom[] nChildren = children;
		for (int i = 0; i != children.length; ++i) {
			Formula.Atom before = children[i];
			Formula.Atom after = substitute(substitution, before);
			if (before != after && nChildren == children) {
				nChildren = Arrays.copyOf(children, children.length);
			}
			nChildren[i] = after;
		}
		return nChildren;
	}
}
