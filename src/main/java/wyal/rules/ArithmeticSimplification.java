package wyal.rules;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Arrays;

import wyal.lang.SyntacticItem;
import wyal.lang.WyalFile.Value;
import wyal.lang.WyalFile.Expr;
import wyal.lang.WyalFile.Expr.Polynomial;
import wyal.lang.WyalFile.Opcode;
import wyal.lang.WyalFile.Tuple;
import wyal.util.AutomatedTheoremProver.RewriteRule;

public class ArithmeticSimplification implements RewriteRule {

	@Override
	public SyntacticItem rewrite(SyntacticItem item) {
		switch (item.getOpcode()) {
		case EXPR_eq:
		case EXPR_neq:
			// FIXME: above two cases broken as need to know if integer
			// comparison or not.
		case EXPR_lt:
		case EXPR_lteq:
		case EXPR_gt:
		case EXPR_gteq: {
			return simplifyEquation((Expr.Operator) item);
		}
		}
		return item;
	}

	private Expr simplifyEquation(Expr.Operator expr) {
		Expr[] children = expr.getOperands();
		Expr[] nChildren = toPolynomial(children);
		Polynomial lhs = (Polynomial) nChildren[0];
		Polynomial rhs = (Polynomial) nChildren[1];
		if (isConstant(lhs) && isConstant(rhs)) {
			return evaluateEquation(expr.getOpcode(), asConstant(lhs), asConstant(rhs));
		} else if ((isZero(lhs) || isZero(rhs)) && children == nChildren) {
			// Equation already in normal form, and cannot be reduced further.
			// Therefore, no need to do anything else
			return expr;
		} else {
			int lhsSigns = countSigns(lhs);
			int rhsSigns = countSigns(rhs);
			if(lhsSigns < rhsSigns) {
				rhs = subtract(rhs, lhs);
				lhs = new Polynomial(BigInteger.ZERO);
			} else {
				lhs = subtract(lhs, rhs);
				rhs = new Polynomial(BigInteger.ZERO);
			}
			return expr.clone(new Expr[]{lhs, rhs});
		}
	}

	private int countSigns(Polynomial p) {
		int signs = 0;
		for(int i=0;i!=p.size();++i) {
			Polynomial.Term term = p.getOperand(i);
			BigInteger b = term.getCoefficient().get();
			int c = b.compareTo(BigInteger.ZERO);
			if(c < 0) {
				signs = signs - 1;
			} else {
				signs = signs + 1;
			}
		}
		return signs;
	}

	/**
	 * Check whether a polynomial is a constant or not.
	 *
	 * @param p
	 * @return
	 */
	private boolean isConstant(Polynomial p) {
		return p.size() == 1 && p.getOperand(0).getAtoms().size() == 0;
	}

	/**
	 * Check whether a polynomial is a constant or not.
	 *
	 * @param p
	 * @return
	 */
	private boolean isZero(Polynomial p) {
		if (p.size() == 1) {
			Polynomial.Term term = p.getOperand(0);
			if (term.getAtoms().size() == 0) {
				BigInteger coefficient = term.getCoefficient().get();
				return coefficient.equals(BigInteger.ZERO);
			}
		}
		return false;
	}

	/**
	 * Check whether a polynomial is a constant or not.
	 *
	 * @param p
	 * @return
	 */
	private BigInteger asConstant(Polynomial p) {
		if (p.size() == 1) {
			Polynomial.Term term = p.getOperand(0);
			if (term.getAtoms().size() == 0) {
				return term.getCoefficient().get();
			}
		}
		throw new IllegalArgumentException("polynomial is not constant");
	}

	private Expr.Constant evaluateEquation(Opcode opcode, BigInteger lhs, BigInteger rhs) {
		boolean result;
		switch (opcode) {
		case EXPR_eq:
			result = lhs.equals(rhs);
			break;
		case EXPR_neq:
			result = !(lhs.equals(rhs));
			break;
		case EXPR_lt:
			result = lhs.compareTo(rhs) < 0;
			break;
		case EXPR_lteq:
			result = lhs.compareTo(rhs) <= 0;
			break;
		case EXPR_gt:
			result = lhs.compareTo(rhs) > 0;
			break;
		case EXPR_gteq:
			result = lhs.compareTo(rhs) >= 0;
			break;
		default:
			throw new IllegalArgumentException("Invalid equation opcode: " + opcode);
		}
		return new Expr.Constant(new Value.Bool(result));
	}

	/**
	 * Recursively simplify a sequence of zero or more expressions. If no
	 * simplifications occur, then the original array is returned untouched.
	 *
	 * @param children
	 * @return
	 */
	private Expr[] toPolynomial(Expr... children) {
		Expr[] nChildren = children;

		for (int i = 0; i != nChildren.length; ++i) {
			Expr child = children[i];
			Polynomial nChild = toPolynomial(child);
			if (child != nChild && children == nChildren) {
				nChildren = Arrays.copyOf(children, children.length);
			}
			nChildren[i] = nChild;
		}
		//
		return nChildren;
	}


	/**
	 * Convert an arbitrary expression to a polynomial.
	 *
	 * @param e
	 * @return
	 */
	private Polynomial toPolynomial(Expr e) {
		switch (e.getOpcode()) {
		case EXPR_poly:
			return (Polynomial) e;
		case EXPR_const:
			return toPolynomial((Expr.Constant) e);
		case EXPR_invoke:
		case EXPR_arridx:
		case EXPR_var:
			return toUnitPolynomial(e);
		case EXPR_add:
		case EXPR_mul:
		case EXPR_sub: {
			Expr.Operator op = (Expr.Operator) e;
			return toPolynomial(e.getOpcode(), op.getOperands());
		}
		default:
			throw new IllegalArgumentException("cannot convert expression to polynomial");
		}
	}

	private Polynomial toPolynomial(Expr.Constant e) {
		Value.Int c = (Value.Int) e.getValue();
		return new Polynomial(new Polynomial.Term(c));
	}

	private Polynomial toUnitPolynomial(Expr e) {
		Tuple<Expr> vs = new Tuple<>(e);
		return new Polynomial(new Polynomial.Term(new Value.Int(1), vs));
	}

	private Polynomial toPolynomial(Opcode opcode, Expr... children) {
		Polynomial result = toPolynomial(children[0]);
		switch (opcode) {
		case EXPR_add: {
			for (int i = 1; i != children.length; ++i) {
				result = add(result, toPolynomial(children[i]));
			}
			break;
		}
		case EXPR_sub: {
			for (int i = 1; i != children.length; ++i) {
				result = subtract(result, toPolynomial(children[i]));
			}
			break;
		}
		case EXPR_mul: {
			for (int i = 1; i != children.length; ++i) {
				result = multiply(result, toPolynomial(children[i]));
			}
			break;
		}
		default:
			throw new IllegalArgumentException("IMPLEMENT ME");
		}

		return result;
	}

	/**
	 * Multiply two polynomials together. This is done by reusing the add()
	 * function as much as possible, though this may not be the most efficient.
	 * In essence, to multiply one polynomial (e.g. <code>2+2x</code>) by
	 * another (e.g.<code>1+3x+4y</code>) it breaks it down into a series of
	 * multiplications over terms and additions. That is, we multiply each term
	 * from the first polynomial by the second (e.g. <code>2*(1+3x+4y)</code>
	 * and <code>2x*(1+3x+4y)</code>). Then, we add the results together (e.g.
	 * <code>(2+6x+8y) + (2x+6x2+8xy)</code>).
	 *
	 * @param lhs
	 * @param rhs
	 * @return
	 */
	private Polynomial multiply(Polynomial lhs, Polynomial rhs) {
		ArrayList<Polynomial.Term> terms = new ArrayList<>();

		for (int i = 0; i != lhs.size(); ++i) {
			Polynomial.Term lhsTerm = lhs.getOperand(i);
			for (int j = 0; j != rhs.size(); ++j) {
				Polynomial.Term rhsTerm = rhs.getOperand(j);
				terms.add(multiply(lhsTerm, rhsTerm));
			}
		}

		return toNormalForm(terms);
	}

	/**
	 * Multiply two polynomial terms together. For example, multiplying
	 * <code>4xy</code> by <code>2x</code> gives <code>8x^2y</code>.
	 *
	 * @param lhs
	 * @param rhs
	 * @return
	 */
	private Polynomial.Term multiply(Polynomial.Term lhs, Polynomial.Term rhs) {
		BigInteger lhsCoeff = lhs.getCoefficient().get();
		BigInteger rhsCoeff = rhs.getCoefficient().get();
		Tuple<Expr> lhsAtoms = lhs.getAtoms();
		Tuple<Expr> rhsAtoms = rhs.getAtoms();
		Expr[] atoms = new Expr[lhsAtoms.size() + rhsAtoms.size()];
		System.arraycopy(lhsAtoms.getOperands(), 0, atoms, 0, lhsAtoms.size());
		System.arraycopy(rhsAtoms.getOperands(), 0, atoms, lhsAtoms.size(), rhsAtoms.size());
		Arrays.sort(atoms);
		Value.Int coefficient = new Value.Int(lhsCoeff.multiply(rhsCoeff));
		return new Polynomial.Term(coefficient, new Tuple<>(atoms));
	}

	/**
	 * A simple implementation of polynomial subtraction.
	 *
	 * @param lhs
	 * @param rhs
	 * @return
	 */
	private Polynomial subtract(Polynomial lhs, Polynomial rhs) {
		return add(lhs, negate(rhs));
	}

	/**
	 * <p>
	 * Add two polynomials together, producing a polynomial in normal form. To
	 * do this, we must add the coefficients for terms which have the same set
	 * of atoms, whilst other terms are incorporated as is. For example,
	 * consider adding <code>2+2x</code> with <code>1+3x+4y</code>. In this
	 * case, we have some terms in common, so the result becomes
	 * <code>(2+1) + (2x+3x) + 4y</code> which is simplified to
	 * <code>3 + 5x + 4y</code>.
	 * </p>
	 *
	 * @param sign
	 * @param lhs
	 * @param rhs
	 * @return
	 */
	private Polynomial add(Polynomial lhs, Polynomial rhs) {
		ArrayList<Polynomial.Term> terms = new ArrayList<>();
		for (int i = 0; i != lhs.size(); ++i) {
			terms.add(lhs.getOperand(i));
		}
		for (int j = 0; j != rhs.size(); ++j) {
			terms.add(rhs.getOperand(j));
		}
		return toNormalForm(terms);
	}

	/**
	 * A simple implementation of polynomial negation. This simple negates the
	 * coefficient of each term.
	 *
	 * @param p
	 * @return
	 */
	private Polynomial negate(Polynomial p) {
		Polynomial.Term[] terms = new Polynomial.Term[p.size()];

		for (int i = 0; i != terms.length; ++i) {
			Polynomial.Term pTerm = p.getOperand(i);
			BigInteger coeff = pTerm.getCoefficient().get();
			terms[i] = new Polynomial.Term(new Value.Int(coeff.negate()), pTerm.getSecond());
		}

		return new Polynomial(terms);
	}

	/**
	 * Given a list of unsorted and potentially overlapping terms, apply the
	 * necessary simplifications to produce a polynomial in normal form. For
	 * example, given <code>[2, 7x, 4y, -x]</code> we would end up with
	 * <code>[1, 3x, 2y]</code>.
	 *
	 * @param terms
	 * @return
	 */
	private Polynomial toNormalForm(ArrayList<Polynomial.Term> terms) {
		for (int i = 0; i != terms.size(); ++i) {
			Polynomial.Term ith = terms.get(i);
			if (ith != null) {
				if (isZero(ith)) {
					// Eliminate any zeros which may have arisen during the calculation.
					terms.set(i,null);
				} else {
					Tuple<Expr> ithAtoms = ith.getAtoms();
					for (int j = i + 1; j != terms.size(); ++j) {
						Polynomial.Term jth = terms.get(j);
						if (jth != null && ithAtoms.equals(jth.getAtoms())) {
							// We have two overlapping terms, namely i and j.
							// Add them together and assign the result to the
							// jth
							// position.
							terms.set(j, add(ith, jth));
							terms.set(i, null);
							break;
						}
					}
				}
			}
		}

		// strip out null entries, factorise and we're done!
		return new Polynomial(cancel(terms));
	}

	private boolean isZero(Polynomial.Term term) {
		BigInteger coefficient = term.getCoefficient().get();
		return coefficient.equals(BigInteger.ZERO);
	}

	private Polynomial.Term add(Polynomial.Term lhs, Polynomial.Term rhs) {
		BigInteger lhsCoeff = lhs.getCoefficient().get();
		BigInteger rhsCoeff = rhs.getCoefficient().get();
		BigInteger r = lhsCoeff.add(rhsCoeff);
		if (r.equals(BigInteger.ZERO)) {
			return null;
		} else {
			return new Polynomial.Term(new Value.Int(r), lhs.getAtoms());
		}
	}

	private Polynomial.Term[] factorise(Polynomial.Term... terms) {
		BigInteger factor = terms[0].getCoefficient().get();
		for (int i = 1; i != terms.length; ++i) {
			factor = factor.gcd(terms[1].getCoefficient().get());
		}
		if (!factor.equals(BigInteger.ONE)) {
			// Found a non-trivial factor, therefore divide each term by it.
			for (int i = 0; i != terms.length; ++i) {
				Polynomial.Term term = terms[i];
				BigInteger coefficient = term.getCoefficient().get().divide(factor);
				terms[i] = new Polynomial.Term(new Value.Int(coefficient), term.getAtoms());
			}
		}
		// FIXME: we should ideally sort terms here!!!
		return terms;
	}

	private Polynomial.Term[] cancel(ArrayList<Polynomial.Term> terms) {
		int count = 0;
		for (int i = 0; i != terms.size(); ++i) {
			if (terms.get(i) != null) {
				count = count + 1;
			}
		}
		if (count == 0) {
			return new Polynomial.Term[] { new Polynomial.Term(BigInteger.ZERO) };
		} else {
			//
			Polynomial.Term[] nTerms = new Polynomial.Term[count];
			for (int i = 0, j = 0; i != terms.size(); ++i) {
				Polynomial.Term term = terms.get(i);
				if (term != null) {
					nTerms[j++] = term;
				}
			}
			//
			return nTerms;
		}
	}

	/**
	 * This determines an upper bound on the number of resulting terms from
	 * either adding or subtracting the two polynomials. It is an upper bound
	 * because it does not take into consideration the possibility of matching
	 * terms which evaluate to zero.
	 *
	 * @param lhs
	 * @param rhs
	 * @return
	 */
	private int estimateMaximumResultingTerms(Polynomial lhs, Polynomial rhs) {
		int count = 0;
		int i = 0;
		int j = 0;
		while (i < lhs.size() && j < rhs.size()) {
			int l_index = lhs.getOperand(i).getSecond().getIndex();
			int r_index = rhs.getOperand(j).getSecond().getIndex();
			if (l_index < r_index) {
				i = i + 1;
			} else if (l_index > r_index) {
				j = j + 1;
			} else {
				i = i + 1;
				j = j + 1;
			}
			count = count + 1;
		}
		//
		return count + (lhs.size() - i) + (rhs.size() - j);
	}
}
