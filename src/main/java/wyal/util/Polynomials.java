package wyal.util;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Arrays;

import wyal.lang.WyalFile.Expr;
import wyal.lang.WyalFile.Opcode;
import wyal.lang.WyalFile.Tuple;
import wyal.lang.WyalFile.Value;
import wyal.lang.WyalFile.Expr.Polynomial;

public class Polynomials {

	/**
	 * Recursively simplify a sequence of zero or more expressions. If no
	 * simplifications occur, then the original array is returned untouched.
	 *
	 * @param children
	 * @return
	 */
	public static Expr[] toPolynomial(Expr... children) {
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
	public static Polynomial toPolynomial(Expr e) {
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

	private static Polynomial toPolynomial(Expr.Constant e) {
		Value.Int c = (Value.Int) e.getValue();
		return new Polynomial(new Polynomial.Term(c));
	}

	private static Polynomial toUnitPolynomial(Expr e) {
		Tuple<Expr> vs = new Tuple<>(e);
		return new Polynomial(new Polynomial.Term(new Value.Int(1), vs));
	}

	private static Polynomial toPolynomial(Opcode opcode, Expr... children) {
		Polynomial result = toPolynomial(children[0]);
		switch (opcode) {
		case EXPR_add: {
			for (int i = 1; i != children.length; ++i) {
				result = result.add(toPolynomial(children[i]));
			}
			break;
		}
		case EXPR_sub: {
			for (int i = 1; i != children.length; ++i) {
				result = result.subtract(toPolynomial(children[i]));
			}
			break;
		}
		case EXPR_mul: {
			for (int i = 1; i != children.length; ++i) {
				result = result.multiply(toPolynomial(children[i]));
			}
			break;
		}
		default:
			throw new IllegalArgumentException("IMPLEMENT ME");
		}

		return result;
	}

	/**
	 * A simple implementation of polynomial negation. This simply negates the
	 * coefficient of each term.
	 *
	 * @param p
	 * @return
	 */
	public static Polynomial negate(Polynomial p) {
		Polynomial.Term[] terms = new Polynomial.Term[p.size()];

		for (int i = 0; i != terms.length; ++i) {
			terms[i] = negate(p.getOperand(i));
		}

		return new Polynomial(terms);
	}

	public static Polynomial.Term negate(Polynomial.Term p) {
		BigInteger coeff = p.getCoefficient().get();
		return new Polynomial.Term(new Value.Int(coeff.negate()), p.getSecond());
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
	public static Polynomial add(Polynomial lhs, Polynomial rhs) {
		ArrayList<Polynomial.Term> terms = new ArrayList<>();
		for (int i = 0; i != lhs.size(); ++i) {
			terms.add(lhs.getOperand(i));
		}
		for (int j = 0; j != rhs.size(); ++j) {
			terms.add(rhs.getOperand(j));
		}
		return toNormalForm(terms);
	}

	public static Polynomial add(Polynomial lhs, Polynomial.Term rhs) {
		ArrayList<Polynomial.Term> terms = new ArrayList<>();
		for (int i = 0; i != lhs.size(); ++i) {
			terms.add(lhs.getOperand(i));
		}
		terms.add(rhs);
		return toNormalForm(terms);
	}

	public static Polynomial.Term add(Polynomial.Term lhs, Polynomial.Term rhs) {
		BigInteger lhsCoeff = lhs.getCoefficient().get();
		BigInteger rhsCoeff = rhs.getCoefficient().get();
		BigInteger r = lhsCoeff.add(rhsCoeff);
		if (r.equals(BigInteger.ZERO)) {
			return null;
		} else {
			return new Polynomial.Term(new Value.Int(r), lhs.getAtoms());
		}
	}

	/**
	 * A simple implementation of polynomial subtraction.
	 *
	 * @param lhs
	 * @param rhs
	 * @return
	 */
	public static Polynomial subtract(Polynomial lhs, Polynomial rhs) {
		return add(lhs, negate(rhs));
	}

	/**
	 * A simple implementation of polynomial subtraction.
	 *
	 * @param lhs
	 * @param rhs
	 * @return
	 */
	public static Polynomial subtract(Polynomial lhs, Polynomial.Term rhs) {
		return add(lhs, negate(rhs));
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
	public static Polynomial multiply(Polynomial lhs, Polynomial rhs) {
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
	public static Polynomial.Term multiply(Polynomial.Term lhs, Polynomial.Term rhs) {
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
	 * Given a list of unsorted and potentially overlapping terms, apply the
	 * necessary simplifications to produce a polynomial in normal form. For
	 * example, given <code>[2, 7x, 4y, -x]</code> we would end up with
	 * <code>[1, 3x, 2y]</code>.
	 *
	 * @param terms
	 * @return
	 */
	public static Polynomial toNormalForm(ArrayList<Polynomial.Term> terms) {
		mergeTerms(terms);
		// Strip out null entries
		Polynomial.Term[] nTerms = removeNulls(terms);
		// Sort remaining terms
		Arrays.sort(nTerms);
		// Done
		return new Polynomial(nTerms);
	}

	private static boolean isZero(Polynomial.Term term) {
		BigInteger coefficient = term.getCoefficient().get();
		return coefficient.equals(BigInteger.ZERO);
	}

	/**
	 * Combine all terms which have the same set of atoms by adding the
	 * coefficients together. For example, [x,2x] is combined into [null,3x].
	 *
	 * @param terms
	 */
	private static void mergeTerms(ArrayList<Polynomial.Term> terms) {
		for (int i = 0; i != terms.size(); ++i) {
			Polynomial.Term ith = terms.get(i);
			if (ith != null) {
				if (isZero(ith)) {
					// Eliminate any zeros which may have arisen during the
					// calculation.
					terms.set(i, null);
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
	}

	/**
	 * This strips out any occurrence of null from the given list of terms.
	 *
	 * @param terms
	 * @return
	 */
	private static Polynomial.Term[] removeNulls(ArrayList<Polynomial.Term> terms) {
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
}
