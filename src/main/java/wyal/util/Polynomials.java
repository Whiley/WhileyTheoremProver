package wyal.util;

import java.math.BigInteger;
import java.util.Arrays;

import wyal.lang.WyalFile;
import wyal.lang.WyalFile.Expr;
import wyal.lang.WyalFile.Expr.Polynomial;
import wyal.lang.WyalFile.Value;
import wycc.util.ArrayUtils;

public class Polynomials {

	// ========================================================================
	// Polynomials
	// ========================================================================

	/**
	 * Given a list of unsorted and potentially overlapping terms, apply the
	 * necessary simplifications to produce a polynomial in normal form. For
	 * example, given <code>[2, 7x, 4y, -x]</code> we would end up with
	 * <code>[1, 3x, 2y]</code>.
	 *
	 * @param terms
	 * @return
	 */
	public static Polynomial toNormalForm(Polynomial.Term[] terms) {
		mergeTerms(terms);
		// Strip out null entries
		Polynomial.Term[] nTerms = ArrayUtils.removeAll(terms, null);
		// In the case that all terms were eliminated as null, simply ensure
		// that zero is present. This can happen is all terms cancelled out.
		if (nTerms.length == 0) {
			// FIXME: can zero be represented using an empty term array?
			// This does make the manipulation of polynomials more awkward than
			// necessary.
			nTerms = new Polynomial.Term[] { new Polynomial.Term(BigInteger.ZERO) };
		}
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
	private static void mergeTerms(Polynomial.Term[] terms) {
		//
		for (int i = 0; i != terms.length; ++i) {
			Polynomial.Term ith = terms[i];
			if (ith != null) {
				if (isZero(ith)) {
					// Eliminate any zeros which may have arisen during the
					// calculation.
					terms[i] = null;
				} else {
					Expr[] ithAtoms = ith.getAtoms();
					for (int j = i + 1; j != terms.length; ++j) {
						Polynomial.Term jth = terms[j];
						if (jth != null && Arrays.equals(ithAtoms,jth.getAtoms())) {
							// We have two overlapping terms, namely i and j.
							// Add them together and assign the result to the
							// jth position.
							terms[j] = mergeTerms(ith,jth);
							terms[i] = null;
							break;
						}
					}
				}
			}
		}
	}

	private static void print(Expr[] atoms) {
		for(Expr a : atoms) {
			WyalFile.print(a);
			System.out.print(" [" + System.identityHashCode(a) + "] ");
		}
	}

	private static Polynomial.Term mergeTerms(Polynomial.Term lhs, Polynomial.Term rhs) {
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

	public static Polynomial.Term negate(Polynomial.Term term) {
		BigInteger coeff = term.getCoefficient().get();
		return new Polynomial.Term(new Value.Int(coeff.negate()), term.getAtoms());
	}

	/**
	 * <p>
	 * Add two polynomials together, producing a polynomial in normal form.
	 * To do this, we must add the coefficients for terms which have the
	 * same set of atoms, whilst other terms are incorporated as is. For
	 * example, consider adding <code>2+2x</code> with <code>1+3x+4y</code>.
	 * In this case, we have some terms in common, so the result becomes
	 * <code>(2+1) + (2x+3x) + 4y</code> which is simplified to
	 * <code>3 + 5x + 4y</code>.
	 * </p>
	 *
	 * @param poly
	 * @return
	 */
	public static Polynomial add(Polynomial lhs, Polynomial poly) {
		Polynomial.Term[] terms = new Polynomial.Term[lhs.size() + poly.size()];
		int this_size = lhs.size();
		//
		for (int i = 0; i != this_size; ++i) {
			terms[i] = lhs.getOperand(i);
		}
		for (int j = 0; j != poly.size(); ++j) {
			terms[this_size + j] = poly.getOperand(j);
		}
		return toNormalForm(terms);
	}

	public static Polynomial add(Polynomial lhs, Polynomial.Term rhs) {
		Polynomial.Term[] terms = new Polynomial.Term[lhs.size() + 1];
		for (int i = 0; i != lhs.size(); ++i) {
			terms[i] = lhs.getOperand(i);
		}
		terms[lhs.size()] = rhs;
		return toNormalForm(terms);
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
	 * @param p
	 * @return
	 */
	public static Polynomial multiply(Polynomial lhs, Polynomial rhs) {
		int lhs_size = lhs.size();
		int rhs_size = rhs.size();
		Polynomial.Term[] terms = new Polynomial.Term[lhs_size * rhs_size];

		for (int i = 0; i != lhs_size; ++i) {
			Polynomial.Term lhsTerm = lhs.getOperand(i);
			int j_base = i * rhs_size;
			for (int j = 0; j != rhs_size; ++j) {
				Polynomial.Term rhsTerm = rhs.getOperand(j);
				terms[j_base + j] = multiply(lhsTerm,rhsTerm);
			}
		}

		return toNormalForm(terms);
	}

	public static Polynomial multiply(Polynomial lhs, Polynomial.Term rhs) {
		int lhs_size = lhs.size();
		Polynomial.Term[] terms = new Polynomial.Term[lhs_size];

		for (int i = 0; i != lhs_size; ++i) {
			Polynomial.Term lhsTerm = lhs.getOperand(i);
			terms[i] = multiply(lhsTerm, rhs);
		}

		return toNormalForm(terms);
	}

	public static Polynomial.Term multiply(Polynomial.Term lhs, Polynomial.Term rhs) {
		BigInteger lhsCoeff = lhs.getCoefficient().get();
		BigInteger rhsCoeff = rhs.getCoefficient().get();
		Expr[] lhsAtoms = lhs.getAtoms();
		Expr[] rhsAtoms = rhs.getAtoms();
		Expr[] atoms = new Expr[lhsAtoms.length + rhsAtoms.length];
		System.arraycopy(lhsAtoms, 0, atoms, 0, lhsAtoms.length);
		System.arraycopy(rhsAtoms, 0, atoms, lhsAtoms.length, rhsAtoms.length);
		Arrays.sort(atoms);
		Value.Int coefficient = new Value.Int(lhsCoeff.multiply(rhsCoeff));
		return new Polynomial.Term(coefficient, atoms);
	}
}
