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
package wytp.proof.util;

import java.math.BigInteger;
import java.util.Arrays;

import wyal.lang.WyalFile;
import wyal.lang.WyalFile.Expr;
import wyal.lang.WyalFile.Value;
import wycc.util.ArrayUtils;


public class Arithmetic {

	public static Polynomial asPolynomial(Expr e) {
		switch (e.getOpcode()) {
		case EXPR_const: {
			Expr.Constant c = (Expr.Constant) e;
			Value.Int i = (Value.Int) c.getValue();
			Polynomial.Term term = new Polynomial.Term(i.get());
			return new Polynomial(term);
		}
		case EXPR_add: {
			Polynomial result = asPolynomial((Expr) e.getOperand(0));
			for(int i=1;i!=e.size();++i) {
				result = result.add(asPolynomial((Expr) e.getOperand(i)));
			}
			return result;
		}
		case EXPR_sub: {
			Polynomial result = asPolynomial((Expr) e.getOperand(0));
			for(int i=1;i!=e.size();++i) {
				result = result.subtract(asPolynomial((Expr) e.getOperand(i)));
			}
			return result;
		}
		case EXPR_mul: {
			Polynomial result = asPolynomial((Expr) e.getOperand(0));
			for(int i=1;i!=e.size();++i) {
				result = result.multiply(asPolynomial((Expr) e.getOperand(i)));
			}
			return result;
		}
		case EXPR_div: {
			throw new IllegalArgumentException("need to support division");
		}
		default: {
			Polynomial.Term term = new Polynomial.Term(BigInteger.ONE, e);
			return new Polynomial(term);
		}
		}
	}
//
//	public class Rational {
//		public Polynomial getNumerator() {
//
//		}
//		public Polynomial getDenominator() {
//
//		}
//	}

	public static class Polynomial implements Comparable<Polynomial> {

		public static final Polynomial ZERO = new Polynomial(new Term(BigInteger.ZERO));

		private Term[] terms;

		Polynomial(Term...terms) {
			this.terms = terms;
		}

		public int size() {
			return terms.length;
		}
		public boolean isConstant() {
			return (terms.length == 1 && terms[0].isConstant());
		}
		public BigInteger toConstant() {
			return terms[0].getCoefficient();
		}
		public Term getTerm(int i) {
			return terms[i];
		}
		public Polynomial negate() {
			Term[] newTerms = new Term[terms.length];
			for(int i=0;i!=terms.length;++i) {
				newTerms[i] = terms[i].negate();
			}
			return new Polynomial(newTerms);
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
		public Polynomial add(Polynomial p) {
			Polynomial.Term[] combined = new Polynomial.Term[terms.length+p.terms.length];
			System.arraycopy(terms, 0, combined, 0, terms.length);
			System.arraycopy(p.terms, 0, combined, terms.length, p.terms.length);
			return construct(combined);
		}

		public Polynomial add(Polynomial.Term p) {
			Polynomial.Term[] combined = new Polynomial.Term[terms.length+1];
			System.arraycopy(terms, 0, combined, 0, terms.length);
			combined[terms.length] = p;
			return construct(combined);
		}
		public Polynomial subtract(Polynomial p) {
			return add(p.negate());
		}
		public Polynomial subtract(Polynomial.Term p) {
			return add(p.negate());
		}

		/**
		 * Multiply two polynomials together. This is done by reusing the add()
		 * function as much as possible, though this may not be the most
		 * efficient. In essence, to multiply one polynomial (e.g.
		 * <code>2+2x</code>) by another (e.g.<code>1+3x+4y</code>) it breaks it
		 * down into a series of multiplications over terms and additions. That
		 * is, we multiply each term from the first polynomial by the second
		 * (e.g. <code>2*(1+3x+4y)</code> and <code>2x*(1+3x+4y)</code>). Then,
		 * we add the results together (e.g.
		 * <code>(2+6x+8y) + (2x+6x2+8xy)</code>).
		 *
		 * @param p
		 * @return
		 */
		public Polynomial multiply(Polynomial p) {
			int lhs_size = terms.length;
			int rhs_size = p.terms.length;
			Polynomial.Term[] combined = new Polynomial.Term[lhs_size * rhs_size];

			for (int i = 0; i != lhs_size; ++i) {
				Polynomial.Term lhsTerm = terms[i];
				int j_base = i * rhs_size;
				for (int j = 0; j != rhs_size; ++j) {
					Polynomial.Term rhsTerm = p.terms[j];
					combined[j_base + j] = Arithmetic.multiply(lhsTerm, rhsTerm);
				}
			}

			return construct(combined);
		}

		public Polynomial multiply(Polynomial.Term rhs) {
			int lhs_size = terms.length;
			Polynomial.Term[] combined = new Polynomial.Term[lhs_size];

			for (int i = 0; i != lhs_size; ++i) {
				Polynomial.Term lhsTerm = terms[i];
				terms[i] = Arithmetic.multiply(lhsTerm, rhs);
			}

			return construct(combined);
		}

		@Override
		public int compareTo(Polynomial p) {
			int lengthDifference = terms.length - p.terms.length;
			if(lengthDifference != 0) {
				return lengthDifference;
			} else {
				for(int i=0;i!=terms.length;++i) {
					Polynomial.Term t1 = terms[i];
					Polynomial.Term t2 = p.terms[i];
					int c = t1.compareTo(t2);
					if(c != 0) {
						return c;
					}
				}
				return 0;
			}
		}

		@Override
		public boolean equals(Object o) {
			if(o instanceof Polynomial) {
				Polynomial p = (Polynomial) o;
				return Arrays.equals(terms, p.terms);
			}
			return false;
		}

		@Override
		public int hashCode() {
			return Arrays.hashCode(terms);
		}

		public Expr toExpression() {
			Expr[] muls = new Expr[terms.length];
			for(int i=0;i!=muls.length;++i) {
				muls[i] = terms[i].toExpression();
			}
			if(muls.length == 1) {
				return muls[0];
			} else {
				return new Expr.Operator(WyalFile.Opcode.EXPR_add,muls);
			}
		}

		@Override
		public String toString() {
			String r = "(";
			for(int i=0;i!=terms.length;++i) {
				if(i != 0) {
					r += " + ";
				}
				r += terms[i].toString();
			}
			return r + ")";
		}

		public static class Term implements Comparable<Term> {
			private final BigInteger coefficient;
			private final Expr[] atoms;

			Term(BigInteger coefficient, Expr...atoms) {
				if(coefficient.equals(BigInteger.ZERO) && atoms.length > 0) {
					throw new IllegalArgumentException("invalid zero term");
				}
				this.coefficient = coefficient;
				this.atoms = atoms;
			}
			public BigInteger getCoefficient() {
				return coefficient;
			}
			public boolean isConstant() {
				return atoms.length == 0;
			}
			public Expr[] getAtoms() {
				return atoms;
			}

			@Override
			public int compareTo(Term t) {
				int lengthDifference = atoms.length - t.atoms.length;
				if (lengthDifference != 0) {
					return lengthDifference;
				} else {
					for (int i = 0; i != atoms.length; ++i) {
						Expr t1 = atoms[i];
						Expr t2 = t.atoms[i];
						int c = t1.compareTo(t2);
						if (c != 0) {
							return c;
						}
					}
					return coefficient.compareTo(t.coefficient);
				}
			}

			@Override
			public boolean equals(Object o) {
				if(o instanceof Term) {
					Term t = (Term) o;
					return coefficient.equals(t.coefficient) && Arrays.equals(atoms, t.atoms);
				}
				return false;
			}

			@Override
			public int hashCode() {
				return coefficient.hashCode() ^ Arrays.hashCode(atoms);
			}

			public Term negate() {
				return new Term(coefficient.negate(),atoms);
			}

			public Expr toExpression() {
				if (atoms.length == 0) {
					return new Expr.Constant(new Value.Int(coefficient));
				} else if (coefficient.equals(BigInteger.ONE)) {
					return new Expr.Operator(WyalFile.Opcode.EXPR_mul, atoms);
				} else {
					Expr[] es = new Expr[atoms.length + 1];
					es[0] = new Expr.Constant(new Value.Int(coefficient));
					System.arraycopy(atoms, 0, es, 1, atoms.length);
					return new Expr.Operator(WyalFile.Opcode.EXPR_mul, es);
				}
			}

			@Override
			public String toString() {
				String r = "";
				if(!coefficient.equals(BigInteger.ONE) || atoms.length == 0) {
					r += coefficient;
					if(atoms.length > 0) {
						r += "*";
					}
				}
				for(int i=0;i!=atoms.length;++i) {
					if(i != 0) {
						r += "*";
					}
					r += atoms[i];
				}
				return r;
			}
		}
	}

	private static Polynomial.Term multiply(Polynomial.Term lhs, Polynomial.Term rhs) {
		if (lhs.coefficient.equals(BigInteger.ZERO)) {
			return lhs;
		} else if (rhs.coefficient.equals(BigInteger.ZERO)) {
			return rhs;
		} else {
			BigInteger coefficient = lhs.getCoefficient().multiply(rhs.getCoefficient());
			Expr[] lhsAtoms = lhs.getAtoms();
			Expr[] rhsAtoms = rhs.getAtoms();
			Expr[] atoms = new Expr[lhsAtoms.length + rhsAtoms.length];
			System.arraycopy(lhsAtoms, 0, atoms, 0, lhsAtoms.length);
			System.arraycopy(rhsAtoms, 0, atoms, lhsAtoms.length, rhsAtoms.length);
			Arrays.sort(atoms);
			return new Polynomial.Term(coefficient, atoms);
		}
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
	private static Polynomial construct(Polynomial.Term... terms) {
		terms = merge(terms);
		// In the case that all terms were eliminated as null, simply ensure
		// that zero is present. This can happen is all terms cancelled out.
		if (terms.length == 0) {
			// FIXME: can zero be represented using an empty term array?
			// This does make the manipulation of polynomials more awkward than
			// necessary.
			terms = new Polynomial.Term[] { new Polynomial.Term(BigInteger.ZERO) };
		}
		// Sort remaining terms
		Arrays.sort(terms);
		// Done
		return new Polynomial(terms);
	}

	private static boolean isZero(Polynomial.Term term) {
		BigInteger coefficient = term.getCoefficient();
		return coefficient.equals(BigInteger.ZERO);
	}

	/**
	 * Combine all terms which have the same set of atoms by adding the
	 * coefficients together. For example, [x,2x] is combined into [null,3x].
	 *
	 * @param terms
	 */
	private static Polynomial.Term[] merge(Polynomial.Term[] terms) {
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
							terms[j] = merge(ith,jth);
							terms[i] = null;
							break;
						}
					}
				}
			}
		}
		// Strip out null entries
		return ArrayUtils.removeAll(terms, null);
	}

	/**
	 * Merge two polynomial terms which are assumed to have the same set of
	 * atoms.
	 *
	 * @param lhs
	 * @param rhs
	 * @return
	 */
	private static Polynomial.Term merge(Polynomial.Term lhs, Polynomial.Term rhs) {
		BigInteger lhsCoeff = lhs.getCoefficient();
		BigInteger rhsCoeff = rhs.getCoefficient();
		BigInteger r = lhsCoeff.add(rhsCoeff);
		if (r.equals(BigInteger.ZERO)) {
			return null;
		} else {
			return new Polynomial.Term(r, lhs.getAtoms());
		}
	}

	/**
	 * Factorise a given polynomial. For example, <code>2x+2</code> is
	 * factorised to be <code>x+1</code>. Observe that this does not preseve the
	 * result of the polynomial. However, it is safe to do when simplifying
	 * equations. For example, <code>2x == 2y</code> can be safely factorised to
	 * <code>x == y</code>.
	 *
	 * @param p
	 * @return
	 */
	private static Polynomial.Term[] factor(Polynomial.Term[] terms) {
		if (terms.length > 1) {
			BigInteger factor = terms[0].getCoefficient();
			// In case of just one coefficient which is negative, we need to
			// compute abs() here.
			factor = factor.abs();
			//
			for (int i = 1; i != terms.length; ++i) {
				BigInteger c = terms[i].getCoefficient();
				factor = factor.gcd(c);
			}
			if (!factor.equals(BigInteger.ZERO) && !factor.equals(BigInteger.ONE)) {
				// Yes, we found a useful factor. Therefore, divide all
				// coefficients by this.
				for (int i = 0; i != terms.length; ++i) {
					Polynomial.Term t = terms[i];
					BigInteger c = t.getCoefficient();
					c = c.divide(factor);
					terms[i] = new Polynomial.Term(c, t.getAtoms());
				}
			}
		}
		return terms;
	}
}
