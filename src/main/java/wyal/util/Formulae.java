package wyal.util;

import java.math.BigInteger;
import java.util.Arrays;

import wyal.lang.Formula;
import wyal.lang.SyntacticItem;
import wyal.lang.WyalFile;
import wyal.lang.WyalFile.Expr;
import wyal.lang.WyalFile.Identifier;
import wyal.lang.WyalFile.Opcode;
import wyal.lang.WyalFile.Pair;
import wyal.lang.WyalFile.Stmt;
import wyal.lang.WyalFile.Tuple;
import wyal.lang.WyalFile.Type;
import wyal.lang.WyalFile.Value;
import wyal.lang.Formula.ArithmeticEquality;
import wyal.lang.Formula.Atom;
import wyal.lang.Formula.Conjunct;
import wyal.lang.Formula.Disjunct;
import wyal.lang.Formula.Equality;
import wyal.lang.Formula.Inequality;
import wyal.lang.Formula.Polynomial;
import wyal.lang.Formula.Truth;
import wycc.util.ArrayUtils;

public class Formulae {

	// ========================================================================
	// Conjuncts / Disjuncts
	// ========================================================================

	/**
	 * Combine formulae together as conjuncts, whilst performing a range of
	 * simplifications:
	 *
	 * <ol>
	 * <li><b>Eliminates boolean constants</b>. Conjuncts containing
	 * <code>false</code> are reduced to <code>false</code>. In contrast,
	 * any occurrences of <code>true</code> are simply removed.</li>
	 * <li><b>Flattens nested conjuncts</b>. All nested conjuncts are
	 * recursively flattened into a single conjunct. For example,
	 * <code> (x && (y && z))</code> is flattened to
	 * <code>(x && y && z)</code>.</li>
	 * <li><b>Eliminates singleton conjuncts</b>. A conjunct containing a
	 * single (non-conjunct) child is reduced to that child.</li>
	 * </ol>
	 *
	 * The implementation attempts to eliminate dynamic memory allocation in
	 * the case that no reduction is applied.
	 *
	 * @author David J. Pearce
	 *
	 */
	public static Formula and(Formula... formulae) {
		// Flatten nested conjuncts
		formulae = Formulae.flattenNestedConjuncts(formulae);
		// Eliminate truths
		formulae = Formulae.eliminateConstants(true, formulae);
		// Ensure sorted and unique
		formulae = Formulae.sortAndRemoveDuplicates(formulae);
		// And, finally...
		if (formulae.length == 0) {
			// Return true here since the only way it's possible to get here
			// is if the conjunct contained only truths at the end.
			return new Truth(true);
		} else if (formulae.length == 1) {
			return formulae[0];
		} else {
			return new Conjunct(formulae);
		}
	}

	/**
	 * Combine formulae together as disjuncts, whilst performing a range of
	 * simplifications:
	 *
	 * <ol>
	 * <li><b>Eliminates boolean constants</b>. Disjuncts containing
	 * <code>true</code> are reduced to <code>true</code>. In contrast, any
	 * occurrences of <code>false</code> are simply removed.</li>
	 * <li><b>Flattens nested disjuncts</b>. All nested disjuncts are
	 * recursively flattened into a single disjunct. For example,
	 * <code> (x || (y || z))</code> is flattened to
	 * <code>(x || y || z)</code>.</li>
	 * <li><b>Eliminates singleton disjuncts</b>. A disjunct containing a
	 * single (non-disjunct) child is reduced to that child.</li>
	 * </ol>
	 *
	 * The implementation attempts to eliminate dynamic memory allocation in
	 * the case that no reduction is applied.
	 *
	 */
	public static Formula or(Formula... formulae) {
		// Flatten nested disjuncts
		formulae = Formulae.flattenNestedDisjuncts(formulae);
		// Eliminate truths
		formulae = Formulae.eliminateConstants(false, formulae);
		// Ensure sorted and unique
		formulae = Formulae.sortAndRemoveDuplicates(formulae);
		// And, finally...
		if (formulae.length == 0) {
			// Return false here since the only way it's possible to get
			// here is if the disjunct contained only falsehoods at the end.
			return new Truth(false);
		} else if (formulae.length == 1) {
			return formulae[0];
		} else {
			return new Disjunct(formulae);
		}
	}

	public static Formula lessThan(Polynomial lhs, Polynomial rhs) {
		if (lhs.isConstant() && rhs.isConstant()) {
			return Formulae.evaluateInequality(Opcode.EXPR_lt, lhs.toConstant(), rhs.toConstant());
		} else if(lhs.equals(rhs)) {
			return new Formula.Truth(false);
		} else {
			Pair<Polynomial,Polynomial> bs = Formulae.normaliseBounds(lhs,rhs);
			return new Inequality(true,bs.getFirst(),bs.getSecond());
		}
	}

	public static Formula greaterThanOrEqual(Polynomial lhs, Polynomial rhs) {
		if (lhs.isConstant() && rhs.isConstant()) {
			return Formulae.evaluateInequality(Opcode.EXPR_gteq, lhs.toConstant(), rhs.toConstant());
		} else if(lhs.equals(rhs)) {
			return new Formula.Truth(true);
		} else {
			Pair<Polynomial,Polynomial> bs = Formulae.normaliseBounds(lhs,rhs);
			return new Inequality(false,bs.getFirst(),bs.getSecond());
		}
	}

	public static Formula equal(Polynomial lhs, Polynomial rhs) {
		if (lhs.isConstant() && rhs.isConstant()) {
			Value lhs_v = lhs.toConstant();
			Value rhs_v = rhs.toConstant();
			return Formulae.evaluateEquality(Opcode.EXPR_eq, lhs_v, rhs_v);
		} else if(lhs.equals(rhs)) {
			return new Formula.Truth(true);
		} else {
			Pair<Polynomial,Polynomial> bs = Formulae.normaliseBounds(lhs,rhs);
			return new ArithmeticEquality(true,bs.getFirst(),bs.getSecond());
		}
	}

	public static Formula notEqual(Polynomial lhs, Polynomial rhs) {
		if (lhs.isConstant() && rhs.isConstant()) {
			Value lhs_v = lhs.toConstant();
			Value rhs_v = rhs.toConstant();
			return Formulae.evaluateEquality(Opcode.EXPR_neq, lhs_v, rhs_v);
		} else if(lhs.equals(rhs)) {
			return new Formula.Truth(false);
		} else {
			Pair<Polynomial,Polynomial> bs = Formulae.normaliseBounds(lhs,rhs);
			return new ArithmeticEquality(false,bs.getFirst(),bs.getSecond());
		}
	}

	public static Formula equal(Atom lhs, Atom rhs) {
		if (lhs instanceof Expr.Constant && rhs instanceof Expr.Constant) {
			Value lhs_v = ((Expr.Constant)lhs).getValue();
			Value rhs_v = ((Expr.Constant)rhs).getValue();
			return Formulae.evaluateEquality(Opcode.EXPR_eq, lhs_v, rhs_v);
		} else if(lhs.equals(rhs)) {
			return new Formula.Truth(true);
		} else {
			return new Equality(true,lhs,rhs);
		}
	}

	public static Formula notEqual(Atom lhs, Atom rhs) {
		if (lhs instanceof Expr.Constant && rhs instanceof Expr.Constant) {
			Value lhs_v = ((Expr.Constant)lhs).getValue();
			Value rhs_v = ((Expr.Constant)rhs).getValue();
			return Formulae.evaluateEquality(Opcode.EXPR_neq, lhs_v, rhs_v);
		} else if(lhs.equals(rhs)) {
			return new Formula.Truth(false);
		} else {
			return new Equality(false,lhs,rhs);
		}
	}


	/**
	 * <p>
	 * Substitute for a given variable within a given syntactic item.
	 * Specifically, this replaces all instances of VariableAccess which match
	 * the given declaration. Observe that the substitution is performed
	 * verbatim and (for example) without simplifying the underlying item.
	 * </p>
	 * <p>
	 * This function preserves the aliasing structure of the original item up to
	 * the substitution itself. Furthermore, if no substitution was performed
	 * then the original item is returned as is.
	 * </p>
	 *
	 * @param substitution
	 * @param item
	 * @return
	 */
	public static SyntacticItem substitute(Pair<Identifier, SyntacticItem> substitution, SyntacticItem item) {
		// FIXME: this function is broken because it should not be using
		// identifiers for substitution. Instead, is should be using variable
		// declarations.
		if (item instanceof Expr.VariableAccess) {
			// In this case, we might be able to make a substitution.
			Expr.VariableAccess v = (Expr.VariableAccess) item;
			Identifier name = v.getVariableDeclaration().getVariableName();
			if (name.equals(substitution.getFirst())) {
				// Yes, we made a substitution!
				return substitution.getSecond();
			}
			return item;
		} else {
			// No immediate substitution possible. Instead, recursively traverse
			// term looking for substitution.
			SyntacticItem[] children = item.getOperands();
			SyntacticItem[] nChildren = children;
			for (int i = 0; i != children.length; ++i) {
				SyntacticItem child = children[i];
				SyntacticItem nChild = substitute(substitution, item);
				if (child != nChild && nChildren == children) {
					// Clone the new children array to avoid interfering with
					// original item.
					nChildren = Arrays.copyOf(children, children.length);
				}
				nChildren[i] = nChild;
			}
			if (nChildren == children) {
				// No children were updated, hence simply return the original
				// item.
				return item;
			} else {
				// At least one child was changed, therefore clone the original
				// item with the new children.
				return item.clone(nChildren);
			}
		}
	}

	/**
	 * Recursively remove nested conjuncts. If no nested conjuncts are
	 * encountered, then the same array is returned. Otherwise, a new array
	 * containing all elements from both is returned. For example
	 * <code>[x, y && z]</code> is returned as <code>[x,y,z]</code>.
	 *
	 *
	 * @param children
	 * @return
	 */
	private static Formula[] flattenNestedConjuncts(Formula[] children) {
		return flattenNestedClauses(true,children);
	}

	/**
	 * Recursively remove nested disjuncts. If no nested disjuncts are
	 * encountered, then the same array is returned. Otherwise, a new array
	 * containing all elements from both is returned. For example
	 * <code>[x, y && z]</code> is returned as <code>[x,y,z]</code>.
	 *
	 *
	 * @param children
	 * @return
	 */
	private static Formula[] flattenNestedDisjuncts(Formula[] children) {
		return flattenNestedClauses(false,children);
	}

	private static Formula[] flattenNestedClauses(boolean sign, Formula[] children) {
		int count = nestedCount(sign, children);
		if (count == children.length) {
			// In this case, there are no nested expressions to include.
			// Therefore, we return the array as is without modification.
			return children;
		} else {
			// Yes, we have at least one nested expression to handle. This means
			// we are definitely returning a new array.
			Formula[] nChildren = new Formula[count];
			nestedCopy(sign, children, nChildren, 0);
			return nChildren;
		}
	}

	/**
	 * Count the total number of elements in this array which are not conjuncts.
	 * This recursively includes nested conjuncts in this count. For example,
	 * <code>[x, y && z]</code> returns a count of <code>3</code>.
	 *
	 * @param children
	 * @return
	 */
	private static int nestedCount(boolean flag, Formula[] children) {
		int count = 0;
		for (int i = 0; i != children.length; ++i) {
			Expr child = children[i];
			if (flag && child.getOpcode() == Opcode.EXPR_and) {
				Formula.Conjunct conjunct = (Formula.Conjunct) child;
				count += nestedCount(flag, conjunct.getOperands());
			} else if (!flag && child.getOpcode() == Opcode.EXPR_or) {
				Formula.Disjunct disjunct = (Formula.Disjunct) child;
				count += nestedCount(flag, disjunct.getOperands());
			} else {
				count = count + 1;
			}
		}
		return count;
	}

	/**
	 * Copy non-conjunct expressions from one array to another. This will
	 * recursively copy the children of conjunct expressions as well.
	 *
	 * @param from
	 *            The array to be copied from.
	 * @param to
	 *            The array to which non-conjuncts are copied.
	 * @param start
	 *            The starting point in the destination array into which
	 *            elements are copied. The underlying assumption is that the
	 *            destination array is always big enough to hold all items to be
	 *            copied.
	 * @return The total number of items copied. This is necessary so that
	 *         recursive calls can determine how much of the destination array
	 *         is now occupied.
	 */
	private static int nestedCopy(boolean flag, Formula[] from, Formula[] to, int start) {
		int count = 0;
		for (int i = 0, j = start; i != from.length; ++i) {
			Expr child = from[i];
			if (flag && child.getOpcode() == Opcode.EXPR_and) {
				Formula.Conjunct conjunct = (Formula.Conjunct) child;
				j += nestedCopy(flag,conjunct.getOperands(), to, j);
			} else if (!flag && child.getOpcode() == Opcode.EXPR_or) {
				Formula.Disjunct disjunct = (Formula.Disjunct) child;
				j += nestedCopy(flag,disjunct.getOperands(), to, j);
			} else {
				to[j++] = from[i];
				count = count + 1;
			}
		}
		return count;
	}

	/**
	 * Remove all constant values (i.e. true or false) from an array of
	 * expressions. This attempts to reduce the among of cloning involved. If
	 * there were no constant values encountered, then the original array is
	 * returned untouched.
	 *
	 * @param children
	 * @return
	 */
	private static Formula[] eliminateConstants(boolean sign, Formula[] children) {
		// Count number of constants
		int numConstants = 0;
		for (int i = 0; i != children.length; ++i) {
			Formula child = children[i];
			if (children[i] instanceof Formula.Truth) {
				Formula.Truth c = (Formula.Truth) child;
				// The following is safe only because we assume the expression
				// tree is well-typed.
				if (c.holds() == sign) {
					numConstants++;
				} else {
					// A conjunct containing sign is sign
					return new Formula[] { c };
				}
			}
		}
		if (numConstants == 0) {
			return children;
		} else {
			//
			Formula[] nChildren = new Formula[children.length - numConstants];
			for (int i = 0, j = 0; i != children.length; ++i) {
				Formula child = children[i];
				if (child instanceof Expr.Constant) {
					// ignore
				} else {
					nChildren[j++] = child;
				}
			}
			return nChildren;
		}
	}

	/**
	 * Sort and remove duplicate expressions from the given array. The concept
	 * of a duplicate expression is based solely on the index of that expression
	 * in the contained syntactic heap. That is, two expressions with the same
	 * index are considered duplicates. Likewise, sorting is conducted based on
	 * heap index, with those with lower indices coming earlier in the resulting
	 * array.
	 *
	 * @param children
	 * @return
	 */
	private static <T extends SyntacticItem> T[] sortAndRemoveDuplicates(T[] children) {
		int r = isSortedAndUnique(children);
		switch(r) {
		case 0:
			// In this case, the array is already sorted and no duplicates were
			// found.
			return children;
		case 1:
			// In this case, the array is already sorted, but duplicates were
			// found
			return ArrayUtils.sortedRemoveDuplicates(children);
		default:
			// In this case, the array is not sorted and may or may not
			// contained duplicates.
			children = Arrays.copyOf(children, children.length);
			Arrays.sort(children);
			return ArrayUtils.sortedRemoveDuplicates(children);
		}
	}

	/**
	 * Normalise bounds of an equation to be positive. For example, consider the
	 * inequality <code>x < y - z</code>. In this case, the right-hand side is
	 * not normalised because it contains a negative term. The normalised
	 * version of this inequality would be <code>x + z < y</code>.
	 *
	 * @param lhs
	 * @param rhs
	 * @return
	 */
	private static Pair<Polynomial,Polynomial> normaliseBounds(Polynomial lhs, Polynomial rhs) {
		Polynomial bound = factorise(lhs.subtract(rhs));
		Polynomial pos = new Polynomial(BigInteger.ZERO);
		Polynomial neg = new Polynomial(BigInteger.ZERO);
		for(int i=0;i!=bound.size();++i) {
			Polynomial.Term t = bound.getOperand(i);
			BigInteger coeff = t.getCoefficient().get();
			if(coeff.compareTo(BigInteger.ZERO) >= 0) {
				pos = add(pos,t);
			} else {
				neg = neg.subtract(t);
			}
		}
		return new Pair<>(pos,neg);
	}

	// ========================================================================
	// Equalities / Inequalities
	// ========================================================================

	/**
	 * Evaluate a given inequality whose bounds are known to be constant integer
	 * values. For example, <code>1 < 0</code> evaluates to <code>false</code>,
	 * etc.
	 *
	 * @param opcode
	 * @param lhs
	 * @param rhs
	 * @return
	 */
	private static Formula.Truth evaluateInequality(Opcode opcode, Value.Int lhs, Value.Int rhs) {
		boolean result;
		switch (opcode) {
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
			throw new IllegalArgumentException("Invalid inequality opcode: " + opcode);
		}
		return new Formula.Truth(result);
	}

	/**
	 * Evaluate a given equality whose bounds are known to be constant values of
	 * some sort. For example, <code>true == false</code> evaluates to
	 * <code>false</code>, etc.
	 *
	 * @param opcode
	 * @param lhs
	 * @param rhs
	 * @return
	 */
	private static Formula.Truth evaluateEquality(Opcode opcode, Value lhs, Value rhs) {
		boolean result;
		switch (opcode) {
		case EXPR_eq:
			result = lhs.equals(rhs);
			break;
		case EXPR_neq:
			result = !(lhs.equals(rhs));
			break;
		default:
			throw new IllegalArgumentException("Invalid equality opcode: " + opcode);
		}
		return new Formula.Truth(result);
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
	private static Polynomial factorise(Polynomial p) {
		BigInteger factor = p.getOperand(0).getCoefficient().get();
		// In case of just one coefficient which is negative, we need to compute
		// abs() here.
		factor = factor.abs();
		//
		for (int i = 1; i != p.size(); ++i) {
			BigInteger c = p.getOperand(i).getCoefficient().get();
			factor = factor.gcd(c);
		}
		if (factor.equals(BigInteger.ONE)) {
			// No useful factor discovered
			return p;
		} else {
			// Yes, we found a useful factor. Therefore, divide all coefficients
			// by this.
			Polynomial r = new Polynomial(BigInteger.ZERO);
			for (int i = 0; i != p.size(); ++i) {
				Polynomial.Term t = p.getOperand(i);
				BigInteger c = t.getCoefficient().get();
				c = c.divide(factor);
				r = add(r, new Polynomial.Term(new Value.Int(c), t.getAtoms()));
			}
			return r;
		}
	}

	/**
	 * Check whether or not the children of this array are sorted according to
	 * syntactic heap index. And, if so, whether or not there are any duplicate
	 * elements encountered.
	 *
	 * @param children
	 * @return
	 */
	private static <T extends SyntacticItem> int isSortedAndUnique(T[] children) {
		int r = 0;
		for (int i = 1; i < children.length; ++i) {
			int c = children[i - 1].compareTo(children[i]);
			if (c == 0) {
				// Duplicate found, though still could be in sorted order.
				r = 1;
			} else if (c > 0) {
				// NOT in sorted order
				return -1;
			}
		}
		// All good
		return r;
	}

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
	private static Polynomial toNormalForm(Polynomial.Term[] terms) {
		mergeTerms(terms);
		// Strip out null entries
		Polynomial.Term[] nTerms = ArrayUtils.removeAll(terms, null);
		// In the case that all terms were eliminated as null, simply ensure
		// that zero is present. This can happen is all terms cancelled out.
		if (nTerms.length == 0) {
			// FIXME: can zero be represented using an empty term array?
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
		for (int i = 0; i != terms.length; ++i) {
			Polynomial.Term ith = terms[i];
			if (ith != null) {
				if (isZero(ith)) {
					// Eliminate any zeros which may have arisen during the
					// calculation.
					terms[i] = null;
				} else {
					Tuple<Atom> ithAtoms = ith.getAtoms();
					for (int j = i + 1; j != terms.length; ++j) {
						Polynomial.Term jth = terms[j];
						if (jth != null && ithAtoms.equals(jth.getAtoms())) {
							// We have two overlapping terms, namely i and j.
							// Add them together and assign the result to the
							// jth position.
							terms[j] = ith.add(jth);
							terms[i] = null;
							break;
						}
					}
				}
			}
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
			terms[i] = p.getOperand(i).negate();
		}

		return new Polynomial(terms);
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
				terms[j_base + j] = lhsTerm.multiply(rhsTerm);
			}
		}

		return toNormalForm(terms);
	}
}
