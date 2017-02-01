package wyal.util;

import java.math.BigInteger;
import java.util.Arrays;

import wyal.lang.SyntacticItem;
import wyal.lang.WyalFile;
import wyal.lang.WyalFile.Expr;
import wyal.lang.WyalFile.Formula;
import wyal.lang.WyalFile.Opcode;
import wyal.lang.WyalFile.Stmt;
import wyal.lang.WyalFile.Value;
import wyal.lang.WyalFile.Expr.Polynomial;
import wycc.util.ArrayUtils;

public class Formulae {

	/**
	 * Take a tree of statements and expressions, and return a formula. This is
	 * the first part of the process in discharging a given assertion.
	 *
	 * @param s
	 * @return
	 */
	public static WyalFile.Formula toFormula(WyalFile.Stmt s) {
		switch (s.getOpcode()) {
		case STMT_block: {
			WyalFile.Stmt.Block b = (WyalFile.Stmt.Block) s;
			Formula[] operands = toFormulae(b.getOperands());
			return Formula.and(operands);
		}
		case STMT_caseof: {
			WyalFile.Stmt.CaseOf b = (WyalFile.Stmt.CaseOf) s;
			Formula[] operands = toFormulae(b.getOperands());
			return Formula.or(operands);
		}
		case STMT_ifthen: {
			WyalFile.Stmt.IfThen it = (WyalFile.Stmt.IfThen) s;
			Formula lhs = toFormula(it.getIfBody());
			Formula rhs = toFormula(it.getThenBody());
			return Formula.or(lhs.invert(), rhs);
		}
		case STMT_forall: {
			Stmt.Quantifier q = (WyalFile.Stmt.Quantifier) s;
			Formula body = toFormula(q.getBody());
			return new Formula.Quantifier(Opcode.EXPR_forall, q.getParameters(), body);
		}
		case STMT_exists: {
			Stmt.Quantifier q = (WyalFile.Stmt.Quantifier) s;
			Formula body = toFormula(q.getBody());
			return new Formula.Quantifier(Opcode.EXPR_exists, q.getParameters(), body);
		}
		case EXPR_eq: {
			Expr.Operator operator = (Expr.Operator) s;
			Expr lhs = operator.getOperand(0);
			Expr rhs = operator.getOperand(1);
			return new Formula.Equality(true, lhs, rhs);
		}
		case EXPR_neq: {
			Expr.Operator operator = (Expr.Operator) s;
			Expr lhs = operator.getOperand(0);
			Expr rhs = operator.getOperand(1);
			return new Formula.Equality(false, lhs, rhs);
		}
		case EXPR_lt: {
			Expr.Operator operator = (Expr.Operator) s;
			Polynomial lhs = Polynomials.toPolynomial(operator.getOperand(0));
			Polynomial rhs = Polynomials.toPolynomial(operator.getOperand(1));
			return Formula.lessThan(lhs, rhs);
		}
		case EXPR_lteq: {
			Expr.Operator operator = (Expr.Operator) s;
			Polynomial lhs = Polynomials.toPolynomial(operator.getOperand(0));
			Polynomial rhs = Polynomials.toPolynomial(operator.getOperand(1));
			return Formula.greaterThanOrEquals(rhs, lhs);
		}
		case EXPR_gt: {
			Expr.Operator operator = (Expr.Operator) s;
			Polynomial lhs = Polynomials.toPolynomial(operator.getOperand(0));
			Polynomial rhs = Polynomials.toPolynomial(operator.getOperand(1));
			return Formula.lessThan(rhs, lhs);
		}
		case EXPR_gteq: {
			Expr.Operator operator = (Expr.Operator) s;
			Polynomial lhs = Polynomials.toPolynomial(operator.getOperand(0));
			Polynomial rhs = Polynomials.toPolynomial(operator.getOperand(1));
			return Formula.greaterThanOrEquals(lhs, rhs);
		}
		case EXPR_not: {
			Expr.Operator operator = (Expr.Operator) s;
			Formula f = toFormula(operator.getOperand(0));
			return f.invert();
		}
		case EXPR_const: {
			Expr.Constant c = (Expr.Constant) s;
			Value.Bool b = (Value.Bool) c.getValue();
			return new Formula.Truth(b);
		}
		default:
			if (s instanceof WyalFile.Expr) {
				Expr.Constant TRUE = new Expr.Constant(new Value.Bool(true));
				return new Formula.Equality(true, TRUE, (WyalFile.Expr) s);
			} else {
				throw new IllegalArgumentException("unknown statement encountered: " + s.getOpcode());
			}
		}
	}

	/**
	 * Convert an array of statements into an array of (equivalent) expressions.
	 *
	 * @param stmts
	 * @return
	 */
	public static Formula[] toFormulae(WyalFile.Stmt[] stmts) {
		Formula[] exprs = new Formula[stmts.length];
		for (int i = 0; i != exprs.length; ++i) {
			exprs[i] = toFormula(stmts[i]);
		}
		return exprs;
	}

	/**
	 * Evaluate a given equality or inequality.
	 *
	 * @param opcode
	 * @param lhs
	 * @param rhs
	 * @return
	 */
	public static Formula.Truth evaluateEquation(Opcode opcode, BigInteger lhs, BigInteger rhs) {
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
		return new Formula.Truth(result);
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
	public static Formula[] flattenNestedConjuncts(Formula[] children) {
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
	public static Formula[] flattenNestedDisjuncts(Formula[] children) {
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
	public static Formula[] eliminateConstants(boolean sign, Formula[] children) {
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
	public static <T extends SyntacticItem> T[] sortAndRemoveDuplicates(T[] children) {
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
}
