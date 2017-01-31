package wyal.rules;

import java.util.Arrays;

import wyal.lang.SyntacticItem;
import wyal.lang.WyalFile.Value;
import wyal.lang.WyalFile.Expr;
import wyal.lang.WyalFile.Opcode;
import wyal.util.AutomatedTheoremProver.RewriteRule;
import wycc.util.ArrayUtils;

/**
 * Performs a range of simplifications related to conjuncts. In particular:
 *
 * <ol>
 * <li><b>Eliminates boolean constants</b>. Conjuncts containing
 * <code>false</code> are reduced to <code>false</code>. In contrast, any
 * occurrences of <code>true</code> are simply removed.</li>
 * <li><b>Flattens nested conjuncts</b>. All nested conjuncts are recursively
 * flattened into a single conjunct. For example, <code> (x && (y && z))</code>
 * is flattened to <code>(x && y && z)</code>.</li>
 * <li><b>Eliminates singleton conjuncts</b>. A conjunct containing a single
 * (non-conjunct) child is reduced to that child.</li>
 * </ol>
 *
 * The implementation attempts to eliminate dynamic memory allocation in the
 * case that no reduction is applied.
 *
 * @author David J. Pearce
 *
 */
public class AndElimination implements RewriteRule {

	@Override
	public SyntacticItem rewrite(SyntacticItem item) {
		if (item.getOpcode() == Opcode.EXPR_and) {
			// Matched conjunct
			Expr.Operator conjunct = (Expr.Operator) item;
			Expr[] children = conjunct.getOperands();
			// Flatten nested intersections
			children = flattenNestedConjuncts(children);
			// Eliminate truths
			children = eliminateConstants(children);
			// Ensure sorted and unique
			children = sortAndRemoveDuplicates(children);
			// And, finally...
			if (children.length == 0) {
				// Return true here since the only way it's possible to get here
				// is if the conjunct contained only truths at the end.
				return new Expr.Constant(new Value.Bool(true));
			} else if (children.length == 1) {
				return children[0];
			} else if (children != item.getOperands()) {
				// The child array has been changed in some way.
				return item.clone(children);
			}
		}
		// nothing has changed.
		return item;
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
	private Expr[] flattenNestedConjuncts(Expr[] children) {
		int count = nestedCount(children);
		if (count == children.length) {
			// In this case, there are no nested expressions to include.
			// Therefore, we return the array as is without modification.
			return children;
		} else {
			// Yes, we have at least one nested expression to handle. This means
			// we are definitely returning a new array.
			Expr[] nChildren = new Expr[count];
			nestedCopy(children, nChildren, 0);
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
	private int nestedCount(Expr[] children) {
		int count = 0;
		for (int i = 0; i != children.length; ++i) {
			Expr child = children[i];
			if (child.getOpcode() == Opcode.EXPR_and) {
				Expr.Operator conjunct = (Expr.Operator) child;
				count += nestedCount(conjunct.getOperands());
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
	private int nestedCopy(Expr[] from, Expr[] to, int start) {
		int count = 0;
		for (int i = 0, j = start; i != from.length; ++i) {
			Expr child = from[i];
			if (child.getOpcode() == Opcode.EXPR_and) {
				Expr.Operator conjunct = (Expr.Operator) child;
				j += nestedCopy(conjunct.getOperands(), to, j);
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
	private Expr[] eliminateConstants(Expr[] children) {
		// Count number of constants
		int numConstants = 0;
		for (int i = 0; i != children.length; ++i) {
			Expr child = children[i];
			if (children[i] instanceof Expr.Constant) {
				Expr.Constant c = (Expr.Constant) child;
				// The following is safe only because we assume the expression
				// tree is well-typed.
				Value.Bool b = (Value.Bool) c.getValue();
				if (b.get()) {
					numConstants++;
				} else {
					// A conjunct containing false is false.
					return new Expr[] { c };
				}
			}
		}
		if (numConstants == 0) {
			return children;
		} else {
			//
			Expr[] nChildren = new Expr[children.length - numConstants];
			for (int i = 0, j = 0; i != children.length; ++i) {
				Expr child = children[i];
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
	public Expr[] sortAndRemoveDuplicates(Expr[] children) {
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
	private int isSortedAndUnique(Expr[] children) {
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
