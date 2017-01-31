package wyal.rules;

import java.util.Arrays;

import wyal.lang.SyntacticItem;
import wyal.lang.WyalFile.Value;
import wyal.lang.WyalFile.Expr;
import wyal.lang.WyalFile.Opcode;
import wyal.util.AutomatedTheoremProver.RewriteRule;
import wycc.util.ArrayUtils;

/**
 * Performs a range of simplifications related to disjuncts. In particular:
 *
 * <ol>
 * <li><b>Eliminates boolean constants</b>. Disjuncts containing
 * <code>true</code> are reduced to <code>true</code>. In contrast, any
 * occurrences of <code>false</code> are simply removed.</li>
 * <li><b>Flattens nested disjuncts</b>. All nested disjuncts are recursively
 * flattened into a single disjunct. For example, <code> (x || (y || z))</code>
 * is flattened to <code>(x || y || z)</code>.</li>
 * <li><b>Eliminates singleton disjuncts</b>. A disjunct containing a single
 * (non-disjunct) child is reduced to that child.</li>
 * </ol>
 *
 * The implementation attempts to eliminate dynamic memory allocation in the
 * case that no reduction is applied.
 *
 * @author David J. Pearce
 *
 */
public class OrElimination implements RewriteRule {

	@Override
	public SyntacticItem rewrite(SyntacticItem item) {
		if (item.getOpcode() == Opcode.EXPR_or) {
			// Matched disjunct
			Expr.Operator disjunct = (Expr.Operator) item;
			Expr[] children = disjunct.getOperands();
			// Flatten nested intersections
			children = flatternNestedDisjuncts(children);
			// Eliminate truths
			children = eliminateConstants(children);
			// Ensure sorted and unique
			children = sortAndRemoveDuplicates(children);
			// And, finally...
			if (children.length == 0) {
				// Return false here since the only way it's possible to get here
				// is if the disjunct contained only false at the end.
				return new Expr.Constant(new Value.Bool(false));
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
	 * Recursively remove nested disjuncts. If no nested disjuncts are
	 * encountered, then the same array is returned. Otherwise, a new array
	 * containing all elements from both is returned. For example
	 * <code>[x, y && z]</code> is returned as <code>[x,y,z]</code>.
	 *
	 *
	 * @param children
	 * @return
	 */
	private Expr[] flatternNestedDisjuncts(Expr[] children) {
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
	 * Count the total number of elements in this array which are not disjuncts.
	 * This recursively includes nested disjuncts in this count. For example,
	 * <code>[x, y && z]</code> returns a count of <code>3</code>.
	 *
	 * @param children
	 * @return
	 */
	private int nestedCount(Expr[] children) {
		int count = 0;
		for (int i = 0; i != children.length; ++i) {
			Expr child = children[i];
			if (child.getOpcode() == Opcode.EXPR_or) {
				Expr.Operator disjunct = (Expr.Operator) child;
				count += nestedCount(disjunct.getOperands());
			} else {
				count = count + 1;
			}
		}
		return count;
	}

	/**
	 * Copy non-disjunct expressions from one array to another. This will
	 * recursively copy the children of disjunct expressions as well.
	 *
	 * @param from
	 *            The array to be copied from.
	 * @param to
	 *            The array to which non-disjuncts are copied.
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
			if (child.getOpcode() == Opcode.EXPR_or) {
				Expr.Operator disjunct = (Expr.Operator) child;
				j += nestedCopy(disjunct.getOperands(), to, j);
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
					// A disjunct containing true is true.
					return new Expr[] { c };
				} else {
					numConstants++;
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
