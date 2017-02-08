package wyal.util;

import java.io.PrintWriter;
import java.util.Arrays;
import java.util.IdentityHashMap;
import java.util.Map;
import java.util.Objects;

import wyal.io.WyalFilePrinter;
import wyal.lang.Formula;
import wyal.lang.SyntacticHeap;
import wyal.lang.SyntacticItem;
import wyal.lang.WyalFile;
import wyal.lang.Formula.Polynomial;
import wyal.lang.Formula.Quantifier;
import wyal.lang.Formula.Truth;
import wyal.lang.WyalFile.*;
import wyal.rules.*;

public class AutomatedTheoremProver {
	/**
	 * The type system encapsulates the core algorithms for type simplification
	 * and subtyping testing.
	 */
	private final TypeSystem types;
	/**
	 * The enclosing WyAL file being checked.
	 */
	private final WyalFile parent;

	public AutomatedTheoremProver(final WyalFile parent) {
		this.parent = parent;
		// FIXME: this should be shared between different compilation stages
		this.types = new TypeSystem(parent);
	}

	public void check() {
		for (int i = 0; i != parent.size(); ++i) {
			SyntacticItem item = parent.getSyntacticItem(i);
			if (item instanceof WyalFile.Declaration.Assert) {
				check((WyalFile.Declaration.Assert) item);
			}
		}
	}

	private final static RewriteRule[] rules = {
			new InequalityClosure(),
			new VariableUnification()
		};

	private void check(WyalFile.Declaration.Assert decl) {
		// Convert the body of the assertion into "expression form". That is,
		// where every node is an expression.
		Formula root = Formulae.toFormula(SyntacticHeaps.clone(decl.getBody()),types);
		// Invert the body of the assertion in order to perform a
		// "proof-by-contradiction". In essence, once rewriting is complete, we
		// should have reduced the term to false (if the original assertion
		// held).
		root = root.invert();
		Formula oRoot = root;
		println(root);
		System.out.println("--------------------------");
		do {
			oRoot = root;
			root = (Formula) pushDownRewrite(root, rules);
		} while(oRoot != root);
		println(root);
		//
		if(isContradiction(root)) {
			return;
		} else {
			// FIXME: throw proper error here
			throw new IllegalArgumentException("Verification error!");
		}
	}

	public static interface RewriteRule {
		/**
		 * Attempt to rewrite a given syntactic item, producing a potentially
		 * updated item. In the case that the rewrite did not apply, then the
		 * original item is returned. Otherwise, a new item may be returned
		 * (which may be completed new, or maybe an existing item in the heap).
		 *
		 * @param item
		 * @return
		 */
		Formula rewrite(Formula item);
	}

	/**
	 * <p>
	 * Apply a given set of rewrite rules to a given syntactic item and
	 * (recursively) all children contained therein. This produces a single item
	 * representing this result of this rewrite. Observe that this may be a
	 * freshly created location and (if so) will be detached.
	 * </p>
	 * <p>
	 * This method implements the <i>push-down</i> rewrite strategy. This
	 * iteratively applies the given rules to the item before recursively
	 * applying them to its children.
	 * </p>
	 *
	 * @param item
	 *            The item being reduced via this rewrite. If no rewrites are
	 *            applied, then the original item is returned untouched.
	 * @param rules
	 *            The array of rules to be applied to the the given item. These
	 *            rules are applied iteratively according to their relative
	 *            order in the array.
	 * @return
	 */
	public static Formula pushDownRewrite(Formula item, RewriteRule[] rules) {
		Formula nItem = item;
		// Iterate rewrites until a fixed-point is reached. That is, when there
		// are no further changes to the item.
		do {
			item = nItem;
			for (int i = 0; i != rules.length; ++i) {
				nItem = rules[i].rewrite(nItem);
			}
		} while (nItem != item);
		// Apply rewrites recursively to all children.
		SyntacticItem[] children = nItem.getOperands();
		// Initially, this will alias children. In the event of a child
		// which is actually updated, then this will refer to a new array.
		// That will be the signal that we need to create a new item to
		// return.
		SyntacticItem[] nChildren = children;
		if (children != null) {
			for (int i = 0; i != children.length; ++i) {
				SyntacticItem child = children[i];
				if (child instanceof Formula) {
					// Apply all rewrite rules to the given child
					Formula nChild = pushDownRewrite((Formula) child, rules);
					// Check whether anything was actually changed
					if (nChild != child && children == nChildren) {
						// Yes, the child changed and we haven't already
						// cloned the children array. Hence, we'd better
						// clone it now to make sure that the original item
						// is preserved.
						nChildren = Arrays.copyOf(children, children.length);
					}
					nChildren[i] = nChild;
				}
			}
			// Now, clone the original item if necessary. This is only
			// necessary if the children array as been updated in some
			// way.
			if (children != nChildren) {
				// Create the new item which, at this point, will be
				// detached.
				nItem = nItem.clone(nChildren);
			}
		}
		// Done
		return nItem;
	}

	/**
	 * A simple helper method for debugging expressions which just prints them
	 * to stdout.
	 *
	 * @param item
	 */
	public static void println(WyalFile.Expr item) {
		print(item);
		System.out.println();
	}

	public static void print(WyalFile.Expr item) {
		PrintWriter out = new PrintWriter(System.out);
		new WyalFilePrinter(out).writeExpression(item);
		out.flush();
	}

	/**
	 * Check whether a given expression represents a contradiction (i.e. is
	 * false).
	 *
	 * @param item
	 * @return
	 */
	private static boolean isContradiction(WyalFile.Expr item) {
		if (item instanceof Expr.Constant) {
			Expr.Constant c = (Expr.Constant) item;
			Value.Bool b = (Value.Bool) c.getValue();
			return !b.get();
		}
		return false;
	}
}
