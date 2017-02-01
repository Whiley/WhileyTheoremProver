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

	private final static RewriteRule[] rules = { new InequalityClosure() };

	private void check(WyalFile.Declaration.Assert decl) {
		AbstractSyntacticHeap heap = new StructurallyEquivalentHeap();
		// Convert the body of the assertion into "expression form". That is,
		// where every node is an expression.
		Formula root = Formulae.toFormula(SyntacticHeaps.clone(decl.getBody()),types);
		// Invert the body of the assertion in order to perform a
		// "proof-by-contradiction". In essence, once rewriting is complete, we
		// should have reduced the term to false (if the original assertion
		// held).
		root = root.invert();
		root = heap.allocate(root);
		Formula oRoot = root;
		print(root);
		System.out.println("--");
		do {
			oRoot = root;
			root = (Formula) pushDownRewrite(root, rules);
		} while(oRoot != root);
		print(root);
		// Prepare for proof-by-contradiction
		heap.print(new PrintWriter(System.out));
		//
		if(isContradiction(root)) {
			return;
		} else {
			// FIXME: throw proper error here
			throw new IllegalArgumentException("Verification error!");
		}
	}


	/**
	 * Initialise the "structural invariant". This invariant states that no two
	 * terms with identical structure can exist.
	 *
	 * @param heap
	 */
	public static void initialiseStructuralInvariant(SyntacticHeap heap) {

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
	 * A structurally equivalent heap is one which maintains the "structural
	 * invariant". Namely, that any two items which are structurally equivalent
	 * are, in fact, the same item.
	 *
	 * @author David J. Pearce
	 *
	 */
	private static class StructurallyEquivalentHeap extends AbstractSyntacticHeap {
		@Override
		public <T extends SyntacticItem> T allocate(T item) {
			SyntacticHeap parent = item.getParent();
			if (parent == this) {
				// Item already allocated to this heap, hence return its existing
				// address.
				return item;
			} else if(parent != null) {
				// This will force an exception
				return super.allocate(item);
			} else {
				// We need to recursively descend into children of this item
				// allocating them all to this heap.
				SyntacticItem[] children = item.getOperands();
				// Initially, this will alias children. In the event of a child
				// which is actually updated, then this will refer to a new
				// array. That will be the signal that we need to create a new
				// item to return.
				SyntacticItem[] nChildren = children;
				if (children != null) {
					for (int i = 0; i != children.length; ++i) {
						SyntacticItem child = children[i];
						// Check for null, since we don't want to try and
						// substitute into null.
						if (child != null) {
							// Perform the substitution in the given child
							SyntacticItem nChild = allocate(child);
							// Check whether anything was actually changed by
							// the substitution.
							if (nChild != child && children == nChildren) {
								// Yes, the child changed and we haven't already
								// cloned the children array. Hence, we'd better
								// clone it now to make sure that the original
								// item is preserved.
								nChildren = Arrays.copyOf(children, children.length);
							}
							nChildren[i] = nChild;
						}
					}
				}
				// Look for any structural equivalents that exist
				// already in this heap. If we find one, then we can
				// just return the directly.
				T equivalent = (T) findStructuralEquivalent(item.getOpcode(), item.getData(), nChildren);
				if (equivalent != null) {
					return equivalent;
				} else if (children != nChildren) {
					// No equivalent was found, but the child array was
					// updated in some way. Therefore, we need to clone
					// the item in order reflect this change.
					item = (T) item.clone(nChildren);
				}
				// Allocate the item (or its clone) into this heap.
				syntacticItems.add(item);
				item.allocate(this, syntacticItems.size()-1);
				return item;
			}
		}

		/**
		 * Look for a structurally equivalent node in the current heap, assuming
		 * that all children are already allocated (and, hence, for which the
		 * invariant is already true).
		 *
		 * @param opcode
		 * @param data
		 * @param children
		 * @return
		 */
		private SyntacticItem findStructuralEquivalent(Opcode opcode, Object data, SyntacticItem[] children) {
			for (int i = 0; i != syntacticItems.size(); ++i) {
				SyntacticItem candidate = syntacticItems.get(i);
				if (opcode == candidate.getOpcode() && Objects.equals(data, candidate.getData())) {
					if (haveIdenticalChildren(children, candidate.getOperands())) {
						return candidate;
					}
				}
			}
			return null;
		}

		private boolean haveIdenticalChildren(SyntacticItem[] left, SyntacticItem[] right) {
			if (left == null || right == null) {
				return left == right;
			} else if (left.length != right.length) {
				return false;
			} else {
				for (int j = 0; j != left.length; ++j) {
					if (left[j] != right[j]) {
						return false;
					}
				}
				return true;
			}
		}
	}

	/**
	 * A simple helper method for debugging expressions which just prints them
	 * to stdout.
	 *
	 * @param item
	 */
	public static void print(WyalFile.Expr item) {
		PrintWriter out = new PrintWriter(System.out);
		new WyalFilePrinter(out).writeExpression(item);
		out.flush();
		System.out.println();
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
