package wyal.util;

import java.util.Arrays;
import java.util.IdentityHashMap;
import java.util.Map;

import wyal.lang.SyntacticHeap;
import wyal.lang.SyntacticItem;

public class SyntacticHeaps {
	/**
	 * <p>
	 * Recursively copy this syntactic item. Observe the resulting cloned
	 * syntactic item is *not* allocated to any heap, and this must be done
	 * separately. All children are recursively cloned as well.
	 * </p>
	 * <p>
	 * This method preserves the underlying aliasing structure of the object
	 * being cloned. However, aliasing information is not preserved across calls
	 * to this method. Furthermore, it is not currently capable of handling
	 * cyclic structures.
	 * </p>
	 *
	 * @return
	 */
	public static <T extends SyntacticItem> T clone(T item) {
		return clone(item, new IdentityHashMap<>());
	}

	/**
	 * Recursively copy this syntactic item. Observe the resulting cloned
	 * syntactic item is *not* allocated to any heap, and this must be done
	 * separately. All children are recursively copied as well.
	 *
	 * @param mapping
	 *            A mapping from the original syntactic items to the cloned
	 *            syntactic items. This is necessary to preserve the aliasing
	 *            structure in the resulting cloned item.
	 * @return
	 */
	private static <T extends SyntacticItem> T clone(T item, Map<SyntacticItem, SyntacticItem> mapping) {
		SyntacticItem clonedItem = mapping.get(item);
		if (clonedItem == null) {
			// Item not previously cloned. Therefore, first create new item
			SyntacticItem[] operands = item.getOperands();
			if (operands != null) {
				operands = Arrays.copyOf(operands, operands.length);
				for (int i = 0; i != operands.length; ++i) {
					SyntacticItem operand = operands[i];
					if (operand != null) {
						operands[i] = clone(operand, mapping);
					}
				}
			}
			// Now, create new item and store that for later.
			clonedItem = item.clone(operands);
			mapping.put(item, clonedItem);
		}
		return (T) clonedItem;
	}

	/**
	 * <p>
	 * Create a new syntactic item by replacing all occurrences of one item
	 * (<code>from</code>) with another (<code>to</code>). In the case that
	 * there is no change to the item (or any of its children) then the original
	 * item is returned untouched. Specifically, the exact same reference will
	 * be returned.
	 * </p>
	 * <p>
	 * Any new items created during this process are allocated into the heap of
	 * the item they are replacing. This is necessary since otherwise a mix of
	 * allocated and unallocated items would be returned, making it difficult to
	 * then allocate them all.
	 * </p>
	 * <p>
	 * This method preserves the underlying aliasing structure of the object
	 * being cloned. However, aliasing information is not preserved across calls
	 * to this method. Furthermore, it is not currently capable of handling
	 * cyclic structures.
	 * </p>
	 *
	 * @param item
	 *            The syntactic item we are currently substituting into
	 * @param from
	 *            The syntactic item we are looking to replace
	 * @param to
	 *            The syntactic item that will replace all occurrences of from
	 * @return
	 */
	public static SyntacticItem substitute(SyntacticItem item, SyntacticItem from, SyntacticItem to) {
		SyntacticItem nItem = substitute(item, from, to, new IdentityHashMap<>());
		if(nItem != item) {
			item.getParent().allocate(nItem);
		}
		return nItem;
	}

	/**
	 * Helper method for above.
	 *
	 * @param mapping
	 *            A mapping from the original syntactic items to the cloned
	 *            syntactic items. This is necessary to preserve the aliasing
	 *            structure in the resulting cloned item.
	 */
	private static SyntacticItem substitute(SyntacticItem item, SyntacticItem from, SyntacticItem to,
			Map<SyntacticItem, SyntacticItem> mapping) {
		SyntacticItem sItem = mapping.get(item);
		if (sItem != null) {
			// We've previously substituted this item already to produce a
			// potentially updated item. Therefore, simply return that item to
			// ensure the original aliasing structure of the ancestor(s) is
			// properly preserved.
			return sItem;
		} else if (item == from) {
			// We've matched the item being replaced, therefore return the item
			// to which it is being replaced.
			return to;
		} else {
			SyntacticItem nItem = item;
			// We need to recursively descend into children of this item looking
			// for the item to replace. The challenge here is that we need to
			// ensure the original item is preserved as is if there is no
			// change.
			SyntacticItem[] children = item.getOperands();
			// Initially, this will alias children. In the event of a child
			// which is actually updated, then this will refer to a new array.
			// That will be the signal that we need to create a new item to
			// return.
			SyntacticItem[] nChildren = children;
			if (children != null) {
				for (int i = 0; i != children.length; ++i) {
					SyntacticItem child = children[i];
					// Check for null, since we don't want to try and substitute
					// into null.
					if (child != null) {
						// Perform the substitution in the given child
						SyntacticItem nChild = substitute(child, from, to, mapping);
						// Check whether anything was actually changed by the
						// substitution.
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
				// necessary if the children array as been updated in some way.
				if (children != nChildren) {
					// Create the new item which, at this point, will be
					// detached.
					nItem = item.clone(nChildren);
				}
			}
			mapping.put(item, nItem);
			return nItem;
		}
	}
}
