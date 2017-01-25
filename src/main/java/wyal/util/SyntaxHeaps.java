package wyal.util;

import java.util.Arrays;
import java.util.IdentityHashMap;
import java.util.Map;

import wyal.lang.SyntacticItem;

public class SyntaxHeaps {
	/**
	 * Recursively copy this syntactic item. Observe the cloned syntactic item
	 * is *not* allocated to any heap, and this must be done separately. Also,
	 * all children are recursively cloned as well.
	 *
	 * @return
	 */
	public static <T extends SyntacticItem> T clone(T item) {
		return clone(item, new IdentityHashMap<>());
	}

	/**
	 * Recursively copy this syntactic item. Observe the cloned syntactic item
	 * is *not* allocated to any heap, and this must be done separately. Also,
	 * all children are recursively copied as well.
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
				for (int i = 0; i !=operands.length; ++i) {
					operands[i] = clone(operands[i], mapping);
				}
			}
			// Now, create new item and store that for later.
			clonedItem = item.clone(operands);
			mapping.put(item, clonedItem);
		}
		return (T) clonedItem;
	}

	/**
	 * Create a new syntactic item by replacing all occurrences of one item
	 * (<code>from</code>) with another (<code>to</code>). In the case that
	 * there is no change to the item (or any of its children) then the original
	 * item is returned untouched.
	 *
	 * @param root
	 * @param from
	 * @param to
	 * @return
	 */
	public static SyntacticItem substitute(SyntacticItem root, SyntacticItem from, SyntacticItem to) {
		return null; // TO DO
	}
}
