package wyal.util;

import java.util.Arrays;
import java.util.Objects;

import wyal.lang.SyntacticHeap;
import wyal.lang.SyntacticItem;
import wyal.lang.WyalFile;

/**
 * A structurally equivalent heap is one which maintains the "structural
 * invariant". Namely, that any two items which are structurally equivalent
 * are, in fact, the same item.
 *
 * @author David J. Pearce
 *
 */
public class StructurallyEquivalentHeap extends AbstractSyntacticHeap {
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
	private SyntacticItem findStructuralEquivalent(WyalFile.Opcode opcode, Object data, SyntacticItem[] children) {
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
