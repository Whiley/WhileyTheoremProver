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

package wyal.heap;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.IdentityHashMap;
import java.util.Map;
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
public class StructurallyEquivalentHeap extends AbstractSyntacticHeap implements SyntacticHeap {
	private final SyntacticHeap parent;
	public StructurallyEquivalentHeap(SyntacticHeap parent) {
		this.parent = parent;
		//
		for(int i=0;i<parent.size();i++) {
			// dummy
			syntacticItems.add(parent.getSyntacticItem(i));
		}
	}

	@Override
	public <T extends SyntacticItem> T allocate(T item) {
		return allocate(item,new IdentityHashMap<>());
	}

	private <T extends SyntacticItem> T allocate(T item, Map<SyntacticItem,SyntacticItem> map) {
		//
		SyntacticHeap parent = item.getParent();
		T allocated = (T) map.get(item);
		if(allocated != null) {
			return allocated;
		} else if (parent == this || parent == this.parent) {
			// Item already allocated to this heap, hence return its existing
			// address.
			return item;
		} else if(parent != null) {
			throw new IllegalArgumentException(
					"Cannot allocate item since a descendent is already allocated to another heap");
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
						SyntacticItem nChild = allocate(child, map);
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
			T nItem = item;
			if (children != nChildren) {
				// No equivalent was found, but the child array was
				// updated in some way. Therefore, we need to clone
				// the item in order reflect this change.
				nItem = (T) item.clone(nChildren);
			}
			// Look for any structural equivalents that exist
			// already in this heap. If we find one, then we can
			// just return the directly.
			T equivalent = (T) findStructuralEquivalent(nItem, item.getClass());
			if (equivalent == null) {
				// Allocate the item (or its clone) into this heap.
				nItem = internalAllocate(nItem);
			} else {
				nItem = equivalent;
			}
			map.put(item,nItem);
			return nItem;
		}
	}

	private <T extends SyntacticItem> T internalAllocate(T item) {
		SyntacticHeap parent = item.getParent();
		if (parent == this || parent == this.parent) {
			// Item already allocated to this heap, hence nothing to do.
		} else if (parent != null) {
			throw new IllegalArgumentException(
					"Cannot allocate item since a descendent is already allocated to another heap");
		} else {
			// Item not allocated to this heap. Therefore, recursively allocate
			// all children ...
			for (int i = 0; i != item.size(); ++i) {
				SyntacticItem child = item.getOperand(i);
				if (child != null) {
					internalAllocate(child);
				}
			}
			// ... and allocate item itself
			int index = syntacticItems.size();
			syntacticItems.add(item);
			item.allocate(this, index);
		}
		// We just return the original item here since, in the abstract case,
		// we're not doing anything fancy. Subclasses may choose to do more,
		// which is why we have this hook here.
		return item;
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
	private SyntacticItem findStructuralEquivalent(SyntacticItem item, Class<?> clazz) {
		for (int i = 0; i != syntacticItems.size(); ++i) {
			SyntacticItem candidate = getSyntacticItem(i);
			if(candidate.getClass() == clazz && item.equals(candidate)) {
				return candidate;
			}
		}
		return null;
	}

	private boolean haveIdenticalChildren(SyntacticItem[] left, SyntacticItem[] right) {
		if (left == null || right == null) {
			return left == right;
		} else if (left.length != right.length) {
			return false;
		} else if(left.getClass().equals(right.getClass())){
			for (int j = 0; j != left.length; ++j) {
				if (left[j] != right[j]) {
					return false;
				}
			}
			return true;
		} else {
			return false;
		}
	}
}
