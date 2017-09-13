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

import wyal.lang.WyalFile;
import wybs.lang.SyntacticHeap;
import wybs.lang.SyntacticItem;
import wybs.util.AbstractSyntacticHeap;

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
	public SyntacticHeap getParent() {
		return parent;
	}

	@Override
	public <T extends SyntacticItem> T allocate(T item) {
		return allocate(item,new IdentityHashMap<>());
	}

	private <T extends SyntacticItem> T allocate(T item, Map<SyntacticItem,SyntacticItem> map) {
		//
		SyntacticHeap parent = item.getHeap();
		T allocated = (T) map.get(item);
		if(allocated != null) {
			return allocated;
		} else if (parent == this || parent == this.parent) {
			// Item already allocated to this heap, hence return its existing
			// address.
			return item;
		} else {
			// We need to recursively descend into children of this item
			// allocating them all to this heap.
			SyntacticItem[] children = item.getAll();
			// Initially, this will alias children. In the event of a child
			// which is actually updated, then this will refer to a new
			// array. That will be the signal that we need to create a new
			// item to return.
			SyntacticItem[] nChildren = new SyntacticItem[item.size()];
			if (children != null) {
				for (int i = 0; i != children.length; ++i) {
					SyntacticItem child = children[i];
					// Check for null, since we don't want to try and
					// substitute into null.
					if (child != null) {
						// Perform the substitution in the given child
						nChildren[i] = allocate(child, map);
					}
				}
			}
			T nItem = (T) item.clone(nChildren);
			// Look for any structural equivalents that exist
			// already in this heap. If we find one, then we can
			// just return the directly.
			T equivalent = (T) findStructuralEquivalent(nItem, item.getClass());
			//
			if (equivalent == null) {
				// Allocate the item (or its clone) into this heap.
				int index = syntacticItems.size();
				syntacticItems.add(nItem);
				nItem.allocate(this, index);
			} else {
				nItem = equivalent;
			}
			map.put(item,nItem);
			return nItem;
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
