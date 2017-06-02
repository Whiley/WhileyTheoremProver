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

import java.io.PrintWriter;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.IdentityHashMap;
import java.util.List;
import java.util.Map;

import wyal.lang.SyntacticHeap;
import wyal.lang.SyntacticItem;
import wyal.lang.WyalFile;
import wybs.lang.Attribute;
import wytp.proof.Formula;

public abstract class AbstractSyntacticHeap implements SyntacticHeap {
	protected final ArrayList<SyntacticItem> syntacticItems = new ArrayList<>();

	@Override
	public int size() {
		return syntacticItems.size();
	}

	@Override
	public SyntacticItem getSyntacticItem(int index) {
		return syntacticItems.get(index);
	}

	@Override
	public int getIndexOf(SyntacticItem item) {
		for (int i = 0; i != syntacticItems.size(); ++i) {
			if (syntacticItems.get(i) == item) {
				return i;
			}
		}
		throw new IllegalArgumentException("invalid syntactic item");
	}

	public <T extends SyntacticItem> List<T> getSyntacticItems(Class<T> kind) {
		ArrayList<T> matches = new ArrayList<>();
		for (int i = 0; i != syntacticItems.size(); ++i) {
			SyntacticItem item = syntacticItems.get(i);
			if (kind.isInstance(item)) {
				matches.add((T) item);
			}
		}
		return matches;
	}

	@Override
	public <T extends SyntacticItem> T allocate(T item) {
		return internalAllocate(item, new HashMap<>());
	}

	private <T extends SyntacticItem> T internalAllocate(T item, Map<SyntacticItem,SyntacticItem> map) {
		SyntacticHeap parent = item.getParent();
		T allocated = (T) map.get(item);
		if(allocated != null) {
			return allocated;
		} else if (parent == this) {
			// Item already allocated to this heap, hence nothing to do.
			return item;
		} else {
			// Item not allocated to this heap. Therefore, recursively allocate
			// all children.
			SyntacticItem[] operands = new SyntacticItem[item.size()];
			for (int i = 0; i != operands.length; ++i) {
				SyntacticItem child = item.getOperand(i);
				if (child != null) {
					child = internalAllocate(child,map);
				}
				operands[i] = child;
			}
			// Clone item prior to allocation
			T nItem = (T) item.clone(operands);
			// Determine index for allocation
			int index = syntacticItems.size();
			syntacticItems.add(nItem);
			// ... and allocate item itself
			nItem.allocate(this, index);
			map.put(item, nItem);
			return nItem;
		}
	}

	public void print(PrintWriter out) {
		String lenStr = Integer.toString(syntacticItems.size());
		for (int i = 0; i != syntacticItems.size(); ++i) {
			SyntacticItem item = syntacticItems.get(i);
			out.print("// ");
			// Right align the string to ensure that all bytecodes are
			// displayed on the same column. This just helps reading them.
			String iStr = Integer.toString(i);
			for (int j = iStr.length(); j < lenStr.length(); ++j) {
				out.print(" ");
			}
			out.print("#" + i + " " + item);
			//
			List<Attribute> attributes = item.attributes();
			if (attributes.size() > 0) {
				out.print(" [");
				for (int j = 0; j != attributes.size(); ++j) {
					if (j != 0) {
						out.print(", ");
					}
					out.print(attributes.get(j));
				}
				out.print("]");
			}

			out.println();
		}
		out.flush();
	}
}
