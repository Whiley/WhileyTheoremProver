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

package wyal.lang;

/**
 * A syntactic heap represents a collection of syntactic items.
 *
 * @author David J. Pearce
 *
 */
public interface SyntacticHeap {
	/**
	 * Get the number of items in the heap.
	 *
	 * @return
	 */
	public int size();

	/**
	 * Return the ith syntactic item in this heap. This may return null if the
	 * item in question has been garbage collected.
	 *
	 * @param index
	 * @return
	 */
	public SyntacticItem getSyntacticItem(int ith);

	/**
	 * Determine the index of a given syntactic item in this heap.
	 *
	 * @param item
	 * @return
	 */
	public int getIndexOf(SyntacticItem item);

	/**
	 * <p>
	 * Allocate a given syntactic item into this heap. The item must not already
	 * be allocated to another heap. This will recursively allocate children not
	 * already allocated to this heap. Observe that the item returned is the
	 * actual object allocated into this heap. One should not assume that the
	 * item given is that which is actually allocated.
	 * </p>
	 * <p>
	 * This method will not permit mixed allocation items. That is, when it
	 * encounters an item already allocated to another heap it will simple throw
	 * an exception.
	 * </p>
	 *
	 * @param item
	 * @return
	 */
	public <T extends SyntacticItem> T allocate(T item);

	/**
	 * Get the parent associated with this heap (if any).
	 *
	 * @return
	 */
	public SyntacticHeap getParent();
}
