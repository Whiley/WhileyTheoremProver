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
	 * Allocate a given syntactic item into this heap. The item must not already
	 * be allocated to another heap. This returns the address (i.e. index) of
	 * the allocated item. This will recursively allocate children not already
	 * allocated to this heap.
	 *
	 * @param item
	 * @return
	 */
	public int allocate(SyntacticItem item);
}
