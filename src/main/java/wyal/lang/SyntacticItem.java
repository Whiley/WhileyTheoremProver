package wyal.lang;

import wyal.lang.WyalFile.Opcode;
import wybs.lang.SyntacticElement;

public interface SyntacticItem extends SyntacticElement {

	/**
	 * Get the enclosing compilation unit in which this syntactic item is
	 * contained. This maybe null if the item is not yet allocate to a heap.
	 *
	 * @return
	 */
	public SyntacticHeap getParent();

	/**
	 * Allocated the given item to a syntactic heap. Note that an item can only
	 * be allocated to one heap at a time. Therefore, an exception will be
	 * raised if this item is already allocated to another heap.
	 *
	 * @param heap
	 */
	public void setParent(SyntacticHeap heap);

	/**
	 * The opcode which defines what this bytecode does. Observe that certain
	 * bytecodes must correspond with specific subclasses. For example,
	 * <code>opcode == LOAD</code> always indicates that <code>this</code> is an
	 * instanceof <code>Load</code>.
	 */
	public Opcode getOpcode();

	/**
	 * Get the number of operands in this bytecode
	 *
	 * @return
	 */
	public int size();

	/**
	 * Return the ith top-level operand in this bytecode.
	 *
	 * @param i
	 * @return
	 */
	public SyntacticItem getOperand(int i);

	/**
	 * Return the top-level operands in this bytecode.
	 *
	 * @return
	 */
	public SyntacticItem[] getOperands();

	/**
	 * Get the index of this item in the parent's items table.
	 *
	 * @return
	 */
	public int getIndex();
}
