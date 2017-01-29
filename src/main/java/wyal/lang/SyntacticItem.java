package wyal.lang;

import java.util.Map;

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
	 *            The heap into which this item is being allocated
	 * @param index
	 *            The index at which this item is being allocated
	 */
	public void allocate(SyntacticHeap heap, int index);

	/**
	 * The opcode which defines what this bytecode does. Observe that certain
	 * bytecodes must correspond with specific subclasses. For example,
	 * <code>opcode == LOAD</code> always indicates that <code>this</code> is an
	 * instanceof <code>Load</code>.
	 */
	public Opcode getOpcode();

	/**
	 * Mutate the opcode of this item
	 *
	 * @param opcode
	 */
	public void setOpcode(Opcode opcode);

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
	 * Mutate the ith child of this item
	 *
	 * @param ith
	 * @param child
	 */
	public void setOperand(int ith, SyntacticItem child);

	/**
	 * Get the index of this item in the parent's items table.
	 *
	 * @return
	 */
	public int getIndex();

	/**
	 * Get any data associated with this item. This will be null if no data is
	 * associated.
	 *
	 * @return
	 */
	public Object getData();

	/**
	 * Create a new copy of the given syntactic item with the given operands.
	 * The number of operands must match <code>size()</code> for this item, and
	 * be of appropriate type.
	 *
	 * @param operands
	 * @return
	 */
	public SyntacticItem clone(SyntacticItem[] operands);
}
