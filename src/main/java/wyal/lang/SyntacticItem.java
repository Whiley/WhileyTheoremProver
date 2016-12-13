package wyal.lang;

import wyal.lang.WyalFile.Opcode;
import wybs.lang.SyntacticElement;

public interface SyntacticItem extends SyntacticElement {

	/**
	 * Get the enclosing compilation unit in which this syntactic item is
	 * contained.
	 *
	 * @return
	 */
	public WyalFile getParent();

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
