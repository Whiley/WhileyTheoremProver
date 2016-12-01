package wyal.lang;

import wyal.lang.Bytecode.Opcode;
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
	public int numberOfOperands();

	/**
	 * Get the first operand. For some bytecodes, this is distinguished from the
	 * remainder
	 *
	 * @return
	 */
	public int getFirstOperand();

	/**
	 * Get all operands after first. For some bytecodes, the first is
	 * distinguished from the remainder.
	 *
	 * @return
	 */
	public int[] getOtherOperands();

	/**
	 * Return the ith top-level operand in this bytecode.
	 *
	 * @param i
	 * @return
	 */
	public int getOperand(int i);

	/**
	 * Return the top-level operands in this bytecode.
	 *
	 * @return
	 */
	public int[] getOperands();

}
