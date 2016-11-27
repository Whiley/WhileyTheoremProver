package wyail.util;

import java.util.Arrays;

import wyail.lang.*;

public abstract class AbstractBytecode implements Bytecode {
	private final int[] operands;

	public AbstractBytecode() {
		this.operands = null;
	}

	public AbstractBytecode(int operand) {
		this.operands = new int[] { operand };
	}

	public AbstractBytecode(int... operands) {
		this.operands = operands;
	}

	@Override
	public int hashCode() {
		return getOpcode().hashCode() ^ Arrays.hashCode(getOperands());
	}

	@Override
	public boolean equals(Object o) {
		if (o instanceof AbstractBytecode) {
			AbstractBytecode bo = (AbstractBytecode) o;
			return getOpcode() == bo.getOpcode() && Arrays.equals(getOperands(), bo.getOperands());
		}
		return false;
	}

	/**
	 * Return the opcode value of this bytecode.
	 *
	 * @return
	 */
	@Override
	public abstract Bytecode.Opcode getOpcode();

	/**
	 * Return the top-level operands in this bytecode.
	 *
	 * @return
	 */
	@Override
	public int[] getOperands() {
		if(operands == null) {
			return new int[0];
		} else {
			return operands;
		}
	}

	/**
	 * Return the number of top-level operands in this bytecode
	 * @return
	 */
	@Override
	public int numberOfOperands() {
		if(operands == null) {
			return 0;
		} else {
			return operands.length;
		}
	}

	/**
	 * Return the ith top-level operand in this bytecode.
	 *
	 * @param i
	 * @return
	 */
	@Override
	public int getOperand(int i) {
		return operands[i];
	}

	@Override
	public String toString() {
		String r = getOpcode().toString();
		if (operands != null) {
			r += "(";
			for (int i = 0; i != operands.length; ++i) {
				if (i != 0) {
					r += ",";
				}
				r += operands[i];
			}
			r += ")";
		}
		return r;
	}

	/**
	 * ==================================================================
	 * Individual Bytecode Schemas
	 * ==================================================================
	 */
	public static final Schema[] schemas = new Schema[255];

	static {
		schemas[Opcode.CONST.ordinal()] = new Schema(Operands.ZERO, Extras.CONSTANT) {
			@Override
			public Bytecode construct(int opcode, int[] operands, int[] blocks, Object[] extras) {
				return new Constant((Value) extras[0]);
			}
		};
	}
}
