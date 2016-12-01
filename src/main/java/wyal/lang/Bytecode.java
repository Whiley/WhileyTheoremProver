package wyal.lang;

import java.math.BigInteger;
import java.util.Arrays;
import java.util.List;

import wybs.lang.Attribute;
import wybs.lang.NameID;
import wybs.lang.SyntacticElement;
import wycc.util.ArrayUtils;

/**
 * Represents a "bytecode" in the language of the Whiley Theorem Prover.
 *
 * @author David J. Pearce
 *
 * @param <T>
 */
public class Bytecode {
	// Constants;
	private final Opcode opcode;
	private final int[] operands;
	protected final Object data;

	public Bytecode(Opcode opcode) {
		this.opcode = opcode;
		this.operands = null;
		this.data = null;
	}

	public Bytecode(Opcode opcode, List<Integer> operands) {
		this(opcode,ArrayUtils.toIntArray(operands));
	}

	public Bytecode(Opcode opcode, int... operands) {
		this.opcode = opcode;
		this.operands = operands;
		this.data = null;
	}

	public Bytecode(Opcode opcode, int firstOperand, int[] otherOperands) {
		this.opcode = opcode;
		this.operands = ArrayUtils.append(new int[]{firstOperand}, otherOperands);
		this.data = null;
	}

	protected Bytecode(Opcode opcode, Object data) {
		this.opcode = opcode;
		this.operands = null;
		this.data = data;
	}

	protected Bytecode(Opcode opcode, Object data, int... operands) {
		this.opcode = opcode;
		this.operands = operands;
		this.data = data;
	}

	@Override
	public int hashCode() {
		int hash = getOpcode().hashCode() ^ Arrays.hashCode(getOperands());
		if (data != null) {
			hash ^= data.hashCode();
		}
		return hash;
	}

	@Override
	public boolean equals(Object o) {
		if (o instanceof Bytecode) {
			Bytecode bo = (Bytecode) o;
			return getOpcode() == bo.getOpcode() && Arrays.equals(getOperands(), bo.getOperands())
					&& (data == bo.data || (data != null && data.equals(bo.data)));
		}
		return false;
	}
	/**
	 * The opcode which defines what this bytecode does. Observe that certain
	 * bytecodes must correspond with specific subclasses. For example,
	 * <code>opcode == LOAD</code> always indicates that <code>this</code> is an
	 * instanceof <code>Load</code>.
	 */
	public Opcode getOpcode() {
		return opcode;
	}

	/**
	 * Get the number of operands in this bytecode
	 *
	 * @return
	 */
	public int numberOfOperands() {
		return operands.length;
	}

	/**
	 * Get the first operand. For some bytecodes, this is distinguished from the
	 * remainder
	 *
	 * @return
	 */
	public int getFirstOperand() {
		return operands[0];
	}

	/**
	 * Get all operands after first. For some bytecodes, the first is
	 * distinguished from the remainder.
	 *
	 * @return
	 */
	public int[] getOtherOperands() {
		return Arrays.copyOfRange(operands, 1, operands.length);
	}

	/**
	 * Return the ith top-level operand in this bytecode.
	 *
	 * @param i
	 * @return
	 */
	public int getOperand(int i) {
		return operands[i];
	}

	/**
	 * Return the top-level operands in this bytecode.
	 *
	 * @return
	 */
	public int[] getOperands() {
		return operands;
	}

	// ==================================================================
	// Classes
	// ==================================================================

	public static enum Opcode {
		// TYPES
		T_VOID(0),
		T_ANY(1),
		T_NULL(2),
		T_BOOL(3),
		T_INT(4),
		T_NOMINAL(5),
		T_REF(6),
		T_ARRAY(7),
		T_RECORD(8),
		T_FUN(9),
		T_UNION(10),
		T_INTERSECTION(11),
		T_NEGATION(12),
		// STMTS
		BLOCK(15),
		VARDECL(16),
		IFTHEN(17),
		CASEOF(18),
		// EXPRESSIONS
		VARACCESS(20),
		CAST(22),
		FUNCALL(23),
		// LOGICAL
		NOT(30),
		AND(31),
		OR(32),
		IMPLIES(33),
		IFF(34),
		EXISTS(35),
		FORALL(36),
		// COMPARATORS
		EQ(40),
		NEQ(41),
		LT(42),
		LTEQ(43),
		GT(44),
		GTEQ(45),
		IS(46),
		// ARITHMETIC
		NEG(50),
		ADD(51),
		SUB(52),
		MUL(53),
		DIV(54),
		REM(55),
		// ARRAY
		ARRAY_INITIALISER(60),
		ARRAY_LENGTH(61),
		ARRAY_GENERATOR(62),
		ARRAY_ACCESS(63),
		// RECORDS
		RECORD_INITIALISER(64),
		RECORD_ACCESS(65),
		// BASE
		NULL(66),
		BOOL(67),
		INT(68),
		UTF8(69),
		PAIR(100),
		IDENTIFIER(101),
		PATH_ID(102),
		NAME_ID(103);

		public int offset;

		private Opcode(int offset) {
			this.offset = offset;
		}
	}

	// =========================================================================
	// Base Terms
	// =========================================================================
	public static class Bool extends Bytecode {
		public Bool(boolean value) {
			super(Opcode.BOOL, value);
		}

		public boolean get() {
			return (Boolean) data;
		}
	}

	public static class Int extends Bytecode {
		public Int(BigInteger value) {
			super(Opcode.INT, value);
		}

		public BigInteger get() {
			return (BigInteger) data;
		}
	}

	public static class UTF8 extends Bytecode {
		public UTF8(byte[] bytes) {
			super(Opcode.UTF8, bytes);
		}

		public byte[] get() {
			return (byte[]) data;
		}
	}

	public static class Identifier extends Bytecode {
		public Identifier(String name) {
			super(Opcode.IDENTIFIER, name);
		}

		public String get() {
			return (String) data;
		}
	}

	// =========================================================================
	// Bytecode Schemas
	// =========================================================================

	public enum Operands {
		ZERO, ONE, TWO, MANY
	}

	public enum Blocks {
		ZERO, ONE, TWO, MANY
	}

	public enum Extras {
		STRING, // index into string pool
		CONSTANT, // index into constant pool
		TYPE, // index into type pool
		NAME, // index into name pool
		STRING_ARRAY, // determined on the fly
		SWITCH_ARRAY, // determined on the fly
	}

	public static abstract class Schema {
		private final Operands operands;
		private final Blocks blocks;
		private final Extras[] extras;

		public Schema(Operands operands, Extras... extras) {
			this.operands = operands;
			this.blocks = Blocks.ZERO;
			this.extras = extras;
		}

		public Schema(Operands operands, Blocks blocks, Extras... extras) {
			this.operands = operands;
			this.blocks = blocks;
			this.extras = extras;
		}

		public Extras[] extras() {
			return extras;
		}

		public Operands getOperands() {
			return operands;
		}

		public Blocks getBlocks() {
			return blocks;
		}

		public abstract Bytecode construct(int opcode, int[] operands, int[] blocks, Object[] extras);

		@Override
		public String toString() {
			return "<" + operands + " operands, " + Arrays.toString(extras) + ">";
		}
	}
}
