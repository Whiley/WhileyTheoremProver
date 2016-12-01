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

	@Override
	public String toString() {
		String r = opcode.toString();
		if(operands != null) {
			r += "(";
			for(int i=0;i!=operands.length;++i) {
				if(i != 0) {
					r += ", ";
				}
				r += operands[i];
			}
			r += ")";
		}
		if(data != null) {
			r += ":" + data;
		}
		return r;
	}

	// ==================================================================
	// Classes
	// ==================================================================

	public static enum Opcode {
		//
		ITEM_pair(100),
		ITEM_ident(101),
		ITEM_path(102),
		ITEM_name(103),
		// DECLARATIONS
		DECL_linecomment(104),
		DECL_blkcomment(105),
		DECL_import(106),
		DECL_assert(107),
		DECL_type(108),
		DECL_fun(109),
		DECL_macro(110),
		// TYPES
		TYPE_void(0),
		TYPE_any(1),
		TYPE_null(2),
		TYPE_bool(3),
		TYPE_int(4),
		TYPE_nom(5),
		TYPE_ref(6),
		TYPE_arr(7),
		TYPE_rec(8),
		TYPE_fun(9),
		TYPE_or(10),
		TYPE_and(11),
		TYPE_not(12),
		// STMTS
		STMT_block(15),
		STMT_vardecl(16),
		STMT_ifthen(17),
		STMT_caseof(18),
		STMT_exists(35),
		STMT_forall(36),
		// EXPRESSIONS
		EXPR_var(20),
		EXPR_cast(22),
		EXPR_invoke(23),
		// LOGICAL
		EXPR_not(30),
		EXPR_and(31),
		EXPR_or(32),
		EXPR_implies(33),
		EXPR_iff(34),
		// COMPARATORS
		EXPR_eq(40),
		EXPR_neq(41),
		EXPR_lt(42),
		EXPR_lteq(43),
		EXPR_gt(44),
		EXPR_gteq(45),
		EXPR_is(46),
		// ARITHMETIC
		EXPR_neg(50),
		EXPR_add(51),
		EXPR_sub(52),
		EXPR_mul(53),
		EXPR_div(54),
		EXPR_rem(55),
		// ARRAY
		EXPR_arrinit(60),
		EXPR_arrlen(61),
		EXPR_arrgen(62),
		EXPR_arridx(63),
		// RECORDS
		EXPR_recinit(64),
		EXPR_recfield(65),
		// BASE
		CONST_null(66),
		CONST_bool(67),
		CONST_int(68),
		CONST_utf8(69);

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
			super(Opcode.CONST_bool, value);
		}

		public boolean get() {
			return (Boolean) data;
		}
	}

	public static class Int extends Bytecode {
		public Int(BigInteger value) {
			super(Opcode.CONST_int, value);
		}

		public BigInteger get() {
			return (BigInteger) data;
		}
	}

	public static class UTF8 extends Bytecode {
		public UTF8(byte[] bytes) {
			super(Opcode.CONST_utf8, bytes);
		}

		public byte[] get() {
			return (byte[]) data;
		}
	}

	public static class Identifier extends Bytecode {
		public Identifier(String name) {
			super(Opcode.ITEM_ident, name);
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
