package wyal.util;

import java.util.Arrays;
import java.util.Collection;
import java.util.List;

import wyal.lang.WyalFile.Opcode;
import wyal.lang.SyntacticItem;
import wyal.lang.WyalFile;
import wycc.util.ArrayUtils;
import wybs.lang.Attribute;
import wybs.lang.SyntacticElement;

public class AbstractSyntacticItem extends SyntacticElement.Impl implements SyntacticItem {
	// Constants;
	private final WyalFile parent;
	private final Opcode opcode;
	private final SyntacticItem[] operands;
	protected final Object data;

	public AbstractSyntacticItem(WyalFile parent, Opcode opcode, Attribute... attributes) {
		super(attributes);
		this.parent = parent;
		this.opcode = opcode;
		this.operands = null;
		this.data = null;
	}

	public AbstractSyntacticItem(WyalFile parent, Opcode opcode, List<SyntacticItem> operands) {
		this(parent, opcode, operands.toArray(new SyntacticItem[operands.size()]));
	}

	public AbstractSyntacticItem(WyalFile parent, Opcode opcode, SyntacticItem[] operands) {
		this.parent = parent;
		this.opcode = opcode;
		this.operands = operands;
		this.data = null;
	}

//	public AbstractSyntacticItem(WyalFile parent, Opcode opcode, int firstOperand, int[] otherOperands, Attribute... attributes) {
//		this.parent = parent;
//		this.opcode = opcode;
//		this.operands = ArrayUtils.append(new int[] { firstOperand }, otherOperands);
//		this.data = null;
//	}

	protected AbstractSyntacticItem(WyalFile parent, Opcode opcode, Object data) {
		this.parent = parent;
		this.opcode = opcode;
		this.operands = null;
		this.data = data;
	}

	protected AbstractSyntacticItem(WyalFile parent, Opcode opcode, Object data, SyntacticItem[] operands) {
		this.parent = parent;
		this.opcode = opcode;
		this.operands = operands;
		this.data = data;
	}

	@Override
	public WyalFile getParent() {
		return parent;
	}

	@Override
	public Opcode getOpcode() {
		return opcode;
	}

	@Override
	public int numberOfOperands() {
		return operands.length;
	}

	@Override
	public SyntacticItem getOperand(int i) {
		return operands[i];
	}

	@Override
	public SyntacticItem[] getOperands() {
		return operands;
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
		if (o instanceof AbstractSyntacticItem) {
			AbstractSyntacticItem bo = (AbstractSyntacticItem) o;
			return getOpcode() == bo.getOpcode() && Arrays.equals(getOperands(), bo.getOperands())
					&& (data == bo.data || (data != null && data.equals(bo.data)));
		}
		return false;
	}

	@Override
	public String toString() {
		String r = opcode.toString();
		if (operands != null) {
			r += "(";
			for (int i = 0; i != operands.length; ++i) {
				if (i != 0) {
					r += ", ";
				}
				r += operands[i];
			}
			r += ")";
		}
		if (data != null) {
			r += ":" + data;
		}
		return r;
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

		public abstract AbstractSyntacticItem construct(int opcode, int[] operands, int[] blocks, Object[] extras);

		@Override
		public String toString() {
			return "<" + operands + " operands, " + Arrays.toString(extras) + ">";
		}
	}
}
