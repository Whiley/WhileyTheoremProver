package wyal.util;

import java.util.Arrays;
import java.util.Collection;
import java.util.List;
import java.util.Map;

import wyal.lang.WyalFile.Opcode;
import wyal.lang.SyntacticHeap;
import wyal.lang.SyntacticItem;
import wyal.lang.WyalFile;
import wycc.util.ArrayUtils;
import wybs.lang.Attribute;
import wybs.lang.SyntacticElement;

public abstract class AbstractSyntacticItem extends SyntacticElement.Impl implements SyntacticItem {
	// Constants;
	private SyntacticHeap parent;
	private Opcode opcode;
	private SyntacticItem[] operands;
	protected Object data;

	public AbstractSyntacticItem(Opcode opcode, Attribute... attributes) {
		super(attributes);
		this.opcode = opcode;
		this.operands = null;
		this.data = null;
	}

	public AbstractSyntacticItem(Opcode opcode, List<SyntacticItem> operands) {
		this(opcode, operands.toArray(new SyntacticItem[operands.size()]));
	}

	public AbstractSyntacticItem(Opcode opcode, SyntacticItem[] operands) {
		this.opcode = opcode;
		this.operands = operands;
		this.data = null;;
	}

	protected AbstractSyntacticItem(Opcode opcode, Object data) {
		this.opcode = opcode;
		this.operands = null;
		this.data = data;
	}

	protected AbstractSyntacticItem(Opcode opcode, Object data, SyntacticItem[] operands) {
		this.opcode = opcode;
		this.operands = operands;
		this.data = data;
	}

	@Override
	public SyntacticHeap getParent() {
		return parent;
	}

	@Override
	public void setParent(SyntacticHeap heap) {
		if(parent != null) {
			throw new IllegalArgumentException("item already allocated to heap");
		}
		this.parent = heap;
	}

	@Override
	public Opcode getOpcode() {
		return opcode;
	}

	@Override
	public void setOpcode(Opcode opcode) {
		this.opcode = opcode;
	}


	@Override
	public int size() {
		if(operands != null) {
			return operands.length;
		} else {
			return 0;
		}
	}

	@Override
	public SyntacticItem getOperand(int i) {
		return operands[i];
	}

	@Override
	public void setOperand(int ith, SyntacticItem child) {
		operands[ith] = child;
	}

	@Override
	public SyntacticItem[] getOperands() {
		return operands;
	}

	@Override
	public int getIndex() {
		return parent.getIndexOf(this);
	}

	@Override
	public Object getData() {
		return data;
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
				SyntacticItem item = operands[i];
				if(item != null) {
					r += item.getIndex();
				} else {
					r += "?";
				}
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
