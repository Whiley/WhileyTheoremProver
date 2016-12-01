package wyal.util;

import java.util.Arrays;
import java.util.Collection;
import java.util.List;

import wyal.lang.Bytecode.Opcode;
import wyal.lang.SyntacticItem;
import wyal.lang.WyalFile;
import wycc.util.ArrayUtils;
import wybs.lang.Attribute;
import wybs.lang.SyntacticElement;

public class AbstractSyntacticItem extends SyntacticElement.Impl implements SyntacticItem {
	// Constants;
	private final WyalFile parent;
	private final Opcode opcode;
	private final int[] operands;
	protected final Object data;

	public AbstractSyntacticItem(WyalFile parent, Opcode opcode, Attribute... attributes) {
		super(attributes);
		this.parent = parent;
		this.opcode = opcode;
		this.operands = null;
		this.data = null;
	}

	public AbstractSyntacticItem(WyalFile parent, Opcode opcode, List<Integer> operands, Attribute... attributes) {
		this(parent, opcode, ArrayUtils.toIntArray(operands));
	}

	public AbstractSyntacticItem(WyalFile parent, Opcode opcode, int[] operands, Collection<Attribute> attributes) {
		super(attributes);
		this.parent = parent;
		this.opcode = opcode;
		this.operands = operands;
		this.data = null;
	}

	public AbstractSyntacticItem(WyalFile parent, Opcode opcode, int firstOperand, int[] otherOperands, Attribute... attributes) {
		this.parent = parent;
		this.opcode = opcode;
		this.operands = ArrayUtils.append(new int[] { firstOperand }, otherOperands);
		this.data = null;
	}

	protected AbstractSyntacticItem(WyalFile parent, Opcode opcode, Object data, Attribute... attributes) {
		super(attributes);
		this.parent = parent;
		this.opcode = opcode;
		this.operands = null;
		this.data = data;
	}

	protected AbstractSyntacticItem(WyalFile parent, Opcode opcode, Object data, int[] operands, Attribute... attributes) {
		super(attributes);
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
	public int getFirstOperand() {
		return operands[0];
	}

	@Override
	public int[] getOtherOperands() {
		return Arrays.copyOfRange(operands, 1, operands.length);
	}

	@Override
	public int getOperand(int i) {
		return operands[i];
	}

	@Override
	public int[] getOperands() {
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
}
