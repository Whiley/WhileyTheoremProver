// Copyright 2017 David J. Pearce
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//    http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

package wyal.heap;

import java.math.BigInteger;
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

public abstract class AbstractSyntacticItem extends SyntacticElement.Impl
		implements Comparable<SyntacticItem>, SyntacticItem {
	// Constants;
	private SyntacticHeap parent;
	private int index; // index in the parent
	private Opcode opcode;
	private SyntacticItem[] operands;
	protected Object data;

	public AbstractSyntacticItem(Opcode opcode) {
		super();
		this.opcode = opcode;
		this.operands = null;
		this.data = null;
	}

	public AbstractSyntacticItem(Opcode opcode, Attribute... attributes) {
		super(attributes);
		this.opcode = opcode;
		this.operands = null;
		this.data = null;
	}

	public AbstractSyntacticItem(Opcode opcode, List<SyntacticItem> operands) {
		this(opcode, operands.toArray(new SyntacticItem[operands.size()]));
	}

	public AbstractSyntacticItem(Opcode opcode, SyntacticItem... operands) {
		this.opcode = opcode;
		this.operands = operands;
		this.data = null;
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
	public void allocate(SyntacticHeap heap, int index) {
		if(parent != null && parent != heap) {
			throw new IllegalArgumentException(
					"item already allocated to different heap (" + getClass().getName() + ";" + parent + ", " + heap
							+ ")");
		}

		this.parent = heap;
		this.index = index;
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
		if (parent != null) {
			return index;
		} else {
			throw new IllegalArgumentException("SyntacticItem not allocated to heap");
		}
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
				if(item != null && item.getParent() != null) {
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

	@Override
	public int compareTo(SyntacticItem other) {
		int diff = opcode.ordinal() - other.getOpcode().ordinal();
		if (diff != 0) {
			return diff;
		}
		// We have two items with the same opcode. Need to investigate their
		// structure.
		diff = size() - other.size();
		if (diff != 0) {
			return diff;
		}
		for (int i = 0; i != size(); ++i) {
			SyntacticItem my_ith = getOperand(i);
			SyntacticItem other_ith = other.getOperand(i);
			if (my_ith == null || other_ith == null) {
				if(other_ith == null) {
					return 0;
				} else {
					// null is below everything
					return -1;
				}
			} else {
				diff = my_ith.compareTo(other_ith);
				if (diff != 0) {
					return diff;
				}
			}
		}
		return compareData(data, other.getData());
	}

	/**
	 * Compare the data object associated with a given syntactic item. An
	 * important question here is what kinds of data are actually permitted. At
	 * this stage, it's not completely clear. However, at least:
	 * <code>Boolean</code>, <code>BigInteger</code>, <code>String</code> and
	 * <code>byte[]</code>.  For simplicity, we'll order them according to this sequence.
	 *
	 * @param leftData
	 * @param rightData
	 * @return
	 */
	private int compareData(Object leftData, Object rightData) {
		if(leftData == null || rightData == null) {
			if(leftData == rightData) {
				return 0;
			} else if(leftData == null) {
				return -1;
			} else {
				return 1;
			}
		}
		// At this point, we have two non-null data items. Therefore, we need to
		// determine whether they refer to the same kind of item or to different
		// kinds. In the latter case, we need to determine the relative ordering
		// of kinds.
		int leftKind = getDataKind(leftData);
		int rightKind = getDataKind(rightData);
		if(leftKind != rightKind) {
			return leftKind - rightKind;
		} else {
			switch(leftKind) {
			case 0: // Boolean
				return ((Boolean)leftData).compareTo((Boolean)rightData);
			case 1: // BigInteger
				return ((BigInteger)leftData).compareTo((BigInteger)rightData);
			case 2: // String
				return ((String)leftData).compareTo((String)rightData);
			default:
				// byte[]
				byte[] leftBytes = (byte[]) leftData;
				byte[] rightBytes = (byte[]) rightData;
				if(leftBytes.length != rightBytes.length) {
					return leftBytes.length - rightBytes.length;
				} else {
					for(int i=0;i!=leftBytes.length;++i) {
						int c = Byte.compare(leftBytes[i], rightBytes[i]);
						if(c != 0) {
							return c;
						}
					}
					//
					return 0;
				}
			}
		}
	}

	private int getDataKind(Object o) {
		if (o instanceof Boolean) {
			return 0;
		} else if (o instanceof BigInteger) {
			return 1;
		} else if (o instanceof String) {
			return 2;
		} else if (o instanceof byte[]) {
			return 3;
		} else {
			throw new IllegalArgumentException("unknown datakind encountered");
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

		public abstract AbstractSyntacticItem construct(int opcode, int[] operands, int[] blocks, Object[] extras);

		@Override
		public String toString() {
			return "<" + operands + " operands, " + Arrays.toString(extras) + ">";
		}
	}
}
