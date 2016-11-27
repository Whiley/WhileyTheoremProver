package wyail.lang;

import java.util.Arrays;
import java.util.List;

import wyail.util.AbstractBytecode;
import wybs.lang.NameID;
import wycc.util.ArrayUtils;

/**
 * Represents a "bytecode" in the language of the Whiley Theorem Prover.
 *
 * @author David J. Pearce
 *
 * @param <T>
 */
public interface Bytecode {

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
		CONST(21),
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
		ARRAY(60),
		ARRAYLENGTH(61),
		ARRAYGEN(62),
		INDEXOF(63),
		// Record
		TUPLE(64),
		LOAD(65);

		public int offset;

		private Opcode(int offset) {
			this.offset = offset;
		}
	}

	// ===============================================================
	// Bytecode Types
	// ===============================================================
	/**
	 * Represents the class of bytecodes which correspond to types in the
	 * source language.
	 *
	 * @author David J. Pearce
	 *
	 */
	public interface Type extends Bytecode {

	}

	public final static class PrimitiveType extends AbstractBytecode implements Type {
		private final Opcode opcode;

		public PrimitiveType(Opcode opcode) {
			if(!isPrimitiveType(opcode)) {
				throw new IllegalArgumentException("invalid primitive type");
			}
			this.opcode = opcode;
		}

		@Override
		public Opcode getOpcode() {
			return opcode;
		}

		private static boolean isPrimitiveType(Opcode opcode) {
			switch (opcode) {
			case T_VOID:
			case T_ANY:
			case T_NULL:
			case T_BOOL:
			case T_INT:
				return true;
			default:
				return false;
			}
		}
	}

	public final static class NominalType extends AbstractBytecode implements Type {
		/**
		 * The string components that are written at the source level. These
		 * need to be resolved in the given context to generate the appropriate
		 * NameID.
		 */
		private final String[] elements;

		/**
		 * The fully resolved NameID that this nominal type refers to. If this
		 * hasn't been resolved yet, then it will be null.
		 */
		private final NameID name;

		public NominalType(List<String> elements, NameID name) {
			this(ArrayUtils.toStringArray(elements), name);
		}

		public NominalType(String[] elements, NameID name) {
			this.elements = elements;
			this.name = name;
		}

		@Override
		public Opcode getOpcode() {
			return Opcode.T_NOMINAL;
		}

		public String[] getElements() {
			return elements;
		}

		public NameID getResolvedName() {
			return name;
		}
	}

	public final static class ArrayType extends AbstractBytecode implements Type {
		public ArrayType(int operand) {
			super(operand);
		}

		@Override
		public Opcode getOpcode() {
			return Opcode.T_ARRAY;
		}
	}

	public final static class ReferenceType extends AbstractBytecode implements Type {
		public ReferenceType(int operand) {
			super(operand);
		}

		@Override
		public Opcode getOpcode() {
			return Opcode.T_REF;
		}
	}

	public final static class NegationType extends AbstractBytecode implements Type {
		public NegationType(int operand) {
			super(operand);
		}

		@Override
		public Opcode getOpcode() {
			return Opcode.T_NEGATION;
		}
	}

	public final static class UnionType extends AbstractBytecode implements Type {
		public UnionType(int... operands) {
			super(operands);
		}

		@Override
		public Opcode getOpcode() {
			return Opcode.T_UNION;
		}
	}

	public final static class IntersectionType extends AbstractBytecode implements Type {
		public IntersectionType(int... operands) {
			super(operands);
		}

		@Override
		public Opcode getOpcode() {
			return Opcode.T_INTERSECTION;
		}
	}

	// ===============================================================
	// Bytecode Expressions
	// ===============================================================

	/**
	 * Represents the class of bytecodes which correspond to expressions in the
	 * source language.
	 *
	 * @author David J. Pearce
	 *
	 */
	public interface Expr extends Bytecode {

	}

	public final static class VariableAccess extends AbstractBytecode implements Expr {
		public VariableAccess(int operand) {
			super(operand);
		}

		@Override
		public Opcode getOpcode() {
			return Opcode.VARACCESS;
		}
	}

	public final static class Constant extends AbstractBytecode implements Expr {
		private final Value value;

		public Constant(Value value) {
			this.value = value;
		}

		public Value getValue() {
			return value;
		}

		@Override
		public Opcode getOpcode() {
			return Opcode.CONST;
		}
	}

	public final static class Cast extends AbstractBytecode implements Expr {
		public Cast(int type, int operand) {
			super(type,operand);
		}

		@Override
		public Opcode getOpcode() {
			return Opcode.CAST;
		}
	}

	public final static class Operator extends AbstractBytecode implements Expr {
		private final Opcode opcode;

		public Operator(Opcode opcode, List<Integer> operands) {
			this(opcode,ArrayUtils.toIntArray(operands));
		}

		public Operator(Opcode opcode, int... operands) {
			super(operands);
			this.opcode = opcode;
		}

		@Override
		public Opcode getOpcode() {
			return opcode;
		}
	}

	// ===============================================================
	// Bytecode Statements
	// ===============================================================

	/**
	 * A statement bytecode represents a bytecode that contains a sequence of
	 * zero or more bytecodes. For example, a loop bytecode contains its loop
	 * body. The nested blocks of bytecodes are represented as a block
	 * identifier in the enclosing forest.
	 *
	 * @author David J. Pearce
	 *
	 */
	public interface Stmt extends Bytecode {

	}

	/**
	 * <p>
	 * A variable declaration bytecode has one of the following two layouts:
	 * </p>
	 *
	 * <pre>
	 * +--------+------+
	 * | opcode | name |
	 * +--------+------+
	 * </pre>
	 *
	 * @author David J. Pearce
	 *
	 */
	public static final class VariableDeclaration extends AbstractBytecode implements Stmt {
		/**
		 * Variable name
		 */
		private final String name;

		public VariableDeclaration(int type, String name) {
			super(type);
			this.name = name;
		}

		public String getName() {
			return name;
		}

		@Override
		public Opcode getOpcode() {
			return Opcode.VARDECL;
		}

		@Override
		public boolean equals(Object o) {
			if(o instanceof VariableDeclaration) {
				VariableDeclaration vd = (VariableDeclaration) o;
				return name.equals(vd.name) && super.equals(o);
			}
			return false;
		}

		@Override
		public int hashCode() {
			return name.hashCode() ^ super.hashCode();
		}

		@Override
		public String toString() {
			return "decl " + name;
		}
	}

	public static final class IfThen extends AbstractBytecode implements Stmt {

		public IfThen(int ifBlock, int thenBlock) {
			super(ifBlock,thenBlock);
		}

		@Override
		public Opcode getOpcode() {
			return Opcode.IFTHEN;
		}
	}

	public static final class CaseOf extends AbstractBytecode implements Stmt {
		public CaseOf(List<Integer> caseBlocks) {
			this(ArrayUtils.toIntArray(caseBlocks));
		}
		public CaseOf(int... caseBlocks) {
			super(caseBlocks);
		}

		@Override
		public Opcode getOpcode() {
			return Opcode.CASEOF;
		}
	}

	public static final class Quantifier extends AbstractBytecode implements Stmt {
		private final boolean isUniversal;

		public Quantifier(boolean isUniversal, int[] parameters, int body) {
			super(ArrayUtils.append(parameters, new int[] { body }));
			this.isUniversal = isUniversal;
		}

		@Override
		public Opcode getOpcode() {
			if (isUniversal) {
				return Opcode.FORALL;
			} else {
				return Opcode.EXISTS;
			}
		}
	}

	// ===============================================================
	// Bytecode Block & Index
	// ===============================================================

	public static class Block extends AbstractBytecode implements Bytecode {
		public Block(List<Integer> operands) {
			super(ArrayUtils.toIntArray(operands));
		}
		public Block(int... operands) {
			super(operands);
		}

		@Override
		public Opcode getOpcode() {
			return Opcode.BLOCK;
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
