package wyal.lang;

import java.io.IOException;
import java.io.InputStream;
import java.io.OutputStream;
import java.io.PrintWriter;
import java.math.BigInteger;
import java.util.ArrayList;

import wyal.heap.AbstractSyntacticHeap;
import wyal.heap.AbstractSyntacticItem;
import wyal.io.WyalFileLexer;
import wyal.io.WyalFileParser;
import wyal.io.WyalFilePrinter;
import wyal.lang.WyalFile;
import wyal.lang.WyalFile.Expr.Polynomial;
import wyal.util.OldAutomatedTheoremProver;
import wyal.util.Formulae;
import wyal.util.Polynomials;
import wyal.util.TypeSystem;
import wybs.lang.CompilationUnit;
import wycc.util.ArrayUtils;
import wyfs.lang.Content;
import wyfs.lang.Path;
import wyfs.lang.Path.Entry;

public class WyalFile extends AbstractSyntacticHeap implements CompilationUnit {

	// =========================================================================
	// Content Type
	// =========================================================================

	public static final Content.Type<WyalFile> ContentType = new Content.Type<WyalFile>() {
		public Path.Entry<WyalFile> accept(Path.Entry<?> e) {
			if (e.contentType() == this) {
				return (Path.Entry<WyalFile>) e;
			}
			return null;
		}

		@Override
		public WyalFile read(Path.Entry<WyalFile> e, InputStream input) throws IOException {
			WyalFileLexer wlexer = new WyalFileLexer(e);
			WyalFileParser wfr = new WyalFileParser(e, wlexer.scan());
			return wfr.read();
		}

		@Override
		public void write(OutputStream output, WyalFile module) throws IOException {
			new WyalFilePrinter(output).write(module);
		}

		@Override
		public String toString() {
			return "Content-Type: wyal";
		}

		@Override
		public String getSuffix() {
			return "wyal";
		}
	};

	public static final Content.Type<WyalFile> CompiledContentType = new Content.Type<WyalFile>() {
		public Path.Entry<WyalFile> accept(Path.Entry<?> e) {
			if (e.contentType() == this) {
				return (Path.Entry<WyalFile>) e;
			}
			return null;
		}

		@Override
		public WyalFile read(Path.Entry<WyalFile> e, InputStream input)
				throws IOException {
			throw new RuntimeException("Implement me!");
		}

		@Override
		public void write(OutputStream output, WyalFile module)
				throws IOException {
			throw new RuntimeException("Implement me!");
		}

		@Override
		public String toString() {
			return "Content-Type: wycs";
		}

		@Override
		public String getSuffix() {
			return "wycs";
		}
	};

	// =========================================================================
	// Item Kinds
	// =========================================================================
	public static enum Opcode {
		//
		ITEM_pair(100),
		ITEM_tuple(101),
		ITEM_ident(103),
		ITEM_path(104),
		ITEM_name(105),
		// DECLARATIONS
		DECL_linecomment(106),
		DECL_blkcomment(107),
		DECL_import(108),
		DECL_assert(109),
		DECL_type(110),
		DECL_fun(111),
		DECL_macro(112),
		// ERRORS
		ERR_verify(113),
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
		TYPE_macro(10),
		TYPE_inv(11),
		TYPE_or(12),
		TYPE_and(13),
		TYPE_not(14),
		// STMTS
		STMT_block(15),
		STMT_vardecl(16),
		STMT_ifthen(17),
		STMT_caseof(18),
		STMT_exists(19),
		STMT_forall(20),
		// EXPRESSIONS
		EXPR_var(20),
		EXPR_const(21),
		EXPR_cast(22),
		EXPR_invoke(23),
		// LOGICAL
		EXPR_not(30),
		EXPR_and(31),
		EXPR_or(32),
		EXPR_implies(33),
		EXPR_iff(34),
		EXPR_exists(35),
		EXPR_forall(36),
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
		EXPR_recfield(56),
		EXPR_arridx(57),
		EXPR_arrlen(58),
		EXPR_arrupdt(59),
		// Initialisers come later so they not given preference for
		// substitution.
		EXPR_arrgen(60),
		EXPR_arrinit(61),
		EXPR_recinit(62),

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
	// State
	// =========================================================================
	protected final Path.Entry<WyalFile> entry;

	// =========================================================================
	// Constructors
	// =========================================================================

	public WyalFile(Path.Entry<WyalFile> entry) {
		this.entry = entry;
	}

	@Override
	public Entry<WyalFile> getEntry() {
		return entry;
	}

	// ============================================================
	// Fundamental Items
	// ============================================================

	public static class Pair<K extends SyntacticItem,V extends SyntacticItem> extends AbstractSyntacticItem {
		public Pair(K lhs, V rhs) {
			super(Opcode.ITEM_pair, lhs, rhs);
		}

		public K getFirst() {
			return (K) getOperand(0);
		}

		public V getSecond() {
			return (V) getOperand(1);
		}

		@Override
		public Pair<K,V> clone(SyntacticItem[] operands) {
			return new Pair<>((K) operands[0], (V)operands[1]);
		}
	}

	public static class Tuple<T extends SyntacticItem> extends AbstractSyntacticItem {
		public Tuple(T... stmts) {
			super(Opcode.ITEM_tuple, stmts);
		}

		@Override
		public T getOperand(int i) {
			return (T) super.getOperand(i);
		}

		@Override
		public T[] getOperands() {
			return (T[]) super.getOperands();
		}

		@Override
		public Tuple<T> clone(SyntacticItem[] operands) {
			return new Tuple((T[]) operands);
		}

		@Override
		public String toString() {
			String r = "";
			for(int i=0;i!=size();++i) {
				if(i!=0) {
					r += ",";
				}
				SyntacticItem child = getOperand(i);
				if(child == null) {
					r += "?";
				} else {
					r += child.toString();
				}
			}
			return "(" + r + ")";
		}
	}

	public static class Identifier extends AbstractSyntacticItem {
		public Identifier(String name) {
			super(Opcode.ITEM_ident, name, new SyntacticItem[0]);
		}

		public String get() {
			return (String) data;
		}

		@Override
		public Identifier clone(SyntacticItem[] operands) {
			return new Identifier(get());
		}
	}

	public static class Name extends AbstractSyntacticItem {
		public Name(Identifier... components) {
			super(Opcode.ITEM_name, components);
		}

		public Identifier[] getComponents() {
			return (Identifier[]) getOperands();
		}

		@Override
		public Name clone(SyntacticItem[] operands) {
			return new Name((Identifier[]) operands);
		}
	}

	public abstract static class Value extends AbstractSyntacticItem {

		public Value(Opcode opcode) {
			super(opcode);
		}

		public Value(Opcode opcode, Object data) {
			super(opcode,data, new SyntacticItem[0]);
		}

		public abstract Type getType();

		public static class Null extends Value {
			public Null() {
				super(Opcode.CONST_null);
			}
			@Override
			public Type getType() {
				return new Type.Null();
			}
			@Override
			public Null clone(SyntacticItem[] operands) {
				return new Null();
			}
		}

		public static class Bool extends Value {
			public Bool(boolean value) {
				super(Opcode.CONST_bool, value);
			}

			public boolean get() {
				return (Boolean) data;
			}
			@Override
			public Type getType() {
				return new Type.Bool();
			}
			@Override
			public Bool clone(SyntacticItem[] operands) {
				return new Bool(get());
			}
		}

		public static class Int extends Value {
			public Int(BigInteger value) {
				super(Opcode.CONST_int, value);
			}

			public Int(long value) {
				super(Opcode.CONST_int, BigInteger.valueOf(value));
			}
			@Override
			public Type getType() {
				return new Type.Int();
			}
			public BigInteger get() {
				return (BigInteger) data;
			}

			@Override
			public Int clone(SyntacticItem[] operands) {
				return new Int(get());
			}
		}

		public static class UTF8 extends Value {
			public UTF8(byte[] bytes) {
				super(Opcode.CONST_utf8, bytes);
			}
			@Override
			public Type getType() {
				throw new UnsupportedOperationException();
			}
			public byte[] get() {
				return (byte[]) data;
			}

			@Override
			public UTF8 clone(SyntacticItem[] operands) {
				return new UTF8(get());
			}
		}
	}

	// ============================================================
	// Declarations
	// ============================================================
	public static interface Declaration extends SyntacticItem {

		/**
		 * Represents an import declaration in a Wycs source file. For example:
		 *
		 * <pre>
		 * import wycs.lang.Map
		 * </pre>
		 *
		 * Here, the package is <code>wycs.lang</code>, and the module is
		 * <code>Map</code>.
		 *
		 * @author David J. Pearce
		 *
		 */
		public static class Import extends AbstractSyntacticItem implements Declaration {
			public Import(Identifier... components) {
				super(Opcode.DECL_import, components);
			}

			public Identifier[] getComponents() {
				return (Identifier[]) getOperands();
			}

			@Override
			public Import clone(SyntacticItem[] operands) {
				return new Import((Identifier[]) operands);
			}
		}

		public static class Assert extends AbstractSyntacticItem implements Declaration {
			private String message;

			public Assert(Stmt.Block body, String message) {
				super(Opcode.DECL_assert, body);
				this.message = message;
			}

			public Stmt.Block getBody() {
				return (Stmt.Block) getOperand(0);
			}

			public String getMessage() {
				return message;
			}

			@Override
			public Assert clone(SyntacticItem[] operands) {
				return new Assert((Stmt.Block) operands[0], message);
			}
		}

		public static interface Named extends Declaration {

			public Identifier getName();

			public static abstract class FunctionOrMacro extends AbstractSyntacticItem implements Named {
				public FunctionOrMacro(Identifier name, Tuple<VariableDeclaration> parameters, Stmt.Block body) {
					super(Opcode.DECL_macro, name, parameters, body);
				}

				public FunctionOrMacro(Identifier name, Tuple<VariableDeclaration> parameters, Tuple<VariableDeclaration> returns) {
					super(Opcode.DECL_fun, name, parameters, returns);
				}

				@Override
				public Identifier getName() {
					return (Identifier) getOperand(0);
				}

				public Tuple<VariableDeclaration> getParameters() {
					return (Tuple) getOperand(1);
				}
			}

			// ============================================================
			// Function Declaration
			// ============================================================
			public static class Function extends FunctionOrMacro {

				public Function(Identifier name, VariableDeclaration[] parameters, VariableDeclaration[] returns) {
					super(name, new Tuple(parameters), new Tuple(returns));
				}

				public Function(Identifier name, Tuple<VariableDeclaration> parameters, Tuple<VariableDeclaration> returns) {
					super(name, parameters, returns);
				}

				public Tuple<VariableDeclaration> getReturns() {
					return (Tuple<VariableDeclaration>) getOperand(2);
				}

				@Override
				public Function clone(SyntacticItem[] operands) {
					return new Function((Identifier) operands[0], (Tuple) operands[1], (Tuple) operands[2]);
				}
			}

			// ============================================================
			// Macro Declaration
			// ============================================================
			public static class Macro extends FunctionOrMacro {
				public Macro(Identifier name, VariableDeclaration[] parameters, Stmt.Block body) {
					super(name, new Tuple<>(parameters), body);
				}

				private Macro(Identifier name, Tuple<VariableDeclaration> parameters, Stmt.Block body) {
					super(name, parameters, body);
				}

				public Stmt.Block getBody() {
					return (Stmt.Block) getOperand(2);
				}

				@Override
				public Macro clone(SyntacticItem[] operands) {
					return new Macro((Identifier) operands[0], (Tuple<VariableDeclaration>) operands[1], (Stmt.Block) operands[2]);
				}
			}

			// ============================================================
			// Type Declaration
			// ============================================================
			public static class Type extends AbstractSyntacticItem implements Named {

				public Type(Identifier name, VariableDeclaration vardecl, Stmt.Block... invariant) {
					super(Opcode.DECL_type, name, vardecl, new Tuple(invariant));
				}

				private Type(Identifier name, VariableDeclaration vardecl, Tuple<Stmt.Block> invariant) {
					super(Opcode.DECL_type, name, vardecl, invariant);
				}

				@Override
				public Identifier getName() {
					return (Identifier) getOperand(0);
				}

				public VariableDeclaration getVariableDeclaration() {
					return (VariableDeclaration) getOperand(1);
				}

				public Tuple<Stmt.Block> getInvariant() {
					return (Tuple) getOperand(2);
				}

				@Override
				public Type clone(SyntacticItem[] operands) {
					return new Type((Identifier) operands[0], (VariableDeclaration) operands[1], (Tuple) operands[2]);
				}
			}
		}
	}

	// ============================================================
	// Types
	// ============================================================
	public static interface Type extends SyntacticItem {

		public interface Primitive extends Type {

		}

		public static abstract class Atom extends AbstractSyntacticItem implements Type {
			public Atom(Opcode opcode, SyntacticItem... items) {
				super(opcode, items);
			}
		}

		public static class Any extends Atom implements Primitive {
			public Any() { super(Opcode.TYPE_any); }
			@Override
			public Any clone(SyntacticItem[] operands) {
				return new Any();
			}
		}

		public static class Void extends Atom implements Primitive {
			public Void() { super(Opcode.TYPE_void); }
			@Override
			public Void clone(SyntacticItem[] operands) {
				return new Void();
			}
		}

		public static class Null extends Atom implements Primitive {
			public Null() { super(Opcode.TYPE_null); }
			@Override
			public Null clone(SyntacticItem[] operands) {
				return new Null();
			}
		}

		public static class Bool extends Atom implements Primitive {
			public Bool() { super(Opcode.TYPE_bool); }
			@Override
			public Bool clone(SyntacticItem[] operands) {
				return new Bool();
			}
		}

		public static class Int extends Atom implements Primitive {
			public Int() { super(Opcode.TYPE_int); }
			@Override
			public Int clone(SyntacticItem[] operands) {
				return new Int();
			}
		}

		public static class Array extends Atom {
			public Array(Type element) {
				super(Opcode.TYPE_arr, element);
			}
			public Type getElement() {
				return (Type) getOperand(0);
			}
			@Override
			public Array clone(SyntacticItem[] operands) {
				return new Array((Type) operands[0]);
			}
		}

		public static class Reference extends Atom {
			public Reference(Type element) {
				super(Opcode.TYPE_arr, element);
			}
			public Type getElement() {
				return (Type) getOperand(0);
			}
			@Override
			public Reference clone(SyntacticItem[] operands) {
				return new Reference((Type) operands[0]);
			}
		}

		public static class Record extends Atom {
			public Record(FieldDeclaration... fields) {
				super(Opcode.TYPE_rec, fields);
			}

			public FieldDeclaration[] getFields() {
				return ArrayUtils.toArray(FieldDeclaration.class, getOperands());
			}

			@Override
			public Record clone(SyntacticItem[] operands) {
				return new Record((FieldDeclaration[]) operands);
			}
		}

		public static class Nominal extends AbstractSyntacticItem implements Type {
			public Nominal(Name name) {
				super(Opcode.TYPE_nom, name);
			}

			public Name getName() {
				return (Name) getOperand(0);
			}

			@Override
			public Nominal clone(SyntacticItem[] operands) {
				return new Nominal((Name) operands[0]);
			}
		}

		public static class Negation extends AbstractSyntacticItem implements Type {
			public Negation(Type element) {
				super(Opcode.TYPE_not, element);
			}
			public Type getElement() {
				return (Type) getOperand(0);
			}

			@Override
			public Negation clone(SyntacticItem[] operands) {
				return new Negation((Type) operands[0]);
			}
		}

		public abstract static class UnionOrIntersection extends AbstractSyntacticItem implements Type {
			public UnionOrIntersection( Opcode kind, Type... types) {
				super(kind, types);
			}
			@Override
			public Type getOperand(int i) {
				return (Type) super.getOperand(i);
			}

			@Override
			public Type[] getOperands() {
				return ArrayUtils.toArray(Type.class, super.getOperands());
			}
		}

		public static class Union extends UnionOrIntersection {
			public Union(Type... types) {
				super(Opcode.TYPE_or, types);
			}

			@Override
			public Union clone(SyntacticItem[] operands) {
				return new Union((Type[]) operands);
			}
		}

		public static class Intersection extends UnionOrIntersection {
			public Intersection(Type... types) {
				super(Opcode.TYPE_and, types);
			}
			@Override
			public Intersection clone(SyntacticItem[] operands) {
				return new Intersection((Type[]) operands);
			}
		}

		public static abstract class FunctionOrMacro extends AbstractSyntacticItem implements Type {
			public FunctionOrMacro(Opcode opcode, Tuple<Type> parameters, Tuple<Type> returns) {
				super(opcode,parameters,returns);
			}
			public Tuple<Type> getParameters() {
				return (Tuple<Type>) getOperand(0);
			}
			public Tuple<Type> getReturns() {
				return (Tuple<Type>) getOperand(1);
			}
		}

		public static class Function extends FunctionOrMacro implements Type {
			public Function(Tuple<Type> parameters, Tuple<Type> returns) {
				super(Opcode.TYPE_fun,parameters,returns);
			}

			@Override
			public Function clone(SyntacticItem[] operands) {
				return new Function((Tuple<Type>) operands[0], (Tuple<Type>) operands[1]);
			}
		}

		public static class Macro extends FunctionOrMacro implements Type {
			public Macro(Tuple<Type> parameters, Tuple<Type> returns) {
				super(Opcode.TYPE_macro, parameters, returns);
			}

			@Override
			public Macro clone(SyntacticItem[] operands) {
				return new Macro((Tuple<Type>) operands[0], (Tuple<Type>) operands[1]);
			}
		}

		public static class Invariant extends FunctionOrMacro implements Type {
			public Invariant(Tuple<Type> parameters) {
				super(Opcode.TYPE_inv, parameters, new Tuple<Type>(new Bool()));
			}

			private Invariant(Tuple<Type> parameters, Tuple<Type> returns) {
				super(Opcode.TYPE_inv, parameters, returns);
			}

			@Override
			public Invariant clone(SyntacticItem[] operands) {
				return new Invariant((Tuple<Type>) operands[0], (Tuple<Type>) operands[1]);
			}
		}
	}

	// ============================================================
	// Variable Declaration
	// ============================================================

	public static class VariableDeclaration extends AbstractSyntacticItem {
		public VariableDeclaration(Type type, Identifier name) {
			super(Opcode.STMT_vardecl, type, name);
		}

		public Type getType() {
			return (Type) getOperand(0);
		}

		public Identifier getVariableName() {
			return (Identifier) getOperand(1);
		}

		@Override
		public boolean equals(Object o) {
			// The reason for this is that we want to treat variable
			// declarations specially. The only way that two variable
			// declarations can be considered equal is if they are the same.
			return o == this;
		}

		@Override
		public VariableDeclaration clone(SyntacticItem[] operands) {
			return new VariableDeclaration((Type) operands[0], (Identifier) operands[1]);
		}
	}

	public static class FieldDeclaration extends AbstractSyntacticItem {
		public FieldDeclaration(Type type, Identifier name) {
			super(Opcode.STMT_vardecl, type, name);
		}

		public Type getType() {
			return (Type) getOperand(0);
		}

		public Identifier getVariableName() {
			return (Identifier) getOperand(1);
		}

		@Override
		public FieldDeclaration clone(SyntacticItem[] operands) {
			return new FieldDeclaration((Type) operands[0], (Identifier) operands[1]);
		}
	}

	// ============================================================
	// Stmt
	// ============================================================

	public interface Stmt extends SyntacticItem {

		public static class Block extends AbstractSyntacticItem implements Stmt {
			public Block(Stmt... stmts) {
				super(Opcode.STMT_block, stmts);
			}

			@Override
			public Stmt getOperand(int i) {
				return (Stmt) super.getOperand(i);
			}

			@Override
			public Stmt[] getOperands() {
				return (Stmt[]) super.getOperands();
			}

			@Override
			public Block clone(SyntacticItem[] operands) {
				return new Block((Stmt[]) operands);
			}
		}

		public static class Quantifier extends AbstractSyntacticItem implements Stmt {
			public Quantifier(Opcode opcode, VariableDeclaration[] parameters, Block body) {
				super(opcode, new Tuple<>(parameters),body);
			}
			public Quantifier(Opcode opcode, Tuple<VariableDeclaration> parameters, Block body) {
				super(opcode, parameters,body);
			}
			public Tuple<VariableDeclaration> getParameters() {
				return (Tuple<VariableDeclaration>) getOperand(0);
			}
			public Block getBody() {
				return (Block) getOperand(1);
			}
			@Override
			public Quantifier clone(SyntacticItem[] operands) {
				return new Quantifier(getOpcode(),(Tuple) operands[0], (Block) operands[1]);
			}
		}

		public static class IfThen extends AbstractSyntacticItem implements Stmt {
			public IfThen(Block ifBlock, Block thenBlock) {
				super(Opcode.STMT_ifthen, ifBlock, thenBlock);
			}
			public Block getIfBody() {
				return (Block) getOperand(0);
			}
			public Block getThenBody() {
				return (Block) getOperand(1);
			}
			@Override
			public IfThen clone(SyntacticItem[] operands) {
				return new IfThen((Block) operands[0], (Block) operands[1]);
			}
		}

		public static class CaseOf extends AbstractSyntacticItem implements Stmt {
			public CaseOf(Block... cases) {
				super(Opcode.STMT_caseof, cases);
			}
			@Override
			public Block getOperand(int i) {
				return (Block) super.getOperand(i);
			}
			@Override
			public Block[] getOperands() {
				return (Block[]) super.getOperands();
			}
			@Override
			public CaseOf clone(SyntacticItem[] operands) {
				return new CaseOf((Block[]) operands);
			}
		}
	}

	public interface Expr extends Stmt {

		/**
		 * Get the type of value returned from evaluating this expression.
		 *
		 * @param types
		 *            Used to expand nominal types in various situations.
		 * @return
		 */
		public Type getReturnType(TypeSystem types);

		public static class Cast extends AbstractSyntacticItem implements Expr {
			public Cast(Type type, Expr rhs) {
				super(Opcode.EXPR_cast, type, rhs);
			}
			@Override
			public Type getReturnType(TypeSystem types) {
				return (Type) super.getOperand(0);
			}
			public Type getCastType() {
				return (Type) super.getOperand(0);
			}
			public Expr getExpr() {
				return (Expr) super.getOperand(1);
			}
			@Override
			public Cast clone(SyntacticItem[] operands) {
				return new Cast((Type) operands[0], (Expr) operands[1]);
			}
		}

		public static class Operator extends AbstractSyntacticItem implements Expr {
			public Operator(Opcode opcode, Expr... operands) {
				super(opcode, operands);
			}

			@Override
			public Type getReturnType(TypeSystem types) {
				switch (getOpcode()) {
				case EXPR_not:
				case EXPR_and:
				case EXPR_or:
				case EXPR_implies:
				case EXPR_iff:
				case EXPR_eq:
				case EXPR_neq:
				case EXPR_lt:
				case EXPR_lteq:
				case EXPR_gt:
				case EXPR_gteq:
					return new Type.Bool();
				case EXPR_neg:
				case EXPR_add:
				case EXPR_sub:
				case EXPR_mul:
				case EXPR_div:
				case EXPR_rem:
				case EXPR_arrlen:
					return new Type.Int();
				case EXPR_arrinit: {
					Type[] ts = new Type[size()];
					for (int i = 0; i != ts.length; ++i) {
						ts[i] = getOperand(i).getReturnType(types);
					}
					Type element = types.union(ts);
					return new Type.Array(element);
				}
				case EXPR_arrgen: {
					Type element = getOperand(0).getReturnType(types);
					return new Type.Array(element);
				}
				case EXPR_arridx: {
					Type src = getOperand(0).getReturnType(types);
					Type.Array effectiveArray = types.expandAsReadableArrayType(src);
					return effectiveArray.getElement();
				}
				case EXPR_arrupdt: {
					Type src = getOperand(0).getReturnType(types);
					Type.Array effectiveArray = types.expandAsReadableArrayType(src);
					return effectiveArray;
				}
				default:
					throw new IllegalArgumentException("invalid operator opcode: " + getOpcode());
				}
			}

			@Override
			public Expr getOperand(int i) {
				return (Expr) super.getOperand(i);
			}

			@Override
			public Expr[] getOperands() {
				return (Expr[]) super.getOperands();
			}

			@Override
			public Expr clone(SyntacticItem[] operands) {
				return new Operator(getOpcode(), (Expr[]) operands);
			}
		}


		public final static class Polynomial extends Expr.Operator {
			public Polynomial(BigInteger constant) {
				super(Opcode.EXPR_add,new Polynomial.Term[]{new Polynomial.Term(constant)});
			}
			public Polynomial(Term... terms) {
				super(Opcode.EXPR_add, terms);
			}

			@Override
			public Term getOperand(int i) {
				return (Term) super.getOperand(i);
			}

			@Override
			public Type getReturnType(TypeSystem types) {
				// FIXME: we could do better than this.
				return new Type.Int();
			}

			@Override
			public Polynomial.Term[] getOperands() {
				return (Polynomial.Term[]) super.getOperands();
			}

			/**
			 * Check whether a polynomial is a constant or not.
			 *
			 * @param p
			 * @return
			 */
			public boolean isConstant() {
				return size() == 1 && getOperand(0).getAtoms().length == 0;
			}

			/**
			 * Extract the constant that this polynomial represents (assuming it
			 * does).
			 *
			 * @param p
			 * @return
			 */
			public Value.Int toConstant() {
				if (size() == 1) {
					Polynomial.Term term = getOperand(0);
					if (term.getAtoms().length == 0) {
						return term.getCoefficient();
					}
				}
				throw new IllegalArgumentException("polynomial is not constant");
			}

			public Polynomial negate() {
				return Polynomials.negate(this);
			}

			public Polynomial add(Polynomial poly) {
				return Polynomials.add(this, poly);
			}

			public Polynomial add(Polynomial.Term term) {
				return Polynomials.add(this, term);
			}

			public Polynomial subtract(Polynomial p) {
				return add(p.negate());
			}

			public Polynomial subtract(Polynomial.Term term) {
				return Polynomials.add(this, Polynomials.negate(term));
			}

			public Polynomial multiply(Polynomial rhs) {
				return Polynomials.multiply(this, rhs);
			}

			public Polynomial multiply(Polynomial.Term rhs) {
				return Polynomials.multiply(this, rhs);
			}

			@Override
			public Polynomial clone(SyntacticItem[] children) {
				return new Polynomial((Term[]) children);
			}

			public static class Term extends Expr.Operator {
				public Term(BigInteger constant) {
					this(new Value.Int(constant));
				}
				public Term(Value.Int constant) {
					super(Opcode.EXPR_mul,new Constant(constant));
				}
				public Term(Expr atom) {
					super(Opcode.EXPR_mul,append(new Value.Int(1),atom));
				}
				public Term(Value.Int coefficient, Expr... variables) {
					super(Opcode.EXPR_mul,append(coefficient,variables));
				}
				Term(Expr[] operands) {
					super(Opcode.EXPR_mul,operands);
				}
				public Value.Int getCoefficient() {
					Constant c = (Constant) getOperand(0);
					return (Value.Int) c.getValue();
				}

				public Expr[] getAtoms() {
					Expr[] children = getOperands();
					Expr[] atoms = new Expr[children.length-1];
					System.arraycopy(children, 1, atoms, 0, atoms.length);
					return atoms;
				}

				static Expr[] append(Value.Int i, Expr... variables) {
					Expr[] exprs = new Expr[variables.length+1];
					exprs[0] = new Expr.Constant(i);
					for(int k=0;k!=variables.length;++k) {
						exprs[k+1] = variables[k];
					}
					return exprs;
				}

				@Override
				public Term clone(SyntacticItem[] children) {
					return new Term((Expr[])children);
				}

			}
		}

		public static class RecordAccess extends AbstractSyntacticItem implements Expr {
			public RecordAccess(Expr lhs, Identifier rhs) {
				super(Opcode.EXPR_recfield, lhs, rhs);
			}

			@Override
			public Type getReturnType(TypeSystem types) {
				Type src = getSource().getReturnType(types);
				Type.Record effectiveRecord = types.expandAsReadableRecordType(src);
				FieldDeclaration[] fields = effectiveRecord.getFields();
				String actualFieldName = getField().get();
				for (int i = 0; i != fields.length; ++i) {
					FieldDeclaration vd = fields[i];
					String declaredFieldName = vd.getVariableName().get();
					if (declaredFieldName.equals(actualFieldName)) {
						return vd.getType();
					}
				}
				//
				throw new RuntimeException("invalid record access: " + actualFieldName);
			}
			public Expr getSource() {
				return (Expr) getOperand(0);
			}
			public Identifier getField() {
				return (Identifier) getOperand(1);
			}
			@Override
			public RecordAccess clone(SyntacticItem[] operands) {
				return new RecordAccess((Expr) operands[0], (Identifier) operands[1]);
			}
		}

		public static class RecordInitialiser extends AbstractSyntacticItem implements Expr {
			public RecordInitialiser(Pair<Identifier,Expr>... fields) {
				super(Opcode.EXPR_recinit, fields);
			}

			@Override
			public Type getReturnType(TypeSystem types) {
				Pair<Identifier, Expr>[] fields = getFields();
				FieldDeclaration[] decls = new FieldDeclaration[fields.length];
				for (int i = 0; i != fields.length; ++i) {
					Identifier fieldName = fields[i].getFirst();
					Type fieldType = fields[i].getSecond().getReturnType(types);
					decls[i] = new FieldDeclaration(fieldType, fieldName);
				}
				//
				return new Type.Record(decls);
			}
			public Pair<Identifier,Expr>[] getFields() {
				return ArrayUtils.toArray(Pair.class, getOperands());
			}
			@Override
			public RecordInitialiser clone(SyntacticItem[] operands) {
				return new RecordInitialiser((Pair[]) operands);
			}
		}

		public static class VariableAccess extends AbstractSyntacticItem implements Expr {
			public VariableAccess(VariableDeclaration decl) {
				super(Opcode.EXPR_var, decl);
			}
			@Override
			public Type getReturnType(TypeSystem types) {
				return getVariableDeclaration().getType();
			}
			public VariableDeclaration getVariableDeclaration() {
				return (VariableDeclaration) getOperand(0);
			}
			@Override
			public VariableAccess clone(SyntacticItem[] operands) {
				return new VariableAccess((VariableDeclaration) operands[0]);
			}
		}

		public static class Constant extends AbstractSyntacticItem implements Expr {
			public Constant(Value value) {
				super(Opcode.EXPR_const, value);
			}
			@Override
			public Type getReturnType(TypeSystem types) {
				return getValue().getType();
			}
			public Value getValue() {
				return (Value) getOperand(0);
			}
			@Override
			public Constant clone(SyntacticItem[] operands) {
				return new Constant((Value) operands[0]);
			}
		}

		public static class Is extends AbstractSyntacticItem implements Expr {
			public Is(Expr lhs, Type rhs) {
				super(Opcode.EXPR_is, lhs, rhs);
			}
			@Override
			public Type getReturnType(TypeSystem types) {
				return new Type.Bool();
			}
			public Expr getExpr() {
				return (Expr) getOperand(0);
			}
			public Type getTypeTest() {
				return (Type) getOperand(1);
			}
			@Override
			public Is clone(SyntacticItem[] operands) {
				return new Is((Expr) operands[0], (Type) operands[1]);
			}
		}

		public static class Invoke extends AbstractSyntacticItem implements Expr {

			// FIXME: making the arguments a tuple prevents traversals following
			// the line of expressions.

			public Invoke(Type.FunctionOrMacro type, Name name, Expr... arguments) {
				super(Opcode.EXPR_invoke, type, name, new Tuple<>(arguments));
			}

			public Invoke(Type.FunctionOrMacro type, Name name, Tuple<Expr> arguments) {
				super(Opcode.EXPR_invoke, type, name, arguments);
			}

			@Override
			public Type getReturnType(TypeSystem types) {
				Type.FunctionOrMacro type = getSignatureType();
				Tuple<Type> returns = type.getReturns();
				if (returns.size() != 1) {
					throw new IllegalArgumentException("need support for multiple returns");
				} else {
					return returns.getOperand(0);
				}
			}

			public Type.FunctionOrMacro getSignatureType() {
				return (Type.FunctionOrMacro) getOperand(0);
			}

			public void setSignatureType(Type.FunctionOrMacro type) {
				this.setOperand(0, type);
			}

			public Name getName() {
				return (Name) getOperand(1);
			}

			public Tuple<Expr> getArguments() {
				return (Tuple) getOperand(2);
			}

			@Override
			public Invoke clone(SyntacticItem[] operands) {
				return new Invoke((Type.FunctionOrMacro) operands[0], (Name) operands[1], (Tuple) operands[2]);
			}
		}

		public static class Quantifier extends AbstractSyntacticItem implements Expr {
			public Quantifier(Opcode opcode, VariableDeclaration[] parameters, Expr body) {
				super(opcode, new Tuple<>(parameters), body);
			}
			public Quantifier(Opcode opcode, Tuple<VariableDeclaration> parameters, Expr body) {
				super(opcode, parameters, body);
			}
			public Tuple<VariableDeclaration> getParameters() {
				return (Tuple<VariableDeclaration>) getOperand(0);
			}
			@Override
			public Type getReturnType(TypeSystem types) {
				return new Type.Bool();
			}
			public Expr getBody() {
				return (Expr) getOperand(1);
			}

			@Override
			public Expr clone(SyntacticItem[] operands) {
				return new Quantifier(getOpcode(), (Tuple<VariableDeclaration>) operands[0], (Expr) operands[1]);
			}
		}
	}

	// ===========================================================
	// Errors
	// ===========================================================
	public static class VerificationError extends AbstractSyntacticItem {

		public VerificationError(Declaration.Assert parent) {
			super(Opcode.ERR_verify, parent);
		}

		@Override
		public SyntacticItem clone(SyntacticItem[] operands) {
			return new VerificationError((Declaration.Assert) operands[0]);
		}

	}

	// ===========================================================
	// DEBUGGING SUPPORT
	// ===========================================================

	public static void println(SyntacticItem... items) {
		print(items);
		System.out.println();
	}

	public static void print(SyntacticItem... items) {
		PrintWriter out = new PrintWriter(System.out);
		WyalFilePrinter printer = new WyalFilePrinter(out);
		for (int i = 0; i != items.length; ++i) {
			if (i != 0) {
				out.print(", ");
			}
			SyntacticItem item = items[i];
			if(item instanceof WyalFile.Expr) {
				printer.writeExpression((Expr) item);
			} else if(item instanceof WyalFile.Stmt) {
				printer.writeStatement((Stmt) item,0);
			} else if(item instanceof WyalFile.Type) {
				printer.writeType((Type) item);
			} else if(item == null) {
				out.print("null");
			} else {
				throw new RuntimeException("Unsupported item category: " + item);
			}
		}
		out.flush();
	}
}
