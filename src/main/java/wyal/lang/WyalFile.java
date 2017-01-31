package wyal.lang;

import java.io.IOException;
import java.io.InputStream;
import java.io.OutputStream;
import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.IdentityHashMap;
import java.util.List;
import java.util.Map;

import static wycc.util.ArrayUtils.*;

import wyal.io.WyalFileLexer;
import wyal.io.WyalFileParser;
import wyal.lang.WyalFile;
import wyal.util.AbstractSyntacticHeap;
import wyal.util.AbstractSyntacticItem;
import wybs.lang.CompilationUnit;
import wybs.util.AbstractCompilationUnit;
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
			throw new RuntimeException("Implement me");
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
		EXPR_poly(56),
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
	// State
	// =========================================================================
	private final ArrayList<SyntacticItem> syntacticItems;

	protected final Path.Entry<WyalFile> entry;

	// =========================================================================
	// Constructors
	// =========================================================================

	public WyalFile(Path.Entry<WyalFile> entry) {
		this.entry = entry;
		this.syntacticItems = new ArrayList<>();
	}

	@Override
	public Entry<WyalFile> getEntry() {
		return entry;
	}

	// ============================================================
	// Fundamental Items
	// ============================================================
	public static abstract class Item extends AbstractSyntacticItem {
		public Item(Opcode opcode, Item... items) {
			super(opcode, items);
		}

		public Item(Opcode opcode, Object data) {
			super(opcode, data);
		}
	}

	public static class Pair<K extends Item,V extends Item> extends Item {
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

	public static class Tuple<T extends Item> extends Item {
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
	}

	public static class Identifier extends Item {
		public Identifier(String name) {
			super(Opcode.ITEM_ident, name);
		}

		public String get() {
			return (String) data;
		}

		@Override
		public Identifier clone(SyntacticItem[] operands) {
			return new Identifier(get());
		}
	}

	public static class Name extends Item {
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

	public abstract static class Value extends Item {

		public Value(Opcode opcode) {
			super(opcode);
		}

		public Value(Opcode opcode, Object data) {
			super(opcode,data);
		}

		public static class Null extends Value {
			public Null() {
				super(Opcode.CONST_null);
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
	public abstract static class Declaration extends Item {
		public Declaration(Opcode opcode, Item... children) {
			super(opcode, children);
		}

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
		public static class Import extends Declaration {
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

		public static class Assert extends Declaration {

			public Assert(Stmt.Block body) {
				super(Opcode.DECL_assert, body);
			}

			public Stmt.Block getBody() {
				return (Stmt.Block) getOperand(0);
			}

			@Override
			public Assert clone(SyntacticItem[] operands) {
				return new Assert((Stmt.Block) operands[0]);
			}
		}

		public static abstract class Named extends Declaration {

			public Named(Opcode opcode, Identifier name, Item... children) {
				super(opcode, append(Item.class, name, children));
			}

			public Identifier getName() {
				return (Identifier) getOperand(0);
			}

			public static abstract class FunctionOrMacro extends Named {
				public FunctionOrMacro(Identifier name, Tuple<VariableDeclaration> parameters, Item body) {
					super(Opcode.DECL_macro, name, append(Item.class, parameters, body));
				}

				public FunctionOrMacro(Identifier name, Tuple<VariableDeclaration> parameters, Tuple<VariableDeclaration> returns) {
					super(Opcode.DECL_fun, name, parameters, returns);
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
			public static class Type extends Named {

				public Type(Identifier name, VariableDeclaration vardecl, Stmt.Block... invariant) {
					super(Opcode.DECL_type, name, append(Item.class, vardecl, new Tuple(invariant)));
				}

				private Type(Identifier name, VariableDeclaration vardecl, Tuple<Stmt.Block> invariant) {
					super(Opcode.DECL_type, name, append(Item.class, vardecl, invariant));
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
	public abstract static class Type extends Item {

		public Type(Opcode opcode, Item... items) {
			super(opcode, items);
		}

		public static abstract class Atom extends Type {
			public Atom(Opcode opcode, Item... items) {
				super(opcode, items);
			}
		}

		public static class Any extends Atom {
			public Any() { super(Opcode.TYPE_any); }
			@Override
			public Any clone(SyntacticItem[] operands) {
				return new Any();
			}
		}

		public static class Void extends Atom {
			public Void() { super(Opcode.TYPE_void); }
			@Override
			public Void clone(SyntacticItem[] operands) {
				return new Void();
			}
		}

		public static class Null extends Atom {
			public Null() { super(Opcode.TYPE_null); }
			@Override
			public Null clone(SyntacticItem[] operands) {
				return new Null();
			}
		}

		public static class Bool extends Atom {
			public Bool() { super(Opcode.TYPE_bool); }
			@Override
			public Bool clone(SyntacticItem[] operands) {
				return new Bool();
			}
		}

		public static class Int extends Atom {
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
			public Record(VariableDeclaration... fields) {
				super(Opcode.TYPE_rec, fields);
			}

			public VariableDeclaration[] getFields() {
				return ArrayUtils.toArray(VariableDeclaration.class, getOperands());
			}

			@Override
			public Record clone(SyntacticItem[] operands) {
				return new Record((VariableDeclaration[]) operands);
			}
		}

		public static class Nominal extends Type {
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

		public static class Negation extends Type {
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

		public abstract static class UnionOrIntersection extends Type {
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
				return new Union();
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
	}

	// ============================================================
	// Variable Declaration
	// ============================================================

	public static class VariableDeclaration extends Item {
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
		public VariableDeclaration clone(SyntacticItem[] operands) {
			return new VariableDeclaration((Type) operands[0], (Identifier) operands[1]);
		}
	}

	// ============================================================
	// Stmt
	// ============================================================

	public abstract static class Stmt extends Item {
		private Stmt(Opcode opcode, Item... operands) {
			super(opcode, operands);
		}
		private Stmt(Opcode opcode, Type type, Item... operands) {
			super(opcode, append(Item.class, type, operands));
		}

		public static class Block extends Stmt {
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

		public static class Quantifier extends Stmt {
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

		public static class IfThen extends Stmt {
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

		public static class CaseOf extends Stmt {
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

	public abstract static class Expr extends Stmt {
		private Expr(Opcode opcode, Item... operands) {
			super(opcode, operands);
		}

		public static class Cast extends Expr {
			public Cast(Type type, Expr rhs) {
				super(Opcode.EXPR_cast, type, rhs);
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

		public static class Operator extends Expr {
			public Operator(Opcode opcode, Expr... operands) {
				super(opcode, operands);
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
			public Operator clone(SyntacticItem[] operands) {
				return new Operator(getOpcode(),(Expr[]) operands);
			}
		}

		public static class Polynomial extends Expr {
			public Polynomial(BigInteger constant) {
				super(Opcode.EXPR_poly,new Polynomial.Term[]{new Polynomial.Term(constant)});
			}
			public Polynomial(Term... terms) {
				super(Opcode.EXPR_poly, terms);
			}

			@Override
			public Term getOperand(int i) {
				return (Term) super.getOperand(i);
			}

			public static class Term extends Pair<Value.Int, Tuple<Expr>> {
				public Term(BigInteger constant) {
					this(new Value.Int(constant));
				}
				public Term(Value.Int constant) {
					super(constant, new Tuple<Expr>());
				}
				public Term(Value.Int v, Tuple<Expr> variables) {
					super(v, variables);
				}

				public Value.Int getCoefficient() {
					return getFirst();
				}

				public Tuple<Expr> getAtoms() {
					return getSecond();
				}

				@Override
				public Term clone(SyntacticItem[] operands) {
					return new Term((Value.Int) operands[0], (Tuple) operands[1]);
				}
			}

			@Override
			public Polynomial clone(SyntacticItem[] operands) {
				return new Polynomial((Term[]) operands);
			}
		}

		public static class RecordAccess extends Expr {
			public RecordAccess(Expr lhs, Identifier rhs) {
				super(Opcode.EXPR_recfield, lhs, rhs);
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

		public static class RecordInitialiser extends Expr {
			public RecordInitialiser(Pair... fields) {
				super(Opcode.EXPR_recinit, fields);
			}
			public Pair[] getFields() {
				return ArrayUtils.toArray(Pair.class, getOperands());
			}
			@Override
			public RecordInitialiser clone(SyntacticItem[] operands) {
				return new RecordInitialiser((Pair[]) operands);
			}
		}

		public static class VariableAccess extends Expr {
			public VariableAccess(VariableDeclaration decl) {
				super(Opcode.EXPR_var, decl);
			}
			public VariableDeclaration getVariableDeclaration() {
				return (VariableDeclaration) getOperand(0);
			}
			@Override
			public VariableAccess clone(SyntacticItem[] operands) {
				return new VariableAccess((VariableDeclaration) operands[0]);
			}
		}

		public static class Constant extends Expr {
			public Constant(Item value) {
				super(Opcode.EXPR_const, value);
			}
			public Item getValue() {
				return (Item) getOperand(0);
			}
			@Override
			public Constant clone(SyntacticItem[] operands) {
				return new Constant((Item) operands[0]);
			}
		}

		public static class Is extends Expr {
			public Is(Expr lhs, Type rhs) {
				super(Opcode.EXPR_is, lhs, rhs);
			}
			public Expr getExpr() {
				return (Expr) getOperand(0);
			}
			public Type getType() {
				return (Type) getOperand(1);
			}
			@Override
			public Is clone(SyntacticItem[] operands) {
				return new Is((Expr) operands[0], (Type) operands[1]);
			}
		}

		public static class Invoke extends Expr {
			public Invoke(Type type, Name name, Expr... arguments) {
				super(Opcode.EXPR_invoke, type, name, new Tuple<>(arguments));
			}

			public Invoke(Type type, Name name, Tuple<Expr> arguments) {
				super(Opcode.EXPR_invoke, type, name, arguments);
			}

			public Type getType() {
				return (Type) getOperand(0);
			}

			public Name getName() {
				return (Name) getOperand(1);
			}

			public Tuple<Expr> getArguments() {
				return (Tuple) getOperand(2);
			}

			@Override
			public Invoke clone(SyntacticItem[] operands) {
				return new Invoke((Type) operands[0], (Name) operands[1], (Tuple) operands[2]);
			}
		}

		public static class Quantifier extends Expr {
			public Quantifier(Opcode opcode, VariableDeclaration[] parameters, Expr body) {
				super(opcode, new Tuple<>(parameters), body);
			}
			public Quantifier(Opcode opcode, Tuple<VariableDeclaration> parameters, Expr body) {
				super(opcode, parameters, body);
			}
			public Tuple<VariableDeclaration> getParameters() {
				return (Tuple<VariableDeclaration>) getOperand(0);
			}

			public Expr getBody() {
				return (Expr) getOperand(1);
			}

			@Override
			public Quantifier clone(SyntacticItem[] operands) {
				return new Quantifier(getOpcode(), (Tuple<VariableDeclaration>) operands[0], (Expr) operands[1]);
			}
		}

	}

	// ===========================================================
	// Constants
	// ===========================================================
	public final static int STAR = -2;
	public final static int UNKNOWN_TYPE = -1;
}
