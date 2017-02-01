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
import wyal.lang.WyalFile.Expr;
import wyal.lang.WyalFile.Opcode;
import wyal.lang.WyalFile.Value;
import wyal.lang.WyalFile.Expr.Polynomial;
import wyal.util.AbstractSyntacticHeap;
import wyal.util.AbstractSyntacticItem;
import wyal.util.Formulae;
import wyal.util.Polynomials;
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

			public Assert(Stmt.Block body) {
				super(Opcode.DECL_assert, body);
				System.out.println("GOT BODY: " + getOperands());
			}

			public Stmt.Block getBody() {
				return (Stmt.Block) getOperand(0);
			}

			@Override
			public Assert clone(SyntacticItem[] operands) {
				return new Assert((Stmt.Block) operands[0]);
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

		public static abstract class Atom extends AbstractSyntacticItem implements Type {
			public Atom(Opcode opcode, SyntacticItem... items) {
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
		public VariableDeclaration clone(SyntacticItem[] operands) {
			return new VariableDeclaration((Type) operands[0], (Identifier) operands[1]);
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
		 * An atom is a special form of expression which is guaranteed to be in
		 * a "normal form".
		 *
		 * @author David J. Pearce
		 *
		 */
		public interface Atom extends Expr {

		}

		public static class Cast extends AbstractSyntacticItem implements Expr {
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

		public static class Operator extends AbstractSyntacticItem implements Expr {
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

		public final static class Polynomial extends AbstractSyntacticItem implements Expr {
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

			/**
			 * Check whether a polynomial is a constant or not.
			 *
			 * @param p
			 * @return
			 */
			public boolean isConstant() {
				return size() == 1 && getOperand(0).getAtoms().size() == 0;
			}

			/**
			 * Extract the constant that this polynomial represents (assuming it
			 * does).
			 *
			 * @param p
			 * @return
			 */
			public BigInteger toConstant() {
				if (size() == 1) {
					Polynomial.Term term = getOperand(0);
					if (term.getAtoms().size() == 0) {
						return term.getCoefficient().get();
					}
				}
				throw new IllegalArgumentException("polynomial is not constant");
			}

			public Polynomial negate() {
				return Polynomials.negate(this);
			}

			public Polynomial add(Polynomial p) {
				return Polynomials.add(this,p);
			}

			public Polynomial subtract(Polynomial.Term p) {
				return Polynomials.subtract(this,p);
			}

			public Polynomial subtract(Polynomial p) {
				return Polynomials.subtract(this,p);
			}

			public Polynomial multiply(Polynomial p) {
				return Polynomials.multiply(this,p);
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

		public static class RecordAccess extends AbstractSyntacticItem implements Expr {
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

		public static class RecordInitialiser extends AbstractSyntacticItem implements Expr {
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

		public static class VariableAccess extends AbstractSyntacticItem implements Expr {
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

		public static class Constant extends AbstractSyntacticItem implements Expr {
			public Constant(Value value) {
				super(Opcode.EXPR_const, value);
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

		public static class Invoke extends AbstractSyntacticItem implements Expr {
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

			public Expr getBody() {
				return (Expr) getOperand(1);
			}

			@Override
			public Quantifier clone(SyntacticItem[] operands) {
				return new Quantifier(getOpcode(), (Tuple<VariableDeclaration>) operands[0], (Expr) operands[1]);
			}
		}
	}

	/**
	 * A special kind of expression which maintains a normal form
	 * representation. As such, formulae are not suitable for representing
	 * source-level syntax, as they do not faithfully retain relevant aspects,
	 * such as ordering, etc. Instead, they are used with the automated theorem
	 * prover for ensuring properties are correct.
	 *
	 * @author David J. Pearce
	 *
	 */
	public interface Formula extends Expr {

		/**
		 * Invert a given formula.
		 * @return
		 */
		public Formula invert();

		@Override
		public Formula clone(SyntacticItem[] operands);

		/**
		 * Combine formulae together as conjuncts, whilst performing a range of
		 * simplifications:
		 *
		 * <ol>
		 * <li><b>Eliminates boolean constants</b>. Conjuncts containing
		 * <code>false</code> are reduced to <code>false</code>. In contrast,
		 * any occurrences of <code>true</code> are simply removed.</li>
		 * <li><b>Flattens nested conjuncts</b>. All nested conjuncts are
		 * recursively flattened into a single conjunct. For example,
		 * <code> (x && (y && z))</code> is flattened to
		 * <code>(x && y && z)</code>.</li>
		 * <li><b>Eliminates singleton conjuncts</b>. A conjunct containing a
		 * single (non-conjunct) child is reduced to that child.</li>
		 * </ol>
		 *
		 * The implementation attempts to eliminate dynamic memory allocation in
		 * the case that no reduction is applied.
		 *
		 * @author David J. Pearce
		 *
		 */
		public static Formula and(Formula... formulae) {
			// Flatten nested conjuncts
			formulae = Formulae.flattenNestedConjuncts(formulae);
			// Eliminate truths
			formulae = Formulae.eliminateConstants(false, formulae);
			// Ensure sorted and unique
			formulae = Formulae.sortAndRemoveDuplicates(formulae);
			// And, finally...
			if (formulae.length == 0) {
				// Return true here since the only way it's possible to get here
				// is if the conjunct contained only truths at the end.
				return new Truth(true);
			} else if (formulae.length == 1) {
				return formulae[0];
			} else {
				return new Conjunct(formulae);
			}
		}

		/**
		 * Combine formulae together as disjuncts, whilst performing a range of
		 * simplifications:
		 *
		 * <ol>
		 * <li><b>Eliminates boolean constants</b>. Disjuncts containing
		 * <code>true</code> are reduced to <code>true</code>. In contrast, any
		 * occurrences of <code>false</code> are simply removed.</li>
		 * <li><b>Flattens nested disjuncts</b>. All nested disjuncts are
		 * recursively flattened into a single disjunct. For example,
		 * <code> (x || (y || z))</code> is flattened to
		 * <code>(x || y || z)</code>.</li>
		 * <li><b>Eliminates singleton disjuncts</b>. A disjunct containing a
		 * single (non-disjunct) child is reduced to that child.</li>
		 * </ol>
		 *
		 * The implementation attempts to eliminate dynamic memory allocation in
		 * the case that no reduction is applied.
		 *
		 */
		public static Formula or(Formula... formulae) {
			// Flatten nested disjuncts
			formulae = Formulae.flattenNestedDisjuncts(formulae);
			// Eliminate truths
			formulae = Formulae.eliminateConstants(true, formulae);
			// Ensure sorted and unique
			formulae = Formulae.sortAndRemoveDuplicates(formulae);
			// And, finally...
			if (formulae.length == 0) {
				// Return false here since the only way it's possible to get
				// here is if the disjunct contained only falsehoods at the end.
				return new Truth(false);
			} else if (formulae.length == 1) {
				return formulae[0];
			} else {
				return new Disjunct(formulae);
			}
		}

		public static Formula lessThan(Polynomial lhs, Polynomial rhs) {
			if (lhs.isConstant() && rhs.isConstant()) {
				return Formulae.evaluateEquation(Opcode.EXPR_lt, lhs.toConstant(), rhs.toConstant());
			} else {
				// FIXME: we need to normalise the left- and right-hand sides
				// here
				return new Inequality(true,lhs,rhs);
			}
		}

		public static Formula greaterThanOrEquals(Polynomial lhs, Polynomial rhs) {
			if (lhs.isConstant() && rhs.isConstant()) {
				return Formulae.evaluateEquation(Opcode.EXPR_gteq, lhs.toConstant(), rhs.toConstant());
			} else {
				// FIXME: we need to normalise the left- and right-hand sides
				// here
				return new Inequality(false, lhs, rhs);
			}
		}

		public static class Truth extends Expr.Constant implements Formula {

			public Truth(boolean value) {
				super(new Value.Bool(value));
			}

			public Truth(Value.Bool value) {
				super(value);
			}

			public boolean holds() {
				return getValue().get();
			}

			@Override
			public Value.Bool getValue() {
				return (Value.Bool) super.getValue();
			}

			@Override
			public Formula invert() {
				return new Truth(!getValue().get());
			}

			@Override
			public Truth clone(SyntacticItem[] operands) {
				return new Truth((Value.Bool) operands[0]);
			}
		}

		public static class Conjunct extends Expr.Operator implements Formula {

			private Conjunct(Formula... operands) {
				super(Opcode.EXPR_and, operands);
			}

			@Override
			public Formula getOperand(int i) {
				return (Formula) super.getOperand(i);
			}

			@Override
			public Formula[] getOperands() {
				return (Formula[]) super.getOperands();
			}

			@Override
			public Formula invert() {
				Formula[] children = getOperands();
				Formula[] nChildren = new Formula[children.length];
				for(int i=0;i!=children.length;++i) {
					nChildren[i] = children[i].invert();
				}
				return or(nChildren);
			}

			@Override
			public Conjunct clone(SyntacticItem[] operands) {
				return new Conjunct((Formula[]) operands);
			}
		}

		public static class Disjunct extends Expr.Operator implements Formula {

			private Disjunct(Formula... operands) {
				super(Opcode.EXPR_or, operands);
			}

			@Override
			public Formula getOperand(int i) {
				return (Formula) super.getOperand(i);
			}

			@Override
			public Formula[] getOperands() {
				return (Formula[]) super.getOperands();
			}

			@Override
			public Formula invert() {
				Formula[] children = getOperands();
				Formula[] nChildren = new Formula[children.length];
				for(int i=0;i!=children.length;++i) {
					nChildren[i] = children[i].invert();
				}
				return and(nChildren);
			}
			@Override
			public Disjunct clone(SyntacticItem[] operands) {
				return new Disjunct((Formula[]) operands);
			}
		}

		public static class Quantifier extends Expr.Quantifier implements Formula {
			public Quantifier(Opcode opcode, VariableDeclaration[] parameters, Formula body) {
				super(opcode, new Tuple<>(parameters), body);
			}

			public Quantifier(Opcode opcode, Tuple<VariableDeclaration> parameters, Formula body) {
				super(opcode, parameters, body);
			}

			@Override
			public Tuple<VariableDeclaration> getParameters() {
				return (Tuple<VariableDeclaration>) getOperand(0);
			}

			@Override
			public Formula getBody() {
				return (Formula) getOperand(1);
			}

			@Override
			public Formula invert() {
				Formula body = getBody().invert();
				if(getOpcode() == Opcode.EXPR_forall) {
					return new Formula.Quantifier(Opcode.EXPR_exists,getParameters(),body);
				} else {
					return new Formula.Quantifier(Opcode.EXPR_forall,getParameters(),body);
				}
			}

			@Override
			public Formula.Quantifier clone(SyntacticItem[] operands) {
				return new Formula.Quantifier(getOpcode(), (Tuple<VariableDeclaration>) operands[0],
						(Formula) operands[1]);
			}
		}

		public static class Inequality extends Expr.Operator implements Formula {

			private Inequality(boolean sign, Polynomial lhs, Polynomial rhs) {
				super(sign ? Opcode.EXPR_lt : Opcode.EXPR_gteq, lhs, rhs);
			}

			@Override
			public Polynomial getOperand(int i) {
				return (Polynomial) super.getOperand(i);
			}

			@Override
			public Polynomial[] getOperands() {
				return (Polynomial[]) super.getOperands();
			}

			@Override
			public Formula invert() {
				Polynomial lhs = getOperand(0);
				Polynomial rhs = getOperand(1);
				return new Inequality(getOpcode() != Opcode.EXPR_lt,lhs,rhs);
			}

			@Override
			public Inequality clone(SyntacticItem[] operands) {
				return new Inequality(getOpcode() == Opcode.EXPR_lt, (Polynomial) operands[0],
						(Polynomial) operands[1]);
			}
		}

		public static class Equality extends Expr.Operator implements Formula {
			public Equality(boolean sign, Expr lhs, Expr rhs) {
				super(sign ? Opcode.EXPR_eq : Opcode.EXPR_neq, lhs, rhs);
			}

			@Override
			public Equality clone(SyntacticItem[] operands) {
				return new Equality(getOpcode() == Opcode.EXPR_eq, (Expr) operands[0], (Expr) operands[1]);
			}

			@Override
			public Formula invert() {
				Expr lhs = getOperand(0);
				Expr rhs = getOperand(1);
				return new Equality(getOpcode() != Opcode.EXPR_eq,lhs,rhs);
			}
		}
	}

	// ===========================================================
	// Constants
	// ===========================================================
	public final static int STAR = -2;
	public final static int UNKNOWN_TYPE = -1;
}
