package wyal.lang;

import java.io.IOException;
import java.io.InputStream;
import java.io.OutputStream;
import java.math.BigInteger;
import java.util.ArrayList;
import java.util.List;

import static wycc.util.ArrayUtils.*;

import wyal.io.WyalFileLexer;
import wyal.io.WyalFileParser;
import wyal.lang.WyalFile;
import wyal.util.AbstractSyntacticItem;
import wybs.util.AbstractCompilationUnit;
import wyfs.lang.Content;
import wyfs.lang.Path;

public class WyalFile extends AbstractCompilationUnit<WyalFile> {

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
		ITEM_block(102),
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
		STMT_vardecl(16),
		STMT_ifthen(17),
		STMT_caseof(18),
		STMT_exists(35),
		STMT_forall(36),
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
	// State
	// =========================================================================
	private final ArrayList<SyntacticItem> syntacticItems;

	// =========================================================================
	// Constructors
	// =========================================================================

	public WyalFile(Path.Entry<WyalFile> entry) {
		super(entry);
		this.syntacticItems = new ArrayList<SyntacticItem>();
	}

	// ============================================================
	// Accessors
	// ============================================================

	public List<SyntacticItem> getSyntacticItems() {
		return syntacticItems;
	}

	public <T extends SyntacticItem> List<T> getSyntacticItems(Class<T> kind) {
		ArrayList<T> matches = new ArrayList<T>();
		for(int i=0;i!=syntacticItems.size();++i) {
			SyntacticItem item = syntacticItems.get(i);
			if(kind.isInstance(item)) {
				matches.add((T) item);
			}
		}
		return matches;
	}

	public int size() {
		return syntacticItems.size();
	}

	public SyntacticItem getSyntacticItem(int index) {
		return syntacticItems.get(index);
	}

	public <T extends SyntacticItem> void getSyntacticItems(T[] result, int... indices) {
		for(int i=0;i!=indices.length;++i) {
			result[i] = (T) getSyntacticItem(indices[i]);
		}
	}

	public int getIndex(SyntacticItem item) {
		for(int i=0;i!=syntacticItems.size();++i) {
			if(syntacticItems.get(i) == item) {
				return i;
			}
		}
		throw new IllegalArgumentException("invalid syntactic item");
	}
	// ============================================================
	// Fundamental Items
	// ============================================================
	public static class Item extends AbstractSyntacticItem {
		public Item(WyalFile parent, Opcode opcode, Item... items) {
			super(parent, opcode, items);
		}

		public Item(WyalFile parent, Opcode opcode, Object data) {
			super(parent, opcode, data);
		}
	}

	public static class Pair extends Item {
		public Pair(WyalFile parent, Item lhs, Item rhs) {
			super(parent, Opcode.ITEM_pair, lhs, rhs);
		}
	}
	public static class Tuple extends Item {
		public Tuple(WyalFile parent, Item... stmts) {
			super(parent, Opcode.ITEM_tuple, stmts);
		}
	}

	public static class Identifier extends Item {
		public Identifier(WyalFile parent, String name) {
			super(parent, Opcode.ITEM_ident, name);
		}

		public String get() {
			return (String) data;
		}
	}

	public static class Name extends Item {
		public Name(WyalFile parent, Identifier... components) {
			super(parent, Opcode.ITEM_name, components);
		}

		public Identifier[] getComponents() {
			return (Identifier[]) getOperands();
		}
	}

	public abstract static class Constant extends Item {

		public Constant(WyalFile parent, Opcode opcode, Object data) {
			super(parent,opcode,data);
		}

		public static class Null extends Constant {
			public Null(WyalFile parent) {
				super(parent, Opcode.CONST_null, null);
			}
		}

		public static class Bool extends Constant {
			public Bool(WyalFile parent, boolean value) {
				super(parent, Opcode.CONST_bool, value);
			}

			public boolean get() {
				return (Boolean) data;
			}
		}

		public static class Int extends Constant {
			public Int(WyalFile parent, BigInteger value) {
				super(parent, Opcode.CONST_int, value);
			}

			public BigInteger get() {
				return (BigInteger) data;
			}
		}

		public static class UTF8 extends Constant {
			public UTF8(WyalFile parent, byte[] bytes) {
				super(parent, Opcode.CONST_utf8, bytes);
			}

			public byte[] get() {
				return (byte[]) data;
			}
		}
	}

	// ============================================================
	// Declarations
	// ============================================================
	public static class Declaration extends Item {
		public Declaration(WyalFile parent, Opcode opcode, Item... children) {
			super(parent, opcode, children);
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
			public Import(WyalFile parent, Identifier... components) {
				super(parent, Opcode.DECL_import, components);
			}
		}

		public static class Assert extends Declaration {

			public Assert(WyalFile parent, Block body) {
				super(parent, Opcode.DECL_assert, body);
			}

			public Block getBody() {
				return (Block) getOperand(0);
			}
		}

		public static class Named extends Declaration {

			public Named(WyalFile parent, Opcode opcode, Identifier name, Item... children) {
				super(parent, opcode, append(Item.class, name, children));
			}

			public Identifier getName() {
				return (Identifier) getOperand(0);
			}

			public static class FunctionOrMacro extends Named {
				public FunctionOrMacro(WyalFile parent, Identifier name, Tuple parameters, Item body) {
					super(parent, Opcode.DECL_macro, name, append(Item.class, parameters, body));
				}

				public FunctionOrMacro(WyalFile parent, Identifier name, Tuple parameters, Tuple returns) {
					super(parent, Opcode.DECL_fun, name, parameters, returns);
				}

				public VariableDeclaration[] getParameters() {
					Tuple params = (Tuple) getOperand(1);
					VariableDeclaration[] vars = new VariableDeclaration[params.numberOfOperands()];
					for (int i = 0; i != vars.length; ++i) {
						vars[i] = (VariableDeclaration) params.getOperand(i);
					}
					return vars;
				}
			}

			// ============================================================
			// Function Declaration
			// ============================================================
			public static class Function extends FunctionOrMacro {

				public Function(WyalFile parent, Identifier name, VariableDeclaration[] parameters,
						VariableDeclaration[] returns) {
					super(parent, name, new Tuple(parent, parameters), new Tuple(parent, returns));
				}

				public VariableDeclaration[] getReturns() {
					Tuple returns = (Tuple) getOperand(2);
					VariableDeclaration[] vars = new VariableDeclaration[returns.numberOfOperands()];
					for (int i = 0; i != vars.length; ++i) {
						vars[i] = (VariableDeclaration) returns.getOperand(i);
					}
					return vars;
				}
			}

			// ============================================================
			// Macro Declaration
			// ============================================================
			public static class Macro extends FunctionOrMacro {
				public Macro(WyalFile parent, Identifier name, VariableDeclaration[] parameters, Block body) {
					super(parent, name, new Tuple(parent, parameters), body);
				}
				public Block getBody() {
					return (Block) getOperand(2);
				}
			}

			// ============================================================
			// Type Declaration
			// ============================================================
			public static class Type extends Named {

				public Type(WyalFile parent, Identifier name, VariableDeclaration vardecl, Block... invariant) {
					super(parent, Opcode.DECL_type, name, append(Item.class, vardecl, invariant));
				}

				public VariableDeclaration getVariableDeclaration() {
					return (VariableDeclaration) getOperand(1);
				}

				public Block[] getInvariant() {
					Block[] invariant = new Block[numberOfOperands()-2];
					for(int i=0;i!=invariant.length;++i) {
						invariant[i] = (Block) getOperand(i+2);
					}
					return invariant;
				}
			}
		}
	}

	// ============================================================
	// Types
	// ============================================================
	public abstract static class Type extends Item {

		public Type(WyalFile parent, Opcode opcode, Item... items) {
			super(parent, opcode, items);
		}

		public static class Any extends Type {
			public Any(WyalFile parent) { super(parent, Opcode.TYPE_any); }
		}

		public static class Void extends Type {
			public Void(WyalFile parent) { super(parent, Opcode.TYPE_void); }
		}

		public static class Null extends Type {
			public Null(WyalFile parent) { super(parent, Opcode.TYPE_null); }
		}

		public static class Bool extends Type {
			public Bool(WyalFile parent) { super(parent, Opcode.TYPE_bool); }
		}

		public static class Int extends Type {
			public Int(WyalFile parent) { super(parent, Opcode.TYPE_int); }
		}

		public static class Array extends Type {
			public Array(WyalFile parent,  Type element) {
				super(parent, Opcode.TYPE_arr, element);
			}
			public Type getElement() {
				return (Type) getOperand(0);
			}
		}

		public static class Reference extends Type {
			public Reference(WyalFile parent,  Type element) {
				super(parent, Opcode.TYPE_arr, element);
			}
			public Type getElement() {
				return (Type) getOperand(0);
			}
		}

		public static class Record extends Type {
			public Record(WyalFile parent, VariableDeclaration... fields) {
				super(parent, Opcode.TYPE_rec, fields);
			}

			public VariableDeclaration[] getFields() {
				VariableDeclaration[] vars = new VariableDeclaration[numberOfOperands()];
				for (int i = 0; i != vars.length; ++i) {
					vars[i] = (VariableDeclaration) getOperand(i);
				}
				return vars;
			}
		}

		public static class Nominal extends Type {
			public Nominal(WyalFile parent, Name name) {
				super(parent, Opcode.TYPE_nom, name);
			}

			public Name getName() {
				return (Name) getOperand(0);
			}
		}

		public static class Negation extends Type {
			public Negation(WyalFile parent,  Type element) {
				super(parent, Opcode.TYPE_not, element);
			}
			public Type getElement() {
				return (Type) getOperand(0);
			}
		}

		public static class Union extends Type {
			public Union(WyalFile parent,  Type... types) {
				super(parent, Opcode.TYPE_or, types);
			}
			@Override
			public Type getOperand(int i) {
				return (Type) super.getOperand(i);
			}
		}

		public static class Intersection extends Type {
			public Intersection(WyalFile parent,  Type... types) {
				super(parent, Opcode.TYPE_and, types);
			}
			@Override
			public Type getOperand(int i) {
				return (Type) super.getOperand(i);
			}
		}
	}

	// ============================================================
	// Variable Declaration
	// ============================================================

	public static class VariableDeclaration extends Item {
		public VariableDeclaration(WyalFile parent, Type type, Identifier name) {
			super(parent, Opcode.STMT_vardecl, type, name);
		}

		public Type getType() {
			return (Type) getOperand(0);
		}

		public Identifier getVariableName() {
			return (Identifier) getOperand(1);
		}
	}

	// ============================================================
	// Term
	// ============================================================

	public static class Block extends Item {
		public Block(WyalFile parent, Stmt... stmts) {
			super(parent, Opcode.ITEM_block, stmts);
		}

		@Override
		public Stmt getOperand(int i) {
			return (Stmt) super.getOperand(i);
		}
	}


	public static class Stmt extends Item {
		private Stmt(WyalFile parent, Opcode opcode, Item... operands) {
			super(parent, opcode, operands);
		}
		private Stmt(WyalFile parent, Opcode opcode, Type type, Item... operands) {
			super(parent, opcode, append(Item.class, type, operands));
		}

		public static class Quantifier extends Stmt {
			public Quantifier(WyalFile parent, Opcode opcode, VariableDeclaration[] parameters, Block body) {
				super(parent, opcode, append(Item.class,parameters,body));
			}
			public VariableDeclaration[] getParameters() {
				VariableDeclaration[] vars = new VariableDeclaration[numberOfOperands()-1];
				for(int i=0;i!=vars.length;++i) {
					vars[i] = (VariableDeclaration) getOperand(i);
				}
				return vars;
			}
			public Block getBody() {
				return (Block) getOperand(numberOfOperands()-1);
			}
		}

		public static class IfThen extends Stmt {
			public IfThen(WyalFile parent, Block ifBlock, Block thenBlock) {
				super(parent, Opcode.STMT_ifthen, ifBlock, thenBlock);
			}
			public Block getIfBody() {
				return (Block) getOperand(0);
			}
			public Block getThenBody() {
				return (Block) getOperand(1);
			}
		}

		public static class CaseOf extends Stmt {
			public CaseOf(WyalFile parent, Block... cases) {
				super(parent, Opcode.STMT_caseof, cases);
			}
			@Override
			public Block getOperand(int i) {
				return (Block) super.getOperand(i);
			}
		}
	}

	public static class Expr extends Stmt {
		private Expr(WyalFile parent, Opcode opcode, Type type, Item... operands) {
			super(parent, opcode, type, operands);
		}

		public static class Cast extends Expr {
			public Cast(WyalFile parent, Type type, Expr rhs) {
				super(parent, Opcode.EXPR_cast, null, type, rhs);
			}
			public Type getCastType() {
				return (Type) super.getOperand(1);
			}
			public Expr getExpr() {
				return (Expr) super.getOperand(2);
			}
		}

		public static class Operator extends Expr {
			public Operator(WyalFile parent, Opcode opcode, Type type, Expr... operands) {
				super(parent, opcode, type, operands);
			}

			@Override
			public Expr getOperand(int i) {
				return (Expr) super.getOperand(i);
			}

			public Expr[] getExprs() {
				SyntacticItem[] items = getOperands();
				Expr[] rs = new Expr[items.length-1];
				System.arraycopy(items, 1, rs, 0, rs.length);
				return rs;
			}
		}

		public static class RecordAccess extends Expr {
			public RecordAccess(WyalFile parent, Type type, Expr lhs, Identifier rhs) {
				super(parent, Opcode.EXPR_recfield, type, lhs, rhs);
			}
			public Expr getSource() {
				return (Expr) getOperand(1);
			}
			public Identifier getField() {
				return (Identifier) getOperand(2);
			}
		}

		public static class RecordInitialiser extends Expr {
			public RecordInitialiser(WyalFile parent, Type type, Pair... fields) {
				super(parent, Opcode.EXPR_recinit, type, fields);
			}
			public Pair[] getFields() {
				SyntacticItem[] items = getOperands();
				Pair[] rs = new Pair[items.length-1];
				System.arraycopy(items, 1, rs, 0, rs.length);
				return rs;
			}
		}

		public static class VariableAccess extends Expr {
			public VariableAccess(WyalFile parent, Type type, VariableDeclaration decl) {
				super(parent, Opcode.EXPR_var, type, decl);
			}
			public VariableDeclaration getVariableDeclaration() {
				return (VariableDeclaration) getOperand(1);
			}
		}

		public static class Constant extends Expr {
			public Constant(WyalFile parent, Item value) {
				super(parent, Opcode.EXPR_const, null, value);
			}
			public Item getValue() {
				return (Item) getOperand(1);
			}
		}

		public static class Is extends Expr {
			public Is(WyalFile parent, Expr lhs, Type rhs) {
				super(parent, Opcode.EXPR_is, null, lhs, rhs);
			}
			public Expr getExpr() {
				return (Expr) getOperand(1);
			}
			public Type getType() {
				return (Type) getOperand(2);
			}
		}

		public static class Invoke extends Expr {
			public Invoke(WyalFile parent, Type type, Name name, Expr... arguments) {
				super(parent, Opcode.EXPR_invoke, type, append(Item.class, name, arguments));
			}
			public Name getName() {
				return (Name) getOperand(1);
			}
			public Expr[] getArguments() {
				Expr[] rs = new Expr[numberOfOperands()-2];
				for(int i=0;i!=rs.length;++i) {
					rs[i] = (Expr) getOperand(i+2);
				}
				return rs;
			}
		}
	}

	// ===========================================================
	// Constants
	// ===========================================================
	public final static int STAR = -2;
	public final static int UNKNOWN_TYPE = -1;
}
