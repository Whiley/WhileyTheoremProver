package wyal.lang;

import java.io.IOException;
import java.io.InputStream;
import java.io.OutputStream;
import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

import static wycc.util.ArrayUtils.*;

import wyal.io.WyalFileLexer;
import wyal.io.WyalFileParser;
import wyal.lang.WyalFile;
import wyal.util.AbstractSyntacticItem;
import wybs.util.AbstractCompilationUnit;
import wycc.util.ArrayUtils;
import wyfs.lang.Content;
import wyfs.lang.Path;

public class WyalFile extends AbstractCompilationUnit<WyalFile> implements SyntacticHeap {

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
		this.syntacticItems = new ArrayList<>();
	}

	// ============================================================
	// Accessors
	// ============================================================

	public List<SyntacticItem> getSyntacticItems() {
		return syntacticItems;
	}

	public <T extends SyntacticItem> List<T> getSyntacticItems(Class<T> kind) {
		ArrayList<T> matches = new ArrayList<>();
		for(int i=0;i!=syntacticItems.size();++i) {
			SyntacticItem item = syntacticItems.get(i);
			if(kind.isInstance(item)) {
				matches.add((T) item);
			}
		}
		return matches;
	}

	@Override
	public int size() {
		return syntacticItems.size();
	}

	@Override
	public SyntacticItem getSyntacticItem(int index) {
		return syntacticItems.get(index);
	}

	@Override
	public int getIndexOf(SyntacticItem item) {
		for(int i=0;i!=syntacticItems.size();++i) {
			if(syntacticItems.get(i) == item) {
				return i;
			}
		}
		throw new IllegalArgumentException("invalid syntactic item");
	}

	@Override
	public int allocate(SyntacticItem item) {
		if (item.getParent() == this) {
			// Item already allocated to this heap, hence return its existing
			// address.
			return getIndexOf(item);
		} else {
			// Item not allocated to this heap.
			int index = syntacticItems.size();
			item.setParent(this);
			syntacticItems.add(item);
			// Recursively allocate all children
			for (int i = 0; i != item.size(); ++i) {
				SyntacticItem child = item.getOperand(i);
				if(child != null) {
					allocate(child);
				}
			}
			return index;
		}
	}

	public <T extends SyntacticItem> void getSyntacticItems(T[] result, int... indices) {
		for(int i=0;i!=indices.length;++i) {
			result[i] = (T) getSyntacticItem(indices[i]);
		}
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

		@Override
		public abstract Item clone();
	}

	public static class Pair extends Item {
		public Pair(Item lhs, Item rhs) {
			super(Opcode.ITEM_pair, lhs, rhs);
		}

		@Override
		public Pair clone() {
			return new Pair((Item) getOperand(0).clone(), (Item) getOperand(1).clone());
		}
	}

	public static class Tuple extends Item {
		public Tuple(Item... stmts) {
			super(Opcode.ITEM_tuple, stmts);
		}
		@Override
		public Tuple clone() {
			return new Tuple(arrayClone((Item[])getOperands()));
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
		public Identifier clone() {
			return new Identifier((String) data);
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
		public Name clone() {
			return new Name(arrayClone(getComponents()));
		}
	}

	public abstract static class Constant extends Item {

		public Constant(Opcode opcode) {
			super(opcode);
		}

		public Constant(Opcode opcode, Object data) {
			super(opcode,data);
		}

		public static class Null extends Constant {
			public Null() {
				super(Opcode.CONST_null);
			}
			@Override
			public Null clone() {
				return new Null();
			}
		}

		public static class Bool extends Constant {
			public Bool(boolean value) {
				super(Opcode.CONST_bool, value);
			}

			public boolean get() {
				return (Boolean) data;
			}

			@Override
			public Bool clone() {
				return new Bool(get());
			}
		}

		public static class Int extends Constant {
			public Int(BigInteger value) {
				super(Opcode.CONST_int, value);
			}

			public BigInteger get() {
				return (BigInteger) data;
			}

			@Override
			public Int clone() {
				return new Int(get());
			}
		}

		public static class UTF8 extends Constant {
			public UTF8(byte[] bytes) {
				super(Opcode.CONST_utf8, bytes);
			}

			public byte[] get() {
				return (byte[]) data;
			}

			@Override
			public UTF8 clone() {
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
			public Import clone() {
				return new Import(arrayClone(getComponents()));
			}
		}

		public static class Assert extends Declaration {

			public Assert(Block body) {
				super(Opcode.DECL_assert, body);
			}

			public Block getBody() {
				return (Block) getOperand(0);
			}

			@Override
			public Assert clone() {
				return new Assert(getBody().clone());
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
				public FunctionOrMacro(Identifier name, Tuple parameters, Item body) {
					super(Opcode.DECL_macro, name, append(Item.class, parameters, body));
				}

				public FunctionOrMacro(Identifier name, Tuple parameters, Tuple returns) {
					super(Opcode.DECL_fun, name, parameters, returns);
				}

				public VariableDeclaration[] getParameters() {
					Tuple tuple = (Tuple) getOperand(1);
					return ArrayUtils.toArray(VariableDeclaration.class, tuple.getOperands());
				}
			}

			// ============================================================
			// Function Declaration
			// ============================================================
			public static class Function extends FunctionOrMacro {

				public Function(Identifier name, VariableDeclaration[] parameters, VariableDeclaration[] returns) {
					super(name, new Tuple(parameters), new Tuple(returns));
				}

				public VariableDeclaration[] getReturns() {
					Tuple tuple = (Tuple) getOperand(2);
					return ArrayUtils.toArray(VariableDeclaration.class, tuple.getOperands());
				}

				@Override
				public Function clone() {
					return new Function(getName().clone(), arrayClone(getParameters()), arrayClone(getReturns()));
				}
			}

			// ============================================================
			// Macro Declaration
			// ============================================================
			public static class Macro extends FunctionOrMacro {
				public Macro(Identifier name, VariableDeclaration[] parameters, Block body) {
					super(name, new Tuple(parameters), body);
				}

				public Block getBody() {
					return (Block) getOperand(2);
				}

				@Override
				public Macro clone() {
					return new Macro(getName().clone(), arrayClone(getParameters()), getBody().clone());
				}
			}

			// ============================================================
			// Type Declaration
			// ============================================================
			public static class Type extends Named {

				public Type(Identifier name, VariableDeclaration vardecl, Block... invariant) {
					super(Opcode.DECL_type, name, append(Item.class, vardecl, new Tuple(invariant)));
				}

				public VariableDeclaration getVariableDeclaration() {
					return (VariableDeclaration) getOperand(1);
				}

				public Block[] getInvariant() {
					Tuple tuple = (Tuple) getOperand(2);
					return ArrayUtils.toArray(Block.class, tuple.getOperands());
				}

				@Override
				public Type clone() {
					return new Type(getName().clone(), getVariableDeclaration().clone(), arrayClone(getInvariant()));
				}
			}
		}
	}

	// ============================================================
	// Types
	// ============================================================
	public abstract static class Type extends Item {

		@Override
		public abstract Type clone();

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
			public Any clone() {
				return new Any();
			}
		}

		public static class Void extends Atom {
			public Void() { super(Opcode.TYPE_void); }
			@Override
			public Void clone() {
				return new Void();
			}
		}

		public static class Null extends Atom {
			public Null() { super(Opcode.TYPE_null); }
			@Override
			public Null clone() {
				return new Null();
			}
		}

		public static class Bool extends Atom {
			public Bool() { super(Opcode.TYPE_bool); }
			@Override
			public Bool clone() {
				return new Bool();
			}
		}

		public static class Int extends Atom {
			public Int() { super(Opcode.TYPE_int); }
			@Override
			public Int clone() {
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
			public Array clone() {
				return new Array((Type) getElement().clone());
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
			public Reference clone() {
				return new Reference((Type) getElement().clone());
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
			public Record clone() {
				return new Record(arrayClone(getFields()));
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
			public Nominal clone() {
				return new Nominal(getName().clone());
			}
		}

		public static class Negation extends Type {
			public Negation( Type element) {
				super(Opcode.TYPE_not, element);
			}
			public Type getElement() {
				return (Type) getOperand(0);
			}

			@Override
			public Negation clone() {
				return new Negation(getElement().clone());
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
			public Union clone() {
				return new Union(arrayClone(getOperands()));
			}
		}

		public static class Intersection extends UnionOrIntersection {
			public Intersection(Type... types) {
				super(Opcode.TYPE_and, types);
			}
			@Override
			public Intersection clone() {
				return new Intersection(arrayClone(getOperands()));
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
		public VariableDeclaration clone() {
			return new VariableDeclaration(getType().clone(),getVariableName().clone());
		}
	}

	// ============================================================
	// Term
	// ============================================================

	public static class Block extends Item {
		public Block(Stmt... stmts) {
			super(Opcode.ITEM_block, stmts);
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
		public Block clone() {
			return new Block(arrayClone(getOperands()));
		}
	}


	public abstract static class Stmt extends Item {
		private Stmt(Opcode opcode, Item... operands) {
			super(opcode, operands);
		}
		private Stmt(Opcode opcode, Type type, Item... operands) {
			super(opcode, append(Item.class, type, operands));
		}

		public static class Quantifier extends Stmt {
			public Quantifier(Opcode opcode, VariableDeclaration[] parameters, Block body) {
				super(opcode, append(Item.class,parameters,body));
			}
			public VariableDeclaration[] getParameters() {
				VariableDeclaration[] vars = new VariableDeclaration[size()-1];
				for(int i=0;i!=vars.length;++i) {
					vars[i] = (VariableDeclaration) getOperand(i);
				}
				return vars;
			}
			public Block getBody() {
				return (Block) getOperand(size()-1);
			}
			@Override
			public Quantifier clone() {
				return new Quantifier(getOpcode(),arrayClone(getParameters()),getBody().clone());
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
			public IfThen clone() {
				return new IfThen(getIfBody().clone(),getThenBody().clone());
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
			public CaseOf clone() {
				return new CaseOf(arrayClone(getOperands()));
			}
		}
	}

	public abstract static class Expr extends Stmt {
		private Expr(Opcode opcode, Item... operands) {
			super(opcode, operands);
		}
		@Override
		public abstract Expr clone();

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
			public Cast clone() {
				return new Cast(getCastType().clone(),getExpr().clone());
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

			public Expr[] getExprs() {
				return ArrayUtils.toArray(Expr.class, getOperands());
			}

			@Override
			public Operator clone() {
				return new Operator(getOpcode(),arrayClone(getExprs()));
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
			public RecordAccess clone() {
				return new RecordAccess(getSource().clone(),getField().clone());
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
			public RecordInitialiser clone() {
				return new RecordInitialiser(arrayClone(getFields()));
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
			public VariableAccess clone() {
				return new VariableAccess(getVariableDeclaration().clone());
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
			public Constant clone() {
				return new Constant(getValue().clone());
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
			public Is clone() {
				return new Is(getExpr().clone(),getType().clone());
			}
		}

		public static class Invoke extends Expr {
			public Invoke(Type type, Name name, Expr... arguments) {
				super(Opcode.EXPR_invoke, append(new Item[] { type, name }, arguments));
			}

			public Type getType() {
				return (Type) getOperand(0);
			}

			public Name getName() {
				return (Name) getOperand(1);
			}

			public Expr[] getArguments() {
				Expr[] rs = new Expr[size() - 2];
				for (int i = 0; i != rs.length; ++i) {
					rs[i] = (Expr) getOperand(i + 2);
				}
				return rs;
			}

			@Override
			public Invoke clone() {
				Type type = getType();
				if (type != null) {
					type = type.clone();
				}
				return new Invoke(type, getName().clone(), arrayClone(getArguments()));
			}
		}
	}

	// ===========================================================
	// Helpers
	// ===========================================================

	/**
	 * Recursively clone an array of syntactic items
	 *
	 * @param arr
	 * @return
	 */
	private static <T extends SyntacticItem> T[] arrayClone(T[] arr) {
		T[] narr = Arrays.copyOf(arr, arr.length);
		for(int i=0;i!=narr.length;++i) {
			T item = narr[i];
			if(item != null) {
				narr[i] = (T) item.clone();
			}
		}
		return narr;
	}

	// ===========================================================
	// Constants
	// ===========================================================
	public final static int STAR = -2;
	public final static int UNKNOWN_TYPE = -1;
}
