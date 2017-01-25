package wyal.lang;

import java.io.IOException;
import java.io.InputStream;
import java.io.OutputStream;
import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.Map;

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
		public Item clone(Map<SyntacticItem,SyntacticItem> mapping) {
			return (Item) super.clone(mapping);
		}
	}

	public static class Pair extends Item {
		public Pair(Item lhs, Item rhs) {
			super(Opcode.ITEM_pair, lhs, rhs);
		}

		@Override
		public Pair copy(Map<SyntacticItem,SyntacticItem> mapping) {
			return new Pair((Item) getOperand(0).clone(mapping), (Item) getOperand(1).clone(mapping));
		}
	}

	public static class Tuple extends Item {
		public Tuple(Item... stmts) {
			super(Opcode.ITEM_tuple, stmts);
		}
		@Override
		public Tuple copy(Map<SyntacticItem,SyntacticItem> mapping) {
			return new Tuple(arrayClone(mapping, (Item[])getOperands()));
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
		public Identifier clone(Map<SyntacticItem,SyntacticItem> mapping) {
			return (Identifier) super.clone(mapping);
		}

		@Override
		public Identifier copy(Map<SyntacticItem,SyntacticItem> mapping) {
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
		public Name clone(Map<SyntacticItem,SyntacticItem> mapping) {
			return (Name) super.clone(mapping);
		}

		@Override
		public Name copy(Map<SyntacticItem,SyntacticItem> mapping) {
			return new Name(arrayClone(mapping, getComponents()));
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
			public Null copy(Map<SyntacticItem,SyntacticItem> mapping) {
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
			public Bool copy(Map<SyntacticItem,SyntacticItem> mapping) {
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
			public Int copy(Map<SyntacticItem,SyntacticItem> mapping) {
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
			public UTF8 copy(Map<SyntacticItem,SyntacticItem> mapping) {
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

		@Override
		public Declaration clone(Map<SyntacticItem,SyntacticItem> mapping) {
			return (Declaration) super.clone(mapping);
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
			public Import copy(Map<SyntacticItem,SyntacticItem> mapping) {
				return new Import(arrayClone(mapping, getComponents()));
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
			public Assert copy(Map<SyntacticItem,SyntacticItem> mapping) {
				return new Assert(getBody().clone(mapping));
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
				public Function copy(Map<SyntacticItem,SyntacticItem> mapping) {
					return new Function(getName().clone(mapping), arrayClone(mapping, getParameters()), arrayClone(mapping, getReturns()));
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
				public Macro copy(Map<SyntacticItem,SyntacticItem> mapping) {
					return new Macro(getName().clone(mapping), arrayClone(mapping, getParameters()), getBody().clone(mapping));
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
				public Type copy(Map<SyntacticItem,SyntacticItem> mapping) {
					return new Type(getName().clone(mapping), getVariableDeclaration().clone(mapping), arrayClone(mapping, getInvariant()));
				}
			}
		}
	}

	// ============================================================
	// Types
	// ============================================================
	public abstract static class Type extends Item {

		@Override
		public Type clone(Map<SyntacticItem,SyntacticItem> mapping) {
			return (Type) super.clone(mapping);
		}

		@Override
		public abstract Type copy(Map<SyntacticItem,SyntacticItem> mapping);

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
			public Any copy(Map<SyntacticItem,SyntacticItem> mapping) {
				return new Any();
			}
		}

		public static class Void extends Atom {
			public Void() { super(Opcode.TYPE_void); }
			@Override
			public Void copy(Map<SyntacticItem,SyntacticItem> mapping) {
				return new Void();
			}
		}

		public static class Null extends Atom {
			public Null() { super(Opcode.TYPE_null); }
			@Override
			public Null copy(Map<SyntacticItem,SyntacticItem> mapping) {
				return new Null();
			}
		}

		public static class Bool extends Atom {
			public Bool() { super(Opcode.TYPE_bool); }
			@Override
			public Bool copy(Map<SyntacticItem,SyntacticItem> mapping) {
				return new Bool();
			}
		}

		public static class Int extends Atom {
			public Int() { super(Opcode.TYPE_int); }
			@Override
			public Int copy(Map<SyntacticItem,SyntacticItem> mapping) {
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
			public Array copy(Map<SyntacticItem,SyntacticItem> mapping) {
				return new Array((Type) getElement().clone(mapping));
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
			public Reference copy(Map<SyntacticItem,SyntacticItem> mapping) {
				return new Reference((Type) getElement().clone(mapping));
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
			public Record copy(Map<SyntacticItem,SyntacticItem> mapping) {
				return new Record(arrayClone(mapping, getFields()));
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
			public Nominal copy(Map<SyntacticItem,SyntacticItem> mapping) {
				return new Nominal(getName().clone(mapping));
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
			public Negation copy(Map<SyntacticItem,SyntacticItem> mapping) {
				return new Negation(getElement().clone(mapping));
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
			public Union copy(Map<SyntacticItem,SyntacticItem> mapping) {
				return new Union(arrayClone(mapping, getOperands()));
			}
		}

		public static class Intersection extends UnionOrIntersection {
			public Intersection(Type... types) {
				super(Opcode.TYPE_and, types);
			}
			@Override
			public Intersection copy(Map<SyntacticItem,SyntacticItem> mapping) {
				return new Intersection(arrayClone(mapping, getOperands()));
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
		public VariableDeclaration clone(Map<SyntacticItem,SyntacticItem> mapping) {
			return (VariableDeclaration) super.clone(mapping);
		}

		@Override
		public VariableDeclaration copy(Map<SyntacticItem,SyntacticItem> mapping) {
			return new VariableDeclaration(getType().clone(mapping),getVariableName().clone(mapping));
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
		public Block clone(Map<SyntacticItem,SyntacticItem> mapping) {
			return (Block) super.clone(mapping);
		}

		@Override
		public Block copy(Map<SyntacticItem,SyntacticItem> mapping) {
			return new Block(arrayClone(mapping, getOperands()));
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
			public Quantifier copy(Map<SyntacticItem,SyntacticItem> mapping) {
				return new Quantifier(getOpcode(),arrayClone(mapping, getParameters()),getBody().clone(mapping));
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
			public IfThen copy(Map<SyntacticItem,SyntacticItem> mapping) {
				return new IfThen(getIfBody().clone(mapping),getThenBody().clone(mapping));
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
			public CaseOf copy(Map<SyntacticItem,SyntacticItem> mapping) {
				return new CaseOf(arrayClone(mapping, getOperands()));
			}
		}
	}

	public abstract static class Expr extends Stmt {
		private Expr(Opcode opcode, Item... operands) {
			super(opcode, operands);
		}
		@Override
		public Expr clone(Map<SyntacticItem,SyntacticItem> mapping) {
			return (Expr) super.clone(mapping);
		}

		@Override
		public abstract Expr copy(Map<SyntacticItem,SyntacticItem> mapping);

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
			public Cast copy(Map<SyntacticItem,SyntacticItem> mapping) {
				return new Cast(getCastType().clone(mapping),getExpr().clone(mapping));
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
			public Operator copy(Map<SyntacticItem,SyntacticItem> mapping) {
				return new Operator(getOpcode(),arrayClone(mapping, getExprs()));
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
			public RecordAccess copy(Map<SyntacticItem,SyntacticItem> mapping) {
				return new RecordAccess(getSource().clone(mapping),getField().clone(mapping));
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
			public RecordInitialiser copy(Map<SyntacticItem,SyntacticItem> mapping) {
				return new RecordInitialiser(arrayClone(mapping, getFields()));
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
			public VariableAccess copy(Map<SyntacticItem,SyntacticItem> mapping) {
				return new VariableAccess(getVariableDeclaration().clone(mapping));
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
			public Constant copy(Map<SyntacticItem,SyntacticItem> mapping) {
				return new Constant(getValue().clone(mapping));
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
			public Is copy(Map<SyntacticItem,SyntacticItem> mapping) {
				return new Is(getExpr().clone(mapping),getType().clone(mapping));
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
			public Invoke copy(Map<SyntacticItem,SyntacticItem> mapping) {
				Type type = getType();
				if (type != null) {
					type = type.clone(mapping);
				}
				return new Invoke(type, getName().clone(mapping), arrayClone(mapping, getArguments()));
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
	private static <T extends SyntacticItem> T[] arrayClone(Map<SyntacticItem,SyntacticItem> mapping, T[] arr) {
		T[] narr = Arrays.copyOf(arr, arr.length);
		for(int i=0;i!=narr.length;++i) {
			T item = narr[i];
			if(item != null) {
				narr[i] = (T) item.clone(mapping);
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
