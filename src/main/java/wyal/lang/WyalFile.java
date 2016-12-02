package wyal.lang;

import java.io.IOException;
import java.io.InputStream;
import java.io.OutputStream;
import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.List;

import static wycc.util.ArrayUtils.*;

import wyal.io.WyalFileLexer;
import wyal.io.WyalFileParser;
import wyal.lang.WyalFile;
import wyal.util.AbstractSyntacticItem;
import wybs.lang.Attribute;
import wybs.lang.SyntacticElement;
import wybs.util.AbstractCompilationUnit;
import wycc.util.ArrayUtils;
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
		ITEM_ident(101),
		ITEM_path(102),
		ITEM_name(103),
		// DECLARATIONS
		DECL_linecomment(104),
		DECL_blkcomment(105),
		DECL_import(106),
		DECL_assert(107),
		DECL_type(108),
		DECL_fun(109),
		DECL_macro(110),
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

	public SyntacticItem getSyntacticItem(int index) {
		return syntacticItems.get(index);
	}

	public <T extends SyntacticItem> void getSyntacticItems(T[] result, int... indices) {
		for(int i=0;i!=indices.length;++i) {
			result[i] = (T) getSyntacticItem(indices[i]);
		}
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

	public static class Null extends Item {
		public Null(WyalFile parent) {
			super(parent, Opcode.CONST_null);
		}
	}

	public static class Bool extends Item {
		public Bool(WyalFile parent, boolean value) {
			super(parent, Opcode.CONST_bool, value);
		}

		public boolean get() {
			return (Boolean) data;
		}
	}

	public static class Int extends Item {
		public Int(WyalFile parent, BigInteger value) {
			super(parent, Opcode.CONST_int, value);
		}

		public BigInteger get() {
			return (BigInteger) data;
		}
	}

	public static class UTF8 extends Item {
		public UTF8(WyalFile parent, byte[] bytes) {
			super(parent, Opcode.CONST_utf8, bytes);
		}

		public byte[] get() {
			return (byte[]) data;
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
			super(parent, Opcode.ITEM_ident, components);
		}
	}

	// ============================================================
	// Declarations
	// ============================================================
	public static class Declaration extends Item {
		public Declaration(WyalFile parent, Opcode opcode, Item... children) {
			super(parent, opcode, children);
		}
	}

	public static class NamedDeclaration extends Declaration {

		public NamedDeclaration(WyalFile parent, Opcode opcode, Identifier name, Item... children) {
			super(parent, opcode, append(name, children));
		}

		public String getName() {
			int nameIndex = getOperand(0);
			SyntacticItem item = getParent().getSyntacticItem(nameIndex);
			return ((Identifier) item).get();
		}
	}

	// ============================================================
	// Imports
	// ============================================================

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
		public Import(WyalFile parent, UTF8... components) {
			super(parent, Opcode.DECL_import, components);
		}
	}

	// ============================================================
	// Function Declaration
	// ============================================================
	public static class Function extends NamedDeclaration {

		public Function(WyalFile parent, Identifier name, VariableDeclaration[] parameters, VariableDeclaration[] returns) {
			super(parent, Opcode.DECL_fun, name, parameters, returns);
		}

		public SemanticType.Function getType() {
			return null;
		}
	}

	// ============================================================
	// Macro Declaration
	// ============================================================
	public static class Macro extends NamedDeclaration {

		public Macro(WyalFile parent, Identifier name, VariableDeclaration[] parameters, Stmt body) {
			super(parent, Opcode.DECL_macro, name, append(body, parameters));
		}

		public Term getBody() {
			int bodyIndex = getOperand(1);
			return (Term) getParent().getSyntacticItem(bodyIndex);
		}

		public SemanticType.Function getType() {
			return null;
		}
	}

	// ============================================================
	// Type Declaration
	// ============================================================
	public static class Type extends NamedDeclaration {

		public Type(WyalFile parent, Identifier name, Stmt... invariant) {
			super(parent, Opcode.DECL_type, name, invariant);
		}

		public Term[] getInvariant() {
			int[] invariantIndices = getOtherOperands();
			Term[] invariant = new Term[invariantIndices.length];
			getParent().getSyntacticItems(invariant, invariantIndices);
			return invariant;
		}

		public SemanticType.Function getType() {
			return null;
		}
	}

	// ============================================================
	// Assertion
	// ============================================================
	public static class Assert extends Declaration {

		public Assert(WyalFile parent, Stmt body) {
			super(parent, Opcode.DECL_assert, body);
		}

		public Term getBody() {
			int bodyIndex = getOperand(0);
			return (Term) getParent().getSyntacticItem(bodyIndex);
		}
	}

	// ============================================================
	// Types
	// ============================================================
	public static class Type extends Item {

	}

	// ============================================================
	// Term
	// ============================================================

	/**
	 * A term represents some kind of operational unit which evaluates to a give
	 * type, such an expression or statement. Statements already evaluate to the
	 * type void.
	 *
	 * @author David J. Pearce
	 *
	 */
	public static class Term extends Item {

		public Term(WyalFile parent, Opcode opcode, Type typeIndex, Item... operands) {
			super(parent, opcode, append(typeIndex, operands));
		}

		/**
		 * Get the number of subterms of this term.
		 *
		 * @return
		 */
		public int numberOfTerms() {
			return numberOfOperands() - 1;
		}

		/**
		 * Return the ith operand associated with this location.
		 *
		 * @param i
		 * @return
		 */
		public Term getTerm(int i) {
			int termIndex = getOperand(i + 1);
			return (Term) getParent().getSyntacticItem(termIndex);
		}
	}

	public static class Stmt extends Term {
		public Stmt(WyalFile parent, Opcode opcode, Item... operands) {
			super(parent, opcode, null, operands);
		}
		protected Stmt(WyalFile parent, Opcode opcode, Type type, Item... operands) {
			super(parent, opcode, type, operands);
		}
	}

	public static class Block extends Stmt {
		public Block(WyalFile parent, Stmt... stmts) {
			super(parent, Opcode.STMT_block, stmts);
		}
	}

	public static class VariableDeclaration extends Stmt {
		public VariableDeclaration(WyalFile parent, Type type, Identifier name) {
			super(parent, Opcode.STMT_vardecl, null, type, name);
		}
		public VariableDeclaration(WyalFile parent, Type type, Identifier name, Expr initialiser) {
			super(parent, Opcode.STMT_vardecl, null, type, name, initialiser);
		}
	}

	public static class Expr extends Stmt {
		private Expr(WyalFile parent, Opcode opcode, Type type, Item... operands) {
			super(parent, opcode, type, operands);
		}
	}

	public static class Cast extends Expr {
		public Cast(WyalFile parent, Type type, Expr rhs) {
			super(parent, Opcode.EXPR_cast, null, type, rhs);
		}
	}

	public static class Operator extends Expr {
		public Operator(WyalFile parent, Opcode opcode, Type type, Expr... operands) {
			super(parent, opcode, type, operands);
		}
	}

	public static class RecordAccess extends Expr {
		public RecordAccess(WyalFile parent, Type type, Expr lhs, Identifier rhs) {
			super(parent, Opcode.EXPR_recfield, type, lhs, rhs);
		}
	}

	public static class RecordInitialiser extends Expr {
		public RecordInitialiser(WyalFile parent, Type type, Pair... fields) {
			super(parent, Opcode.EXPR_recfield, type, fields);
		}
	}

	public static class VariableAccess extends Expr {
		public VariableAccess(WyalFile parent, Type type, VariableDeclaration decl) {
			super(parent, Opcode.EXPR_recfield, type, decl);
		}
	}

	public static class Constant extends Expr {
		public Constant(WyalFile parent, Item value) {
			super(parent, Opcode.EXPR_const, null, value);
		}
	}

	public static class Is extends Expr {
		public Is(WyalFile parent, Expr lhs, Type rhs) {
			super(parent, Opcode.EXPR_is, null, lhs, rhs);
		}
	}

	// ===========================================================
	// Constants
	// ===========================================================
	public final static int STAR = -2;
	public final static int UNKNOWN_TYPE = -1;
}
