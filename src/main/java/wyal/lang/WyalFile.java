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

package wyal.lang;

import java.io.IOException;
import java.io.InputStream;
import java.io.OutputStream;
import java.io.PrintWriter;
import java.math.BigInteger;

import wyal.heap.AbstractSyntacticHeap;
import wyal.heap.AbstractSyntacticItem;
import wyal.io.WyalFileLexer;
import wyal.io.WyalFileParser;
import wyal.io.WyalFilePrinter;
import wyal.lang.WyalFile;
import wybs.lang.CompilationUnit;
import wybs.lang.NameID;
import wycc.util.ArrayUtils;
import wyfs.lang.Content;
import wyfs.lang.Path;
import wyfs.lang.Path.Entry;
import wyfs.util.Trie;
import wytp.proof.Proof;

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
		public WyalFile read(Path.Entry<WyalFile> e, InputStream input) throws IOException {
			throw new RuntimeException("Implement me!");
		}

		@Override
		public void write(OutputStream output, WyalFile module) throws IOException {
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
		// REFERENCES
		EXPR_deref(56),
		// RECORDS
		EXPR_recfield(57),
		EXPR_recupdt(58),
		// ARRAYS
		EXPR_arridx(59),
		EXPR_arrlen(60),
		EXPR_arrupdt(61),
		// Initialisers come later so they not given preference for
		// substitution.
		EXPR_arrgen(62),
		EXPR_arrinit(63),
		EXPR_recinit(64),
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

	/**
	 * Represents a pair of items in a compilation unit.
	 *
	 * @author David J. Pearce
	 *
	 * @param <K>
	 * @param <V>
	 */
	public static class Pair<K extends SyntacticItem, V extends SyntacticItem> extends AbstractSyntacticItem {
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
		public Pair<K, V> clone(SyntacticItem[] operands) {
			return new Pair<>((K) operands[0], (V) operands[1]);
		}

		@Override
		public String toString() {
			return "(" + getFirst() + ", " + getSecond() + ")";
		}
	}

	/**
	 * Represents a sequence of zero or more items in a compilation unit.
	 *
	 * @author David J. Pearce
	 *
	 * @param <T>
	 */
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
			for (int i = 0; i != size(); ++i) {
				if (i != 0) {
					r += ",";
				}
				SyntacticItem child = getOperand(i);
				if (child == null) {
					r += "?";
				} else {
					r += child.toString();
				}
			}
			return "(" + r + ")";
		}
	}

	/**
	 * Represents an <i>identifier</i> in a compilation unit. For example, this
	 * could be used to represent a variable access. Or, it could be part of a
	 * partially or fully qualified name.
	 *
	 * @author David J. Pearce
	 *
	 */
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

		@Override
		public String toString() {
			return get();
		}
	}

	/**
	 * Represents a <i>partial-</i> or <i>fully-qualified</i> name within a
	 * compilation unit.
	 *
	 * @author David J. Pearce
	 *
	 */
	public static class Name extends AbstractSyntacticItem {
		public Name(Identifier... components) {
			super(Opcode.ITEM_name, components);
		}

		@Override
		public Identifier getOperand(int i) {
			return (Identifier) super.getOperand(i);
		}

		public Identifier[] getComponents() {
			return (Identifier[]) getOperands();
		}

		@Override
		public Name clone(SyntacticItem[] operands) {
			return new Name((Identifier[]) operands);
		}

		@Override
		public String toString() {
			String r = getOperand(0).get();
			for (int i = 1; i != size(); ++i) {
				r += "." + getOperand(i).get();
			}
			return r;
		}

		public NameID toNameID() {
			Trie pkg = Trie.ROOT;
			for (int i = 0; i < size() - 1; ++i) {
				pkg = pkg.append(getOperand(i).get());
			}
			String n = getOperand(size() - 1).get();
			return new NameID(pkg, n);
		}
	}

	/**
	 * Represents a raw value within a compilation unit. This is not a
	 * source-level item, though could be a component of a source-level item
	 * (e.g. a constant expression).
	 *
	 * @author David J. Pearce
	 *
	 */
	public abstract static class Value extends AbstractSyntacticItem {

		public Value(Opcode opcode) {
			super(opcode);
		}

		public Value(Opcode opcode, Object data) {
			super(opcode, data, new SyntacticItem[0]);
		}

		public abstract Type getType();

		@Override
		public String toString() {
			return getData().toString();
		}

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

			@Override
			public String toString() {
				return "null";
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
			public Identifier getOperand(int i) {
				return (Identifier) super.getOperand(i);
			}

			@Override
			public Import clone(SyntacticItem[] operands) {
				return new Import((Identifier[]) operands);
			}

			@Override
			public String toString() {
				String r = "import ";
				for (int i = 0; i != size(); ++i) {
					if (i != 0) {
						r += ".";
					}
					Identifier component = getOperand(i);
					if (component == null) {
						r += "*";
					} else {
						r += component.get();
					}
				}
				return r;
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

			@Override
			public String toString() {
				return "assert " + getBody();
			}
		}

		public static interface Named extends Declaration {

			public Identifier getName();

			public static abstract class FunctionOrMacro extends AbstractSyntacticItem implements Named {
				public FunctionOrMacro(Identifier name, Tuple<VariableDeclaration> parameters, Stmt.Block body) {
					super(Opcode.DECL_macro, name, parameters, body);
				}

				public FunctionOrMacro(Identifier name, Tuple<VariableDeclaration> parameters,
						Tuple<VariableDeclaration> returns) {
					super(Opcode.DECL_fun, name, parameters, returns);
				}

				@Override
				public Identifier getName() {
					return (Identifier) getOperand(0);
				}

				public Tuple<VariableDeclaration> getParameters() {
					return (Tuple) getOperand(1);
				}

				public abstract WyalFile.Type.FunctionOrMacro getSignatureType();
			}

			// ============================================================
			// Function Declaration
			// ============================================================
			public static class Function extends FunctionOrMacro {

				public Function(Identifier name, VariableDeclaration[] parameters, VariableDeclaration[] returns) {
					super(name, new Tuple(parameters), new Tuple(returns));
				}

				public Function(Identifier name, Tuple<VariableDeclaration> parameters,
						Tuple<VariableDeclaration> returns) {
					super(name, parameters, returns);
				}

				public Tuple<VariableDeclaration> getReturns() {
					return (Tuple<VariableDeclaration>) getOperand(2);
				}

				@Override
				public WyalFile.Type.Function getSignatureType() {
					return new WyalFile.Type.Function(projectTypes(getParameters()), projectTypes(getReturns()));
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
				public WyalFile.Type.Macro getSignatureType() {
					return new WyalFile.Type.Macro(projectTypes(getParameters()));
				}

				@Override
				public Macro clone(SyntacticItem[] operands) {
					return new Macro((Identifier) operands[0], (Tuple<VariableDeclaration>) operands[1],
							(Stmt.Block) operands[2]);
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

		public static Any Any = new Any();
		public static Void Void = new Void();
		public static Bool Bool = new Bool();
		public static Int Int = new Int();
		public static Null Null = new Null();

		public interface Primitive extends Type {

		}

		public static abstract class Atom extends AbstractSyntacticItem implements Type {
			public Atom(Opcode opcode, SyntacticItem... items) {
				super(opcode, items);
			}
		}

		public static class Any extends Atom implements Primitive {
			public Any() {
				super(Opcode.TYPE_any);
			}

			@Override
			public Any clone(SyntacticItem[] operands) {
				return new Any();
			}

			@Override
			public String toString() {
				return "any";
			}
		}

		public static class Void extends Atom implements Primitive {
			public Void() {
				super(Opcode.TYPE_void);
			}

			@Override
			public Void clone(SyntacticItem[] operands) {
				return new Void();
			}

			@Override
			public String toString() {
				return "void";
			}
		}

		public static class Null extends Atom implements Primitive {
			public Null() {
				super(Opcode.TYPE_null);
			}

			@Override
			public Null clone(SyntacticItem[] operands) {
				return new Null();
			}

			@Override
			public String toString() {
				return "null";
			}
		}

		public static class Bool extends Atom implements Primitive {
			public Bool() {
				super(Opcode.TYPE_bool);
			}

			@Override
			public Bool clone(SyntacticItem[] operands) {
				return new Bool();
			}

			@Override
			public String toString() {
				return "bool";
			}
		}

		public static class Int extends Atom implements Primitive {
			public Int() {
				super(Opcode.TYPE_int);
			}

			@Override
			public Int clone(SyntacticItem[] operands) {
				return new Int();
			}

			@Override
			public String toString() {
				return "int";
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

			@Override
			public String toString() {
				return "(" + getElement() + ")[]";
			}
		}

		public static class Reference extends Atom {
			public Reference(Type element) {
				super(Opcode.TYPE_ref, element);
			}

			public Type getElement() {
				return (Type) getOperand(0);
			}

			@Override
			public Reference clone(SyntacticItem[] operands) {
				return new Reference((Type) operands[0]);
			}

			@Override
			public String toString() {
				return "&(" + getElement() + ")";
			}
		}

		public static class Record extends Atom {
			public Record(boolean isOpen, FieldDeclaration... fields) {
				super(Opcode.TYPE_rec, ArrayUtils.append(SyntacticItem.class, new Value.Bool(isOpen), fields));
			}

			private Record(SyntacticItem[] operands) {
				super(Opcode.TYPE_rec, operands);
			}

			public boolean isOpen() {
				Value.Bool flag = (Value.Bool) getOperand(0);
				return flag.get();
			}

			public FieldDeclaration[] getFields() {
				SyntacticItem[] operands = getOperands();
				FieldDeclaration[] fields = new FieldDeclaration[size() - 1];
				System.arraycopy(operands, 1, fields, 0, fields.length);
				return fields;
			}

			@Override
			public Record clone(SyntacticItem[] operands) {
				return new Record(operands);
			}

			@Override
			public String toString() {
				String r = "{";
				FieldDeclaration[] fields = getFields();
				for (int i = 0; i != fields.length; ++i) {
					if (i != 0) {
						r += ",";
					}
					FieldDeclaration field = fields[i];
					r += field.getType() + " " + field.getVariableName();
				}
				if (isOpen()) {
					if (fields.length > 0) {
						r += ", ...";
					} else {
						r += "...";
					}
				}
				return r + "}";
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

			@Override
			public String toString() {
				return getName().toString();
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

			@Override
			public String toString() {
				return "!(" + getElement() + ")";
			}
		}

		public abstract static class UnionOrIntersection extends AbstractSyntacticItem implements Type {
			public UnionOrIntersection(Opcode kind, Type... types) {
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

			@Override
			public String toString() {
				String r = "";
				for (int i = 0; i != size(); ++i) {
					if (i != 0) {
						r += "|";
					}
					r += getOperand(i);
				}
				return "(" + r + ")";
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

			@Override
			public String toString() {
				String r = "";
				for (int i = 0; i != size(); ++i) {
					if (i != 0) {
						r += "&";
					}
					r += getOperand(i);
				}
				return "(" + r + ")";
			}
		}

		public static abstract class FunctionOrMacroOrInvariant extends Atom implements Type {
			public FunctionOrMacroOrInvariant(Opcode opcode, Tuple<Type> parameters, Tuple<Type> returns) {
				super(opcode, parameters, returns);
			}

			public Tuple<Type> getParameters() {
				return (Tuple<Type>) getOperand(0);
			}

			public Tuple<Type> getReturns() {
				return (Tuple<Type>) getOperand(1);
			}

			@Override
			public String toString() {
				return getParameters() + "->" + getReturns();
			}
		}

		public static abstract class FunctionOrMacro extends FunctionOrMacroOrInvariant {
			public FunctionOrMacro(Opcode opcode, Tuple<Type> parameters, Tuple<Type> returns) {
				super(opcode, parameters, returns);
			}
		}

		public static class Function extends FunctionOrMacro implements Type {
			public Function(Tuple<Type> parameters, Tuple<Type> returns) {
				super(Opcode.TYPE_fun, parameters, returns);
			}

			@Override
			public Function clone(SyntacticItem[] operands) {
				return new Function((Tuple<Type>) operands[0], (Tuple<Type>) operands[1]);
			}

			@Override
			public String toString() {
				return "function" + super.toString();
			}
		}

		public static class Macro extends FunctionOrMacro implements Type {
			public Macro(Tuple<Type> parameters) {
				super(Opcode.TYPE_macro, parameters, new Tuple<>(new Type.Bool()));
			}

			private Macro(Tuple<Type> parameters, Tuple<Type> returns) {
				super(Opcode.TYPE_macro, parameters, returns);
			}

			@Override
			public Macro clone(SyntacticItem[] operands) {
				return new Macro((Tuple<Type>) operands[0], (Tuple<Type>) operands[1]);
			}

			@Override
			public String toString() {
				return "macro" + super.toString();
			}
		}

		public static class Invariant extends FunctionOrMacroOrInvariant implements Type {
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

			@Override
			public String toString() {
				return "invariant" + super.toString();
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

		public static abstract class Quantifier extends AbstractSyntacticItem implements Stmt {
			public Quantifier(Opcode opcode, VariableDeclaration[] parameters, Block body) {
				super(opcode, new Tuple<>(parameters), body);
			}

			public Quantifier(Opcode opcode, Tuple<VariableDeclaration> parameters, Block body) {
				super(opcode, parameters, body);
			}

			public Tuple<VariableDeclaration> getParameters() {
				return (Tuple<VariableDeclaration>) getOperand(0);
			}

			public Block getBody() {
				return (Block) getOperand(1);
			}

			@Override
			public abstract Quantifier clone(SyntacticItem[] operands);
		}

		/**
		 * Represents an unbounded universally quantified expression of the form
		 * "<code>forall(T v1, ... T vn): block</code>" where
		 * <code>T1 v1</code> ... <code>Tn vn</code> are the <i>quantified
		 * variable declarations</i> and <code>block</code> is the body
		 * consisting of a statement block
		 *
		 * @author David J. Pearce
		 *
		 */
		public static class UniversalQuantifier extends Quantifier {
			public UniversalQuantifier(VariableDeclaration[] parameters, Block body) {
				super(Opcode.STMT_forall, new Tuple<>(parameters), body);
			}

			public UniversalQuantifier(Tuple<VariableDeclaration> parameters, Block body) {
				super(Opcode.STMT_forall, parameters, body);
			}

			@Override
			public Quantifier clone(SyntacticItem[] operands) {
				return new UniversalQuantifier((Tuple<VariableDeclaration>) operands[0],
						(Block) operands[1]);
			}
		}

		/**
		 * Represents an unbounded existentially quantified expression of the
		 * form "<code>some(T v1, ... T vn): block</code>" where
		 * <code>T1 v1</code> ... <code>Tn vn</code> are the <i>quantified
		 * variable declarations</i> and <code>block</code> is the body
		 * consisting of a statement block.
		 *
		 * @author David J. Pearce
		 *
		 */
		public static class ExistentialQuantifier extends Quantifier {
			public ExistentialQuantifier(VariableDeclaration[] parameters, Block body) {
				super(Opcode.STMT_exists, new Tuple<>(parameters), body);
			}

			public ExistentialQuantifier(Tuple<VariableDeclaration> parameters, Block body) {
				super(Opcode.STMT_exists, parameters, body);
			}

			@Override
			public Quantifier clone(SyntacticItem[] operands) {
				return new ExistentialQuantifier((Tuple<VariableDeclaration>) operands[0], (Block) operands[1]);
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

		// =========================================================================
		// General Expressions
		// =========================================================================

		/**
		 * Represents a cast expression of the form "<code>(T) e</code>" where
		 * <code>T</code> is the <i>cast type</i> and <code>e</code> the
		 * <i>casted expression</i>.
		 *
		 * @author David J. Pearce
		 *
		 */
		public static class Cast extends AbstractSyntacticItem implements Expr {
			public Cast(Type type, Expr rhs) {
				super(Opcode.EXPR_cast, type, rhs);
			}

			public Type getCastType() {
				return (Type) super.getOperand(0);
			}

			public Expr getCastedExpr() {
				return (Expr) super.getOperand(1);
			}

			@Override
			public Cast clone(SyntacticItem[] operands) {
				return new Cast((Type) operands[0], (Expr) operands[1]);
			}

			@Override
			public String toString() {
				return "(" + getCastType() + ") " + getCastedExpr();
			}
		}

		/**
		 * Represents the use of a constant within some expression. For example,
		 * in <code>x + 1</code> the expression <code>1</code> is a constant
		 * expression.
		 *
		 * @author David J. Pearce
		 *
		 */
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

			@Override
			public String toString() {
				return getValue().toString();
			}
		}

		/**
		 * Represents a <i>type test expression</i> of the form
		 * "<code>e is T</code>" where <code>e</code> is the <i>test
		 * expression</i> and <code>T</code> is the <i>test type</i>.
		 *
		 * @author David J. Pearce
		 *
		 */
		public static class Is extends AbstractSyntacticItem implements Expr {
			public Is(Expr lhs, Type rhs) {
				super(Opcode.EXPR_is, lhs, rhs);
			}

			public Expr getTestExpr() {
				return (Expr) getOperand(0);
			}

			public Type getTestType() {
				return (Type) getOperand(1);
			}

			@Override
			public Is clone(SyntacticItem[] operands) {
				return new Is((Expr) operands[0], (Type) operands[1]);
			}

			@Override
			public String toString() {
				return getTestExpr() + " is " + getTestType();
			}
		}

		/**
		 * Represents an invocation of the form "<code>x.y.f(e1,..en)</code>".
		 * Here, <code>x.y.f</code> constitute a <i>partially-</i> or
		 * <i>fully-qualified name</i> and <code>e1</code> ... <code>en</code>
		 * are the <i>argument expressions</i>.
		 *
		 * @author David J. Pearce
		 *
		 */
		public static class Invoke extends AbstractSyntacticItem implements Expr {

			public Invoke(Type.FunctionOrMacroOrInvariant type, Name name, Integer selector, Expr... arguments) {
				super(Opcode.EXPR_invoke, type, name, selector != null ? new Value.Int(selector) : null,
						new Tuple<>(arguments));
			}

			public Invoke(Type.FunctionOrMacroOrInvariant type, Name name, Value.Int selector, Tuple<Expr> arguments) {
				super(Opcode.EXPR_invoke, type, name, selector, arguments);
			}

			public Type.FunctionOrMacroOrInvariant getSignatureType() {
				return (Type.FunctionOrMacroOrInvariant) getOperand(0);
			}

			public void setSignatureType(Type.FunctionOrMacroOrInvariant type) {
				this.setOperand(0, type);
			}

			public Name getName() {
				return (Name) getOperand(1);
			}

			public Value.Int getSelector() {
				return (Value.Int) getOperand(2);
			}

			public Tuple<Expr> getArguments() {
				return (Tuple) getOperand(3);
			}

			@Override
			public Invoke clone(SyntacticItem[] operands) {
				return new Invoke((Type.FunctionOrMacroOrInvariant) operands[0], (Name) operands[1],
						(Value.Int) operands[2], (Tuple) operands[3]);
			}

			@Override
			public String toString() {
				String r = getName().toString();
				r += getArguments();
				r += "#" + getSelector();
				return r;
			}
		}

		/**
		 * Represents an abstract operator expression over one or more
		 * <i>operand expressions</i>. For example. in <code>arr[i+1]</code> the
		 * expression <code>i+1</code> is an operator expression.
		 *
		 * @author David J. Pearce
		 *
		 */
		public abstract static class Operator extends AbstractSyntacticItem implements Expr {
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
			public abstract Expr clone(SyntacticItem[] operands);
		}

		/**
		 * Represents an abstract quantified expression of the form
		 * "<code>forall(T v1, ... T vn).e</code>" or
		 * "<code>exists(T v1, ... T vn).e</code>" where <code>T1 v1</code> ...
		 * <code>Tn vn</code> are the <i>quantified variable declarations</i>
		 * and <code>e</code> is the body.
		 *
		 * @author David J. Pearce
		 *
		 */
		public abstract static class Quantifier extends AbstractSyntacticItem implements Expr {
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
			public abstract Expr clone(SyntacticItem[] operands);
		}

		/**
		 * Represents an unbounded universally quantified expression of the form
		 * "<code>forall(T v1, ... T vn).e</code>" where <code>T1 v1</code> ...
		 * <code>Tn vn</code> are the <i>quantified variable declarations</i>
		 * and <code>e</code> is the body.
		 *
		 * @author David J. Pearce
		 *
		 */
		public static class UniversalQuantifier extends Quantifier {
			public UniversalQuantifier(VariableDeclaration[] parameters, Expr body) {
				super(Opcode.EXPR_forall, new Tuple<>(parameters), body);
			}

			public UniversalQuantifier(Tuple<VariableDeclaration> parameters, Expr body) {
				super(Opcode.EXPR_forall, parameters, body);
			}

			@Override
			public Expr clone(SyntacticItem[] operands) {
				return new UniversalQuantifier((Tuple<VariableDeclaration>) operands[0],
						(Expr) operands[1]);
			}

			@Override
			public String toString() {
				String r = "forall";
				r += getParameters();
				r += ".";
				r += getBody();
				return r;
			}
		}

		/**
		 * Represents an unbounded existentially quantified expression of the
		 * form "<code>some(T v1, ... T vn).e</code>" where <code>T1 v1</code>
		 * ... <code>Tn vn</code> are the <i>quantified variable
		 * declarations</i> and <code>e</code> is the body.
		 *
		 * @author David J. Pearce
		 *
		 */
		public static class ExistentialQuantifier extends Quantifier {
			public ExistentialQuantifier(VariableDeclaration[] parameters, Expr body) {
				super(Opcode.EXPR_exists, new Tuple<>(parameters), body);
			}

			public ExistentialQuantifier(Tuple<VariableDeclaration> parameters, Expr body) {
				super(Opcode.EXPR_exists, parameters, body);
			}

			@Override
			public Expr clone(SyntacticItem[] operands) {
				return new ExistentialQuantifier((Tuple<VariableDeclaration>) operands[0], (Expr) operands[1]);
			}

			@Override
			public String toString() {
				String r = "exists";
				r += getParameters();
				r += ".";
				r += getBody();
				return r;
			}
		}

		/**
		 * Represents a use of some variable within an expression. For example,
		 * in <code>x + 1</code> the expression <code>x</code> is a variable
		 * access expression. Every variable access is associated with a
		 * <i>variable declaration</i> that unique identifies which variable is
		 * being accessed.
		 *
		 * @author David J. Pearce
		 *
		 */
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

			@Override
			public String toString() {
				return getVariableDeclaration().getVariableName().toString();
			}
		}


		public abstract static class InfixOperator extends Operator {
			public InfixOperator(Opcode opcode, Expr... operands) {
				super(opcode, operands);
			}

			@Override
			public String toString() {
				String str = getOperatorString();
				String r = "";
				for (int i = 0; i != size(); ++i) {
					if (i != 0) {
						r += str;
					}
					r += getOperand(i);
				}
				return r;
			}

			protected abstract String getOperatorString();
		}

		// =========================================================================
		// Logical Expressions
		// =========================================================================
		/**
		 * Represents a <i>logical conjunction</i> of the form
		 * "<code>e1 && .. && en</code>" where <code>e1</code> ...
		 * <code>en</code> are the <i>operand expressions</i>.
		 *
		 * @author David J. Pearce
		 *
		 */
		public static class LogicalAnd extends InfixOperator {
			public LogicalAnd(Expr... operands) {
				super(Opcode.EXPR_and, operands);
			}

			@Override
			public Expr clone(SyntacticItem[] operands) {
				if(operands.length <= 1) {
					throw new IllegalArgumentException("invalid number of operands");
				}
				return new LogicalAnd(ArrayUtils.toArray(Expr.class, operands));
			}

			@Override
			protected String getOperatorString() {
				return " && ";
			}
		}

		/**
		 * Represents a <i>logical disjunction</i> of the form
		 * "<code>e1 || .. || en</code>" where <code>e1</code> ...
		 * <code>en</code> are the <i>operand expressions</i>.
		 *
		 * @author David J. Pearce
		 *
		 */
		public static class LogicalOr extends InfixOperator {
			public LogicalOr(Expr... operands) {
				super(Opcode.EXPR_or, operands);
			}

			@Override
			public Expr clone(SyntacticItem[] operands) {
				if(operands.length <= 1) {
					throw new IllegalArgumentException("invalid number of operands");
				}
				return new LogicalOr(ArrayUtils.toArray(Expr.class, operands));
			}


			@Override
			protected String getOperatorString() {
				return " && ";
			}
		}

		/**
		 * Represents a <i>logical implication</i> of the form
		 * "<code>e1 ==> ... ==> en</code>" where <code>e1</code> ...
		 * <code>en</code> are the <i>operand expressions</i>.
		 *
		 * @author David J. Pearce
		 *
		 */
		public static class LogicalImplication extends InfixOperator {
			public LogicalImplication(Expr... operands) {
				super(Opcode.EXPR_implies, operands);
			}

			@Override
			public Expr clone(SyntacticItem[] operands) {
				if(operands.length <= 1) {
					throw new IllegalArgumentException("invalid number of operands");
				}
				return new LogicalImplication(ArrayUtils.toArray(Expr.class, operands));
			}


			@Override
			protected String getOperatorString() {
				return " ==> ";
			}
		}

		/**
		 * Represents a <i>logical biconditional</i> of the form
		 * "<code>e1 <==> ... <==> en</code>" where <code>e1</code> ...
		 * <code>en</code> are the <i>operand expressions</i>.
		 *
		 * @author David J. Pearce
		 *
		 */
		public static class LogicalIff extends InfixOperator {
			public LogicalIff(Expr... operands) {
				super(Opcode.EXPR_iff, operands);
			}

			@Override
			public Expr clone(SyntacticItem[] operands) {
				if(operands.length <= 1) {
					throw new IllegalArgumentException("invalid number of operands");
				}
				return new LogicalIff(ArrayUtils.toArray(Expr.class, operands));
			}


			@Override
			protected String getOperatorString() {
				return " <==> ";
			}
		}

		/**
		 * Represents a <i>logical negation</i> of the form "<code>!e</code>"
		 * where <code>e</code> is the <i>operand expression</i>.
		 *
		 * @author David J. Pearce
		 *
		 */
		public static class LogicalNot extends Operator {
			public LogicalNot(Expr operand) {
				super(Opcode.EXPR_not, operand);
			}

			public Expr getOperand() {
				return getOperand(0);
			}

			@Override
			public Expr clone(SyntacticItem[] operands) {
				if(operands.length != 1) {
					throw new IllegalArgumentException("invalid number of operands");
				}
				return new LogicalNot((Expr) operands[0]);
			}
		}

		// =========================================================================
		// Comparator Expressions
		// =========================================================================

		/**
		 * Represents an equality expression of the form
		 * "<code>e1 == ... == en</code>" where <code>e1</code> ...
		 * <code>en</code> are the <i>operand expressions</i>.
		 *
		 * @author David J. Pearce
		 *
		 */
		public static class Equal extends InfixOperator {
			public Equal(Expr... operands) {
				super(Opcode.EXPR_eq, operands);
			}

			@Override
			public Expr clone(SyntacticItem[] operands) {
				if(operands.length <= 1) {
					throw new IllegalArgumentException("invalid number of operands");
				}
				return new Equal(ArrayUtils.toArray(Expr.class, operands));
			}

			@Override
			public String getOperatorString() {
				return " == ";
			}
		}

		/**
		 * Represents an unequality expression of the form
		 * "<code>e1 != ... != en</code>" where <code>e1</code> ...
		 * <code>en</code> are the <i>operand expressions</i>.
		 *
		 * @author David J. Pearce
		 *
		 */
		public static class NotEqual extends InfixOperator {
			public NotEqual(Expr... operands) {
				super(Opcode.EXPR_neq, operands);
			}

			@Override
			public Expr clone(SyntacticItem[] operands) {
				if(operands.length <= 1) {
					throw new IllegalArgumentException("invalid number of operands");
				}
				return new NotEqual(ArrayUtils.toArray(Expr.class, operands));
			}

			@Override
			protected String getOperatorString() {
				return " != ";
			}
		}

		/**
		 * Represents a strict <i>inequality expression</i> of the form
		 * "<code>e1 < ... < en</code>" where <code>e1</code> ...
		 * <code>en</code> are the <i>operand expressions</i>.
		 *
		 * @author David J. Pearce
		 *
		 */
		public static class LessThan extends InfixOperator {
			public LessThan(Expr... operands) {
				super(Opcode.EXPR_lt, operands);
			}

			@Override
			public Expr clone(SyntacticItem[] operands) {
				if (operands.length <= 1) {
					throw new IllegalArgumentException("invalid number of operands");
				}
				return new LessThan(ArrayUtils.toArray(Expr.class, operands));
			}

			@Override
			protected String getOperatorString() {
				return " < ";
			}
		}

		/**
		 * Represents a non-strict <i>inequality expression</i> of the form
		 * "<code>e1 <= ... <= en</code>" where <code>e1</code> ...
		 * <code>en</code> are the <i>operand expressions</i>.
		 *
		 * @author David J. Pearce
		 *
		 */
		public static class LessThanOrEqual extends InfixOperator {
			public LessThanOrEqual(Expr... operands) {
				super(Opcode.EXPR_lteq, operands);
			}

			@Override
			public Expr clone(SyntacticItem[] operands) {
				if (operands.length <= 1) {
					throw new IllegalArgumentException("invalid number of operands");
				}
				return new LessThanOrEqual(ArrayUtils.toArray(Expr.class, operands));
			}

			@Override
			protected String getOperatorString() {
				return " <= ";
			}
		}

		/**
		 * Represents a strict <i>inequality expression</i> of the form
		 * "<code>e1 > ... > en</code>" where <code>e1</code> ...
		 * <code>en</code> are the <i>operand expressions</i>.
		 *
		 * @author David J. Pearce
		 *
		 */
		public static class GreaterThan extends InfixOperator {
			public GreaterThan(Expr... operands) {
				super(Opcode.EXPR_gt, operands);
			}

			@Override
			public Expr clone(SyntacticItem[] operands) {
				if (operands.length <= 1) {
					throw new IllegalArgumentException("invalid number of operands");
				}
				return new GreaterThan(ArrayUtils.toArray(Expr.class, operands));
			}

			@Override
			protected String getOperatorString() {
				return " > ";
			}
		}

		/**
		 * Represents a non-strict <i>inequality expression</i> of the form
		 * "<code>e1 >= ... >= en</code>" where <code>e1</code> ...
		 * <code>en</code> are the <i>operand expressions</i>.
		 *
		 * @author David J. Pearce
		 *
		 */
		public static class GreaterThanOrEqual extends InfixOperator {
			public GreaterThanOrEqual(Expr... operands) {
				super(Opcode.EXPR_gteq, operands);
			}

			@Override
			public Expr clone(SyntacticItem[] operands) {
				if (operands.length <= 1) {
					throw new IllegalArgumentException("invalid number of operands");
				}
				return new GreaterThanOrEqual(ArrayUtils.toArray(Expr.class, operands));
			}

			@Override
			protected String getOperatorString() {
				return " >= ";
			}
		}

		// =========================================================================
		// Arithmetic Expressions
		// =========================================================================

		/**
		 * Represents an arithmetic <i>addition expression</i> of the form
		 * "<code>e1 + ... + en</code>" where <code>e1</code> ...
		 * <code>en</code> are the <i>operand expressions</i>.
		 *
		 * @author David J. Pearce
		 *
		 */
		public static class Addition extends InfixOperator {
			public Addition(Expr... operands) {
				super(Opcode.EXPR_add, operands);
			}

			@Override
			public Expr clone(SyntacticItem[] operands) {
				if (operands.length <= 1) {
					throw new IllegalArgumentException("invalid number of operands");
				}
				return new Addition(ArrayUtils.toArray(Expr.class, operands));
			}

			@Override
			protected String getOperatorString() {
				return " + ";
			}
		}

		/**
		 * Represents an arithmetic <i>subtraction expression</i> of the form
		 * "<code>e1 - ... - en</code>" where <code>e1</code> ...
		 * <code>en</code> are the <i>operand expressions</i>.
		 *
		 * @author David J. Pearce
		 *
		 */
		public static class Subtraction extends InfixOperator {
			public Subtraction(Expr... operands) {
				super(Opcode.EXPR_sub, operands);
			}

			@Override
			public Expr clone(SyntacticItem[] operands) {
				if (operands.length <= 1) {
					throw new IllegalArgumentException("invalid number of operands");
				}
				return new Subtraction(ArrayUtils.toArray(Expr.class, operands));
			}

			@Override
			protected String getOperatorString() {
				return " - ";
			}
		}

		/**
		 * Represents an arithmetic <i>multiplication expression</i> of the form
		 * "<code>e1 * ... * en</code>" where <code>e1</code> ...
		 * <code>en</code> are the <i>operand expressions</i>.
		 *
		 * @author David J. Pearce
		 *
		 */
		public static class Multiplication extends InfixOperator {
			public Multiplication(Expr... operands) {
				super(Opcode.EXPR_mul, operands);
			}

			@Override
			public Expr clone(SyntacticItem[] operands) {
				if (operands.length <= 1) {
					throw new IllegalArgumentException("invalid number of operands");
				}
				return new Multiplication(ArrayUtils.toArray(Expr.class, operands));
			}

			@Override
			protected String getOperatorString() {
				return " * ";
			}
		}

		/**
		 * Represents an arithmetic <i>division expression</i> of the form
		 * "<code>e1 / ... / en</code>" where <code>e1</code> ...
		 * <code>en</code> are the <i>operand expressions</i>.
		 *
		 * @author David J. Pearce
		 *
		 */
		public static class Division extends InfixOperator {
			public Division(Expr... operands) {
				super(Opcode.EXPR_div, operands);
			}

			@Override
			public Expr clone(SyntacticItem[] operands) {
				if (operands.length <= 1) {
					throw new IllegalArgumentException("invalid number of operands");
				}
				return new Division(ArrayUtils.toArray(Expr.class, operands));
			}

			@Override
			protected String getOperatorString() {
				return " / ";
			}
		}

		/**
		 * Represents an arithmetic <i>remainder expression</i> of the form
		 * "<code>e1 / ... / en</code>" where <code>e1</code> ...
		 * <code>en</code> are the <i>operand expressions</i>.
		 *
		 * @author David J. Pearce
		 *
		 */
		public static class Remainder extends InfixOperator {
			public Remainder(Expr... operands) {
				super(Opcode.EXPR_rem, operands);
			}

			@Override
			public Expr clone(SyntacticItem[] operands) {
				if (operands.length <= 1) {
					throw new IllegalArgumentException("invalid number of operands");
				}
				return new Remainder(ArrayUtils.toArray(Expr.class, operands));
			}

			@Override
			protected String getOperatorString() {
				return " % ";
			}
		}

		/**
		 * Represents an arithmetic <i>negation expression</i> of the form
		 * "<code>-e</code>" where <code>e</code> is the <i>operand
		 * expression</i>.
		 *
		 * @author David J. Pearce
		 *
		 */
		public static class Negation extends Operator {
			public Negation(Expr operand) {
				super(Opcode.EXPR_neg, operand);
			}

			public Expr getOperand() {
				return getOperand(0);
			}

			@Override
			public Expr clone(SyntacticItem[] operands) {
				if (operands.length != 1) {
					throw new IllegalArgumentException("invalid number of operands");
				}
				return new Negation((Expr) operands[0]);
			}


			@Override
			public String toString() {
				return "-" + getOperand();
			}
		}

		// =========================================================================
		// Reference Expressions
		// =========================================================================
		public static class Dereference extends Operator {
			public Dereference(Expr operand) {
				super(Opcode.EXPR_deref, operand);
			}

			public Expr getOperand() {
				return getOperand(0);
			}

			@Override
			public Expr clone(SyntacticItem[] operands) {
				if (operands.length != 1) {
					throw new IllegalArgumentException("invalid number of operands");
				}
				return new Dereference((Expr) operands[0]);
			}

			@Override
			public String toString() {
				return "*" + getOperand();
			}
		}

		// =========================================================================
		// Array Expressions
		// =========================================================================

		/**
		 * Represents an <i>array access expression</i> of the form
		 * "<code>arr[e]</code>" where <code>arr</code> is the <i>source
		 * array</i> and <code>e</code> the <i>subscript expression</i>. This
		 * returns the value held in the element determined by <code>e</code>.
		 *
		 * @author David J. Pearce
		 *
		 */
		public static class ArrayAccess extends Expr.Operator {
			public ArrayAccess(Expr src, Expr index) {
				super(Opcode.EXPR_arridx, src, index);
			}

			public Expr getSource() {
				return (Expr) getOperand(0);
			}

			public Expr getSubscript() {
				return (Expr) getOperand(1);
			}

			@Override
			public ArrayAccess clone(SyntacticItem[] operands) {
				return new ArrayAccess((Expr) operands[0], (Expr) operands[1]);
			}
		}

		/**
		 * Represents an <i>array update expression</i> of the form
		 * "<code>arr[e1:=e2]</code>" where <code>arr</code> is the <i>source
		 * array</i>, <code>e1</code> the <i>subscript expression</i> and
		 * <code>e2</code> is the value expression. This returns a new array
		 * which is equivalent to <code>arr</code> but where the element
		 * determined by <code>e1</code> has the value resulting from
		 * <code>e2</code>.
		 *
		 * @author David J. Pearce
		 *
		 */
		public static class ArrayUpdate extends Expr.Operator {
			public ArrayUpdate(Expr src, Expr index, Expr value) {
				super(Opcode.EXPR_arrupdt, src, index, value);
			}

			public Expr getSource() {
				return (Expr) getOperand(0);
			}

			public Expr getSubscript() {
				return (Expr) getOperand(1);
			}

			public Expr getValue() {
				return (Expr) getOperand(2);
			}

			@Override
			public ArrayUpdate clone(SyntacticItem[] operands) {
				return new ArrayUpdate((Expr) operands[0], (Expr) operands[1], (Expr) operands[2]);
			}

			@Override
			public String toString() {
				return getSource() + "[" + getSubscript() + ":=" + getValue() + "]";
			}
		}

		/**
		 * Represents an <i>array initialiser expression</i> of the form
		 * "<code>[e1,...,en]</code>" where <code>e1</code> ... <code>en</code>
		 * are the <i>initialiser expressions</i>. Thus returns a new array made
		 * up from those values resulting from the initialiser expressions.
		 *
		 * @author David J. Pearce
		 *
		 */
		public static class ArrayInitialiser extends Expr.Operator {
			public ArrayInitialiser(Expr... elements) {
				super(Opcode.EXPR_arrinit, elements);
			}

			@Override
			public ArrayInitialiser clone(SyntacticItem[] operands) {
				return new ArrayInitialiser(ArrayUtils.toArray(Expr.class, operands));
			}
		}

		/**
		 * Represents an <i>array generator expression</i> of the form
		 * "<code>[e1;e2]</code>" where <code>e1</code> is the <i>element
		 * expression</i> and <code>e2</code> is the <i>length expression</i>.
		 * This returns a new array whose length is determined by
		 * <code>e2</code> and where every element has contains the value
		 * determined by <code>e1</code>.
		 *
		 * @author David J. Pearce
		 *
		 */
		public static class ArrayGenerator extends Expr.Operator {
			public ArrayGenerator(Expr value, Expr length) {
				super(Opcode.EXPR_arrgen, value, length);
			}

			public Expr getValue() {
				return (Expr) getOperand(0);
			}

			public Expr getLength() {
				return (Expr) getOperand(1);
			}

			@Override
			public ArrayGenerator clone(SyntacticItem[] operands) {
				return new ArrayGenerator((Expr) operands[0], (Expr) operands[1]);
			}
		}

		/**
		 * Represents an <i>array length expression</i> of the form
		 * "<code>|arr|</code>" where <code>arr</code> is the <i>source
		 * array</i>. This simply returns the length of array <code>arr</code>.
		 * <code>e</code>.
		 *
		 * @author David J. Pearce
		 *
		 */
		public static class ArrayLength extends Expr.Operator {
			public ArrayLength(Expr src) {
				super(Opcode.EXPR_arrlen, src);
			}

			public Expr getSource() {
				return (Expr) getOperand(0);
			}

			@Override
			public ArrayLength clone(SyntacticItem[] operands) {
				return new ArrayLength((Expr) operands[0]);
			}

			@Override
			public String toString() {
				return "|" + getSource() + "|";
			}
		}

		// =========================================================================
		// Record Expressions
		// =========================================================================

		/**
		 * Represents a <i>record access expression</i> of the form
		 * "<code>rec.f</code>" where <code>rec</code> is the <i>source record</i>
		 * and <code>f</code> is the <i>field</i>.
		 *
		 * @author David J. Pearce
		 *
		 */
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

			@Override
			public String toString() {
				return getSource() + "." + getField();
			}
		}

		/**
		 * Represents a <i>record initialiser</i> expression of the form
		 * <code>{ f1: e1, ..., fn: en }</code> where <code>f1: e1</code> ...
		 * <code>fn: en</code> are <i>field initialisers</code>. This returns a
		 * new record where each field holds the value resulting from its
		 * corresponding expression.
		 *
		 * @author David J. Pearce
		 *
		 */
		public static class RecordInitialiser extends AbstractSyntacticItem implements Expr {
			public RecordInitialiser(Pair<Identifier, Expr>... fields) {
				super(Opcode.EXPR_recinit, fields);
			}

			public Pair<Identifier, Expr>[] getFields() {
				return ArrayUtils.toArray(Pair.class, getOperands());
			}

			@Override
			public RecordInitialiser clone(SyntacticItem[] operands) {
				return new RecordInitialiser((Pair[]) operands);
			}
		}

		/**
		 * Represents a <i>record update expression</i> of the form
		 * "<code>rec[f:=e]</code>" where <code>rec</code> is the <i>source
		 * record</i>, <code>f</code> is the <i>field</i> and <code>e</code> is
		 * the <i>value expression</i>. This returns a new record which is
		 * equivalent to <code>rec</code> but where the element in field
		 * <code>f</code> has the value resulting from <code>e</code>.
		 *
		 * @author David J. Pearce
		 *
		 */
		public static class RecordUpdate extends AbstractSyntacticItem implements Expr {
			public RecordUpdate(Expr lhs, Identifier mhs, Expr rhs) {
				super(Opcode.EXPR_recupdt, lhs, mhs, rhs);
			}

			public Expr getSource() {
				return (Expr) getOperand(0);
			}

			public Identifier getField() {
				return (Identifier) getOperand(1);
			}

			public Expr getValue() {
				return (Expr) getOperand(2);
			}

			@Override
			public RecordUpdate clone(SyntacticItem[] operands) {
				return new RecordUpdate((Expr) operands[0], (Identifier) operands[1], (Expr) operands[2]);
			}

			@Override
			public String toString() {
				return getSource() + "{" + getField() + ":=" + getValue() + "}";
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
	// Misc
	// ===========================================================
	public static Tuple<Type> projectTypes(Tuple<VariableDeclaration> decls) {
		Type[] types = new Type[decls.size()];
		for (int i = 0; i != types.length; ++i) {
			types[i] = decls.getOperand(i).getType();
		}
		return new Tuple<>(types);
	}

	// ===========================================================
	// DEBUGGING SUPPORT
	// ===========================================================

	public static void println(Proof.Delta delta) {
		print(delta);
		System.out.println();
	}

	public static void print(Proof.Delta delta) {
		Proof.Delta.Set additions = delta.getAdditions();
		Proof.Delta.Set removals = delta.getRemovals();
		for (int i = 0; i != additions.size(); ++i) {
			if (i != 0) {
				System.out.print(", ");
			}
			System.out.print("+");
			print(additions.get(i));
		}
		for (int i = 0; i != removals.size(); ++i) {
			if (i != 0 || additions.size() > 0) {
				System.out.print(", ");
			}
			System.out.print("-");
			print(removals.get(i));
		}
	}

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
			if (item instanceof WyalFile.Expr) {
				printer.writeExpression((Expr) item);
			} else if (item instanceof WyalFile.Stmt) {
				printer.writeStatement((Stmt) item, 0);
			} else if (item instanceof WyalFile.Type) {
				printer.writeType((Type) item);
			} else if (item instanceof WyalFile.VariableDeclaration) {
				printer.writeVariableDeclaration((WyalFile.VariableDeclaration) item);
			} else if (item instanceof WyalFile.Tuple) {
				WyalFile.Tuple tuple = (WyalFile.Tuple) item;
				out.print("(");
				for (int j = 0; j != tuple.size(); ++j) {
					if (j != 0) {
						out.print(",");
					}
					out.flush();
					print(tuple.getOperand(j));
				}
				out.print(")");
			} else if (item == null) {
				out.print("null");
			} else {
				out.print(item);
			}
		}
		out.flush();
	}
}
