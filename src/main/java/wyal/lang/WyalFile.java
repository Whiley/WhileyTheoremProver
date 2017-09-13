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
import java.util.Arrays;
import java.util.Iterator;
import java.util.List;

import wyal.io.WyalFileLexer;
import wyal.io.WyalFileParser;
import wyal.io.WyalFilePrinter;
import wyal.lang.WyalFile;
import wybs.lang.Attribute;
import wybs.lang.CompilationUnit;
import wybs.lang.NameID;
import wybs.lang.SyntacticHeap;
import wybs.lang.SyntacticItem;
import wybs.util.AbstractCompilationUnit;
import wybs.util.AbstractSyntacticHeap;
import wybs.util.AbstractSyntacticItem;
import static wybs.util.AbstractCompilationUnit.*;
import wycc.util.ArrayUtils;
import wyfs.lang.Content;
import wyfs.lang.Path;
import wyfs.lang.Path.Entry;
import wyfs.util.Trie;
import wytp.proof.Proof;

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
			WyalFileParser wfr = new WyalFileParser(new WyalFile(e), wlexer.scan());
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

	public static final Content.Type<WyalFile> BinaryContentType = new Content.Type<WyalFile>() {
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
	// DECLARATIONS: 00010000 (16) -- 00011111 (31)
	public static final int DECL_mask = 0b00010000;
	public static final int DECL_linecomment = DECL_mask + 0;
	public static final int DECL_blkcomment = DECL_mask + 1;
	public static final int DECL_import = DECL_mask + 2;
	public static final int DECL_assert = DECL_mask + 3;
	public static final int DECL_type = DECL_mask + 4;
	public static final int DECL_fun = DECL_mask + 5;
	public static final int DECL_macro = DECL_mask + 6;
	// ERRORS
	public static final int ERR_verify = DECL_mask + 7;
	// TYPES: 00100000 (32) -- 00111111 (63)
	public static final int TYPE_mask = 0b000100000;
	public static final int TYPE_void = TYPE_mask + 0;
	public static final int TYPE_any = TYPE_mask + 1;
	public static final int TYPE_null = TYPE_mask + 2;
	public static final int TYPE_bool = TYPE_mask + 3;
	public static final int TYPE_int = TYPE_mask + 4;
	public static final int TYPE_nom = TYPE_mask + 5;
	public static final int TYPE_ref = TYPE_mask + 6;
	public static final int TYPE_arr = TYPE_mask + 8;
	public static final int TYPE_rec = TYPE_mask + 9;
	public static final int TYPE_fun = TYPE_mask + 10;
	public static final int TYPE_meth = TYPE_mask + 11;
	public static final int TYPE_property = TYPE_mask + 12;
	public static final int TYPE_inv = TYPE_mask + 13;
	public static final int TYPE_or = TYPE_mask + 14;
	public static final int TYPE_and = TYPE_mask + 15;
	public static final int TYPE_not = TYPE_mask + 16;
	public static final int TYPE_byte = TYPE_mask + 17;
	// STATEMENTS: 01000000 (64) -- 001011111 (95)
	public static final int STMT_mask = 0b01000000;
	public static final int STMT_block = STMT_mask + 0;
	public static final int STMT_vardecl = STMT_mask + 1;
	public static final int STMT_ifthen = STMT_mask + 2;
	public static final int STMT_caseof = STMT_mask + 3;
	public static final int STMT_exists = STMT_mask + 4;
	public static final int STMT_forall = STMT_mask + 5;
	// EXPRESSIONS: 01100000 (96) -- 10011111 (159)
	public static final int EXPR_mask = 0b01100000;
	public static final int EXPR_varcopy = EXPR_mask + 0;
	public static final int EXPR_varmove = EXPR_mask + 1;
	public static final int EXPR_staticvar = EXPR_mask + 2;
	public static final int EXPR_const = EXPR_mask + 3;
	public static final int EXPR_cast = EXPR_mask + 4;
	public static final int EXPR_invoke = EXPR_mask + 5;
	public static final int EXPR_qualifiedinvoke = EXPR_mask + 6;
	public static final int EXPR_indirectinvoke = EXPR_mask + 7;
	// LOGICAL
	public static final int EXPR_not = EXPR_mask + 8;
	public static final int EXPR_and = EXPR_mask + 9;
	public static final int EXPR_or = EXPR_mask + 10;
	public static final int EXPR_implies = EXPR_mask + 11;
	public static final int EXPR_iff = EXPR_mask + 12;
	public static final int EXPR_exists = EXPR_mask + 13;
	public static final int EXPR_forall = EXPR_mask + 14;
	// COMPARATORS
	public static final int EXPR_eq = EXPR_mask + 16;
	public static final int EXPR_neq = EXPR_mask + 17;
	public static final int EXPR_lt = EXPR_mask + 18;
	public static final int EXPR_lteq = EXPR_mask + 19;
	public static final int EXPR_gt = EXPR_mask + 20;
	public static final int EXPR_gteq = EXPR_mask + 21;
	public static final int EXPR_is = EXPR_mask + 22;
	// ARITHMETIC
	public static final int EXPR_neg = EXPR_mask + 24;
	public static final int EXPR_add = EXPR_mask + 25;
	public static final int EXPR_sub = EXPR_mask + 26;
	public static final int EXPR_mul = EXPR_mask + 27;
	public static final int EXPR_div = EXPR_mask + 28;
	public static final int EXPR_rem = EXPR_mask + 29;
	// BITWISE
	public static final int EXPR_bitwisenot = EXPR_mask + 32;
	public static final int EXPR_bitwiseand = EXPR_mask + 33;
	public static final int EXPR_bitwiseor = EXPR_mask + 34;
	public static final int EXPR_bitwisexor = EXPR_mask + 35;
	public static final int EXPR_bitwiseshl = EXPR_mask + 36;
	public static final int EXPR_bitwiseshr = EXPR_mask + 37;
	// REFERENCES
	public static final int EXPR_deref = EXPR_mask + 40;
	public static final int EXPR_new = EXPR_mask + 41;
	public static final int EXPR_qualifiedlambda = EXPR_mask + 42;
	public static final int EXPR_lambda = EXPR_mask + 43;
	// RECORDS
	public static final int EXPR_recfield = EXPR_mask + 48;
	public static final int EXPR_recupdt = EXPR_mask + 49;
	public static final int EXPR_recinit = EXPR_mask + 50;
	// ARRAYS
	public static final int EXPR_arridx = EXPR_mask + 56;
	public static final int EXPR_arrlen = EXPR_mask + 57;
	public static final int EXPR_arrupdt = EXPR_mask + 58;
	public static final int EXPR_arrgen = EXPR_mask + 59;
	public static final int EXPR_arrinit = EXPR_mask + 60;
	public static final int EXPR_arrrange = EXPR_mask + 61;

	// =========================================================================
	// Constructors
	// =========================================================================

	public WyalFile(Path.Entry<WyalFile> entry) {
		super(entry);
	}

	@Override
	public Entry<WyalFile> getEntry() {
		return entry;
	}

	@Override
	public SyntacticHeap getParent() {
		return null;
	}

	// ============================================================
	// Fundamental Items
	// ============================================================


	// ============================================================
	// Declarations
	// ============================================================
	public static interface Declaration extends CompilationUnit.Declaration {

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
				super(DECL_import, components);
			}

			public Identifier[] getComponents() {
				return (Identifier[]) getAll();
			}

			@Override
			public Identifier get(int i) {
				return (Identifier) super.get(i);
			}

			@Override
			public Import clone(SyntacticItem[] operands) {
				return new Import(ArrayUtils.toArray(Identifier.class, operands));
			}

			@Override
			public String toString() {
				String r = "import ";
				for (int i = 0; i != size(); ++i) {
					if (i != 0) {
						r += ".";
					}
					Identifier component = get(i);
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
				super(DECL_assert, body);
				this.message = message;
			}

			public Stmt.Block getBody() {
				return (Stmt.Block) get(0);
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

			public Tuple<VariableDeclaration> getParameters();

			public static abstract class FunctionOrMacro extends AbstractSyntacticItem implements Named {
				public FunctionOrMacro(Identifier name, Tuple<VariableDeclaration> parameters, Stmt.Block body) {
					super(DECL_macro, name, parameters, body);
				}

				public FunctionOrMacro(Identifier name, Tuple<VariableDeclaration> parameters,
						Tuple<VariableDeclaration> returns) {
					super(DECL_fun, name, parameters, returns);
				}

				@Override
				public Identifier getName() {
					return (Identifier) get(0);
				}

				@Override
				public Tuple<VariableDeclaration> getParameters() {
					return (Tuple) get(1);
				}

				public abstract WyalFile.Type.FunctionOrMethodOrProperty getSignatureType();
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
					return (Tuple<VariableDeclaration>) get(2);
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
					return (Stmt.Block) get(2);
				}

				@Override
				public WyalFile.Type.Property getSignatureType() {
					return new WyalFile.Type.Property(projectTypes(getParameters()));
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
					super(DECL_type, name, vardecl, new Tuple(invariant));
				}

				private Type(Identifier name, VariableDeclaration vardecl, Tuple<Stmt.Block> invariant) {
					super(DECL_type, name, vardecl, invariant);
				}

				@Override
				public Identifier getName() {
					return (Identifier) get(0);
				}

				public VariableDeclaration getVariableDeclaration() {
					return (VariableDeclaration) get(1);
				}

				public Tuple<Stmt.Block> getInvariant() {
					return (Tuple) get(2);
				}

				@Override
				public Type clone(SyntacticItem[] operands) {
					return new Type((Identifier) operands[0], (VariableDeclaration) operands[1], (Tuple) operands[2]);
				}

				@Override
				public Tuple<VariableDeclaration> getParameters() {
					return new Tuple<>(getVariableDeclaration());
				}
			}
		}
	}

	// ============================================================
	// Types
	// ============================================================
	public static interface Type extends SyntacticItem {

		public static final Any Any = new Any();
		public static final Void Void = new Void();
		public static final Bool Bool = new Bool();
		public static final Int Int = new Int();
		public static final Null Null = new Null();

		public interface Primitive extends Type {

		}

		public static abstract class Atom extends AbstractSyntacticItem implements Type {
			public Atom(int opcode) {
				super(opcode);
			}

			public Atom(int opcode, SyntacticItem item) {
				super(opcode, item);
			}

			public Atom(int opcode, SyntacticItem first, SyntacticItem second) {
				super(opcode, first, second);
			}

			public Atom(int opcode, SyntacticItem[] items) {
				super(opcode, items);
			}
		}

		/**
		 * The type <code>any</code> represents the type whose variables may hold
		 * any possible value. <b>NOTE:</b> the any type is top in the type lattice.
		 *
		 * @author David J. Pearce
		 *
		 */
		public static class Any extends Atom implements Primitive {
			public Any() {
				super(TYPE_any);
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

		/**
		 * A void type represents the type whose variables cannot exist! That is,
		 * they cannot hold any possible value. Void is used to represent the return
		 * type of a function which does not return anything. However, it is also
		 * used to represent the element type of an empty list of set. <b>NOTE:</b>
		 * the void type is a subtype of everything; that is, it is bottom in the
		 * type lattice.
		 *
		 * @author David J. Pearce
		 *
		 */
		public static class Void extends Atom implements Primitive {
			public Void() {
				super(TYPE_void);
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

		/**
		 * The null type is a special type which should be used to show the absence
		 * of something. It is distinct from void, since variables can hold the
		 * special <code>null</code> value (where as there is no special "void"
		 * value). With all of the problems surrounding <code>null</code> and
		 * <code>NullPointerException</code>s in languages like Java and C, it may
		 * seem that this type should be avoided. However, it remains a very useful
		 * abstraction to have around and, in Whiley, it is treated in a completely
		 * safe manner (unlike e.g. Java).
		 *
		 * @author David J. Pearce
		 *
		 */
		public static class Null extends Atom implements Primitive {
			public Null() {
				super(TYPE_null);
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

		/**
		 * Represents the set of boolean values (i.e. true and false)
		 * @author David J. Pearce
		 *
		 */
		public static class Bool extends Atom implements Primitive {
			public Bool() {
				super(TYPE_bool);
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

		/**
		 * Represents a sequence of 8 bits. Note that, unlike many languages, there
		 * is no representation associated with a byte. For example, to extract an
		 * integer value from a byte, it must be explicitly decoded according to
		 * some representation (e.g. two's compliment) using an auxillary function
		 * (e.g. <code>Byte.toInt()</code>).
		 *
		 * @author David J. Pearce
		 *
		 */
		public static class Byte extends Atom implements Primitive {
			public Byte() {
				super(TYPE_byte);
			}

			@Override
			public Null clone(SyntacticItem[] operands) {
				return new Null();
			}

			@Override
			public String toString() {
				return "byte";
			}
		}

		/**
		 * Represents the set of (unbound) integer values. Since integer types in
		 * Whiley are unbounded, there is no equivalent to Java's
		 * <code>MIN_VALUE</code> and <code>MAX_VALUE</code> for <code>int</code>
		 * types.
		 *
		 * @author David J. Pearce
		 *
		 */
		public static class Int extends Atom implements Primitive {
			public Int() {
				super(TYPE_int);
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

		/**
		 * Represents a list type, which is of the form:
		 *
		 * <pre>
		 * ArrayType ::= Type '[' ']'
		 * </pre>
		 *
		 * @return
		 */
		public static class Array extends Atom {
			public Array(Type element) {
				super(TYPE_arr, element);
			}

			public Type getElement() {
				return (Type) get(0);
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

		/**
		 * Parse a reference type, which is of the form:
		 *
		 * <pre>
		 * ReferenceType ::= '&' Type
		 * </pre>
		 *
		 * @return
		 */
		public static class Reference extends Atom {
			public Reference(Type element, Identifier lifetime) {
				super(TYPE_ref, element, lifetime);
			}

			public Type getElement() {
				return (Type) get(0);
			}
			public Identifier getLifetime() {
				return (Identifier) get(1);
			}

			@Override
			public Reference clone(SyntacticItem[] operands) {
				return new Reference((Type) operands[0], (Identifier) operands[1]);
			}

			@Override
			public String toString() {
				Identifier lifetime = getLifetime();
				if (lifetime != null) {
					return "&(" + getElement() + ")";
				} else {
					return "&" + lifetime + ":(" + getElement() + ")";
				}
			}
		}

		/**
		 * Represents record type, which is of the form:
		 *
		 * <pre>
		 * RecordType ::= '{' Type Identifier (',' Type Identifier)* [ ',' "..." ] '}'
		 * </pre>
		 *
		 * @return
		 */
		public static class Record extends Atom {
			public Record(boolean isOpen, FieldDeclaration[] fields) {
				super(TYPE_rec, ArrayUtils.append(SyntacticItem.class, new Value.Bool(isOpen), fields));
			}

			private Record(SyntacticItem[] operands) {
				super(TYPE_rec, operands);
			}

			public boolean isOpen() {
				Value.Bool flag = (Value.Bool) get(0);
				return flag.get();
			}

			public FieldDeclaration[] getFields() {
				// FIXME: this should be packed as a Tuple and return a Tuple
				SyntacticItem[] operands = getAll();
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

		/**
		 * Represents a nominal type, which is of the form:
		 *
		 * <pre>
		 * NominalType ::= Identifier ('.' Identifier)*
		 * </pre>
		 *
		 * A nominal type specifies the name of a type defined elsewhere. In some
		 * cases, this type can be expanded (or "inlined"). However, visibility
		 * modifiers can prevent this and, thus, give rise to true nominal types.
		 *
		 * @return
		 */
		public static class Nominal extends AbstractSyntacticItem implements Type {
			public Nominal(Name name) {
				super(TYPE_nom, name);
			}

			public Name getName() {
				return (Name) get(0);
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

		/**
		 * Parse a negation type, which is of the form:
		 *
		 * <pre>
		 * ReferenceType ::= '!' Type
		 * </pre>
		 *
		 * @return
		 */
		public static class Negation extends AbstractSyntacticItem implements Type {
			public Negation(Type element) {
				super(TYPE_not, element);
			}

			public Type getElement() {
				return (Type) get(0);
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
			public UnionOrIntersection(int kind, Type[] types) {
				super(kind, types);
			}

			@Override
			public Type get(int i) {
				return (Type) super.get(i);
			}

			@Override
			public Type[] getAll() {
				return (Type[]) super.getAll();
			}
		}

		/**
		 * Represents a union type, which is of the form:
		 *
		 * <pre>
		 * UnionType ::= IntersectionType ('|' IntersectionType)*
		 * </pre>
		 *
		 * Union types are used to compose types together. For example, the type
		 * <code>int|null</code> represents the type which is either an
		 * <code>int</code> or <code>null</code>.
		 *
		 * @return
		 */
		public static class Union extends UnionOrIntersection {
			public Union(Type[] types) {
				super(TYPE_or, types);
			}

			@Override
			public Union clone(SyntacticItem[] operands) {
				return new Union(ArrayUtils.toArray(Type.class,operands));
			}

			@Override
			public String toString() {
				String r = "";
				for (int i = 0; i != size(); ++i) {
					if (i != 0) {
						r += "|";
					}
					r += get(i);
				}
				return "(" + r + ")";
			}
		}

		/**
		 * Represents an intersection type, which is of the form:
		 *
		 * <pre>
		 * IntersectionType ::= BaseType ('&' BaseType)*
		 * </pre>
		 *
		 * Intersection types are used to unify types together. For example, the
		 * type <code>{int x, int y}&MyType</code> represents the type which is both
		 * an instanceof of <code>{int x, int y}</code> and an instance of
		 * <code>MyType</code>.
		 *
		 * @return
		 */
		public static class Intersection extends UnionOrIntersection {
			public Intersection(Type[] types) {
				super(TYPE_and, types);
			}

			@Override
			public Intersection clone(SyntacticItem[] operands) {
				return new Intersection(ArrayUtils.toArray(Type.class, operands));
			}

			@Override
			public String toString() {
				String r = "";
				for (int i = 0; i != size(); ++i) {
					if (i != 0) {
						r += "&";
					}
					r += get(i);
				}
				return "(" + r + ")";
			}
		}

		public static abstract class FunctionOrMacroOrInvariant extends Atom implements Type {
			public FunctionOrMacroOrInvariant(int opcode, Tuple<Type> parameters, Tuple<Type> returns) {
				super(opcode, parameters, returns);
			}
			public FunctionOrMacroOrInvariant(int opcode, SyntacticItem[] items) {
				super(opcode, items);
			}
			public Tuple<Type> getParameters() {
				return (Tuple<Type>) get(0);
			}

			public Tuple<Type> getReturns() {
				return (Tuple<Type>) get(1);
			}

			@Override
			public String toString() {
				return getParameters() + "->" + getReturns();
			}
		}

		public static abstract class FunctionOrMethodOrProperty extends FunctionOrMacroOrInvariant {
			public FunctionOrMethodOrProperty(int opcode, Tuple<Type> parameters, Tuple<Type> returns) {
				super(opcode, parameters, returns);
			}
			public FunctionOrMethodOrProperty(int opcode, SyntacticItem[] operands) {
				super(opcode, operands);
			}
		}

		public static class Function extends FunctionOrMethodOrProperty implements Type {
			public Function(Type[] parameters, Type[] returns) {
				super(TYPE_fun, new Tuple(parameters), new Tuple(returns));
			}
			public Function(Tuple<Type> parameters, Tuple<Type> returns) {
				super(TYPE_fun, parameters, returns);
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

		public static class Method extends FunctionOrMethodOrProperty implements Type {

			public Method(Tuple<Type> parameters, Tuple<Type> returns, Tuple<Identifier> contextLifetimes,
					Tuple<Identifier> lifetimeParameters) {
				super(TYPE_meth,
						new SyntacticItem[] { parameters, returns, contextLifetimes, lifetimeParameters });
			}

			@Override
			public Method clone(SyntacticItem[] operands) {
				return new Method((Tuple<Type>) operands[0], (Tuple<Type>) operands[1],
						(Tuple<Identifier>) operands[2], (Tuple<Identifier>) operands[3]);
			}

			public Tuple<Identifier> getContextLifetimes() {
				return (Tuple<Identifier>) get(2);
			}

			public Tuple<Identifier> getLifetimeParameters() {
				return (Tuple<Identifier>) get(3);
			}

			@Override
			public String toString() {
				return "method" + super.toString();
			}
		}

		public static class Property extends FunctionOrMethodOrProperty implements Type {
			public Property(Tuple<Type> parameters) {
				super(TYPE_property, parameters, new Tuple<>(new Type.Bool()));
			}

			private Property(Tuple<Type> parameters, Tuple<Type> returns) {
				super(TYPE_property, parameters, returns);
			}

			@Override
			public Property clone(SyntacticItem[] operands) {
				return new Property((Tuple<Type>) operands[0], (Tuple<Type>) operands[1]);
			}

			@Override
			public String toString() {
				return "macro" + super.toString();
			}
		}

		public static class Invariant extends FunctionOrMacroOrInvariant implements Type {
			public Invariant(Tuple<Type> parameters) {
				super(TYPE_inv, parameters, new Tuple<Type>(new Bool()));
			}

			private Invariant(Tuple<Type> parameters, Tuple<Type> returns) {
				super(TYPE_inv, parameters, returns);
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
			super(STMT_vardecl, type, name);
		}

		public Type getType() {
			return (Type) get(0);
		}

		public Identifier getVariableName() {
			return (Identifier) get(1);
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
			super(STMT_vardecl, type, name);
		}

		public Type getType() {
			return (Type) get(0);
		}

		public Identifier getVariableName() {
			return (Identifier) get(1);
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
				super(STMT_block, stmts);
			}

			@Override
			public Stmt get(int i) {
				return (Stmt) super.get(i);
			}

			@Override
			public Stmt[] getAll() {
				return (Stmt[]) super.getAll();
			}

			@Override
			public Block clone(SyntacticItem[] operands) {
				return new Block(ArrayUtils.toArray(Stmt.class, operands));
			}
		}

		public static abstract class Quantifier extends AbstractSyntacticItem implements Stmt {
			public Quantifier(int opcode, VariableDeclaration[] parameters, Block body) {
				super(opcode, new Tuple<>(parameters), body);
			}

			public Quantifier(int opcode, Tuple<VariableDeclaration> parameters, Block body) {
				super(opcode, parameters, body);
			}

			public Tuple<VariableDeclaration> getParameters() {
				return (Tuple<VariableDeclaration>) get(0);
			}

			public Block getBody() {
				return (Block) get(1);
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
				super(STMT_forall, new Tuple<>(parameters), body);
			}

			public UniversalQuantifier(Tuple<VariableDeclaration> parameters, Block body) {
				super(STMT_forall, parameters, body);
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
				super(STMT_exists, new Tuple<>(parameters), body);
			}

			public ExistentialQuantifier(Tuple<VariableDeclaration> parameters, Block body) {
				super(STMT_exists, parameters, body);
			}

			@Override
			public Quantifier clone(SyntacticItem[] operands) {
				return new ExistentialQuantifier((Tuple<VariableDeclaration>) operands[0], (Block) operands[1]);
			}
		}

		public static class IfThen extends AbstractSyntacticItem implements Stmt {
			public IfThen(Block ifBlock, Block thenBlock) {
				super(STMT_ifthen, ifBlock, thenBlock);
			}

			public Block getIfBody() {
				return (Block) get(0);
			}

			public Block getThenBody() {
				return (Block) get(1);
			}

			@Override
			public IfThen clone(SyntacticItem[] operands) {
				return new IfThen((Block) operands[0], (Block) operands[1]);
			}
		}

		public static class CaseOf extends AbstractSyntacticItem implements Stmt {
			public CaseOf(Block... cases) {
				super(STMT_caseof, cases);
			}

			@Override
			public Block get(int i) {
				return (Block) super.get(i);
			}

			@Override
			public Block[] getAll() {
				return (Block[]) super.getAll();
			}

			@Override
			public CaseOf clone(SyntacticItem[] operands) {
				return new CaseOf(ArrayUtils.toArray(Block.class, operands));
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
				super(EXPR_cast, type, rhs);
			}

			public Type getCastType() {
				return (Type) super.get(0);
			}

			public Expr getCastedExpr() {
				return (Expr) super.get(1);
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
				super(EXPR_const, value);
			}

			public Value getValue() {
				return (Value) get(0);
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
				super(EXPR_is, lhs, rhs);
			}

			public Expr getTestExpr() {
				return (Expr) get(0);
			}

			public Type getTestType() {
				return (Type) get(1);
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

			public Invoke(Type.FunctionOrMacroOrInvariant type, Name name, Integer selector, Expr[] arguments) {
				super(EXPR_invoke, new SyntacticItem[] { type, name,
						selector != null ? new Value.Int(selector) : null, new Tuple<>(arguments) });
			}

			public Invoke(Type.FunctionOrMacroOrInvariant type, Name name, Value.Int selector, Tuple<Expr> arguments) {
				super(EXPR_invoke, new SyntacticItem[] { type, name, selector, arguments });
			}

			public Type.FunctionOrMacroOrInvariant getSignatureType() {
				return (Type.FunctionOrMacroOrInvariant) get(0);
			}

			public void setSignatureType(Type.FunctionOrMacroOrInvariant type) {
				this.setOperand(0, type);
			}

			public Name getName() {
				return (Name) get(1);
			}

			public Value.Int getSelector() {
				return (Value.Int) get(2);
			}

			public Tuple<Expr> getArguments() {
				return (Tuple) get(3);
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
			public Operator(int opcode, Expr... operands) {
				super(opcode, operands);
			}

			@Override
			public Expr get(int i) {
				return (Expr) super.get(i);
			}

			@Override
			public Expr[] getAll() {
				return (Expr[]) super.getAll();
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
			public Quantifier(int opcode, VariableDeclaration[] parameters, Expr body) {
				super(opcode, new Tuple<>(parameters), body);
			}

			public Quantifier(int opcode, Tuple<VariableDeclaration> parameters, Expr body) {
				super(opcode, parameters, body);
			}

			public Tuple<VariableDeclaration> getParameters() {
				return (Tuple<VariableDeclaration>) get(0);
			}

			public Expr getBody() {
				return (Expr) get(1);
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
				super(EXPR_forall, new Tuple<>(parameters), body);
			}

			public UniversalQuantifier(Tuple<VariableDeclaration> parameters, Expr body) {
				super(EXPR_forall, parameters, body);
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
				super(EXPR_exists, new Tuple<>(parameters), body);
			}

			public ExistentialQuantifier(Tuple<VariableDeclaration> parameters, Expr body) {
				super(EXPR_exists, parameters, body);
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
				super(EXPR_varcopy, decl);
			}

			public VariableDeclaration getVariableDeclaration() {
				return (VariableDeclaration) get(0);
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
			public InfixOperator(int opcode, Expr... operands) {
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
					r += get(i);
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
				super(EXPR_and, operands);
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
				super(EXPR_or, operands);
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
				super(EXPR_implies, operands);
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
				super(EXPR_iff, operands);
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
				super(EXPR_not, operand);
			}

			public Expr getOperand() {
				return get(0);
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
				super(EXPR_eq, operands);
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
				super(EXPR_neq, operands);
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
				super(EXPR_lt, operands);
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
				super(EXPR_lteq, operands);
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
				super(EXPR_gt, operands);
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
				super(EXPR_gteq, operands);
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
				super(EXPR_add, operands);
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
				super(EXPR_sub, operands);
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
				super(EXPR_mul, operands);
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
				super(EXPR_div, operands);
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
				super(EXPR_rem, operands);
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
				super(EXPR_neg, operand);
			}

			public Expr getOperand() {
				return get(0);
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
				super(EXPR_deref, operand);
			}

			public Expr getOperand() {
				return get(0);
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
				super(EXPR_arridx, src, index);
			}

			public Expr getSource() {
				return (Expr) get(0);
			}

			public Expr getSubscript() {
				return (Expr) get(1);
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
				super(EXPR_arrupdt, src, index, value);
			}

			public Expr getSource() {
				return (Expr) get(0);
			}

			public Expr getSubscript() {
				return (Expr) get(1);
			}

			public Expr getValue() {
				return (Expr) get(2);
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
				super(EXPR_arrinit, elements);
			}

			@Override
			public ArrayInitialiser clone(SyntacticItem[] operands) {
				return new ArrayInitialiser(ArrayUtils.toArray(Expr.class, operands));
			}

			@Override
			public String toString() {
				return Arrays.toString(getAll());
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
				super(EXPR_arrgen, value, length);
			}

			public Expr getValue() {
				return (Expr) get(0);
			}

			public Expr getLength() {
				return (Expr) get(1);
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
				super(EXPR_arrlen, src);
			}

			public Expr getSource() {
				return (Expr) get(0);
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
				super(EXPR_recfield, lhs, rhs);
			}

			public Expr getSource() {
				return (Expr) get(0);
			}

			public Identifier getField() {
				return (Identifier) get(1);
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
				super(EXPR_recinit, fields);
			}

			public Pair<Identifier, Expr>[] getFields() {
				return ArrayUtils.toArray(Pair.class, getAll());
			}

			@Override
			public RecordInitialiser clone(SyntacticItem[] operands) {
				return new RecordInitialiser(ArrayUtils.toArray(Pair.class, operands));
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
				super(EXPR_recupdt, lhs, mhs, rhs);
			}

			public Expr getSource() {
				return (Expr) get(0);
			}

			public Identifier getField() {
				return (Identifier) get(1);
			}

			public Expr getValue() {
				return (Expr) get(2);
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

	// ============================================================
	// Attributes
	// ============================================================
	public interface Attribute {
		public class Proof implements wybs.lang.Attribute {
			private final wytp.proof.Proof proof;

			public Proof(wytp.proof.Proof proof) {
				this.proof = proof;
			}

			public wytp.proof.Proof getProof() {
				return proof;
			}
		}
	}
	// ===========================================================
	// Errors
	// ===========================================================
	public static class VerificationError extends AbstractSyntacticItem {

		public VerificationError(Declaration.Assert parent) {
			super(ERR_verify, parent);
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
			types[i] = decls.get(i).getType();
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
					print(tuple.get(j));
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
