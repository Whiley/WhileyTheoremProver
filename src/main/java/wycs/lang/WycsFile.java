package wycs.lang;

import java.io.IOException;
import java.io.InputStream;
import java.io.OutputStream;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.List;

import wybs.lang.Attribute;
import wybs.lang.CompilationUnit;
import wybs.lang.SyntacticElement;
import wybs.util.AbstractCompilationUnit;
import wycs.lang.Bytecode.Block;
import wycs.lang.Bytecode.VariableDeclaration;
import wycs.lang.SyntaxTree.Location;
import wyfs.lang.Content;
import wyfs.lang.Path;

public class WycsFile extends AbstractCompilationUnit {

	// =========================================================================
	// Content Type
	// =========================================================================

	public static final Content.Type<WycsFile> ContentType = new Content.Type<WycsFile>() {
		public Path.Entry<WycsFile> accept(Path.Entry<?> e) {
			if (e.contentType() == this) {
				return (Path.Entry<WycsFile>) e;
			}
			return null;
		}

		@Override
		public WycsFile read(Path.Entry<WycsFile> e, InputStream input)
				throws IOException {
			throw new RuntimeException("Implement me!");
		}

		@Override
		public void write(OutputStream output, WycsFile module)
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
	// State
	// =========================================================================

	private final ArrayList<Declaration> declarations;

	// =========================================================================
	// Constructors
	// =========================================================================

	public WycsFile(Path.Entry<? extends CompilationUnit> entry) {
		super(entry);
		this.declarations = new ArrayList<Declaration>();
	}

	// =========================================================================
	// Accessors
	// =========================================================================

	public List<Declaration> getDeclarations() {
		return declarations;
	}

	public Declaration getDeclaration(String name) {
		for(Declaration d : declarations) {
			if(d.name.equals(name)) {
				return d;
			}
		}
		return null;
	}

	public Declaration getDeclaration(String name, SemanticType type) {
		for (Declaration d : declarations) {
			if (d.name.equals(name)) {
				if (d instanceof Function && ((Function) d).getType().equals(type)) {
					return d;
				} else if (d instanceof Macro && ((Macro) d).getType().equals(type)) {
					return d;
				}
			}
		}
		return null;
	}

	public <T extends Declaration> T getDeclaration(String name, Class<T> type) {
		for (Declaration d : declarations) {
			if (d.name.equals(name) && type.isInstance(d)) {
				return (T) d;
			}
		}
		return null;
	}

	// =========================================================================
	// Types
	// =========================================================================

	public static class Context extends SyntacticElement.Impl {
		private final WycsFile parent;

		public Context(WycsFile parent, Attribute... attributes) {
			this(parent,Arrays.asList(attributes));
		}

		public Context(WycsFile parent, Collection<Attribute> attributes) {
			super(attributes);
			this.parent = parent;
		}

		public WycsFile getParent() {
			return parent;
		}
	}

	public static class Declaration extends Context{
		private final String name;
		private final SyntaxTree tree;

		public Declaration(WycsFile parent, String name, Attribute... attributes) {
			this(parent,name,Arrays.asList(attributes));
		}

		public Declaration(WycsFile parent, String name, Collection<Attribute> attributes) {
			super(parent,attributes);
			this.name = name;
			this.tree = new SyntaxTree(this);
		}

		public String getName() {
			return name;
		}

		public SyntaxTree getTree() {
			return tree;
		}
	}

	public static class Function extends Declaration {
		private final SemanticType.Function type;

		public Function(WycsFile parent, String name, SemanticType.Function type, Attribute... attributes) {
			this(parent,name,type,Arrays.asList(attributes));
		}

		public Function(WycsFile parent, String name, SemanticType.Function type, Collection<Attribute> attributes) {
			super(parent,name,attributes);
			this.type = type;
		}

		public SemanticType.Function getType() {
			return type;
		}
	}

	public static class Macro extends Declaration {
		private final SemanticType.Function type;
		private Location<?> body;

		public Macro(WycsFile parent, String name, SemanticType.Function type, Attribute... attributes) {
			this(parent, name, type, Arrays.asList(attributes));
		}

		public Macro(WycsFile parent, String name, SemanticType.Function type, Collection<Attribute> attributes) {
			super(parent, name, attributes);
			this.type = type;
		}

		public SemanticType.Function getType() {
			return type;
		}

		public Location<?> getBody() {
			return body;
		}

		public void setBody(Location<?> condition) {
			this.body = condition;
		}
	}

	public static class Assert extends Declaration {
		private final List<Location<VariableDeclaration>> parameters;
		private Location<Block> body;

		public Assert(WycsFile parent, String name, Attribute... attributes) {
			this(parent,name,Arrays.asList(attributes));
		}

		public Assert(WycsFile parent, String name, Collection<Attribute> attributes) {
			super(parent,name,attributes);
			this.parameters = new ArrayList<Location<VariableDeclaration>>();
		}

		public List<Location<VariableDeclaration>> getParameters() {
			return parameters;
		}

		public Location<Block> getBody() {
			return body;
		}

		public void setBody(Location<Block> body) {
			this.body = body;
		}
	}

	public static class Type extends Declaration {
		private final SemanticType type;
		private final List<Location<?>> invariant;

		public Type(WycsFile parent, String name, SemanticType type, Attribute... attributes) {
			this(parent,name,type,Arrays.asList(attributes));
		}

		public Type(WycsFile parent, String name, SemanticType type, Collection<Attribute> attributes) {
			super(parent, name, attributes);
			this.type = type;
			this.invariant = new ArrayList<Location<?>>();
		}

		public SemanticType getType() {
			return type;
		}

		public List<Location<?>> getInvariant() {
			return invariant;
		}
	}
}
