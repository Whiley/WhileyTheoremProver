package wyail.lang;

import java.io.IOException;
import java.io.InputStream;
import java.io.OutputStream;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.List;

import wyail.lang.Bytecode.Block;
import wyail.lang.Bytecode.VariableDeclaration;
import wyail.lang.SyntaxTree.Location;
import wybs.lang.Attribute;
import wybs.lang.CompilationUnit;
import wybs.lang.SyntacticElement;
import wybs.util.AbstractCompilationUnit;
import wyfs.lang.Content;
import wyfs.lang.Path;

public class WyailFile extends AbstractCompilationUnit {

	// =========================================================================
	// Content Type
	// =========================================================================

	public static final Content.Type<WyailFile> ContentType = new Content.Type<WyailFile>() {
		public Path.Entry<WyailFile> accept(Path.Entry<?> e) {
			if (e.contentType() == this) {
				return (Path.Entry<WyailFile>) e;
			}
			return null;
		}

		@Override
		public WyailFile read(Path.Entry<WyailFile> e, InputStream input)
				throws IOException {
			throw new RuntimeException("Implement me!");
		}

		@Override
		public void write(OutputStream output, WyailFile module)
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

	public WyailFile(Path.Entry<? extends CompilationUnit> entry) {
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
		private final WyailFile parent;

		public Context(WyailFile parent, Attribute... attributes) {
			this(parent,Arrays.asList(attributes));
		}

		public Context(WyailFile parent, Collection<Attribute> attributes) {
			super(attributes);
			this.parent = parent;
		}

		public WyailFile getParent() {
			return parent;
		}
	}

	public static class Declaration extends Context{
		private final String name;
		private final SyntaxTree tree;

		public Declaration(WyailFile parent, String name, Attribute... attributes) {
			this(parent,name,Arrays.asList(attributes));
		}

		public Declaration(WyailFile parent, String name, Collection<Attribute> attributes) {
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

		public Function(WyailFile parent, String name, SemanticType.Function type, Attribute... attributes) {
			this(parent,name,type,Arrays.asList(attributes));
		}

		public Function(WyailFile parent, String name, SemanticType.Function type, Collection<Attribute> attributes) {
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

		public Macro(WyailFile parent, String name, SemanticType.Function type, Attribute... attributes) {
			this(parent, name, type, Arrays.asList(attributes));
		}

		public Macro(WyailFile parent, String name, SemanticType.Function type, Collection<Attribute> attributes) {
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
		private Location<Block> body;

		public Assert(WyailFile parent, Attribute... attributes) {
			this(parent,Arrays.asList(attributes));
		}

		public Assert(WyailFile parent, Collection<Attribute> attributes) {
			super(parent,"",attributes);
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

		public Type(WyailFile parent, String name, SemanticType type, Attribute... attributes) {
			this(parent,name,type,Arrays.asList(attributes));
		}

		public Type(WyailFile parent, String name, SemanticType type, Collection<Attribute> attributes) {
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
