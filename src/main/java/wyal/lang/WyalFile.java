package wyal.lang;

import java.io.IOException;
import java.io.InputStream;
import java.io.OutputStream;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.List;

import wyal.io.WyalFileLexer;
import wyal.io.WyalFileParser;
import wyal.lang.WyalFile;
import wybs.lang.Attribute;
import wybs.lang.CompilationUnit;
import wybs.lang.SyntacticElement;
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
	// State
	// =========================================================================
	private final ArrayList<ConstantPoolItem> contantPool;

	// =========================================================================
	// Constructors
	// =========================================================================

	public WyalFile(Path.Entry<WyalFile> entry) {
		super(entry);
		this.contantPool = new ArrayList<ConstantPoolItem>();
	}

	// ============================================================
	// Accessors
	// ============================================================

	public List<ConstantPoolItem> getConstantPool() {
		return contantPool;
	}

	public <T extends ConstantPoolItem> List<T> getSyntacticItems(Class<T> kind) {
		ArrayList<T> matches = new ArrayList<T>();
		for(int i=0;i!=contantPool.size();++i) {
			ConstantPoolItem item = contantPool.get(i);
			if(kind.isInstance(item)) {
				matches.add((T) item);
			}
		}
		return matches;
	}

	// ============================================================
	// Item
	// ============================================================
	public static interface ConstantPoolItem {

	}

	// ============================================================
	// Comments
	// ============================================================
	public static class Comment extends SyntacticElement.Impl implements ConstantPoolItem {
		// This is just here to illustrate another kind of node which could
		// exist.
	}

	// ============================================================
	// Context
	// ============================================================

	public static class Context extends SyntacticElement.Impl {
		private final WyalFile parent;

		public Context(WyalFile parent, Attribute... attributes) {
			this(parent,Arrays.asList(attributes));
		}

		public Context(WyalFile parent, Collection<Attribute> attributes) {
			super(attributes);
			this.parent = parent;
		}

		public WyalFile getParent() {
			return parent;
		}
	}
	// ============================================================
	// Location
	// ============================================================
	/**
	 * A source-level location represents a syntactic entity which represents
	 * some kind of operational unit, such as an expression or statement.
	 *
	 * @author David J. Pearce
	 *
	 */
	public static class Location extends Context implements ConstantPoolItem {
		private final int typeIndex;
		private final Bytecode bytecode;

		public Location(WyalFile parent, int typeIndex, Bytecode bytecode, Attribute...attributes) {
			super(parent,attributes);
			this.typeIndex = typeIndex;
			this.bytecode = bytecode;
		}

		public Location(WyalFile parent, int typeIndex, Bytecode bytecode, List<Attribute> attributes) {
			super(parent,attributes);
			this.typeIndex = typeIndex;
			this.bytecode = bytecode;
		}

		/**
		 * Get the bytecode associated with this location
		 *
		 * @return
		 */
		public Bytecode getCode() {
			return bytecode;
		}

		/**
		 * Get the underlying opcode for this location
		 *
		 * @return
		 */
		public Bytecode.Opcode getOpcode() {
			return bytecode.getOpcode();
		}

		/**
		 * Get the number of operand groups in this location.
		 *
		 * @return
		 */
		public int numberOfOperands() {
			return bytecode.numberOfOperands();
		}

		/**
		 * Return the ith operand associated with this location.
		 *
		 * @param i
		 * @return
		 */
		public Location getOperand(int i) {
			return getParent().getLocation(bytecode.getOperand(i));
		}
	}

	// ============================================================
	// Declaration
	// ============================================================
	public static class Declaration extends Context implements ConstantPoolItem {
		public Declaration(WyalFile parent, Attribute... attributes) {
			this(parent, Arrays.asList(attributes));
		}

		public Declaration(WyalFile parent, Collection<Attribute> attributes) {
			super(parent, attributes);
		}
	}

	// ============================================================
	// Declaration
	// ============================================================
	public static class NamedDeclaration extends Declaration implements ConstantPoolItem {
		private final int nameIndex;

		public NamedDeclaration(WyalFile parent, int nameIndex, Attribute... attributes) {
			this(parent, nameIndex, Arrays.asList(attributes));
		}

		public NamedDeclaration(WyalFile parent, int nameIndex, Collection<Attribute> attributes) {
			super(parent, attributes);
			this.nameIndex = nameIndex;
		}

		public String getName() {
			return getParent().getIdentifier(nameIndex);
		}
	}

	// ============================================================
	// Function Declaration
	// ============================================================
	public static class Function extends NamedDeclaration {
		private final int[] parameterIndices;
		private final int[] returnIndices;

		public Function(WyalFile parent, int nameIndex, int[] parameterIndices, int[] returnIndices,
				Attribute... attributes) {
			this(parent, nameIndex, parameterIndices, returnIndices, Arrays.asList(attributes));
		}

		public Function(WyalFile parent, int nameIndex, int[] parameterIndices, int[] returnIndices,
				Collection<Attribute> attributes) {
			super(parent, nameIndex, attributes);
			this.parameterIndices = parameterIndices;
			this.returnIndices = returnIndices;
		}

		public SemanticType.Function getType() {
			return null;
		}
	}

	// ============================================================
	// Macro Declaration
	// ============================================================
	public static class Macro extends NamedDeclaration {
		private final int[] parameterIndices;
		private final int bodyIndex;

		public Macro(WyalFile parent, int nameIndex, int[] parameterIndices, int bodyIndex, Attribute... attributes) {
			this(parent, nameIndex, parameterIndices, bodyIndex, Arrays.asList(attributes));
		}

		public Macro(WyalFile parent, int nameIndex, int[] parameterIndices, int bodyIndex, Collection<Attribute> attributes) {
			super(parent, nameIndex, attributes);
			this.bodyIndex = bodyIndex;
			this.parameterIndices = parameterIndices;
		}

		public Location getBody() {
			return getParent().getLocation(bodyIndex);
		}

		public SemanticType.Function getType() {
			return null;
		}
	}

	// ============================================================
	// Type Declaration
	// ============================================================
	public static class Type extends NamedDeclaration {
		private final int[] invariantIndices;

		public Type(WyalFile parent, int nameIndex, int[] invariantIndices, Attribute... attributes) {
			this(parent,nameIndex,invariantIndices,Arrays.asList(attributes));
		}

		public Type(WyalFile parent, int nameIndex, int[] invariantIndices, Collection<Attribute> attributes) {
			super(parent, nameIndex, attributes);
			this.invariantIndices = invariantIndices;
		}

		public Location[] getInvariant() {
			return getParent().getLocations(invariantIndices);
		}

		public SemanticType.Function getType() {
			return null;
		}
	}

	// ============================================================
	// Assertion
	// ============================================================
	public static class Assert extends Declaration {
		private final int bodyIndex;

		public Assert(WyalFile parent, int bodyIndex, Attribute... attributes) {
			this(parent,bodyIndex,Arrays.asList(attributes));
		}

		public Assert(WyalFile parent, int bodyIndex, Collection<Attribute> attributes) {
			super(parent,attributes);
			this.bodyIndex = bodyIndex;
		}

		public Location getBody() {
			return getParent().getLocation(bodyIndex);
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
		public final int[] pathIndices;

		public Import(WyalFile parent, int[] pathIndices, Attribute... attributes) {
			super(parent,attributes);
			this.pathIndices = pathIndices;
		}
	}
	// ===========================================================
	// Helper accessor methods
	// ===========================================================

	public String getIdentifier(int index) {
		Bytecode.Identifier id = (Bytecode.Identifier) contantPool.get(index);
		return id.get();
	}

	public Location getLocation(int index) {
		return (Location) contantPool.get(index);
	}

	public Location[] getLocations(int... indices) {
		Location[] locations = new Location[indices.length];
		for(int i=0;i!=indices.length;++i) {
			locations[i] = getLocation(indices[i]);
		}
		return locations;
	}

	public Location[] getLocations(List<Integer> indices) {
		Location[] locations = new Location[indices.size()];
		for(int i=0;i!=locations.length;++i) {
			locations[i] = getLocation(indices.get(i));
		}
		return locations;
	}

	// ===========================================================
	// Constants
	// ===========================================================
	public final static int STAR = -2;
	public final static int UNKNOWN_TYPE = -1;
}
