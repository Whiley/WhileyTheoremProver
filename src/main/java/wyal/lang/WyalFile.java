package wyal.lang;

import java.io.IOException;
import java.io.InputStream;
import java.io.OutputStream;
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

	public String getIdentifier(int index) {
		Bytecode.Identifier id = (Bytecode.Identifier) syntacticItems.get(index);
		return id.get();
	}

	public Location getLocation(int index) {
		return (Location) syntacticItems.get(index);
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
	public static class Location extends AbstractSyntacticItem {
		private final int typeIndex;
		private final Bytecode bytecode;

		public Location(WyalFile parent, int typeIndex, Bytecode bytecode, Attribute...attributes) {
			super(parent,null,attributes);
			this.typeIndex = typeIndex;
			this.bytecode = bytecode;
		}

		public Location(WyalFile parent, int typeIndex, Bytecode bytecode, List<Attribute> attributes) {
			super(parent,null,attributes);
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
		@Override
		public Bytecode.Opcode getOpcode() {
			return bytecode.getOpcode();
		}

		/**
		 * Get the number of operand groups in this location.
		 *
		 * @return
		 */
		@Override
		public int numberOfOperands() {
			return bytecode.numberOfOperands();
		}

		/**
		 * Return the ith operand associated with this location.
		 *
		 * @param i
		 * @return
		 */
		@Override
		public Location getOperand(int i) {
			return getParent().getLocation(bytecode.getOperand(i));
		}

		@Override
		public String toString() {
			return bytecode.toString();
		}
	}

	// ============================================================
	// Declaration
	// ============================================================
	public static class Declaration extends AbstractSyntacticItem {
		public Declaration(WyalFile parent, Bytecode.Opcode opcode, int[] children, Attribute... attributes) {
			this(parent, opcode, children, Arrays.asList(attributes));
		}

		public Declaration(WyalFile parent, Bytecode.Opcode opcode, int[] children, Collection<Attribute> attributes) {
			super(parent, opcode, children, attributes);
		}
	}

	// ============================================================
	// Declaration
	// ============================================================
	public static class NamedDeclaration extends Declaration {
		public NamedDeclaration(WyalFile parent, Bytecode.Opcode opcode, int[] children, Attribute... attributes) {
			this(parent, opcode, children, Arrays.asList(attributes));
		}

		public NamedDeclaration(WyalFile parent, Bytecode.Opcode opcode, int[] children, Collection<Attribute> attributes) {
			super(parent, opcode, children, attributes);
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
			super(parent, Bytecode.Opcode.DECL_fun, new int[] { nameIndex }, attributes);
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

		public Macro(WyalFile parent, int nameIndex, int bodyIndex, int[] parameterIndices, Attribute... attributes) {
			this(parent, nameIndex, bodyIndex, parameterIndices, Arrays.asList(attributes));
		}

		public Macro(WyalFile parent, int nameIndex, int bodyIndex, int[] parameterIndices,
				Collection<Attribute> attributes) {
			super(parent, Bytecode.Opcode.DECL_macro,
					append(nameIndex, bodyIndex, parameterIndices), attributes);
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
			super(parent, Bytecode.Opcode.DECL_type, append(nameIndex, invariantIndices), attributes);
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
		public Assert(WyalFile parent, int bodyIndex, Attribute... attributes) {
			this(parent,bodyIndex,Arrays.asList(attributes));
		}

		public Assert(WyalFile parent, int bodyIndex, Collection<Attribute> attributes) {
			super(parent,Bytecode.Opcode.DECL_assert,new int[]{bodyIndex},attributes);
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
		public Import(WyalFile parent, int[] pathIndices, Attribute... attributes) {
			super(parent, Bytecode.Opcode.DECL_import, pathIndices, attributes);
		}
	}
	// ===========================================================
	// Helper accessor methods
	// ===========================================================

	// ===========================================================
	// Constants
	// ===========================================================
	public final static int STAR = -2;
	public final static int UNKNOWN_TYPE = -1;
}
