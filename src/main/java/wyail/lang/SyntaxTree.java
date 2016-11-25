package wyail.lang;

import java.util.ArrayList;
import java.util.List;

import wybs.lang.Attribute;
import wybs.lang.SyntacticElement;

/**
 * A SyntaxTree representation of the Whiley Intermediate Language (WyIL).
 * Specifically, bytecodes in WyIL are "flat" rather than being nested trees,
 * etc. This makes them easier to work with for performing optimisation, amongst
 * other things. This also means they are close to their byte-level
 * representation on disk. However, the tree-like nature of a typically abstract
 * syntax tree is convenient in many ways, and this class provides a "wrapper"
 * for bytecodes which makes them appear as a tree-like structure.
 *
 * @author David J. Pearce
 *
 */
public class SyntaxTree {
	/**
	 * The enclosing declaration for this tree
	 */
	private final WyailFile.Declaration parent;

	/**
	 * The set of locations making up this tree. Each location is some kind of
	 * component of the tree. For example, an expression or statement.
	 */
	private final List<Location<?>> locations;

	public SyntaxTree(WyailFile.Declaration enclosingDeclaration) {
		this.parent = enclosingDeclaration;
		this.locations = new ArrayList<Location<?>>();
	}

	public SyntaxTree(SyntaxTree tree) {
		this.parent = tree.parent;
		this.locations = new ArrayList<Location<?>>(tree.locations);
	}

	/**
	 * Returns the number of locations in this syntax tree.
	 *
	 * @return
	 */
	public int size() {
		return locations.size();
	}

	/**
	 * Get the location at a given index in this syntax tree.
	 *
	 * @param index
	 *            --- index of location to return
	 * @return
	 */
	public Location<?> getLocation(int index) {
		return locations.get(index);
	}

	/**
	 * Get the location at a given index in this syntax tree.
	 *
	 * @param index
	 *            --- index of location to return
	 * @return
	 */
	public Location<?>[] getLocations(int... indices) {
		Location<?>[] locs = new Location<?>[indices.length];
		for(int i=0;i!=indices.length;++i) {
			locs[i] = getLocation(indices[i]);
		}
		return locs;
	}

	public List<Location<?>> getLocations() {
		return locations;
	}

	/**
	 * Get the index of a given location in this tree.
	 *
	 * @param location
	 * @return
	 */
	public int getIndexOf(Location<?> location) {
		return locations.indexOf(location);
	}

	/**
	 * Get the enclosing declaration of this syntax tree.
	 *
	 * @return
	 */
	public WyailFile.Declaration getEnclosingDeclaration() {
		return parent;
	}

	// ============================================================
	// Location
	// ============================================================

	public static class Location<T extends Bytecode> extends SyntacticElement.Impl {
		private final SyntaxTree parent;

		private final SemanticType type;

		private final T bytecode;

		public Location(SyntaxTree parent, SemanticType type, T bytecode, Attribute...attributes) {
			super(attributes);
			this.parent = parent;
			this.type = type;
			this.bytecode = bytecode;
		}

		public Location(SyntaxTree parent, SemanticType type, T bytecode, List<Attribute> attributes) {
			super(attributes);
			this.parent = parent;
			this.type = type;
			this.bytecode = bytecode;
		}

		/**
		 * Get the index of this location in the enclosing syntax tree. Every
		 * location has a unique index.
		 *
		 * @return
		 */
		public int getIndex() {
			return parent.getIndexOf(this);
		}

		/**
		 * Get the enclosing syntax tree of this location.
		 *
		 * @return
		 */
		public SyntaxTree getEnclosingTree() {
			return parent;
		}

		/**
		 * Get a specific type of this location.
		 *
		 * @return
		 */
		public SemanticType getType() {
			return type;
		}

		/**
		 * Get the bytecode associated with this location
		 *
		 * @return
		 */
		public T getCode() {
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
		public Location<?> getOperand(int i) {
			return parent.getLocation(bytecode.getOperand(i));
		}

		/**
		 * Return the ith operand associated with this location.
		 *
		 * @param i
		 * @return
		 */
		public Location<?>[] getOperands() {
			return parent.getLocations(bytecode.getOperands());
		}

		@Override
		public String toString() {
			int index = getIndex();
			return index + ":" + type + ":" + bytecode;
		}
	}

	/**
	 * Some helpful context to make reading the code using syntax trees simpler.
	 */
	public static final int CONDITION = 0;
	public static final int BODY = 0;
	public static final int VARIABLE = 0;
	public static final int TRUEBRANCH = 0;
	public static final int PARAMETERS = 0;
	public static final int ARGUMENTS = 0;
	public static final int LEFTHANDSIDE = 0;
	//
	public static final int START = 1;
	public static final int FALSEBRANCH = 1;
	public static final int RIGHTHANDSIDE = 1;
	public static final int ENVIRONMENT = 0;
	//
	public static final int END = 2;

}
