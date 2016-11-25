package wyal.lang;

import java.io.IOException;
import java.io.InputStream;
import java.io.OutputStream;
import java.util.*;

import wyail.lang.WyailFile;
import wybs.lang.Attribute;
import wyfs.lang.Content;
import wyfs.lang.Path;
import wyfs.util.Trie;

public class WyalFile extends WyailFile {

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
			throw new RuntimeException("Implement me");
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

	public WyalFile(Path.Entry<WyalFile> entry) {
		super(entry);
	}

	// =========================================================================
	// Types
	// =========================================================================

	/**
	 * Construct an appropriate list of import statements for a declaration in a
	 * given file. Thus, only import statements up to and including the given
	 * declaration will be included in the returned list.
	 *
	 * @param wf
	 *            --- Whiley File in question to obtain list of import
	 *            statements.
	 * @param decl
	 *            --- declaration in Whiley File for which the list is desired.
	 * @return
	 */
	public List<Import> imports(Declaration d) {
		Path.ID id = getEntry().id();
		// this computation could (should?) be cached.
		ArrayList<Import> imports = new ArrayList<Import>();
		imports.add(new WyalFile.Import(this,Trie.fromString(id.parent(), "*"), null));

		for(Declaration pd : this.getDeclarations()) {
			if(d == pd) {
				break;
			} else if(d instanceof Import) {
				imports.add((Import)pd);
			}
		}
		imports.add(new WyalFile.Import(this,Trie.fromString(id), "*"));

		Collections.reverse(imports);

		return imports;
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
		public final Trie filter;
		public final String name;

		public Import(WyalFile parent, Trie filter, String name, Attribute... attributes) {
			super(parent,null,attributes);
			this.filter = filter;
			this.name = name;
		}
	}
}
