package wycs.lang;

import java.io.IOException;
import java.io.InputStream;
import java.io.OutputStream;

import wybs.util.AbstractCompilationUnit;
import wyfs.lang.Content;
import wyfs.lang.Path;
import wyfs.lang.Path.Entry;

public class WyalFile extends AbstractCompilationUnit {
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
			//
			return null;
		}

		@Override
		public void write(OutputStream output, WyalFile module) throws IOException {
			//
		}

		@Override
		public String toString() {
			return "Content-Type: wya;";
		}

		@Override
		public String getSuffix() {
			return "wyal";
		}
	};

	// =========================================================================
	// Constructors
	// =========================================================================

	public WyalFile(Entry entry) {
		super(entry);
		// TODO Auto-generated constructor stub
	}
}
