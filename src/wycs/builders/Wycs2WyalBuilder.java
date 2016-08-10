package wycs.builders;

import java.io.IOException;
import java.util.Collection;
import java.util.HashSet;
import java.util.Set;

import wycommon.util.Pair;
import wycommon.util.Logger;
import wybs.lang.*;
import wycs.core.WycsFile;
import wycs.io.WycsFilePrinter;
import wycs.syntax.WyalFile;
import wyfs.lang.Path;
import wyfs.lang.Path.Entry;

public class Wycs2WyalBuilder implements Build.Task {

	/**
	 * The master namespace for identifying all resources available to the
	 * builder. This includes all modules declared in the project being verified
	 * and/or defined in external resources (e.g. jar files).
	 */
	protected final Build.Project project;

	protected Logger logger = Logger.NULL;

	protected boolean debug = false;

	public Wycs2WyalBuilder(Build.Project project) {
		this.project = project;
	}

	public Build.Project project() {
		return project;
	}

	public void setLogger(Logger logger) {
		this.logger = logger;
	}

	public void setDebug(boolean debug) {
		this.debug = debug;
	}

	// ======================================================================
	// Build Method
	// ======================================================================

	@Override
	public Set<Path.Entry<?>> build(Collection<Pair<Entry<?>, Path.Root>> delta, Build.Graph graph) throws IOException {
		Runtime runtime = Runtime.getRuntime();
		long startTime = System.currentTimeMillis();
		long startMemory = runtime.freeMemory();
		long tmpTime = startTime;
		long tmpMem = startMemory;

		// ========================================================================
		// Parse and register source files
		// ========================================================================

		int count = 0;
		HashSet<Path.Entry<?>> generatedFiles = new HashSet<Path.Entry<?>>();
		for (Pair<Path.Entry<?>, Path.Root> p : delta) {
			Path.Entry<?> src = p.first();
			Path.Root dst = p.second();
			if (src.contentType() == WycsFile.ContentType) {
				Path.Entry<WycsFile> source = (Path.Entry<WycsFile>) src;
				Path.Entry<WyalFile> target = (Path.Entry<WyalFile>) dst.create(source.id(), WyalFile.ContentType);
				graph.registerDerivation(source, source);
				generatedFiles.add(target);
				WycsFile wf = source.read();
				// NOTE: following is really a temporary hack
				new WycsFilePrinter(System.err).write(wf);
				WyalFile waf = decompile(wf);
				target.write(waf);
				count++;
			}
		}

		// ========================================================================
		// Done
		// ========================================================================

		long endTime = System.currentTimeMillis();
		logger.logTimedMessage("Wycs => Wyal: decompiled " + delta.size() + " file(s)",
				endTime - startTime, startMemory - runtime.freeMemory());

		return generatedFiles;
	}

	protected WyalFile decompile(WycsFile wycsFile) {
		return new WyalFile(wycsFile.getEntry());
	}
}
