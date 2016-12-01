package wyal.tasks;

import java.io.IOException;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashSet;
import java.util.Set;

import wyal.lang.WyalFile;
import wyal.lang.WyalFile;
import wybs.lang.Build;
import wybs.lang.Build.Graph;
import wybs.lang.Build.Project;
import wycc.util.Logger;
import wycc.util.Pair;
import wyfs.lang.Path;
import wyfs.lang.Path.Entry;
import wyfs.lang.Path.Root;

public class CompileTask implements Build.Task {

	/**
	 * The master project for identifying all resources available to the
	 * builder. This includes all modules declared in the project being compiled
	 * and/or defined in external resources (e.g. jar files).
	 */
	private final Build.Project project;

	/**
	 * The logger used for logging system events
	 */
	private Logger logger;


	public CompileTask(Build.Project project) {
		this.logger = Logger.NULL;
		this.project = project;

	}

	@Override
	public Project project() {
		return project;
	}

	public void setLogger(Logger logger) {
		this.logger = logger;
	}

	@Override
	public Set<Entry<?>> build(Collection<Pair<Entry<?>, Root>> delta, Graph graph) throws IOException {
		Runtime runtime = Runtime.getRuntime();
		long startTime = System.currentTimeMillis();
		long startMemory = runtime.freeMemory();
		long tmpTime = startTime;
		long tmpMemory = startMemory;

		// ========================================================================
		// Parse and register source files
		// ========================================================================

		int count = 0;
		for (Pair<Path.Entry<?>, Path.Root> p : delta) {
			Path.Entry<?> src = p.first();
			if (src.contentType() == WyalFile.ContentType) {
				Path.Entry<WyalFile> sf = (Path.Entry<WyalFile>) src;
				sf.read(); // force file to be parsed
				count++;
			}
		}

		logger.logTimedMessage("Parsed " + count + " source file(s).", System.currentTimeMillis() - tmpTime,
				tmpMemory - runtime.freeMemory());


		// ========================================================================
		// Type Check source files
		// ========================================================================

		runtime = Runtime.getRuntime();
		tmpTime = System.currentTimeMillis();
		tmpMemory = runtime.freeMemory();

		ArrayList<WyalFile> files = new ArrayList<WyalFile>();
		for (Pair<Path.Entry<?>, Path.Root> p : delta) {
			Path.Entry<?> entry = p.first();
			if (entry.contentType() == WyalFile.ContentType) {
				Path.Entry<WyalFile> source = (Path.Entry<WyalFile>) entry;
				WyalFile wf = source.read();
				files.add(wf);
				// Write WyIL skeleton. This is a stripped down version of the
				// source file which is easily translated into a temporary
				// WyilFile. This is needed for resolution.
				Path.Root dst = p.second();
				Path.Entry<WyalFile> target = dst.create(entry.id(), WyalFile.CompiledContentType);
				target.write(createSkeleton(wf,target));
				// Register the derivation in the build graph. This is important
				// to understand what a particular intermediate file was
				// derived from.
				graph.registerDerivation(source, target);
			}
		}

//		TypeChecker typeChecker = new TypeChecker(this);
//		typeChecker.propagate(files);
//
//		logger.logTimedMessage("Typed " + count + " source file(s).", System.currentTimeMillis() - tmpTime,
//				tmpMemory - runtime.freeMemory());

		// ========================================================================
		// Code Generation
		// ========================================================================

		runtime = Runtime.getRuntime();
		tmpTime = System.currentTimeMillis();
		tmpMemory = runtime.freeMemory();

		HashSet<Path.Entry<?>> generatedFiles = new HashSet<Path.Entry<?>>();
		for (Pair<Path.Entry<?>, Path.Root> p : delta) {
			Path.Entry<?> src = p.first();
			Path.Root dst = p.second();
			if (src.contentType() == WyalFile.ContentType) {
				Path.Entry<WyalFile> source = (Path.Entry<WyalFile>) src;
				Path.Entry<WyalFile> target = dst.get(src.id(), WyalFile.CompiledContentType);
				generatedFiles.add(target);
				// FIXME: need to actually generate code here
			}
		}

		logger.logTimedMessage("Generated code for " + count + " source file(s).", System.currentTimeMillis() - tmpTime,
				tmpMemory - runtime.freeMemory());
		// ========================================================================
		// Done
		// ========================================================================

		long endTime = System.currentTimeMillis();
		logger.logTimedMessage("Wyal => Wyail: compiled " + delta.size() + " file(s)", endTime - startTime,
				startMemory - runtime.freeMemory());

		return generatedFiles;
	}


	// ======================================================================
	// Private Implementation
	// ======================================================================

	private WyalFile createSkeleton(WyalFile whileyFile, Path.Entry<WyalFile> target) {
		// FIXME: this is a temporary hack
		return null;
	}
}
