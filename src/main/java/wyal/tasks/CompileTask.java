// Copyright 2011 The Whiley Project Developers
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
package wyal.tasks;

import java.io.IOException;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashSet;
import java.util.Set;

import wyal.lang.WyalFile;
import wyal.util.TypeChecker;
import wybs.lang.Build;
import wybs.lang.CompilationUnit;
import wybs.lang.Build.Graph;
import wybs.lang.Build.Project;
import wycc.util.Logger;
import wycc.util.Pair;
import wyfs.lang.Path;
import wyfs.lang.Path.Entry;
import wyfs.lang.Path.Root;
import wytp.provers.AutomatedTheoremProver;
import wytp.types.TypeSystem;
import wytp.types.subtyping.CoerciveSubtypeOperator;

public class CompileTask implements Build.Task {

	/**
	 * The master project for identifying all resources available to the
	 * builder. This includes all modules declared in the project being compiled
	 * and/or defined in external resources (e.g. jar files).
	 */
	private final Build.Project project;

	/**
	 * The type system used by this task.
	 */
	private final TypeSystem typeSystem;

	/**
	 * The theorem prover this task uses for verification.
	 */
	private final AutomatedTheoremProver prover;

	/**
	 * The logger used for logging system events
	 */
	private Logger logger;

	/**
	 * Signals whether or not verification should be enabled.
	 */
	private  boolean verify = true;

	public CompileTask(Build.Project project, TypeSystem typeSystem, AutomatedTheoremProver prover) {
		this.logger = Logger.NULL;
		this.project = project;
		this.typeSystem = typeSystem;
		this.prover = prover;
	}

	@Override
	public Project project() {
		return project;
	}

	public void setLogger(Logger logger) {
		this.logger = logger;
	}

	public void setVerify(boolean flag) {
		this.verify = flag;
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
		ArrayList<Pair<Path.Entry,WyalFile>> files = new ArrayList<>();
		for (Pair<Path.Entry<?>, Path.Root> p : delta) {
			Path.Entry<?> src = p.first();
			if (src.contentType() == WyalFile.ContentType) {
				Path.Entry<WyalFile> sf = (Path.Entry<WyalFile>) src;
				WyalFile wf = sf.read(); // force file to be parsed
				// Write WyIL skeleton. This is a stripped down version of the
				// source file which is easily translated into a temporary
				// WyilFile. This is needed for resolution.
				Path.Root dst = p.second();
				Path.Entry<WyalFile> target = dst.create(sf.id(), WyalFile.BinaryContentType);
				target.write(createSkeleton(wf,target));
				// Register the derivation in the build graph. This is important
				// to understand what a particular intermediate file was
				// derived from.
				graph.registerDerivation(sf, target);
				//
				Path.Entry<? extends CompilationUnit> originalSource = determineSource(sf,graph);

				files.add(new Pair<>(originalSource,wf));
			}
		}

		logger.logTimedMessage("Parsed " + files.size() + " source file(s).", System.currentTimeMillis() - tmpTime,
				tmpMemory - runtime.freeMemory());

		// ========================================================================
		// Type Check source files
		// ========================================================================

		runtime = Runtime.getRuntime();
		tmpTime = System.currentTimeMillis();
		tmpMemory = runtime.freeMemory();

		for (Pair<Path.Entry, WyalFile> p : files) {
			new TypeChecker(typeSystem, p.second(), p.first()).check();
		}

		logger.logTimedMessage("Typed " + files.size() + " source file(s).", System.currentTimeMillis() - tmpTime,
				tmpMemory - runtime.freeMemory());

		// ========================================================================
		// Verify source files
		// ========================================================================

		runtime = Runtime.getRuntime();
		tmpTime = System.currentTimeMillis();
		tmpMemory = runtime.freeMemory();

		if (verify) {
			for (Pair<Path.Entry, WyalFile> p : files) {
				Path.Entry<? extends CompilationUnit> originalSource = p.first();
				WyalFile wf = p.second();
				prover.check(wf, originalSource);
			}
		}

		logger.logTimedMessage("Verified " + files.size() + " source file(s).", System.currentTimeMillis() - tmpTime,
				tmpMemory - runtime.freeMemory());


		// ========================================================================
		// Code Generation
		// ========================================================================

		runtime = Runtime.getRuntime();
		tmpTime = System.currentTimeMillis();
		tmpMemory = runtime.freeMemory();

		HashSet<Path.Entry<?>> generatedFiles = new HashSet<>();
		for (Pair<Path.Entry<?>, Path.Root> p : delta) {
			Path.Entry<?> src = p.first();
			Path.Root dst = p.second();
			if (src.contentType() == WyalFile.ContentType) {
				Path.Entry<WyalFile> source = (Path.Entry<WyalFile>) src;
				Path.Entry<WyalFile> target = dst.get(src.id(), WyalFile.BinaryContentType);
				generatedFiles.add(target);
				// FIXME: need to actually generate code here
			}
		}

		logger.logTimedMessage("Generated code for " + files.size() + " source file(s).", System.currentTimeMillis() - tmpTime,
				tmpMemory - runtime.freeMemory());

		// ========================================================================
		// Done
		// ========================================================================

		long endTime = System.currentTimeMillis();
		logger.logTimedMessage("Wyal => Wyail: compiled " + delta.size() + " file(s)", endTime - startTime,
				startMemory - runtime.freeMemory());

		return generatedFiles;
	}

	private static Path.Entry<? extends CompilationUnit> determineSource(Path.Entry<?> child, Build.Graph graph) {
		// FIXME: this is a temporary hack
		Path.Entry<?> parent = graph.parent(child);
		while (parent != null) {
			child = parent;
			parent = graph.parent(child);
		}
		return (Path.Entry<? extends CompilationUnit>) child;
	}

	// ======================================================================
	// Private Implementation
	// ======================================================================

	private WyalFile createSkeleton(WyalFile whileyFile, Path.Entry<WyalFile> target) {
		// FIXME: this is a temporary hack
		return whileyFile;
	}
}
