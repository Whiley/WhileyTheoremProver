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
import wyal.lang.WyalFile.Declaration;
import wyal.util.Interpreter;
import wyal.util.NameResolver;
import wyal.util.SmallWorldDomain;
import wyal.util.TypeChecker;
import wyal.util.WyalFileResolver;
import wybs.lang.Build;
import wybs.lang.CompilationUnit;
import wybs.lang.SyntacticException;
import wybs.lang.SyntacticItem;
import wybs.lang.Build.Graph;
import wybs.lang.Build.Project;
import wycc.util.Logger;
import wycc.util.Pair;
import wyfs.lang.Path;
import wyfs.lang.Path.Entry;
import wyfs.lang.Path.Root;
import wytp.provers.AutomatedTheoremProver;
import wytp.types.TypeSystem;
import wytp.types.extractors.TypeInvariantExtractor;
import wytp.types.subtyping.CoerciveSubtypeOperator;

public class CompileTask implements Build.Task {

	/**
	 * The master project for identifying all resources available to the builder.
	 * This includes all modules declared in the project being compiled and/or
	 * defined in external resources (e.g. jar files).
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
	private boolean verify = true;

	/**
	 * Signals whether not to try and generate counterexamples
	 */
	private boolean counterexamples = false;

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

	public void setCounterExamples(boolean flag) {
		this.counterexamples = flag;
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
		ArrayList<Pair<Path.Entry, WyalFile>> files = new ArrayList<>();
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
				target.write(createSkeleton(wf, target));

				files.add(new Pair<>(sf, wf));
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
			try {
				for (Pair<Path.Entry, WyalFile> p : files) {
					Path.Entry<? extends CompilationUnit> originalSource = p.first();
					WyalFile wf = p.second();
					prover.check(wf, project.getRoot());
				}
			} catch (SyntacticException e) {
				SyntacticItem item = e.getElement();
				if (counterexamples && item instanceof Declaration.Assert) {
					String message = findCounterexamples((Declaration.Assert) item);
					if (message != null) {
						throw new SyntacticException(e.getMessage() + " " + message, e.getEntry(), item, e.getCause());
					} else {
						throw e;
					}
				}
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

		logger.logTimedMessage("Generated code for " + files.size() + " source file(s).",
				System.currentTimeMillis() - tmpTime, tmpMemory - runtime.freeMemory());

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
		return whileyFile;
	}

	public String findCounterexamples(WyalFile.Declaration.Assert assertion) {
		// FIXME: it doesn't feel right creating new instances here.
		NameResolver resolver = new WyalFileResolver(project);
		TypeInvariantExtractor extractor = new TypeInvariantExtractor(resolver);
		Interpreter interpreter = new Interpreter(new SmallWorldDomain(resolver), resolver, extractor);
		try {
			Interpreter.Result result = interpreter.evaluate(assertion);
			if (!result.holds()) {
				return result.getEnvironment().toString();
			}
		} catch (Interpreter.UndefinedException e) {
			// do nothing for now
		}
//		catch (Exception e) {
//			// NOTE: getting here usually means some kind of exception occurred in the
//			// interpreter. At the moment this can happen as a result of incorrectly
//			// processed undefined values.
//			return "{" + e.getMessage() + "}";
//		}
		return "{}";
	}

}
