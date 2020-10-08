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
import java.util.Arrays;
import java.util.concurrent.Callable;
import java.util.function.Function;

import wyal.lang.WyalFile;
import wyal.lang.WyalFile.Declaration;
import wyal.util.Interpreter;
import wyal.util.NameResolver;
import wyal.util.SmallWorldDomain;
import wyal.util.TypeChecker;
import wyal.util.WyalFileResolver;
import wybs.lang.Build;
import wybs.lang.Build.Meter;
import wybs.lang.Build.Project;
import wybs.lang.SyntacticException;
import wybs.lang.SyntacticItem;
import wybs.util.AbstractBuildTask;
import wybs.util.Logger;
import wyfs.lang.Path;
import wytp.provers.AutomatedTheoremProver;
import wytp.types.TypeSystem;
import wytp.types.extractors.TypeInvariantExtractor;

public class CompileTask extends AbstractBuildTask<WyalFile, WyalFile> {

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

	public CompileTask(Build.Project project, Path.Root sourceRoot, Path.Entry<WyalFile> target,
			Path.Entry<WyalFile> source, TypeSystem typeSystem, AutomatedTheoremProver prover) {
		super(project, target, Arrays.asList(source));
		this.logger = Logger.NULL;
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
	public Function<Meter, Boolean> initialise() throws IOException {
		// Extract target and source files for compilation. This is the component which
		// requires I/O.
		WyalFile src = sources.get(0).read();
		// Construct the lambda for subsequent execution. This will eventually make its
		// way into some kind of execution pool, possibly for concurrent execution with
		// other tasks.
		return m -> execute(src);
	}

	private boolean execute(WyalFile src) {
		new TypeChecker(typeSystem, src, null).check();
		//
		if (verify) {
			try {
				prover.check(src);
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
		//
		return true;
	}

	// ======================================================================
	// Private Implementation
	// ======================================================================

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
