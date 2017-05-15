// Copyright 2017 David J. Pearce
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

package wyal.commands;

import java.io.File;
import java.io.OutputStream;
import java.io.PrintStream;
import java.util.ArrayList;
import java.util.List;

import wyal.lang.WyalFile;
import wyal.lang.WyalFile.VerificationError;
import wyal.tasks.CompileTask;
import wyal.util.AbstractProjectCommand;
import wybs.lang.SyntaxError;
import wybs.lang.SyntaxError.InternalFailure;
import wybs.util.StdBuildRule;
import wybs.util.StdProject;
import wycc.util.Logger;
import wyfs.lang.Content;
import wyfs.lang.Path;
import wytp.provers.AutomatedTheoremProver;
import wytp.types.TypeSystem;
import wyfs.lang.Content.Registry;

public class VerifyCommand extends AbstractProjectCommand<VerifyCommand.Result> {

	/**
	 * Result kind for this command
	 *
	 */
	public enum Result {
		SUCCESS, ERRORS, INTERNAL_FAILURE
	}

	/**
	 * Provides a generic place to which normal output should be directed. This
	 * should eventually be replaced.
	 */
	private final PrintStream sysout;

	/**
	 * Provides a generic place to which error output should be directed. This
	 * should eventually be replaced.
	 */
	private final PrintStream syserr;

	/**
	 * Signals that verbose output should be produced.
	 */
	protected boolean verbose = false;

	/**
	 * Signals that compile-time verification of source files should be
	 * performed.
	 */
	protected boolean verify = true;

	/**
	 * Signals whether proofs should be printed to the console. This is useful
	 * for debugging purposes.
	 */
	protected boolean printProof = false;

	/**
	 * Set the maximum size for a proof. This in effect limits the search space
	 * to ensure termination.
	 */
	protected int proofLimit = 1000;

	/**
	 * Set the display width for the proof printer
	 */
	protected int proofWidth = 80;

	/**
	 * Identifies which wyal source files should be considered for compilation.
	 * By default, all files reachable from srcdir are considered.
	 */
	protected Content.Filter<WyalFile> wyalIncludes = Content.filter("**", WyalFile.ContentType);

	/**
	 * Identifies which wyal source files should not be considered for
	 * compilation. This overrides any identified by <code>whileyIncludes</code>
	 * . By default, no files files reachable from srcdir are excluded.
	 */
	protected Content.Filter<WyalFile> wyalExcludes = null;

	public VerifyCommand(Registry registry, Logger logger) {
		super(registry, logger);
		this.sysout = System.out;
		this.syserr = System.err;
	}

	public VerifyCommand(Registry registry, Logger logger, OutputStream sysout, OutputStream syserr) {
		super(registry, logger);
		this.sysout = new PrintStream(sysout);
		this.syserr = new PrintStream(syserr);
	}

	// =======================================================================
	// Configuration
	// =======================================================================

	@Override
	public String getDescription() {
		return "Compile and verify one or more WyAL files";
	}

	@Override
	public String describe(String option) {
		switch (option) {
		case "verbose":
			return "Enable verbose output from verifier";
		case "verify":
			return "Enable verification";
		case "proof":
			return "Print proofs to console";
		case "width":
			return "Set display width for printing proofs";
		default:
			return super.describe(option);
		}
	}

	@Override
	public void set(String option, Object value) throws ConfigurationError {
		switch (option) {
		case "verbose":
			this.verbose = true;
			break;
		case "verify":
			this.verify = (Boolean) value;
			break;
		case "proof":
			this.printProof = true;
			break;
		case "width":
			this.proofWidth = (Integer) value;
			break;
		case "limit":
			this.proofLimit = (Integer) value;
			break;
		default:
			super.set(option, value);
		}
	}

	// =======================================================================
	// Execute
	// =======================================================================

	@Override
	public Result execute(String... args) {
		try {
			ArrayList<File> delta = new ArrayList<>();
			for (String arg : args) {
				delta.add(new File(arg));
			}

			// FIXME: somehow, needing to use physical files at this point is
			// rather cumbersome. It would be much better if the enclosing
			// framework could handle this aspect for us.
			for (File f : delta) {
				if (!f.exists()) {
					// FIXME: sort this out!
					sysout.println("verify: file not found: " + f.getName());
					return Result.ERRORS;
				}
			}
			// Finalise the configuration before continuing.
			StdProject project = initialiseProject();
			// Determine source files to build
			List<Path.Entry<WyalFile>> entries = wyaldir.find(delta, WyalFile.ContentType);
			// Execute the build over the set of files requested
			return compile(project, entries);
		} catch (RuntimeException e) {
			throw e;
		} catch (Exception e) {
			// FIXME: this is a problem because it is swallowing exceptions!!
			return Result.INTERNAL_FAILURE;
		}
	}

	public Result execute(List<Path.Entry<WyalFile>> entries) {
		try {
			StdProject project = initialiseProject();
			return compile(project, entries);
		} catch (RuntimeException e) {
			throw e;
		} catch (Exception e) {
			// FIXME: this is a problem because it is swallowing exceptions!!
			return Result.INTERNAL_FAILURE;
		}
	}

	// =======================================================================
	// Helpers
	// =======================================================================

	private Result compile(StdProject project, List<Path.Entry<WyalFile>> entries) {
		// Initialise Project
		try {
			addCompilationBuildRules(project);
			// =====================================================================
			// Build Delta + Santity Check
			// =====================================================================
			// Build the source files
			project.build(entries);
			// Force all wyil files to be written to disk
			wycsdir.flush();
			//
			return Result.SUCCESS;
		} catch (InternalFailure e) {
			throw e;
		} catch (SyntaxError e) {
			e.outputSourceError(syserr, false);
			if (verbose) {
				printStackTrace(syserr, e);
			}
			return Result.ERRORS;
		} catch (Exception e) {
			// now what?
			throw new RuntimeException(e);
		}
	}

	/**
	 * Add build rules necessary for compiling whiley source files into binary
	 * wyil files.
	 *
	 * @param project
	 */
	protected void addCompilationBuildRules(StdProject project) {
		addWhiley2WyalBuildRule(project);
	}

	/**
	 * Add the rule for compiling Whiley source files into WyIL files.
	 *
	 * @param project
	 */
	protected void addWhiley2WyalBuildRule(StdProject project) {
		// Rule for compiling Whiley to WyIL
		TypeSystem typeSystem = new TypeSystem(project);
		AutomatedTheoremProver prover = new AutomatedTheoremProver(typeSystem);
		prover.setPrintProof(printProof);
		prover.setProofLimit(proofLimit);
		prover.setProofWidth(proofWidth);
		CompileTask wyalBuildTask = new CompileTask(project, typeSystem, prover);
		wyalBuildTask.setVerify(verify);
		if (verbose) {
			wyalBuildTask.setLogger(logger);
		}
		project.add(new StdBuildRule(wyalBuildTask, wyaldir, wyalIncludes, wyalExcludes, wycsdir));
	}

	/**
	 * Print a complete stack trace. This differs from
	 * Throwable.printStackTrace() in that it always prints all of the trace.
	 *
	 * @param out
	 * @param err
	 */
	private static void printStackTrace(PrintStream out, Throwable err) {
		out.println(err.getClass().getName() + ": " + err.getMessage());
		for (StackTraceElement ste : err.getStackTrace()) {
			out.println("\tat " + ste.toString());
		}
		if (err.getCause() != null) {
			out.print("Caused by: ");
			printStackTrace(out, err.getCause());
		}
	}

	@Override
	public String getName() {
		return "verify";
	}
}
