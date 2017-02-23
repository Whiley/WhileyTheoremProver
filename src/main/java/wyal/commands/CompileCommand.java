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
import wyfs.lang.Content.Registry;

public class CompileCommand extends AbstractProjectCommand<CompileCommand.Result> {

	/**
	 * Result kind for this command
	 *
	 */
	public enum Result {
		SUCCESS,
		ERRORS,
		INTERNAL_FAILURE
	}


	/**
	 * List of configuration options recognised by this command
	 */
	private static String[] configOptions = {
			"verbose",
			"verify",
			"includes",
			"excludes"
	};

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
	protected boolean verify = false;

	/**
	 * Identifies which wyal source files should be considered for
	 * compilation. By default, all files reachable from srcdir are considered.
	 */
	protected Content.Filter<WyalFile> wyalIncludes = Content.filter("**", WyalFile.ContentType);

	/**
	 * Identifies which wyal source files should not be considered for
	 * compilation. This overrides any identified by <code>whileyIncludes</code>
	 * . By default, no files files reachable from srcdir are excluded.
	 */
	protected Content.Filter<WyalFile> wyalExcludes = null;

	public CompileCommand(Registry registry, Logger logger) {
		super(registry, logger, configOptions);
		this.sysout = System.out;
		this.syserr = System.err;
	}

	public CompileCommand(Registry registry, Logger logger, OutputStream sysout, OutputStream syserr) {
		super(registry, logger, configOptions);
		this.sysout = new PrintStream(sysout);
		this.syserr = new PrintStream(syserr);
	}

	// =======================================================================
	// Configuration
	// =======================================================================

	public String describeVerify() {
		return "Enable verification of Whiley source files";
	}

	public void setVerify() {
		verify = true;
	}

	public void setVerify(boolean b) {
		verify = b;
	}

	public String describeVerbose() {
		return "Enable verbose output from Whiley compiler";
	}

	public void setVerbose() {
		setVerbose(true);
	}

	public void setVerbose(boolean b) {
		verbose = b;
	}

	public String describeIncludes() {
		return "Specify where find Whiley source files";
	}

	public void setIncludes(Content.Filter<WyalFile> includes) {
		this.wyalIncludes = includes;
	}

	public String describeExcludes() {
		return "Specify WyAL source files to be excluded from consideration";
	}

	public void setExcludes(Content.Filter<WyalFile> excludes) {
		this.wyalExcludes = excludes;
	}

	@Override
	public String getDescription() {
		return "Compile and verify one or more WyAL files";
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
					sysout.println("compile: file not found: " + f.getName());
					return Result.ERRORS;
				}
			}
			// Finalise the configuration before continuing.
			StdProject project = initialiseProject();
			// Determine source files to build
			List<Path.Entry<WyalFile>> entries = wyaldir.find(delta, WyalFile.ContentType);
			// Execute the build over the set of files requested
			return compile(project,entries);
		} catch(RuntimeException e) {
			throw e;
		} catch (Exception e) {
			// FIXME: this is a problem because it is swallowing exceptions!!
			return Result.INTERNAL_FAILURE;
		}
	}


	public Result execute(List<Path.Entry<WyalFile>> entries) {
		try {
			StdProject project = initialiseProject();
			return compile(project,entries);
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
		} catch(InternalFailure e) {
			throw e;
		} catch (SyntaxError e) {
			e.outputSourceError(syserr,false);
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
		addWhiley2WyilBuildRule(project);
	}

	/**
	 * Add the rule for compiling Whiley source files into WyIL files.
	 *
	 * @param project
	 */
	protected void addWhiley2WyilBuildRule(StdProject project) {
		// Rule for compiling Whiley to WyIL
		CompileTask wyalBuildTask = new CompileTask(project);
		if(verbose) {
			wyalBuildTask.setLogger(logger);
		}
		if(verify) {
			wyalBuildTask.setVerify(true);
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
		for(StackTraceElement ste : err.getStackTrace()) {
			out.println("\tat " + ste.toString());
		}
		if(err.getCause() != null) {
			out.print("Caused by: ");
			printStackTrace(out,err.getCause());
		}
	}
}
