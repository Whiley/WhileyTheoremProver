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
package wyal.util;

import java.io.ByteArrayOutputStream;
import java.io.File;
import java.io.IOException;
import java.io.PrintStream;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

import wyal.lang.WyalFile;
import wyal.tasks.CompileTask;
import wybs.lang.Build;
import wybs.lang.SyntaxError;
import wybs.util.StdBuildGraph;
import wybs.util.StdBuildRule;
import wybs.util.StdProject;
import wycc.util.Pair;
import wyfs.lang.Content;
import wyfs.lang.Path;
import wyfs.util.DirectoryRoot;
import wyfs.util.Trie;
import wytp.provers.AutomatedTheoremProver;
import wytp.types.TypeSystem;

public class TestUtils {

	/**
	 * Identifies which whiley source files should be considered for compilation. By
	 * default, all files reachable from srcdir are considered.
	 */
	private static Content.Filter<WyalFile> wyalIncludes = Content.filter("**", WyalFile.ContentType);
	/**
	 * Identifies which WyIL source files should be considered for verification. By
	 * default, all files reachable from srcdir are considered.
	 */
	private static Content.Filter<WyalFile> wyailIncludes = Content.filter("**", WyalFile.BinaryContentType);
	/**
	 * A simple default registry which knows about whiley files and wyil files.
	 */
	private static final Content.Registry registry = new Content.Registry() {
		@Override
		public void associate(Path.Entry e) {
			String suffix = e.suffix();

			if (suffix.equals("wyal")) {
				e.associate(WyalFile.ContentType, null);
			}
		}

		@Override
		public String suffix(Content.Type<?> t) {
			return t.getSuffix();
		}
	};

	/**
	 * Run the Whiley Compiler with the given list of arguments.
	 *
	 * @param args --- list of tests to compile.
	 * @return
	 * @throws IOException
	 */
	public static Pair<Boolean, String> compile(File whileydir, boolean verify, String... args) throws IOException {
		ByteArrayOutputStream syserr = new ByteArrayOutputStream();
		ByteArrayOutputStream sysout = new ByteArrayOutputStream();
		//
		boolean result = true;
		//
		try {
			// Construct the project
			DirectoryRoot root = new DirectoryRoot(whileydir, registry);
			StdProject project = new StdProject(root);
			// Add build rules
			addCompilationRules(project,root,verify);
			// Create empty build graph
			Build.Graph graph = new StdBuildGraph();
			// Identify source files and build project
			project.build(findSourceFiles(root,args),graph);
			// Flush any created resources (e.g. wyil files)
			root.flush();
		} catch (SyntaxError e) {
			// Print out the syntax error
			e.outputSourceError(new PrintStream(syserr),false);
			result = false;
		} catch (Exception e) {
			// Print out the syntax error
			e.printStackTrace(new PrintStream(syserr));
			result = false;
		}
		// Convert bytes produced into resulting string.
		byte[] errBytes = syserr.toByteArray();
		byte[] outBytes = sysout.toByteArray();
		String output = new String(errBytes) + new String(outBytes);
		return new Pair<>(result, output);
	}

	/**
	 * Add compilation rules for compiling a Whiley file into a WyIL file and, where
	 * appropriate, for performing verification as well.
	 *
	 * @param project
	 * @param root
	 * @param verify
	 */
	private static void addCompilationRules(StdProject project, Path.Root root, boolean verify) {
		TypeSystem typeSystem = new TypeSystem(project);
		AutomatedTheoremProver prover = new AutomatedTheoremProver(typeSystem);
		CompileTask task = new CompileTask(project, typeSystem, prover);
		// Add compilation rule(s) (wyal => wyalc)
		project.add(new StdBuildRule(task, root, wyalIncludes, null, root));
	}

	/**
	 * For each test, identify the corresponding Whiley file entry in the source
	 * root.
	 *
	 * @param root
	 * @param args
	 * @return
	 * @throws IOException
	 */
	public static List<Path.Entry<WyalFile>> findSourceFiles(Path.Root root, String... args) throws IOException {
		List<Path.Entry<WyalFile>> sources = new ArrayList<>();
		for (String arg : args) {
			Path.Entry<WyalFile> e = root.get(Trie.fromString(arg), WyalFile.ContentType);
			if (e == null) {
				throw new IllegalArgumentException("file not found: " + arg);
			}
			sources.add(e);
		}
		return sources;
	}

}
