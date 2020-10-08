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
import java.util.Collection;
import java.util.List;
import java.util.concurrent.ForkJoinPool;

import wyal.lang.WyalFile;
import wyal.tasks.CompileTask;
import wybs.lang.Build;
import wybs.lang.SyntacticException;
import wybs.util.SequentialBuildProject;
import wyfs.util.Pair;
import wyfs.lang.Content;
import wyfs.lang.Content.Type;
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

		@Override
		public Type<?> contentType(String suffix) {
			// TODO Auto-generated method stub
			return null;
		}
	};

	/**
	 * Run the Whiley Compiler with the given list of arguments.
	 *
	 * @param args --- list of tests to compile.
	 * @return
	 * @throws IOException
	 */
	public static Pair<Boolean, String> compile(File whileydir, boolean verify, String arg) throws IOException {
		ByteArrayOutputStream syserr = new ByteArrayOutputStream();
		ByteArrayOutputStream sysout = new ByteArrayOutputStream();
		//
		boolean result = true;
		//
		try {
			DirectoryRoot root = new DirectoryRoot(whileydir, registry);
			SequentialBuildProject project = new SequentialBuildProject(root);
			//
			TypeSystem typeSystem = new TypeSystem(project);
			AutomatedTheoremProver prover = new AutomatedTheoremProver(typeSystem);
			// Identify source files
			Pair<Path.Entry<WyalFile>,Path.Entry<WyalFile>> p = findSourceFiles(root,arg);
			Path.Entry<WyalFile> source = p.first();
			Path.Entry<WyalFile> target = p.second();
			// Add build rule
			project.add(new Build.Rule() {
				@Override
				public void apply(Collection<Build.Task> tasks) throws IOException {
					// Construct a new build task
					CompileTask task = new CompileTask(project, root, target, source, typeSystem, prover);
					//
					task.setVerify(verify);
					// Submit the task for execution
					tasks.add(task);
				}
			});
			// Sync project with filesystem.
			project.refresh();
			// Actually force the project to build!
			result = project.build(ForkJoinPool.commonPool(), Build.NULL_METER).get();
			// Flush any created resources (e.g. wyil files)
			root.flush();
		} catch (SyntacticException e) {
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
	 * For each test, identify the corresponding Whiley file entry in the source
	 * root.
	 *
	 * @param root
	 * @param args
	 * @return
	 * @throws IOException
	 */
	public static Pair<Path.Entry<WyalFile>,Path.Entry<WyalFile>> findSourceFiles(Path.Root root, String arg) throws IOException {
		Path.ID id = Trie.fromString(arg);
		Path.Entry<WyalFile> source = root.get(id, WyalFile.ContentType);
		if (source == null) {
			throw new IllegalArgumentException("file not found: " + arg);
		}
		// Construct target
		Path.Entry<WyalFile> target = root.get(id, WyalFile.BinaryContentType);
		// Doesn't exist, so create with default value
		target = root.create(id, WyalFile.BinaryContentType);
		//
		return new Pair<>(source,target);
	}

}
