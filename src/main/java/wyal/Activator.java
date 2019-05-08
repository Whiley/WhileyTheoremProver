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
package wyal;

import java.io.IOException;
import java.util.Collection;
import java.util.List;

import wyal.lang.WyalFile;
import wyal.tasks.CompileTask;
import wybs.lang.Build;
import wybs.lang.Build.Task;
import wybs.util.AbstractBuildRule;
import wybs.util.AbstractCompilationUnit.Value;
import wycc.cfg.Configuration;
import wycc.lang.Module;
import wyfs.lang.Content;
import wyfs.lang.Path;
import wyfs.lang.Path.Root;
import wyfs.util.Trie;
import wytp.provers.AutomatedTheoremProver;
import wytp.types.TypeSystem;

public class Activator implements Module.Activator {
	private static Trie PKGNAME_CONFIG_OPTION = Trie.fromString("package/name");
	public static Trie SOURCE_CONFIG_OPTION = Trie.fromString("build/wyal/source");
	public static Trie TARGET_CONFIG_OPTION = Trie.fromString("build/wyal/target");
	private static Value.UTF8 TARGET_DEFAULT = new Value.UTF8("bin");

	public static Build.Platform WYAL_PLATFORM = new Build.Platform() {

		//
		@Override
		public String getName() {
			return "wyal";
		}

		@Override
		public Configuration.Schema getConfigurationSchema() {
			return Configuration.fromArray(
					Configuration.UNBOUND_STRING(SOURCE_CONFIG_OPTION, "Specify location for wyal source files", TARGET_DEFAULT),
					Configuration.UNBOUND_STRING(TARGET_CONFIG_OPTION, "Specify location for compiled wyal files", TARGET_DEFAULT));
		}

		@Override
		public void initialise(Configuration configuration, Build.Project project) throws IOException {
			Trie pkg = Trie.fromString(configuration.get(Value.UTF8.class, PKGNAME_CONFIG_OPTION).unwrap());
			//
			// Extract source path
			Trie source = Trie.fromString(configuration.get(Value.UTF8.class, SOURCE_CONFIG_OPTION).unwrap());
			Trie target = Trie.fromString(configuration.get(Value.UTF8.class, TARGET_CONFIG_OPTION).unwrap());
			//
			Content.Filter<WyalFile> includes = Content.filter("**", WyalFile.ContentType);
			// Construct the source root
			Path.Root sourceRoot = project.getRoot().createRelativeRoot(source);
			// Construct the binary root
			Path.Root binaryRoot = project.getRoot().createRelativeRoot(target);
			//
			Path.Entry<WyalFile> binary = binaryRoot.create(target, WyalFile.BinaryContentType);
			//
			TypeSystem typeSystem = new TypeSystem(project);
			AutomatedTheoremProver prover = new AutomatedTheoremProver(typeSystem);
			// Add build rule to project.
			project.getRules().add(new AbstractBuildRule<WyalFile, WyalFile>(sourceRoot, includes, null) {
				@Override
				protected void apply(List<Path.Entry<WyalFile>> matches, Collection<Build.Task> tasks)
						throws IOException {
					// Construct a new build task
					CompileTask task = new CompileTask(project, sourceRoot, binary, matches.get(0), typeSystem, prover);
					//
					task.setVerify(true);
					// Submit the task for execution
					tasks.add(task);
				}
			});
		}

		@Override
		public Content.Type<?> getSourceType() {
			return WyalFile.ContentType;
		}

		@Override
		public Content.Type<?> getTargetType() {
			return WyalFile.BinaryContentType;
		}

		@Override
		public void execute(Build.Project project, Path.ID id, String method, Value... args) {
			throw new UnsupportedOperationException();
		}
	};

	// =======================================================================
	// Start
	// =======================================================================

	@Override
	public Module start(Module.Context context) {
		// List of commands to use
		context.register(Build.Platform.class, WYAL_PLATFORM);
		// List of content types
		context.register(Content.Type.class, WyalFile.ContentType);
		context.register(Content.Type.class, WyalFile.BinaryContentType);
		// Done
		return new Module() {
			// what goes here?
		};
	}

	// =======================================================================
	// Stop
	// =======================================================================

	@Override
	public void stop(Module module, Module.Context context) {
		// could do more here?
	}
}
