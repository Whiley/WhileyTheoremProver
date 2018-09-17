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

import wyal.lang.WyalFile;
import wyal.tasks.CompileTask;
import wybs.lang.Build;
import wybs.lang.Build.Task;
import wybs.util.AbstractCompilationUnit.Value;
import wycc.cfg.Configuration;
import wycc.lang.Module;
import wyfs.lang.Content;
import wyfs.lang.Path;
import wyfs.util.Trie;
import wytp.provers.AutomatedTheoremProver;
import wytp.types.TypeSystem;

public class Activator implements Module.Activator {
	public static Trie SOURCE_CONFIG_OPTION = Trie.fromString("build/wyal/source");
	public static Trie TARGET_CONFIG_OPTION = Trie.fromString("build/wyal/target");
	private static Value.UTF8 TARGET_DEFAULT = new Value.UTF8("bin");

	public static Build.Platform WYAL_PLATFORM = new Build.Platform() {
		private Trie source;
		// Specify directory where generated WyIL files are dumped.
		private Trie target;
		//
		@Override
		public String getName() {
			return "whiley";
		}

		@Override
		public Configuration.Schema getConfigurationSchema() {
			return Configuration.fromArray(
					Configuration.UNBOUND_STRING(SOURCE_CONFIG_OPTION, "Specify location for wyal source files", TARGET_DEFAULT),
					Configuration.UNBOUND_STRING(TARGET_CONFIG_OPTION, "Specify location for compiled wyal files", TARGET_DEFAULT));
		}

		@Override
		public void apply(Configuration configuration) {
			// Extract source path
			this.source = Trie.fromString(configuration.get(Value.UTF8.class, SOURCE_CONFIG_OPTION).unwrap());
			this.target = Trie.fromString(configuration.get(Value.UTF8.class, TARGET_CONFIG_OPTION).unwrap());
		}

		@Override
		public Task initialise(Build.Project project) {
			TypeSystem typeSystem = new TypeSystem(project);
			AutomatedTheoremProver prover = new AutomatedTheoremProver(typeSystem);
			return new CompileTask(project, typeSystem, prover);
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
		public Content.Filter<?> getSourceFilter() {
			return Content.filter("**", WyalFile.ContentType);
		}

		@Override
		public Content.Filter<?> getTargetFilter() {
			return Content.filter("**", WyalFile.BinaryContentType);
		}

		@Override
		public Path.Root getSourceRoot(Path.Root root) throws IOException {
			return root.createRelativeRoot(source);
		}

		@Override
		public Path.Root getTargetRoot(Path.Root root) throws IOException {
			return root.createRelativeRoot(target);
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
