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
package wyal.util;

import java.io.File;
import java.io.IOException;
import java.util.ArrayList;
import java.util.List;

import wybs.util.StdProject;
import wycc.lang.Command;
import wycc.lang.Feature.ConfigurationError;
import wycc.util.ArrayUtils;
import wycc.util.Logger;
import wyfs.lang.Content;
import wyfs.lang.Path;
import wyfs.util.DirectoryRoot;
import wyfs.util.JarFileRoot;
import wyfs.util.VirtualRoot;

/**
 * Provides an abstract command from which other commands for controlling the
 * Whiley compiler can be derived. Specifically, this class handles all the
 * issues related to managing the various project roots, etc.
 *
 * @author David J. Pearce
 *
 */
public abstract class AbstractProjectCommand<T> implements Command<T> {

	/**
	 * The master project content type registry. This is needed for the build
	 * system to determine the content type of files it finds on the file
	 * system.
	 */
	public final Content.Registry registry;

	/**
	 * The location in which wyal source files are stored, or null if not
	 * specified.
	 */
	protected DirectoryRoot wyaldir;

	/**
	 * The location in which wycs binary files are stored, or null if not
	 * specified.
	 */
	protected Path.Root wycsdir;

	/**
	 * The logger used for logging system events
	 */
	protected Logger logger;

	/**
	 * Construct a new instance of this command.
	 *
	 * @param registry
	 *            The content registry being used to match files to content
	 *            types.
	 * @throws IOException
	 */
	public AbstractProjectCommand(Content.Registry registry, Logger logger) {
		this.registry = registry;
		this.logger = logger;
	}

	// =======================================================================
	// Configuration
	// =======================================================================

	public String describeWyaldir() {
		return "Specify where to place generated verification (WyAL) files";
	}

	public void setWyaldir(String dir) throws IOException {
		this.wyaldir = new DirectoryRoot(dir, registry);
	}

	public void setWyaldir(File dir) throws IOException {
		this.wyaldir = new DirectoryRoot(dir, registry);
	}

	private static final String[] SCHEMA = {
		"wyaldir"

	};

	@Override
	public String[] getOptions() {
		return SCHEMA;
	}

	@Override
	public String describe(String option) {
		switch(option) {
		case "wyaldir":
			return "Specify where to place generated verification (WyAL) files";
		default:
			throw new IllegalArgumentException("invalid option \"" + option + "\"");
		}
	}

	@Override
	public void set(String option, Object value) throws ConfigurationError {
		try {
			switch(option) {
			case "wyaldir":
				wyaldir = new DirectoryRoot((String) value,registry);
				break;
			default:
				throw new IllegalArgumentException("invalid option \"" + option + "\"");
			}
		} catch(IOException e) {
			throw new ConfigurationError(e);
		}
	}

	@Override
	public Object get(String name) {
		// TODO Auto-generated method stub
		return null;
	}

	// =======================================================================
	// Configuration
	// =======================================================================

	/**
	 * Construct a new temporary project. This project is temporary because it
	 * only exists for the life of an execution of this command.
	 *
	 * @return
	 * @throws IOException
	 */
	protected StdProject initialiseProject() throws IOException {
		// Finalise configuration
		finaliseConfiguration();
		// Add roots and construct project
		ArrayList<Path.Root> roots = new ArrayList<>();

		roots.add(wyaldir);
		roots.add(wycsdir);
		//
		addBootpath(roots);

		return new StdProject(roots);
	}

	/**
	 * Finalise the given configuration to ensure it is an consistent state.
	 * This means, in particular, that roots which have not been defined by the
	 * user are created as necessary.
	 */
	private void finaliseConfiguration() throws IOException {
		wyaldir = getDirectoryRoot(wyaldir,new DirectoryRoot(".",registry));
		wycsdir = getAbstractRoot(wycsdir);
	}

	/**
	 * Initialise the bootpath for use with the compiler. The bootpath basically
	 * identifies the location of the standard library for automatic inclusion
	 * into the whileypath.
	 *
	 * @param roots
	 * @throws IOException
	 */
	private void addBootpath(List<Path.Root>roots) throws IOException {
		// Configure boot path
		String bootpath = System.getProperty("wdk.bootpath");
		if (bootpath != null) {
			roots.add(new JarFileRoot(bootpath, registry));
		}
	}

	/**
	 * Construct a root which must correspond to a physical directory.
	 *
	 * @throws IOException
	 *
	 */
	private DirectoryRoot getDirectoryRoot(DirectoryRoot dir, DirectoryRoot defaulT) throws IOException {
		if(dir != null) {
			return dir;
		} else {
			return defaulT;
		}
	}

	/**
	 * Construct a root which is either virtual or corresponds to a physical
	 * directory.
	 *
	 * @throws IOException
	 *
	 */
	private Path.Root getAbstractRoot(Path.Root dir) throws IOException {
		if(dir != null) {
			return dir;
		} else {
			return new VirtualRoot(registry);
		}
	}

}
