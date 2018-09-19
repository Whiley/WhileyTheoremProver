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

import java.io.IOException;
import java.util.ArrayList;
import java.util.List;

import wyal.Activator;
import wyal.lang.WyalFile;
import wybs.lang.CompilationUnit.Name;
import wybs.lang.CompilationUnit.Identifier;
import wybs.lang.CompilationUnit.Declaration;
import wybs.lang.Build;
import wybs.lang.CompilationUnit;
import wybs.lang.NameID;
import wybs.lang.NameResolver;
import wybs.lang.SyntacticElement;
import wybs.lang.SyntacticHeap;
import wybs.lang.SyntacticItem;
import wybs.util.AbstractCompilationUnit.Tuple;
import wybs.util.AbstractCompilationUnit.Value;
import wycc.cfg.Configuration;
import wyfs.lang.Content;
import wyfs.lang.Path;
import wyfs.util.Trie;

public final class WyalFileResolver implements NameResolver {
	private final Build.Project project;

	public WyalFileResolver(Build.Project project) {
		this.project = project;
	}

	@Override
	public NameID resolve(CompilationUnit.Name name) throws ResolutionError {
		//
		if (name.size() == 1) {
			CompilationUnit.Identifier ident = name.get(0);
			// This name is not fully qualified. Therefore, attempt to resolve
			// it.
			WyalFile enclosing = (WyalFile) name.getHeap();
			if (localNameLookup(ident.get(), enclosing)) {
				return new NameID(enclosing.getEntry().id(), ident.get());
			}
			// Failed local lookup
		}
		// If we get here, then either we failed the local lookup or it was already a
		// partially or fully qualified name. Eitherway, we need to validate that it has
		// indeed been imported.
		return nonLocalNameLookup(name);
	}

	@Override
	public <T extends Declaration> T resolveExactly(CompilationUnit.Name name, Class<T> kind) throws ResolutionError {
		List<T> matches = resolveAll(name, kind);
		if (matches.size() == 1) {
			return matches.get(0);
		} else {
			throw new NameResolver.AmbiguousNameError(name);
		}
	}

	@Override
	public <T extends Declaration> List<T> resolveAll(CompilationUnit.Name name, Class<T> kind) throws ResolutionError {
		try {
			NameID nid = resolve(name);
			WyalFile enclosing = loadModule(nid,name);
			ArrayList<T> result = new ArrayList<>();
			// Look through the enclosing file first!
			for (int i = 0; i != enclosing.size(); ++i) {
				SyntacticItem item = enclosing.getSyntacticItem(i);
				if (item instanceof WyalFile.Declaration.Named) {
					WyalFile.Declaration.Named nd = (WyalFile.Declaration.Named) item;
					if (nd.getName().get().equals(nid.name()) && kind.isInstance(nd)) {
						result.add((T) nd);
					}
				}
			}
			//
			if (!result.isEmpty()) {
				//
				return result;
			}
			throw new NameResolver.NameNotFoundError(name);
		} catch (IOException e) {
			// Slight unclear what the best course of action is here.
			throw new NameResolver.NameNotFoundError(name);
		}
	}


	/**
	 * Load a given WyIL file from this project. This will search through local
	 * roots and package dependencies in search of a matching file.
	 *
	 * @param id
	 *            The module ID of the file to load.
	 * @return
	 * @throws IOException
	 */
	public Path.Entry<WyalFile> load(Path.ID id) throws IOException {
		// Check within this project
		for(Path.Root root : project.getRoots()) {
			Path.Entry<WyalFile> e = root.get(id, WyalFile.BinaryContentType);
			if(e != null) {
				return e;
			}
		}
		// Check within dependencies
		for(Build.Package pkg : project.getPackages()) {
			Path.Root root = getPlatformBinaryRoot(pkg);
			//
			Path.Entry<WyalFile> e = root.get(id, WyalFile.BinaryContentType);
			if(e != null) {
				return e;
			}
		}
		//
		return null;
	}


	private WyalFile loadModule(NameID nid, CompilationUnit.Name name) throws IOException, ResolutionError {
		WyalFile enclosing = getWyalFile(name.getHeap());
		if (enclosing.getEntry().id().equals(nid.module())) {
			// This is a local lookup.

			// FIXME: unclear why necessary to distinguish local from non-local
			// look ups. Specifically, the project.get(...) should return
			// enclosing if the module path identifies the enclosing module.

			return enclosing;
		} else {
			// This is a non-local lookup.
			Path.Entry<WyalFile> entry = load(nid.module());
			if (entry != null) {
				return entry.read();
			} else {
				throw new NameResolver.NameNotFoundError(name);
			}
		}
	}

	/**
	 * Look up the given named item in the given heap. The precondition is that
	 * this name has exactly one component.
	 *
	 * @param name
	 * @param heap
	 * @param kind
	 * @return
	 * @throws NameNotFoundError
	 */
	private <T extends WyalFile.Declaration.Named> boolean localNameLookup(String name, SyntacticHeap heap) {
		// Look through the enclosing file first!
		for (int i = 0; i != heap.size(); ++i) {
			SyntacticItem item = heap.getSyntacticItem(i);
			if (item instanceof WyalFile.Declaration.Named) {
				WyalFile.Declaration.Named nd = (WyalFile.Declaration.Named) item;
				if (nd.getName().get().equals(name)) {
					return true;
				}
			}
		}
		//
		return false;
	}

	/**
	 * Attempt to look up a non-local name. That is, one which may not be
	 * defined in the enclosing module.
	 *
	 * @throws NameNotFoundError
	 */
	private NameID nonLocalNameLookup(CompilationUnit.Name name) throws NameResolver.ResolutionError {
		try {
			WyalFile enclosing = (WyalFile) getWyalFile(name.getHeap());
			List<WyalFile.Declaration.Import> imports = getImportsInReverseOrder(enclosing);
			// Check name against import statements
			for (WyalFile.Declaration.Import imp : imports) {
				NameID nid = matchImport(imp, name);
				if (nid != null) {
					return nid;
				}
			}
			// Check whether name is fully qualified or not
			NameID nid = name.toNameID();
			if (name.size() > 1) {
				// Could be fully or partially qualified name
				Path.Entry<WyalFile> e = load(nid.module());
				if (e != null) {
					// Look inside to see whether a matching item is found
					if (localNameLookup(nid.name(), e.read())) {
						return nid;
					}
				} else {
					// If we get here, then there is still an actual chance it could
					// be referring to something declared in this compilation unit
					// (i.e. a local lookup with a partially- or fully-qualified
					// name)
					Path.ID localPathID = enclosing.getEntry().id();
					//
					if (matchPartialModulePath(nid.module(), localPathID)) {
						// Yes, ok, we've matched a local item!
						return new NameID(localPathID, nid.name());
					}
					// Otherwise, we really couldn't figure out this name.
				}
			}
		} catch (IOException e) {
			e.printStackTrace();
		}
		throw new NameResolver.NameNotFoundError(name);
	}

	/**
	 * Extract the list of imports from the given WyalFile. These are returned
	 * in reverse order, since that is the order in which they will be examined
	 * for the given named item.
	 *
	 * @param heap
	 * @return
	 */
	private List<WyalFile.Declaration.Import> getImportsInReverseOrder(SyntacticHeap heap) {
		ArrayList<WyalFile.Declaration.Import> imports = new ArrayList<>();
		for (int i = heap.size() - 1; i >= 0; --i) {
			SyntacticElement element = heap.getSyntacticItem(i);
			if (element instanceof WyalFile.Declaration.Import) {
				imports.add((WyalFile.Declaration.Import) element);
			}
		}
		return imports;
	}

	/**
	 * Match a given import against a given partially or fully quantified name.
	 * For example, we might match <code>import wyal.lang.*</code> against the
	 * name <code>Test.f</code>. This would succeed if the package
	 * <code>wyal.lang</code> contained a module <code>Test</code> which in turn
	 * contained a named declaration <code>f</code>.
	 *
	 * @param imp
	 * @param name
	 * @return
	 * @throws IOException
	 */
	private NameID matchImport(WyalFile.Declaration.Import imp, CompilationUnit.Name name) throws IOException {
		NameID nid = name.toNameID();
		for (Path.Entry<WyalFile> e : expandImport(imp)) {
			WyalFile module = e.read();
			// Path.ID id = toPathID(module.getModule().getName());
			Path.ID id = e.id();
			// Determine whether this concrete module path matches the partial
			// module path or not.
			if (matchPartialModulePath(nid.module(), id)) {
				// Yes, it does match. Therefore, do we now have a valid name
				// identifier?
				if (localNameLookup(nid.name(), module)) {
					// Ok, we have found a matching item. Therefore, we are
					// done.
					return new NameID(id, nid.name());
				}
			}
		}
		//
		return null;
	}

	/**
	 * Match a partial module path (e.g. <code>Test</code>) against a complete
	 * module path (e.g. <code>wyal.lang.Test</code>).
	 *
	 * @param completeModulePath
	 * @param partialModulePath
	 * @return
	 */
	private boolean matchPartialModulePath(Path.ID partialModulePath, Path.ID completeModulePath) {
		int completeSize = completeModulePath.size();
		int partialSize = partialModulePath.size();
		if (partialSize <= completeSize) {
			// The partial module path cannot be larger than the complete module
			// path, otherwise there can be no match.
			for (int i = 1; i <= partialModulePath.size(); ++i) {
				String concrete = completeModulePath.get(completeSize - i);
				String partial = partialModulePath.get(partialSize - i);
				if (!concrete.equals(partial)) {
					// One specified component does not match
					return false;
				}
			}
			return true;
		}
		return false;
	}

	/**
	 * Expand a given import into one or more valid module paths. For example,
	 * <code>wyal.lang.Test</code> will expand into just
	 * <code>wyal.lang.Test</code>. However, <code>wyal.lang.*</code> will
	 * expand into <code>wyal.lang.Test</code> and
	 * <code>wyal.lang.OtherTest</code> if <code>Test</code> and
	 * <code>OtherTest</code> are the only modues in the package
	 * <code>wyal.lang</code>
	 *
	 * @param imp
	 * @return
	 * @throws IOException
	 */
	private List<Path.Entry<WyalFile>> expandImport(WyalFile.Declaration.Import imp) throws IOException {
		Trie filter = Trie.ROOT;
		//
		for (int i = 0; i != imp.size(); ++i) {
			Identifier component = imp.get(i);
			if (component == null) {
				filter = filter.append("*");
			} else {
				filter = filter.append(component.get());
			}
		}
		//
		Content.Filter<WyalFile> cf = Content.filter(filter, WyalFile.BinaryContentType);
		//
		ArrayList<Path.Entry<WyalFile>> matches = new ArrayList<>();
		//
		for(Path.Root root : project.getRoots()) {
			matches.addAll(root.get(cf));
		}
		// Check within dependencies
		for(Build.Package pkg : project.getPackages()) {
			Path.Root root = getPlatformBinaryRoot(pkg);
			matches.addAll(root.get(cf));
		}
		return matches;
	}

	private Path.Root getPlatformBinaryRoot(Build.Package pkg) throws IOException {
		// Extract package configuration. This tells us where the binary root for the
		// "whiley" platform is.
		Configuration configuration = pkg.getConfiguration();
		// Extract the path for the binary root of the Whiley platform.
		Path.ID binroot = Trie.fromString(configuration.get(Value.UTF8.class, Activator.TARGET_CONFIG_OPTION).unwrap());
		// Create relative root from pkg root.
		return pkg.getRoot().createRelativeRoot(binroot);
	}

	public WyalFile getWyalFile(SyntacticHeap heap) {
		if(heap instanceof WyalFile) {
			return (WyalFile) heap;
		} else {
			return getWyalFile(heap.getParent());
		}
	}

	private Path.ID toPathID(CompilationUnit.Name name) {
		Trie r = Trie.ROOT;
		for(int i=0;i!=name.size();++i) {
			r = r.append(name.get(i).get());
		}
		return r;
	}
}
