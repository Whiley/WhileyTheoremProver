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

import java.util.ArrayList;
import java.util.List;

import wyal.lang.WyalFile;
import wybs.lang.CompilationUnit.Declaration;
import wybs.lang.Build;
import wybs.lang.CompilationUnit;
import wyal.util.NameResolver;
import wybs.lang.SyntacticHeap;
import wyfs.lang.Path;
import wyfs.util.Trie;

public final class WyalFileResolver implements NameResolver {
	private final Build.Project project;

	public WyalFileResolver(Build.Project project) {
		this.project = project;
	}

	@Override
	public <T extends Declaration> T resolveExactly(CompilationUnit.Name name, Class<T> kind) throws ResolutionError {
		WyalFile parent = getWyalFile(name.getHeap());
		for(WyalFile.Declaration.Named d : parent.getSyntacticItems(WyalFile.Declaration.Named.class)) {
			if(kind.isInstance(d) && name.equals(d.getName())) {
				return (T) d;
			}
		}
		throw new ResolutionError(name, "resolution error (" + name + ")");
	}

	@Override
	public <T extends Declaration> List<T> resolveAll(CompilationUnit.Name name, Class<T> kind) throws ResolutionError {
		WyalFile parent = getWyalFile(name.getHeap());
		List<T> results = new ArrayList<>();
		for (WyalFile.Declaration.Named d : parent.getSyntacticItems(WyalFile.Declaration.Named.class)) {
			if (kind.isInstance(d) && name.equals(d.getName())) {
				results.add((T) d);
			}
		}
		return results;
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
