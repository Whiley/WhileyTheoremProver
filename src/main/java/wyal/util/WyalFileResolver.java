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

import java.io.IOException;
import java.util.ArrayList;
import java.util.List;

import wyal.lang.NameResolver;
import wyal.lang.SyntacticHeap;
import wyal.lang.SyntacticItem;
import wyal.lang.WyalFile;
import wyal.lang.WyalFile.Declaration.Named;
import wyal.lang.WyalFile.Declaration;
import wyal.lang.WyalFile.Identifier;
import wyal.lang.WyalFile.Name;
import wybs.lang.Build;
import wybs.lang.NameID;
import wybs.lang.SyntacticElement;
import wyfs.lang.Path;
import wyfs.util.Trie;

public class WyalFileResolver implements NameResolver {
	private final Build.Project project;

	public WyalFileResolver(Build.Project project) {
		this.project = project;
	}

	@Override
	public NameID resolve(Name name) throws NameNotFoundError {
		if (name.size() == 1) {
			// This name is not fully qualified. Therefore, attempt to resolve
			// it.
			WyalFile enclosing = (WyalFile) name.getParent();
			if (lookup(name.getOperand(0), enclosing, Named.class)) {
				return new NameID(enclosing.getEntry().id(), name.getOperand(0).get());
			}
			// FIXME: need to process imports here!
			throw new NameResolver.NameNotFoundError(name);
		} else {
			// This must be already fully qualified.
			return name.toNameID();
		}
	}

	@Override
	public <T extends Named> T resolveExactly(Name name, Class<T> kind)
			throws NameNotFoundError, AmbiguousNameError {
		List<T> matches = resolveAll(name,kind);
		if(matches.size() == 1) {
			return matches.get(0);
		} else {
			throw new NameResolver.AmbiguousNameError(name);
		}
	}

	@Override
	public <T extends Named> List<T> resolveAll(Name name, Class<T> kind)
			throws NameNotFoundError {
		try {
			NameID nid = resolve(name);
			WyalFile enclosing = project.get(nid.module(), WyalFile.ContentType).read();
			ArrayList<T> result = new ArrayList<>();
			// Look through the enclosing file first!
			for (int i = 0; i != enclosing.size(); ++i) {
				SyntacticItem item = enclosing.getSyntacticItem(i);
				if (item instanceof Declaration.Named) {
					Declaration.Named nd = (Declaration.Named) item;
					if (nd.getName().get().equals(nid.name()) && kind.isInstance(nd)) {
						result.add((T) nd);
					}
				}
			}
			//
			if (result.isEmpty()) {
				throw new NameResolver.NameNotFoundError(name);
			} else {
				//
				return result;
			}
		} catch (IOException e) {
			// Slight unclear what the best course of action is here.
			throw new NameResolver.NameNotFoundError(name);
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
	private <T extends Named> boolean lookup(Identifier name, SyntacticHeap heap, Class<T> kind) {
		int count = 0;
		// Look through the enclosing file first!
		for (int i = 0; i != heap.size(); ++i) {
			SyntacticItem item = heap.getSyntacticItem(i);
			if (item instanceof Declaration.Named) {
				Declaration.Named nd = (Declaration.Named) item;
				if (nd.getName().equals(name)) {
					count = count + 1;
				}
			}
		}
		//
		if (count == 0) {
			return false;
		} else {
			//
			return true;
		}
	}
}
