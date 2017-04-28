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
import wybs.lang.SyntacticElement;

public class WyalFileResolver implements NameResolver {

	@Override
	public Name resolveFully(Name name) {
		// FIXME: this is clearly broken.
		return name;
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
		ArrayList<T> result = new ArrayList<>();
		Identifier[] components = name.getComponents(); // FIXME: need to handle
		// case where more than one component
		Identifier last = components[components.length - 1];
		// Look through the enclosing file first!
		SyntacticHeap parent = name.getParent();
		for (int i = 0; i != parent.size(); ++i) {
			SyntacticItem item = parent.getSyntacticItem(i);
			if (item instanceof Declaration.Named) {
				Declaration.Named nd = (Declaration.Named) item;
				if (nd.getName().equals(last) && kind.isInstance(nd)) {
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
	}

}
