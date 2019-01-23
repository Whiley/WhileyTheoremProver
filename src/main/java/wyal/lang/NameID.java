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
package wyal.lang;

import wyfs.lang.Path;
import wyfs.util.Trie;


/**
 * A Name Identifier consists of a module, and a name within that module. The
 * purpose of this is to provide a uniform way of referring to modules +
 * names throughout the compiler.
 *
 * @author David J. Pearce
 *
 */
public final class NameID implements Comparable<NameID> {
	private final Path.ID module;
	private final String name;

	public NameID(Path.ID module, String name) {
		this.module = module;
		this.name = name;
	}

	public String name() {
		return name;
	}

	public Path.ID module() {
		return module;
	}

	@Override
	public String toString() {
		return module + ":" + name;
	}


	@Override
	public boolean equals(Object o) {
		if (o instanceof NameID) {
			NameID u = (NameID) o;
			return u.module.equals(module) && u.name.equals(name);
		}
		return false;
	}

	@Override
	public int compareTo(NameID o) {
		int r = module.compareTo(o.module);
		if(r == 0) {
			r = name.compareTo(o.name);
		}
		return r;
	}

	@Override
	public int hashCode() {
		return name.hashCode() ^ module.hashCode();
	}

	/**
	 * Create a NameID from a string representation. This is of the form
	 * "module/id:name".
	 *
	 * @param str
	 * @return
	 */
	public static NameID fromString(String str) {
		int index = str.indexOf(':');
		String module = str.substring(0, index);
		String name = str.substring(index + 1);
		return new NameID(Trie.fromString(module), name);
	}

}