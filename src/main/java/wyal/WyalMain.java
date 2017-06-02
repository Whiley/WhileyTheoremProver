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
package wyal;

import java.io.IOException;

import wyal.io.WyalFileLexer;
import wyal.io.WyalFileParser;
import wyal.io.WyalFilePrinter;
import wyal.lang.WyalFile;
import wyal.lang.WyalFile;
import wyfs.lang.Content;
import wyfs.lang.Content.Type;
import wyfs.lang.Path;
import wyfs.lang.Path.Entry;
import wyfs.util.DirectoryRoot;
import wyfs.util.Trie;

public class WyalMain {

	public static Content.Registry registry = new Content.Registry() {
		@Override
		public void associate(Entry e) {
			if(e.suffix().equals("wyal")) {
				e.associate(WyalFile.ContentType, null);
			}
		}

		@Override
		public String suffix(Type<?> t) {
			return t.getSuffix();
		}
	};

	public static void main(String[] args) throws IOException {
		// Construct a dummy project
		DirectoryRoot dir = new DirectoryRoot(".",registry);
		Path.ID id = Trie.fromString(args[0]);
		Path.Entry e = dir.get(id,WyalFile.ContentType);
		// Now, lex and parse the source file
		WyalFileLexer lexer = new WyalFileLexer(e);
		WyalFileParser parser = new WyalFileParser(new WyalFile(e),lexer.scan());
		WyalFile file = parser.read();
		// Finally, print it out
		new WyalFilePrinter(System.out).write(file);
	}

}
