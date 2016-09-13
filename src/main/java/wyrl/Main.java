// Copyright (c) 2013, David J. Pearce (djp@ecs.vuw.ac.nz)
// All rights reserved.
//
// Redistribution and use in source and binary forms, with or without
// modification, are permitted provided that the following conditions are met:
//    * Redistributions of source code must retain the above copyright
//      notice, this list of conditions and the following disclaimer.
//    * Redistributions in binary form must reproduce the above copyright
//      notice, this list of conditions and the following disclaimer in the
//      documentation and/or other materials provided with the distribution.
//    * Neither the name of the <organization> nor the
//      names of its contributors may be used to endorse or promote products
//      derived from this software without specific prior written permission.
//
// THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS" AND
// ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED
// WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
// DISCLAIMED. IN NO EVENT SHALL DAVID J. PEARCE BE LIABLE FOR ANY
// DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES
// (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES;
// LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND
// ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
// (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS
// SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.


package wyrl;

import java.io.*;
import java.util.*;

// import wyone.util.SyntaxError;
import wyrl.core.*;
import wyrl.io.*;
import wyrl.util.*;

/**
 * This class provides a simple text interface to the Solver, allowing simple
 * conditions to be checked for satisfiability.
 *
 * @author djp
 *
 */
public class Main {

	public static void main(String[] args) {
		if(args.length == 0) {
			System.out.println("usage: java wyrl.Main <options> <spec-file>");
			System.exit(1);
		}

		int optIndex = 0;
		boolean verbose = false;
		OutputStream fout = System.out;

		while(optIndex < args.length && args[optIndex].startsWith("-")) {
			String arg = args[optIndex];
			if(arg.equals("-verbose")) {
				optIndex++;
				verbose = true;
			}
		}

		for(int i=optIndex;i!=args.length;++i) {
			String filename = args[i];
			try {
				try {
					File file = new File(filename);
					SpecLexer lexer = new SpecLexer(file);
					SpecParser parser = new SpecParser(file, lexer.scan());
					SpecFile sf = parser.parse();
					new TypeExpansion().expand(sf);
					new TypeInference().infer(sf);
					BufferedOutputStream bout = new BufferedOutputStream(fout,65536);
					new JavaFileWriter(bout).write(sf);
				} catch (SyntaxError e) {
					outputSourceError(e.filename(), e.start(), e.end(),
							e.getMessage());

					if (verbose) {
						e.printStackTrace(System.err);
					}
				}
			} catch(IOException e) {
				System.err.println("I/O error - " + e.getMessage());
			}
		}
	}

	/**
	 * This method simply reads in the input file, and prints out a
	 * given line of text, with little markers (i.e. '^') placed
	 * underneath a portion of it.
	 *
	 * @param fileArg - the name of the file whose line to print
	 * @param start - the start position of the offending region.
	 * @param end - the end position of the offending region.
	 * @param message - the message to print about the error
	 */
	public static void outputSourceError(String fileArg, int start, int end,
			String message) throws IOException {
		BufferedReader in = new BufferedReader(new FileReader(fileArg));

		int line = 0;
		String lineText = "";
		while (in.ready() && start >= lineText.length()) {
			start -= lineText.length() + 1;
			end -= lineText.length() + 1;
			lineText = in.readLine();
			line = line + 1;
		}

		System.err.println(fileArg + ":" + line + ": " + message);
		System.err.println(lineText);
		for (int i = 0; i <= start; ++i) {
			if (lineText.charAt(i) == '\t') {
				System.err.print("\t");
			} else {
				System.err.print(" ");
			}
		}
		for (int i = start; i <= end; ++i) {
			System.err.print("^");
		}
		System.err.println("");
	}
}
