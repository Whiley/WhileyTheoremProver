// Copyright (c) 2011, David J. Pearce (djp@ecs.vuw.ac.nz)
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

package wycs.testing;

import static org.junit.Assert.fail;

import java.io.*;

import wyail.WycsMain;
import wyal.commands.CompileCommand;
import wycc.util.Logger;
import wycc.util.Pair;
import wyfs.lang.Content;

public class TestHarness {
	/**
	 * The directory containing the source files for each test case. Every test
	 * corresponds to a file in this directory.
	 */
	public final static String WYAL_SRC_DIR = "tests/valid".replace('/', File.separatorChar);

	protected void verifyPassTest(String testName) {
		try {
			// this will need to turn on verification at some point.
			String whileyFilename = WYAL_SRC_DIR + File.separatorChar + testName
					+ ".wyal";

			Pair<CompileCommand.Result,String> p = compile(
					WYAL_SRC_DIR,      // location of source directory
					false,               // no verification
					whileyFilename);     // name of test to compile

			CompileCommand.Result r = p.first();

			System.out.print(p.second());

			if (r != CompileCommand.Result.SUCCESS) {
				fail("Test failed to compile!");
			} else if (r == CompileCommand.Result.INTERNAL_FAILURE) {
				fail("Test caused internal failure!");
			}
		} catch(IOException e) {
			fail("Test threw IOException");
		}
	}

	protected void verifyFailTest(String name) {

	}

	public static Pair<CompileCommand.Result,String> compile(String wyaldir, boolean verify, String... args) throws IOException {
		ByteArrayOutputStream syserr = new ByteArrayOutputStream();
		ByteArrayOutputStream sysout = new ByteArrayOutputStream();
		Content.Registry registry = new wyal.Activator.Registry();
		CompileCommand cmd = new CompileCommand(registry,Logger.NULL,sysout,syserr);
		cmd.setWyaldir(wyaldir);
		if(verify) {
			cmd.setVerify();
		}
		CompileCommand.Result result = cmd.execute(args);
		byte[] errBytes = syserr.toByteArray();
		byte[] outBytes = sysout.toByteArray();
		String output = new String(errBytes) + new String(outBytes);
		return new Pair<CompileCommand.Result,String>(result,output);
	}
}
