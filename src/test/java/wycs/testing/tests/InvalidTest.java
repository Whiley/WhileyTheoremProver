package wycs.testing.tests;

import static org.junit.Assert.fail;

import java.io.ByteArrayOutputStream;
import java.io.File;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.Comparator;
import java.util.HashMap;
import java.util.Map;

import org.junit.Assume;
import org.junit.Before;
import org.junit.Ignore;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameters;

import wyal.commands.CompileCommand;
import wycc.util.Logger;
import wycc.util.Pair;
import wyfs.lang.Content;

@RunWith(Parameterized.class)
public class InvalidTest {
	/**
	 * The directory containing the source files for each test case. Every test
	 * corresponds to a file in this directory.
	 */
	public final static String WYAL_SRC_DIR = "tests/invalid".replace('/', File.separatorChar);

	/**
	 * Ignored tests and a reason why we ignore them.
	 */
	public final static Map<String, String> IGNORED = new HashMap<>();

	static {
		IGNORED.put("test_053", "unknown");
		IGNORED.put("test_058", "unknown");
		IGNORED.put("test_059", "unknown");
		IGNORED.put("test_060", "unknown");
		IGNORED.put("test_061", "infinite loop");
		IGNORED.put("test_062", "unknown");
		IGNORED.put("test_065", "unknown");
		IGNORED.put("test_066", "unknown");
		IGNORED.put("test_067", "unknown");
		IGNORED.put("test_068", "unknown");
		IGNORED.put("test_069", "unknown");
		IGNORED.put("test_101", "infinite loop");
		IGNORED.put("test_103", "infinite loop");
	}

	// ======================================================================
	// Test Harness
	// ======================================================================

	protected void runTest(String testName) throws IOException {
		try {
			// this will need to turn on verification at some point.
			String whileyFilename = WYAL_SRC_DIR + File.separatorChar + testName
					+ ".wyal";

			Pair<CompileCommand.Result,String> p = compile(
					WYAL_SRC_DIR,      // location of source directory
					true,              // use verification
					whileyFilename);   // name of test to compile

			CompileCommand.Result r = p.first();

			System.out.print(p.second());

			if (r == CompileCommand.Result.SUCCESS) {
				fail("Test compiled when it shouldn't have!");
			} else if (r == CompileCommand.Result.INTERNAL_FAILURE) {
				fail("Test caused internal failure!");
			}
		} catch(IOException e) {
			fail("Test threw IOException");
		}
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
		return new Pair<>(result,output);
	}

	// ======================================================================
	// Tests
	// ======================================================================

	// Parameter to test case is the name of the current test.
	// It will be passed to the constructor by JUnit.
	private final String testName;

	public InvalidTest(String testName) {
		this.testName = testName;
	}

	// Here we enumerate all available test cases.
	@Parameters(name = "{0}")
	public static Collection<Object[]> data() {
		return findTestNames(WYAL_SRC_DIR);
	}

	// Skip ignored tests
	@Before
	public void beforeMethod() {
		String ignored = IGNORED.get(this.testName);
		Assume.assumeTrue("Test " + this.testName + " skipped: " + ignored, ignored == null);
	}

	@Test
	public void valid() throws IOException {
		if (new File("../../running_on_travis").exists()) {
			System.out.println(".");
		}
		runTest(this.testName);
	}

	/**
	 * Scan a directory to get the names of all the whiley source files
	 * in that directory. The list of file names can be used as input
	 * parameters to a JUnit test.
	 *
	 * If the system property <code>test.name.contains</code> is set,
	 * then the list of files returned will be filtered. Only file
	 * names that contain the property will be returned. This makes it
	 * possible to run a subset of tests when testing interactively
	 * from the command line.
	 *
	 * @param srcDir The path of the directory to scan.
	 */
	public static Collection<Object[]> findTestNames(String srcDir) {
		final String suffix = ".wyal";
		String containsFilter = System.getProperty("test.name.contains");

		ArrayList<Object[]> testcases = new ArrayList<>();
		for (File f : new File(srcDir).listFiles()) {
			// Check it's a file
			if (!f.isFile()) {
				continue;
			}
			String name = f.getName();
			// Check it's a whiley source file
			if (!name.endsWith(suffix)) {
				continue;
			}
			// Get rid of ".whiley" extension
			String testName = name.substring(0, name.length() - suffix.length());
			// If there's a filter, check the name matches
			if (containsFilter != null && !testName.contains(containsFilter)) {
				continue;
			}
			testcases.add(new Object[] { testName });
		}
		// Sort the result by filename
		Collections.sort(testcases, new Comparator<Object[]>() {
				@Override
				public int compare(Object[] o1, Object[] o2) {
					return ((String) o1[0]).compareTo((String) o2[0]);
				}
		});
		return testcases;
	}
}
