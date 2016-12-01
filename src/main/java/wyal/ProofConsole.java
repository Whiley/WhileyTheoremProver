package wyal;

import java.util.BitSet;
import java.util.List;

import wyal.io.WyalFileLexer;
import wyal.io.WyalFileParser;
import wyal.io.WyalFilePrinter;
import wyal.lang.Bytecode;
import wyal.lang.WyalFile;
import wyal.util.InteractiveProof;
import wyal.util.InteractiveProver;
import wyal.lang.WyalFile;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.UnsupportedEncodingException;
import java.lang.reflect.InvocationTargetException;
import java.lang.reflect.Method;

import wyfs.lang.Path;
import wyfs.util.DirectoryRoot;
import wyfs.util.Trie;

/**
 * Provides a command-line oriented interface for performing interactive proofs.
 *
 * @author David J. Pearce
 *
 */
public class ProofConsole {
	/**
	 * The current prover being used.
	 */
	private InteractiveProver prover;

	/**
	 * The current proof being worked on.
	 */
	private int cursor;

	// =========================================================================
	// Commands.
	// =========================================================================
	// Below here is the set of all commands recognised by the interface. If you
	// want to add a new command, then add a public static function for it and
	// an appropriate entry in the commands array.

	/**
	 * The list of commands recognised by the readEvaluatePrintLoop(). To add
	 * more functions, simply extend this list!
	 */
	private Command[] commands = { this.new Command("quit", getMethod("quit")),
			this.new Command("help", getMethod("printHelp")),
			this.new Command("verbose", getMethod("setVerbose", boolean.class)),
			this.new Command("print", getMethod("print")),
			this.new Command("status", getMethod("status")),
			this.new Command("load", getMethod("load", String.class)),
			this.new Command("begin", getMethod("begin", int.class))
	};

	public void quit() {
		System.exit(0);
	}

	public void printHelp() {
		System.out.println("Commands:");
		for (Command c : commands) {
			System.out.println("\t" + c.keyword);
		}
	}

	public void setVerbose(boolean verbose) {
		verbose = true;
	}

	public void print() {
		System.out.println("GOT HERE");;
	}

	public void status() {
		if (prover == null) {
			System.out.println("No file loaded");
		} else {
			InteractiveProof[] proofs = prover.getProofs();
			for(int i=0;i!=proofs.length;++i) {
				InteractiveProof p = proofs[i];
				System.out.print("#" + i + "\t");
				if(p == null) {
					System.out.println("(empty)");
				} else if(p.isComplete()) {
					System.out.println("(completed)");
				} else {
					System.out.println("(in progress)");
				}
			}
		}
	}

	public void load(String filename) throws IOException {
		System.out.print("Loading " + filename + "...");
		// Construct a dummy project
		DirectoryRoot dir = new DirectoryRoot(".", WycsMain.registry);
		Path.ID id = Trie.fromString(filename);
		Path.Entry e = dir.get(id, WyalFile.ContentType);
		// Lex and parse the source file
		WyalFileLexer lexer = new WyalFileLexer(e);
		WyalFileParser parser = new WyalFileParser(e, lexer.scan());
		WyalFile file = parser.read();
		System.out.println("OK");
		// Create the interactive prover
		prover = new InteractiveProver(file);
		//
		System.out.println("Found " + prover.getProofs().length + " assertion(s).");
	}

	public void begin(int proof) throws UnsupportedEncodingException {
		System.out.println("Proof-by-contradiction");
		this.cursor = proof;
		prover.beginByContradiction(proof);
		printProofState(prover.getProof(proof));
	}
	private void printProofState(InteractiveProof proof) throws UnsupportedEncodingException {
		printProofState(proof, proof.getHEAD());
	}

	private void printProofState(InteractiveProof proof, int stateIndex) throws UnsupportedEncodingException {
		InteractiveProof.State state = proof.getState(stateIndex);
		BitSet truths = state.getTruths();
		WyalFilePrinter printer = new WyalFilePrinter(System.out);
		for (int i = truths.nextSetBit(0); i >= 0; i = truths.nextSetBit(i+1)) {
			System.out.print(i + ") ");
			printer.writeStatement(proof.getLocation(i),1);
		}
	}

	// =========================================================================
	// Read, Evaluate, Print loop
	// =========================================================================
	// Below here is all the machinery for the REPL. You shouldn't need to touch
	// this.

	/**
	 * This function provides a simple interface to the model railway system. In
	 * essence, it waits for user input. Each command consists of a line of
	 * text, and has a specific form. The commands are dispatched to handlers
	 * which then interface with the railway. The interface remains in the loop
	 * continually waiting for user input.
	 */
	public void readEvaluatePrintLoop() {
		final BufferedReader input = new BufferedReader(new InputStreamReader(System.in));

		try {
			System.out.println("Proof Console.");
			while (true) {
				System.out.print("> ");
				// Read the input line
				String line = input.readLine();
				// Attempt to execute the input line
				boolean isOK = execute(line);
				if (!isOK) {
					// If we get here, then it means that the command was not
					// recognised. Therefore, print error!
					System.out.println("Error: command not recognised");
				}
			}
		} catch (IOException e) {
			System.err.println("I/O Error - " + e.getMessage());
		}
	}

	/**
	 * Attempt to execute a command-line
	 *
	 * @param line
	 * @param railway
	 * @return
	 */
	public boolean execute(String line) {
		Command candidate = null;
		for (Command c : commands) {
			if (c.canMatch(line)) {
				if (candidate != null) {
					System.out.println("Ambiguos Command \"" + c.keyword);
				} else {
					candidate = c;
				}
			}
		}
		if (candidate != null) {
			Object[] args = candidate.match(line);
			if (args != null) {
				// Yes, this command was matched. Now, sanity check the
				// arguments.
				for (int i = 0; i != args.length; ++i) {
					if (args[i] == null) {
						// this indicates a problem converting this
						// argument, so report an error to the user.
						System.out
								.println("Command \"" + candidate.keyword + "\": syntax error on argument " + (i + 1));
						return false;
					}
				}
				try {
					// Ok, attemp to execute the command;
					candidate.method.invoke(this, args);
					return true;
				} catch (IllegalAccessException e) {
					e.printStackTrace();
				} catch (IllegalArgumentException e) {
					e.printStackTrace();
				} catch (InvocationTargetException e) {
					printFullStackTrace(e);
				}
			}
		}
		return false;
	}

	/**
	 * This simply returns a reference to a given name. If the method doesn't
	 * exist, then it will throw a runtime exception.
	 *
	 * @param name
	 * @param paramTypes
	 * @return
	 */
	public static Method getMethod(String name, Class... paramTypes) {
		try {
			return ProofConsole.class.getMethod(name, paramTypes);
		} catch (Exception e) {
			throw new RuntimeException("No such method: " + name, e);
		}
	}

	/**
	 * Represents a given interface command in the railway. Each command
	 * consists of an initial keyword, followed by zero or more parameters. The
	 * class provides simplistic checking of option types.
	 *
	 * @author David J. Pearce
	 *
	 */
	private class Command {
		public final String keyword;
		public final Method method;

		public Command(String keyword, Method method) {
			this.keyword = keyword;
			this.method = method;
		}

		/**
		 * Check whether a given line of text could match the given command or
		 * not. Specifically, a command can match if it has the right number of
		 * arguments, and the given command begins with the string command
		 * provided.
		 *
		 * @param line
		 * @return
		 */
		public boolean canMatch(String line) {
			Class[] parameters = method.getParameterTypes();
			String[] tokens = line.split(" ");
			if (tokens.length != parameters.length + 1) {
				return false;
			} else if (!keyword.startsWith(tokens[0])) {
				return false;
			} else {
				return true;
			}
		}

		/**
		 * Check whether a given line of text matches the command or not. For
		 * this to be true, the number of arguments must match the expected
		 * number, and the given keyword must match as well. If so, an array of
		 * the converted arguments is returned; otherwise, null is returned.
		 * When we cannot convert a given argument because it has the wrong
		 * type, a null entry is recorded to help with error reporting,
		 *
		 * @param line
		 * @return
		 */
		public Object[] match(String line) {
			Class[] parameters = method.getParameterTypes();
			String[] tokens = line.split(" ");
			if (tokens.length != parameters.length + 1) {
				return null;
			} else if (!keyword.startsWith(tokens[0])) {
				return null;
			} else {
				Object[] arguments = new Object[tokens.length - 1];
				for (int i = 1; i != tokens.length; ++i) {
					arguments[i - 1] = convert(parameters[i - 1], tokens[i]);
				}
				return arguments;
			}
		}

		/**
		 * Convert a string representation of this argument into an actual
		 * object form. If this fails for some reason, then null is returned.
		 *
		 * @param token
		 * @return
		 */
		private Object convert(Class parameter, String token) {
			if (parameter == boolean.class) {
				if (token.equals("off")) {
					return false;
				} else if (token.equals("on")) {
					return true;
				} else {
					return null;
				}
			} else if (parameter == int.class) {
				try {
					return Integer.parseInt(token);
				} catch (NumberFormatException e) {
					return null;
				}
			} else if (parameter == float.class) {
				try {
					return Float.parseFloat(token);
				} catch (NumberFormatException e) {
					return null;
				}
			} else if (parameter == int[].class) {
				String[] numbers = token.split(",");
				int[] array = new int[numbers.length];
				for (int i = 0; i != numbers.length; ++i) {
					try {
						array[i] = Integer.parseInt(numbers[i]);
					} catch (NumberFormatException e) {
						return null;
					}
				}
				return array;
			} else if (parameter == String.class) {
				return token;
			} else if (parameter == String[].class) {
				return token.split(",");
			} else {
				// In this case, the argument was not recognised.
				return null;
			}
		}
	}

	private static void printFullStackTrace(Throwable e) {
		while(e != null) {
			System.out.println(e.getMessage());
			for(StackTraceElement ste : e.getStackTrace()) {
				System.out.println("\t" + ste.toString());
			}
			e = e.getCause();
		}
	}

	public static void main(String[] args) {
		new ProofConsole().readEvaluatePrintLoop();
	}
}
