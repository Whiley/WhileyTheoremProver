package wyrl;

import java.io.BufferedReader;
import java.io.FileReader;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.Reader;
import java.io.StringReader;
import java.lang.reflect.InvocationTargetException;
import java.lang.reflect.Method;
import java.util.*;

import wyautl.core.*;
import wyautl.io.PrettyAutomataReader;
import wyautl.io.PrettyAutomataWriter;
import wyrw.core.*;
import wyrw.util.*;

/**
 * Provides a general console-based interface for a given rewrite system. The
 * intention is that this interface can be reused by the generated rewriters.
 * 
 * @author David J. Pearce
 *
 */
public class ConsoleRewriter {
	
	public enum RwMode { REDUCE, INFER };
	
	/**
	 * Schema of rewrite system used in this session
	 */
	private final Schema schema;
	
	/**
	 * Set of reduction rules for use in this session
	 */
	private final ReductionRule[] reductions;
	
	/**
	 * Set of inference rules for use in this session
	 */
	private final InferenceRule[] inferences;
	
	
	/**
	 * Rewriter being used in this session
	 */
	private Rewriter rewriter;
	
	/**
	 * Current rewrite being worked on in this session.
	 */
	private Rewrite rewrite;
	
	/**
	 * State in rewrite where currently at in this session.
	 */
	private int HEAD;
	
	/**
	 * List of indents being used
	 */
	private String[] indents = {};
	
	/**
	 * Indicate whether or not to print term indices
	 */
	private boolean indices = true;
	
	/**
	 * Enable rewrite caching
	 */
	private boolean caching = true;
	
	/**
	 * Collapse reductions or not
	 */
	private boolean collapse = false;
	
	/**
	 * Linear rewriter
	 */
	private boolean linear = true;
	
	/**
	 * If true, generate verbose information about rewriting.
	 */
	private boolean verbose;
	
	public ConsoleRewriter(Schema schema, InferenceRule[] inferences, ReductionRule[] reductions) {
		this.schema = schema;
		this.inferences = inferences;
		this.reductions = reductions;		
	}
	
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
	private Command[] commands = {
			this.new Command("quit",getMethod("quit")),
			this.new Command("help",getMethod("printHelp")),
			this.new Command("verbose",getMethod("setVerbose",boolean.class)),
			this.new Command("print",getMethod("print")),
			this.new Command("indent",getMethod("setIndent",String[].class)),
			this.new Command("indices",getMethod("setIndices",boolean.class)),
			this.new Command("caching",getMethod("setCaching",boolean.class)),
			this.new Command("collapse",getMethod("setCollapse",boolean.class)),
			this.new Command("linear",getMethod("setLinear",boolean.class)),
			this.new Command("log",getMethod("printLog")),
			this.new Command("reduce",getMethod("startReduce",String.class)),
			this.new Command("infer",getMethod("startInfer",String.class)),
			this.new Command("load",getMethod("loadRewrite",String.class)),			
			this.new Command("grind",getMethod("grind",int.class)),
			this.new Command("apply",getMethod("applyActivation",int.class)),
			this.new Command("reset",getMethod("reset",int.class)),
	};

	public void quit() {
		System.exit(0);
	}

	public void printHelp() {
		System.out.println("Commands:");
		for(Command c : commands) {
			System.out.println("\t" + c.keyword);
		}
	}	
	
	public void setVerbose(boolean verbose) {
		verbose = true;
	}
	
	public void print() {
		try {
			Rewrite.State state = rewrite.states().get(HEAD); 
			PrettyAutomataWriter writer = new PrettyAutomataWriter(System.out,schema,indents);
			writer.setIndices(indices);
			// FIXME: this is clearly broken because it won't work for a
			// reduction.
			Automaton automaton = state.automaton();
			writer.write(automaton.getRoot(HEAD),automaton);
			writer.flush();
			System.out.println("\n");
			for(int i=0;i!=state.size();++i) {
				AbstractActivation activation = state.activation(i);
				System.out.print("[" + i + "] ");
				print(activation,state.step(i));	
				System.out.println();
			}
			System.out.println("\nCurrent: " + HEAD + " (" + state.rank() + " / " + state.size() + " unvisited)");
		} catch(IOException e) { System.err.println("I/O error printing automaton"); }
	}
	
	private void print(AbstractActivation activation, Rewrite.Step step) {
		if(activation.rule() instanceof InferenceRule) {
			System.out.print("* ");
		}
		if(activation.rule().annotation("name") != null) {
			System.out.print(activation.rule().annotation("name"));
		}
		System.out.print(" #" + activation.target());
		if(step != null) {
			System.out.print(" (" + step.after() + ")");
		}
	}
	
	public void printLog() {
		List<Rewrite.Step> history = rewrite.steps();
		for(int i = 0;i!=history.size();++i) {
			System.out.print("[" + i + "] ");
			Rewrite.Step step = history.get(i);			
			int before = step.before();
			AbstractActivation activation = rewrite.states().get(before).activation(step.activation());
			int after = step.after();
			System.out.print(before + " => " + after);			
			System.out.println(" (" + activation.target() + ", " + activation.rule().annotation("name") + ")");
		}
	}		
	
	public void setIndent(String[] indents) {
		this.indents = indents;
	}
	
	public void setIndices(boolean indices) {
		this.indices = indices;
	}
	
	public void setCaching(boolean flag) {
		this.caching = flag;
	}
	
	public void setCollapse(boolean flag) {
		this.collapse = flag;
	}
	
	public void setLinear(boolean flag) {
		this.linear = flag;
	}
	
	public void loadRewrite(String input) throws Exception {
		FileReader reader = new FileReader(input);
		// THIS NEEDS TO BE FIXED!!
		startRewrite(reader,RwMode.INFER);
	}
	
	public void startReduce(String input) throws Exception {
		startRewrite(new StringReader(input),RwMode.REDUCE);
	}
	
	public void startInfer(String input) throws Exception {
		startRewrite(new StringReader(input),RwMode.INFER);
	}
	
	public void startRewrite(Reader input, RwMode mode) throws Exception {
		PrettyAutomataReader reader = new PrettyAutomataReader(input, schema);
		Automaton automaton = reader.read();
		rewrite = constructRewrite(schema,reductions,inferences,mode);
		rewriter = constructRewriter(schema);
		HEAD = rewrite.initialise(automaton);
		rewriter.reset(HEAD);
		print();
	}
	
	private Rewrite constructRewrite(final Schema schema, final ReductionRule[] reductions,
			InferenceRule[] inferences, RwMode mode) {
		if (mode == RwMode.INFER) {
			return new Inference(schema, null, inferences, reductions);
		} else {
			return new Reduction(schema, null, reductions);
		}
	}
	
	private Rewriter constructRewriter(final Schema schema) {
		return new LinearRewriter(rewrite,LinearRewriter.UNFAIR_HEURISTIC);		
	}
	
	private RewriteRule[] append(RewriteRule[] lhs, RewriteRule[] rhs) {
		RewriteRule[] rules = new RewriteRule[lhs.length+rhs.length];
		System.arraycopy(lhs, 0, rules, 0, lhs.length);
		System.arraycopy(rhs, 0, rules, lhs.length, rhs.length);
		return rules;
	}
	
	public void applyActivation(int activation) {
		// Yes, there is at least one activation left to try
		HEAD = rewrite.step(HEAD, activation);		
		print();
	}
	
	public void grind(int count) {
		rewriter.apply(count);
		print();
	}
	
	public void reset(int id) {
		HEAD = id;		
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
		final BufferedReader input = new BufferedReader(new InputStreamReader(
				System.in));

		try {
			System.out.println("Rewriter read/evaluate/print loop.");
			while (true) {
				System.out.print("> ");
				// Read the input line
				String line = input.readLine();
				// Attempt to execute the input line
				boolean isOK = execute(line);
				if(!isOK) {
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
	 * @param line
	 * @param railway
	 * @return
	 */
	public boolean execute(String line) {
		Command candidate = null;
		for (Command c : commands) {
			if(c.canMatch(line)) {
				if(candidate != null) {
					System.out.println("Ambiguos Command \"" + c.keyword);
				} else {
					candidate = c;
				}
			}
		}
		if(candidate != null) {
			Object[] args = candidate.match(line);
			if (args != null) {
				// Yes, this command was matched. Now, sanity check the
				// arguments.
				for (int i = 0; i != args.length; ++i) {
					if (args[i] == null) {
						// this indicates a problem converting this
						// argument, so report an error to the user.
						System.out.println("Command \"" + candidate.keyword
								+ "\": syntax error on argument " + (i+1));
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
			return ConsoleRewriter.class.getMethod(name, paramTypes);
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
				Object[] arguments = new Object[tokens.length-1];
				for(int i=1;i!=tokens.length;++i) {
					arguments[i-1] = convert(parameters[i-1],tokens[i]);
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
			if(parameter == boolean.class) {
				if(token.equals("off")) {
					return false;
				} else if(token.equals("on")) {
					return true;
				} else {
					return null;
				}
			} else if(parameter == int.class) {
				try {
					return Integer.parseInt(token);
				} catch(NumberFormatException e) {
					return null;
				}
			} else if(parameter == float.class) {
				try {
					return Float.parseFloat(token);
				} catch(NumberFormatException e) {
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
			} else if(parameter == String.class) {
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
}
