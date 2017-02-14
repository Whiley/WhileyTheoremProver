package wyal.util;

import java.io.PrintWriter;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.BitSet;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import wyal.io.WyalFilePrinter;
import wyal.lang.Formula;
import wyal.lang.SyntacticHeap;
import wyal.lang.SyntacticItem;
import wyal.lang.WyalFile;
import wyal.lang.WyalFile.*;
import wyal.lang.WyalFile.Expr.Polynomial;
import wyal.lang.WyalFile.Stmt.Block;

public class AutomatedTheoremProver {
	/**
	 * The type system encapsulates the core algorithms for type simplification
	 * and subtyping testing.
	 */
	private final TypeSystem types;
	/**
	 * The enclosing WyAL file being checked.
	 */
	private final WyalFile parent;

	public AutomatedTheoremProver(final WyalFile parent) {
		this.parent = parent;
		// FIXME: this should be shared between different compilation stages
		this.types = new TypeSystem(parent);
	}

	public void check() {
		for (int i = 0; i != parent.size(); ++i) {
			SyntacticItem item = parent.getSyntacticItem(i);
			if (item instanceof WyalFile.Declaration.Assert) {
				check((WyalFile.Declaration.Assert) item);
			}
		}
	}

	private void check(WyalFile.Declaration.Assert decl) {
		// Convert the body of the assertion into "expression form". That is,
		// where every node is an expression.
		Formula root = Formulae.toFormula(decl.getBody(), types);
		// Check whether or not this formula is valid.
		boolean valid = checkValidity(decl.getParent(), root);
		//
		if (!valid) {
			// FIXME: throw proper error here
			throw new IllegalArgumentException("Verification error!");
		}
	}

	/**
	 * Check whether a given formula is unsatisfiable or not. That is, whether
	 * or not it can be reduces to false.
	 *
	 * @param formula
	 * @return
	 */
	private boolean checkValidity(SyntacticHeap parent, Formula formula) {
		SyntacticHeap heap = new StructurallyEquivalentHeap(parent);
		Formula.Truth FALSE = heap.allocate(new Formula.Truth(false));
		// Invert the body of the assertion in order to perform a
		// "proof-by-contradiction".
		formula = Formulae.invert(formula);
		println(formula);
		System.out.println("--------------------------");
		// Simplify the formula, since inversion does not do this.
		formula = Formulae.simplify(formula);
		println(formula);
		System.out.println("--------------------------");
		// Allocate initial formula to the heap
		formula = heap.allocate(SyntacticHeaps.clone(formula));
		// Create initial state
		State state = new State(heap);
		// Assume the formula holds
		state.set(formula);
		//
		System.out.println("==== BEGIN CHECK UNSAT ====");
		return checkUnsat(state, 0, FALSE);
	}

	private static final int MAX_DEPTH=2;

	private boolean checkUnsat(State state, int depth, Formula.Truth FALSE) {
		println(depth,state);
		if(state.contains(FALSE)) {
			System.out.println("FALSE");
			return true;
		} else if(depth == MAX_DEPTH) {
			return false;
		} else {
			// The following loop is *very* primitive in nature.
			for (int i = 0; i != state.size(); ++i) {
				Formula truth = state.get(i);
				if (truth instanceof Formula.Conjunct) {
					Formula.Conjunct conjunct = (Formula.Conjunct) truth;
					state.unset(conjunct);
					state.set(conjunct.getOperands());
					return checkUnsat(state, depth, FALSE);
				} else if (truth instanceof Formula.Disjunct) {
					Formula.Disjunct disjunct = (Formula.Disjunct) truth;
					state.unset(disjunct);
					State[] splits = state.split(disjunct.getOperands());
					for (int j = 0; j != splits.length; ++j) {
						if (!checkUnsat(splits[j], depth, FALSE)) {
							return false;
						}
					}
					return true;
				} else if (truth instanceof Formula.Quantifier) {
					Formula.Quantifier quantifier = (Formula.Quantifier) truth;
					if (!quantifier.getSign()) {
						// existential
						state.unset(quantifier);
						state.set(quantifier.getBody());
						return checkUnsat(state, depth, FALSE);
					}
				} else if (truth instanceof Formula.Invoke) {
					// FIXME: this is broken in the case of recursive macros.
					// The reason for this is simply that it will expand forever :)
					// FIXME: also broken because assume this is a type
					// invariant invocation
					Formula.Invoke ivk = (Formula.Invoke) truth;
					// Determine the type declaration in question
					Type.AbstractFunction af = ivk.getSignatureType();
					// FIXME: this resolution should have already been performed
					// elsewhere
					Declaration.Named decl = types.resolveAsDeclaration(ivk.getName());
					// Calculate the invariant
					Formula invariant = extractDeclarationInvariant(decl, ivk.getArguments());
					if (!ivk.getSign()) {
						invariant = Formulae.invert(invariant);
					}
					// Update the state
					// FIXME: this should be a subsume operation, since
					// otherwise we end up repeating ourselves a lot.
					state.unset(truth);
					state.set(state.allocate(invariant));
					return checkUnsat(state, depth, FALSE);
				}
			}
			// If we get here, then we have a fully expanded state which
			// contains
			// only primitive formulae.
			//
			// Apply congruence closure
			closeOverCongruence(state);
			// Apply transitive closure over inequalities
			closeOverInequalities(state);
			// Instantiate any quantified formulae
			instantiateUniversalQuantifiers(state);
			// Done
			return checkUnsat(state, depth + 1, FALSE);
		}
	}

	private Formula extractDeclarationInvariant(Declaration.Named decl, Tuple<Expr> arguments) {
		if(decl instanceof Declaration.Named.Type) {
			// This is a type invariant macro call. In such case, we
			// need to first determine what the invariant actually is.
			Declaration.Named.Type td = (Declaration.Named.Type) decl;
			// Expand the corresponding type invariant
			return expandTypeInvariant(td, arguments.getOperand(0));
		} else {
			Declaration.Named.Macro md = (Declaration.Named.Macro) decl;
			// Expand the macro body with appropriate substitutions
			return expandMacroBody(md, arguments.getOperands());
		}
	}

	private Formula expandMacroBody(Declaration.Named.Macro md, Expr[] arguments) {
		VariableDeclaration[] parameters = md.getParameters().getOperands();
		Formula body = Formulae.toFormula(md.getBody(), types);
		for (int i = 0; i != arguments.length; ++i) {
			// At this point, we must substitute the parameter name used in
			// the type declaration for the name used as the invocation
			// argument.
			Expr.VariableAccess parameter = new Expr.VariableAccess(parameters[i]);
			body = (Formula) Formulae.substitute(parameter, arguments[i], body);
		}
		return Formulae.simplify(body);
	}

	private Formula expandTypeInvariant(Declaration.Named.Type td, Expr argument) {
		// Extract only the explicit invariants given using where clauses.
		Tuple<Block> invariant = td.getInvariant();
		Formula result = null;
		for (int i = 0; i != invariant.size(); ++i) {
			// Convert the invariant clause into a formula
			Formula ith = Formulae.toFormula(invariant.getOperand(i), types);
			//
			result = i == 0 ? ith : new Formula.Conjunct(result, ith);
		}
		// At this point, we must substitute the variable name used in
		// the type declaration for the name used as the invocation
		// argument.
		Expr.VariableAccess parameter = new Expr.VariableAccess(td.getVariableDeclaration());
		result = (Formula) Formulae.substitute(parameter, argument, result);
		return Formulae.simplify(result);
	}

	private void closeOverCongruence(State state) {
		int count = 10;
		boolean changed = true;
		while (changed) {
			changed = false;
			for (int i = 0; i != state.size(); ++i) {
				Formula ith = state.get(i);
				if (ith instanceof Formula.Equality) {
					Formula.Equality eq = (Formula.Equality) ith;
					if (eq.getSign()) {
						Pair<Expr, Expr> substitution = Formulae.rearrangeForSubstitution(eq);
						changed |= applySubstitution(substitution, i, state);
						if(--count == 0) {
							throw new RuntimeException("trip count reached");
						}
					}
				}
			}
		}
	}

	private boolean applySubstitution(Pair<Expr, Expr> substitution, int ignored, State state) {
		boolean nochange = true;

		if (substitution != null) {
			// We've found a suitable substitution
			for (int j = 0; j < state.size(); ++j) {
				Formula before = state.get(j);
				if (j != ignored && before != null) {
					Formula after = (Formula) Formulae.substitute(substitution.getFirst(), substitution.getSecond(),
							before);
					//
					if (before != after) {
						System.out.print("REWROTE: ");
						AutomatedTheoremProver.print(before);
						System.out.print(" -----> ");
						AutomatedTheoremProver.println(Formulae.simplify(after));
						println(0,state);
					}
					if (before != after) {
						state.unset(before);
						after = state.allocate(Formulae.simplify(after));
						nochange &= state.contains(after);
						state.set(after);
					}
				}
			}
		}
		return !nochange;
	}

	private void closeOverInequalities(State state) {
		boolean nochange = false;
		int count = 50;
		while (!nochange) {
			nochange = true;
			//
			for (int i = 0; i != state.size(); ++i) {
				Formula ith = state.get(i);
				if (ith instanceof Formula.Inequality) {
					Formula.Inequality ith_ieq = (Formula.Inequality) ith;
					for (int j = i + 1; j != state.size(); ++j) {
						Formula jth = state.get(j);
						if (jth instanceof Formula.Inequality) {
							Formula.Inequality jth_ieq = (Formula.Inequality) jth;
							Formula inferred = Formulae.closeOver(ith_ieq, jth_ieq);
							if (inferred != null) {
								if(--count == 0) {
									throw new RuntimeException("trip count reached");
								}
								inferred = state.allocate(inferred);
								System.out.print("INFERRED: ");
								println(inferred);
								nochange &= state.contains(inferred);
								state.set(inferred);
							}
						}
					}
				}
			}
		}
	}

	private void instantiateUniversalQuantifiers(State state) {
		Expr[] grounds = determineGroundTerms(state);
		System.out.print("GROUNDS: ");
		println(grounds);
		for (int i = 0; i != state.size(); ++i) {
			Formula ith = state.get(i);
			if (ith instanceof Formula.Quantifier) {
				Formula.Quantifier qf = (Formula.Quantifier) ith;
				if (qf.getSign()) {
					// This is a universal quantifier
					instantiateUniversalQuantifier(qf, new Expr[0], grounds, state);
				}
			}
		}
	}

	private Expr[] determineGroundTerms(State state) {
		HashSet<Expr> grounds = new HashSet<>();
		for (int i = 0; i != state.size(); ++i) {
			Formula ith = state.get(i);
			if (ith instanceof Formula.Equality || ith instanceof Formula.Inequality) {
				Expr lhs = (Expr) ith.getOperand(0);
				Expr rhs = (Expr) ith.getOperand(1);
				extractGrounds(lhs, grounds);
				extractGrounds(rhs, grounds);
			}
		}
		return grounds.toArray(new Expr[grounds.size()]);
	}

	private void extractGrounds(Expr e, Set<Expr> grounds) {
		for (int i = 0; i != e.size(); ++i) {
			SyntacticItem child = e.getOperand(i);
			if(child instanceof Expr) {
				extractGrounds((Expr) child, grounds);
			}
		}
		if(e instanceof Polynomial) {
			grounds.add(e);
		}
	}

	private void instantiateUniversalQuantifier(Formula.Quantifier qf, Expr[] binding, Expr[] grounds,
			State state) {
		VariableDeclaration[] parameters = qf.getParameters().getOperands();
		if (parameters.length == binding.length) {
			// Binding now complete, so proceed to instantiate quantifier.
			// First, substitute body through for the binding obtained for each
			// parameter.
			Formula body = qf.getBody();
			// FIXME: there is a bug of sorts here related to skolems
			System.out.print("INSTANTIATING: ");
			for (int i = 0; i != parameters.length; ++i) {
				VariableDeclaration parameter = parameters[i];
				// FIXME: I'm assuming integer only quantification!!
				System.out.print("[" + parameter.getVariableName() + " / ");
				print(binding[i]);
				System.out.print("]");
				Expr.VariableAccess access = new Expr.VariableAccess(parameter);
				body = (Formula) Formulae.substitute(access, binding[i], body);
			}
			// Second, instantiate the ground body
			System.out.print(" ");
			print(qf.getBody());
			body = state.allocate(Formulae.simplify(body));
			System.out.print(" ===> ");
			println(body);
			state.set(body);
		} else {
			// Exhaustively instantiate this variable with all possible ground
			// terms.
			for (int i = 0; i != grounds.length; ++i) {
				Expr[] nBinding = Arrays.copyOf(binding, binding.length + 1);
				nBinding[binding.length] = grounds[i];
				instantiateUniversalQuantifier(qf, nBinding, grounds, state);
			}
		}
	}

	private static class State {
		private final SyntacticHeap heap;
		private final BitSet truths;

		public State(SyntacticHeap heap) {
			this.heap = heap;
			this.truths = new BitSet();
		}

		public State(State state) {
			this.heap = state.heap;
			this.truths = (BitSet) state.truths.clone();
		}

		public int size() {
			return truths.length();
		}

		public SyntacticHeap getHeap() {
			return heap;
		}

		public boolean contains(Formula truth) {
			return truths.get(truth.getIndex());
		}

		public Formula get(int index) {
			if (truths.get(index)) {
				return (Formula) heap.getSyntacticItem(index);
			} else {
				return null;
			}
		}

		public void set(Formula truth) {
			final int index = truth.getIndex();
			truths.set(index);
		}

		public void set(Formula... truths) {
			for (int i = 0; i != truths.length; ++i) {
				this.truths.set(truths[i].getIndex());
			}
		}

		public void unset(Formula formula) {
			this.truths.clear(formula.getIndex());
		}

		public State[] split(Formula... cases) {
			State[] result = new State[cases.length];
			for (int i = 0; i != cases.length; ++i) {
				State child = new State(this);
				result[i] = child;
				child.set(cases[i]);
			}
			return result;
		}

		public Formula allocate(Formula f) {
			return heap.allocate(f);
		}
	}

	public static void println(int indent, State state) {
		print(indent,state);
		System.out.println();
	}

	public static void print(int indent, State state) {
		for(int i=0;i!=state.size();++i) {
			Formula ith = state.get(i);
			if(ith != null) {
				println(indent,ith);
			}
		}
	}
	public static void println(int indent, Formula f) {
		print(indent,f);
		System.out.println();
	}
	public static void print(int indent, Formula f) {
		if(f instanceof Formula.Conjunct) {
			Formula.Conjunct conjunct = (Formula.Conjunct) f;
			for(int i=0;i!=conjunct.size();++i) {
				println(indent, conjunct.getOperand(i));
			}
		} else if(f instanceof Formula.Disjunct) {
			Formula.Disjunct disjunct = (Formula.Disjunct) f;
			for(int i=0;i!=disjunct.size();++i) {
				if(i != 0) {
					System.out.println("==========");
				}
				println(indent+1, disjunct.getOperand(i));
			}
		} else {
			tab(indent);
			print(f);
		}
	}

	/**
	 * A simple helper method for debugging expressions which just prints them
	 * to stdout.
	 *
	 * @param item
	 */
	public static void println(WyalFile.Expr... items) {
		print(items);
		System.out.println();
	}

	public static void print(WyalFile.Expr... items) {
		PrintWriter out = new PrintWriter(System.out);
		WyalFilePrinter printer = new WyalFilePrinter(out);
		for(int i=0;i!=items.length;++i) {
			if(i != 0) {
				out.print(", ");
			}
			printer.writeExpression(items[i]);
		}
		out.flush();
	}

	public static void tab(int indent) {
		for(int i=0;i!=indent;++i) {
			System.out.print("\t");
		}
	}
}
