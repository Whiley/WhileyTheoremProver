package wyal.util;

import java.io.PrintWriter;
import java.util.BitSet;

import wyal.io.WyalFilePrinter;
import wyal.lang.Formula;
import wyal.lang.SyntacticHeap;
import wyal.lang.SyntacticItem;
import wyal.lang.WyalFile;
import wyal.lang.WyalFile.*;

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
		Formula root = Formulae.toFormula(SyntacticHeaps.clone(decl.getBody()),types);
		// Check whether or not this formula is valid.
		boolean valid = checkValidity(root);
		//
		if(!valid) {
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
	private boolean checkValidity(Formula formula) {
		SyntacticHeap heap = new StructurallyEquivalentHeap();
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
		formula = heap.allocate(formula);
		// Create initial state
		State state = new State(heap);
		// Assume the formula holds
		state.set(formula);
		//
		return checkUnsat(state,FALSE);
	}

	private boolean checkUnsat(State state, Formula.Truth FALSE) {
		// The following loop is *very* primitive in nature.
		for (int i = 0; i != state.size(); ++i) {
			Formula truth = state.get(i);
			if (truth instanceof Formula.Conjunct) {
				Formula.Conjunct conjunct = (Formula.Conjunct) truth;
				state.unset(conjunct);
				state.set(conjunct.getOperands());
				return checkUnsat(state, FALSE);
			} else if (truth instanceof Formula.Disjunct) {
				Formula.Disjunct disjunct = (Formula.Disjunct) truth;
				state.unset(disjunct);
				State[] splits = state.split(disjunct.getOperands());
				for (int j = 0; j != splits.length; ++j) {
					if (!checkUnsat(splits[j], FALSE)) {
						return false;
					}
				}
				return true;
			} else if (truth instanceof Formula.Quantifier){
				Formula.Quantifier quantifier = (Formula.Quantifier) truth;
				if(!quantifier.getSign()) {
					// existential
					state.unset(quantifier);
					state.set(quantifier.getBody());
					return checkUnsat(state, FALSE);
				}
			}
		}
		// If we get here, then we have a fully expanded state which contains
		// only primitive formulae.
		//
		// Apply congurence closure
		System.out.println("Applying congruence...");
		closeOverCongruence(state);
		// Apply transitive closure over inequalities
		System.out.println("Applying closure...");
		closeOverInequalities(state);
		// Done
		return state.contains(FALSE);
	}

	private void closeOverCongruence(State state) {
		boolean changed = true;
		while(changed) {
			changed=false;
			for (int i = 0; i != state.size(); ++i) {
				Formula ith = state.get(i);
				if (ith instanceof Formula.Equality) {
					Formula.Equality eq = (Formula.Equality) ith;
					if (eq.getSign()) {
						Pair<Identifier, Formula.Atom> substitution = Formulae.rearrangeForSubstitution(eq);
						changed |= applySubstitution(substitution,i,state);
					}
				}
			}
		}
	}

	private boolean applySubstitution(Pair<Identifier, Formula.Atom> substitution, int ignored, State state) {
		boolean nochange = true;

		if (substitution != null) {
			// We've found a suitable substitution
			for (int j = 0; j < state.size(); ++j) {
				Formula before = state.get(j);
				if (j != ignored && before != null) {
					Formula after = (Formula) Formulae.substitute(substitution, before);
					//
					if (before != after) {
						System.out.print("REWROTE: ");
						AutomatedTheoremProver.print(before);
						System.out.print(" -----> ");
						AutomatedTheoremProver.print(Formulae.simplify(after));
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
								inferred = state.allocate(inferred);
								System.out.print("INFERRED: ");println(inferred);
								nochange &= state.contains(inferred);
								state.set(inferred);
							}
						}
					}
				}
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
			for(int i=0;i!=truths.length;++i) {
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

	/**
	 * A simple helper method for debugging expressions which just prints them
	 * to stdout.
	 *
	 * @param item
	 */
	public static void println(WyalFile.Expr item) {
		print(item);
		System.out.println();
	}

	public static void print(WyalFile.Expr item) {
		PrintWriter out = new PrintWriter(System.out);
		new WyalFilePrinter(out).writeExpression(item);
		out.flush();
	}

	/**
	 * Check whether a given expression represents a contradiction (i.e. is
	 * false).
	 *
	 * @param item
	 * @return
	 */
	private static boolean isContradiction(WyalFile.Expr item) {
		if (item instanceof Expr.Constant) {
			Expr.Constant c = (Expr.Constant) item;
			Value.Bool b = (Value.Bool) c.getValue();
			return !b.get();
		}
		return false;
	}
}
