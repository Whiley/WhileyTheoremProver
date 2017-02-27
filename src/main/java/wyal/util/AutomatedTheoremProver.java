package wyal.util;

import java.io.PrintWriter;
import java.math.BigInteger;
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
import wybs.lang.SyntaxError;

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
		ArrayList<VerificationError> errors = new ArrayList<>();
		for (int i = 0; i != parent.size(); ++i) {
			SyntacticItem item = parent.getSyntacticItem(i);
			if (item instanceof WyalFile.Declaration.Assert) {
				WyalFile.Declaration.Assert ast = (WyalFile.Declaration.Assert) item;
				if (!check(ast)) {
					throw new SyntaxError("verification failure", parent.getEntry(), item);
				}
			}
		}
	}

	private boolean check(WyalFile.Declaration.Assert decl) {
		// Convert the body of the assertion into "expression form". That is,
		// where every node is an expression.
		Formula root = Formulae.toFormula(decl.getBody(), types);
		// Check whether or not this formula is valid.
		return checkValidity(decl.getParent(), root);
		//
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
		// Simplify the formula, since inversion does not do this.
		formula = Formulae.simplify(formula, types);
		// Allocate initial formula to the heap
		formula = heap.allocate(SyntacticHeaps.clone(formula));
		// Create initial state
		State state = new State(heap);
		// Assume the formula holds
		state.set(formula);
		//
		return checkUnsat(state, 0, FALSE);
	}

	private static final int MAX_DEPTH = 2;

	private boolean checkUnsat(State state, int depth, Formula.Truth FALSE) {
		print(depth, state);
		//
		if (state.contains(FALSE)) {
			return true;
		} else if (depth == MAX_DEPTH) {
			return false;
		} else {
			// The following loop is *very* primitive in nature.
			for (int i = 0; i != state.size(); ++i) {
				Formula truth = state.getActive(i);
				if (truth instanceof Formula.Conjunct) {
					Formula.Conjunct conjunct = (Formula.Conjunct) truth;
					state.subsume(conjunct, conjunct.getOperands());
					return checkUnsat(state, depth, FALSE);
				} else if (truth instanceof Formula.Disjunct) {
					Formula.Disjunct disjunct = (Formula.Disjunct) truth;
					state.subsume(disjunct);
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
						state.subsume(quantifier, quantifier.getBody());
						return checkUnsat(state, depth, FALSE);
					}
				} else if (truth instanceof Formula.Invoke) {
					// FIXME: this is broken in the case of recursive macros.
					// The reason for this is simply that it will expand forever
					// :)
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
					if (invariant != null) {
						if (!ivk.getSign()) {
							invariant = Formulae.invert(invariant);
						}
						// Update the state
						state.subsume(truth, state.allocate(invariant));
						return checkUnsat(state, depth, FALSE);
					}
				} else if (truth != null) {
					Formula invariant = generateImplicitAxioms(truth);
					if (invariant != null) {
						invariant = state.allocate(Formulae.simplify(invariant, types));
						if (!state.contains(invariant)) {
							state.set(invariant);
							return checkUnsat(state, depth, FALSE);
						}
					}
					//
					Expr split = findSplitPoint(truth);
					if(split != null) {
						Formula[] cases = generateSplitCases(split,truth);
						Formula disjunct = state.allocate(Formulae.simplify(new Formula.Disjunct(cases),types));
						state.subsume(truth, disjunct);
						return checkUnsat(state, depth, FALSE);
					}
				}
			}
			// If we get here, then we have a fully expanded state which
			// contains
			// only primitive formulae.
			//
			boolean change = true;
			int count = 5;
			while (change && !state.contains(FALSE)) {
				change = false;
				// Apply congruence closure
				change |= closeOverCongruence(state, FALSE);
				// Apply transitive closure over inequalities
				change |= closeOverInequalities(state, FALSE);
				//
				if (count-- == 0) {
					throw new IllegalArgumentException("trip count reached");
				}
			}
			// Instantiate any quantified formulae
			instantiateUniversalQuantifiers(state);
			// Done
			return checkUnsat(state, depth + 1, FALSE);
		}
	}

	/**
	 * A split point is a subexpression which can be divided into two or more
	 * "options". For example, the expression <code>xs[i:=0][j] >= 0</code> is
	 * broken down into
	 * <code>(j == i && 0 >= 0) || (j != i && xs[j] >= 0)</code>.
	 *
	 * @param e
	 * @return
	 */
	private Expr findSplitPoint(Expr e) {
		switch (e.getOpcode()) {
		case EXPR_arridx: {
			if (e.getOperand(0).getOpcode() == Opcode.EXPR_arrupdt) {
				// This represents a split point.
				return e;
			}
		}
		}
		// Generic traversal, returning first split point encountered.
		for (int i = 0; i != e.size(); ++i) {
			SyntacticItem item = e.getOperand(i);
			if (item instanceof Expr) {
				Expr cf = findSplitPoint((Expr) item);
				if (cf != null) {
					return cf;
				}
			}
		}
		// No split points found
		return null;
	}

	private Formula[] generateSplitCases(Expr split, Formula truth) {
		Formula[] result;
		switch(split.getOpcode()) {
		case EXPR_arridx: {
			// xs[i:=v][j]
			Expr.Operator src = (Expr.Operator) split.getOperand(0);
			Expr xs = src.getOperand(0);
			Expr.Polynomial i = (Expr.Polynomial) src.getOperand(1);
			Expr v = src.getOperand(2);
			Expr.Polynomial j = (Expr.Polynomial) split.getOperand(1);
			result = new Formula[2];
			Formula case1 = (Formula) Formulae.substitute(split, v, truth);
			Formula case2 = (Formula) Formulae.substitute(split, new Expr.Operator(Opcode.EXPR_arridx, xs, j), truth);
			result[0] = Formulae.and(new Formula.ArithmeticEquality(true, i, j), case1);
			result[1] = Formulae.and(new Formula.ArithmeticEquality(false, i, j), case2);
			break;
		}
		default:
			throw new IllegalArgumentException("unknown split kind encountered");
		}
		return result;
	}

	private Formula generateImplicitAxioms(Expr e) {
		Formula axiom = null;
		switch (e.getOpcode()) {
		case EXPR_invoke: {
			Expr.Invoke ivk = (Expr.Invoke) e;
			// Determine the type declaration in question
			Type.AbstractFunction af = ivk.getSignatureType();
			// FIXME: this resolution should have already been performed
			// elsewhere
			Declaration.Named decl = types.resolveAsDeclaration(ivk.getName());
			Declaration.Named.Function md = (Declaration.Named.Function) decl;
			VariableDeclaration[] params = md.getParameters().getOperands();
			VariableDeclaration[] returns = md.getReturns().getOperands();
			if (returns.length > 1) {
				throw new IllegalArgumentException("problem");
			} else {
				axiom = Formulae.extractTypeInvariant(returns[0].getType(), e, types);
			}
			break;
		}
		case EXPR_arridx: {
			Expr.Operator idx = (Expr.Operator) e;
			Expr src = idx.getOperand(0);
			Polynomial index = Formulae.toPolynomial(idx.getOperand(1));
			Polynomial srclen = Formulae.toPolynomial(new Expr.Operator(Opcode.EXPR_arrlen, src));
			Formula.Inequality lb = new Formula.Inequality(true, index, srclen);
			Formula.Inequality gb = new Formula.Inequality(false, index, new Polynomial(BigInteger.ZERO));
			axiom = new Formula.Conjunct(lb, gb);
			break;
		}
		case EXPR_div: {
			Expr.Operator op = (Expr.Operator) e;
			axiom = new Formula.Equality(false, op.getOperand(1), new Expr.Constant(new Value.Int(0)));
			break;
		}
		}
		//
		for (int i = 0; i != e.size(); ++i) {
			SyntacticItem item = e.getOperand(i);
			if (item instanceof Expr) {
				Formula cf = generateImplicitAxioms((Expr) item);
				if (cf != null) {
					axiom = axiom == null ? cf : new Formula.Conjunct(axiom, cf);
				}
			}
		}
		return axiom;
	}

	private Formula extractDeclarationInvariant(Declaration.Named decl, Tuple<Expr> arguments) {
		if (decl instanceof Declaration.Named.Type) {
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
		return Formulae.simplify(body, types);
	}

	private Formula expandTypeInvariant(Declaration.Named.Type td, Expr argument) {
		// Extract only the explicit invariants given using where clauses.
		Tuple<Block> invariant = td.getInvariant();
		Formula result = Formulae.extractTypeInvariant(td.getVariableDeclaration().getType(), argument, types);
		for (int i = 0; i != invariant.size(); ++i) {
			// Convert the invariant clause into a formula
			Formula ith = Formulae.toFormula(invariant.getOperand(i), types);
			//
			result = result == null ? ith : new Formula.Conjunct(result, ith);
		}
		if (result == null) {
			return null;
		} else {
			// At this point, we must substitute the variable name used in
			// the type declaration for the name used as the invocation
			// argument.
			Expr.VariableAccess parameter = new Expr.VariableAccess(td.getVariableDeclaration());
			result = (Formula) Formulae.substitute(parameter, argument, result);
			return Formulae.simplify(result, types);
		}
	}

	private boolean closeOverCongruence(State state, Formula.Truth FALSE) {
		int size = state.size();
		boolean changed = false;
		for (int i = 0; i != size && !state.contains(FALSE); ++i) {
			Formula ith = state.getActive(i);
			if (ith instanceof Formula.Equality) {
				Formula.Equality eq = (Formula.Equality) ith;
				if (eq.getSign()) {
					Pair<Expr, Expr> substitution = Formulae.rearrangeForSubstitution(eq);
					changed |= applySubstitution(substitution, i, state, FALSE);
				}
			}
		}
		return changed;
	}

	private boolean applySubstitution(Pair<Expr, Expr> substitution, int ignored, State state, Formula.Truth FALSE) {
		boolean nochange = true;

		if (substitution != null) {
			// We've found a suitable substitution
			AutomatedTheoremProver.print(substitution.getFirst());
			System.out.print(" ==> ");
			AutomatedTheoremProver.print(substitution.getSecond());
			System.out.println();
			for (int j = 0; j < state.size() && !state.contains(FALSE); ++j) {
				Formula before = state.getActive(j);
				if (j != ignored && before != null) {
					System.out.print("SUBSTITUTING: ");
					AutomatedTheoremProver.print(before);
					System.out.print("[" );
					AutomatedTheoremProver.print(substitution.getFirst());
					System.out.print(" / " );
					AutomatedTheoremProver.print(substitution.getSecond());
					System.out.print("] ==> ");
					Formula after = (Formula) Formulae.substitute(substitution.getFirst(), substitution.getSecond(),
							before);
					AutomatedTheoremProver.println(after);
					//
					if (before != after) {
						after = state.allocate(Formulae.simplify(after, types));
						nochange &= state.contains(after);
						state.subsume(before, after);
					}
				}
			}
		}
		return !nochange;
	}

	private boolean closeOverInequalities(State state, Formula.Truth FALSE) {
		boolean change = false;
		int size = state.size();
		//
		for (int i = 0; i != size; ++i) {
			Formula ith = state.getActive(i);
			if (ith instanceof Formula.Inequality) {
				Formula.Inequality ith_ieq = (Formula.Inequality) ith;
				for (int j = i + 1; j != size; ++j) {
					Formula jth = state.getActive(j);
					if (jth instanceof Formula.Inequality) {
						Formula.Inequality jth_ieq = (Formula.Inequality) jth;
						Formula inferred = Formulae.closeOver(ith_ieq, jth_ieq, types);
						if (inferred != null) {
							inferred = state.allocate(inferred);
							change |= !state.contains(inferred);
							if (inferred instanceof Formula.Equality) {
								state.subsume(ith, inferred);
								state.subsume(jth, inferred);
								break;
							} else {
								state.set(inferred);
							}
						}
					}
				}
			}
		}
		return change;
	}

	private void instantiateUniversalQuantifiers(State state) {
		Expr[] grounds = determineGroundTerms(state);

		for (int i = 0; i != state.size(); ++i) {
			Formula ith = state.getActive(i);
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
			Formula ith = state.getActive(i);
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
			if (child instanceof Expr) {
				extractGrounds((Expr) child, grounds);
			}
		}
		if (e instanceof Polynomial) {
			grounds.add(e);
		}
	}

	private void instantiateUniversalQuantifier(Formula.Quantifier qf, Expr[] binding, Expr[] grounds, State state) {
		VariableDeclaration[] parameters = qf.getParameters().getOperands();
		if (parameters.length == binding.length) {
			// Binding now complete, so proceed to instantiate quantifier.
			// First, substitute body through for the binding obtained for each
			// parameter.
			Formula body = qf.getBody();
			// FIXME: there is a bug of sorts here related to skolems
			String dbg = "";
			for (int i = 0; i != parameters.length; ++i) {
				VariableDeclaration parameter = parameters[i];
				// FIXME: I'm assuming integer only quantification!!
				dbg += ("[" + parameter.getVariableName() + " / ??? ]");
				Expr.VariableAccess access = new Expr.VariableAccess(parameter);
				body = (Formula) Formulae.substitute(access, binding[i], body);
			}
			// Second, instantiate the ground body
			body = state.allocate(Formulae.simplify(body, types));
			if (!state.contains(body)) {
				state.set(body);
			}
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
		/**
		 * The set of all known truths, including those which are subsumed.
		 * Always a superset of activeTruths.
		 */
		private final BitSet allTruths;
		/**
		 * The set of all known truths, excluding those which are subsumed.
		 * Always a subset of allTruths.
		 */
		private final BitSet activeTruths;

		public State(SyntacticHeap heap) {
			this.heap = heap;
			this.allTruths = new BitSet();
			this.activeTruths = new BitSet();
		}

		public State(State state) {
			this.heap = state.heap;
			this.allTruths = (BitSet) state.allTruths.clone();
			this.activeTruths = (BitSet) state.activeTruths.clone();
		}

		public int size() {
			return activeTruths.length();
		}

		public SyntacticHeap getHeap() {
			return heap;
		}

		/**
		 * Determine whether a given truth is known or not.
		 *
		 * @param truth
		 * @return
		 */
		public boolean contains(Formula truth) {
			return allTruths.get(truth.getIndex());
		}

		public Formula getActive(int index) {
			if (activeTruths.get(index)) {
				return (Formula) heap.getSyntacticItem(index);
			} else {
				return null;
			}
		}

		/**
		 * Subume one formula with one or more formulae. This implication is
		 * that latter "cover" the former. The former is no longer active,
		 * though it remains a known truth. The new formula are active.
		 *
		 * @param from
		 * @param to
		 */
		public void subsume(Formula from, Formula... tos) {
			final int fromIndex = from.getIndex();
			activeTruths.clear(fromIndex);
			for (int i = 0; i != tos.length; ++i) {
				final int toIndex = tos[i].getIndex();
				allTruths.set(toIndex);
				activeTruths.set(toIndex);
			}
		}

		public void set(Formula truth) {
			final int index = truth.getIndex();
			allTruths.set(index);
			activeTruths.set(index);
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
		System.out.println("*** STATE ***");
		print(indent, state);
		System.out.println();
	}

	public static void print(int indent, State state) {
		for (int i = 0; i != state.size(); ++i) {
			Formula ith = state.getActive(i);
			if (ith != null) {
				// println(indent,ith);
				print(indent, ith);
				System.out.println(" " + ith.getIndex());
			}
		}
	}

	public static void println(int indent, Formula f) {
		print(indent, f);
		System.out.println();
	}

	public static void print(int indent, Formula f) {
		if (f instanceof Formula.Conjunct) {
			Formula.Conjunct conjunct = (Formula.Conjunct) f;
			for (int i = 0; i != conjunct.size(); ++i) {
				println(indent, conjunct.getOperand(i));
			}
		} else if (f instanceof Formula.Disjunct) {
			Formula.Disjunct disjunct = (Formula.Disjunct) f;
			for (int i = 0; i != disjunct.size(); ++i) {
				if (i != 0) {
					System.out.println("==========");
				}
				println(indent + 1, disjunct.getOperand(i));
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
		for (int i = 0; i != items.length; ++i) {
			if (i != 0) {
				out.print(", ");
			}
			printer.writeExpression(items[i]);
		}
		out.flush();
	}

	public static void tab(int indent) {
		for (int i = 0; i != indent; ++i) {
			System.out.print("\t");
		}
	}
}
