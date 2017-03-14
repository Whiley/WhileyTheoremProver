package wyal.util;

import java.io.PrintWriter;
import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.BitSet;
import java.util.HashSet;
import java.util.IdentityHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

import wyal.io.ProofPrinter;
import wyal.io.WyalFilePrinter;
import wyal.lang.Formula;
import wyal.lang.Proof;
import wyal.lang.SyntacticHeap;
import wyal.lang.SyntacticItem;
import wyal.lang.WyalFile;
import wyal.lang.WyalFile.*;
import wyal.lang.WyalFile.Expr.Polynomial;
import wyal.lang.WyalFile.Stmt.Block;
import wyal.util.AbstractProof.AbstractStep;
import wyal.util.BitSetProof.State;
import wybs.lang.SyntaxError;
import wyfs.lang.Path;

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

	public void check(Path.Entry<?> originalSource) {
		ArrayList<VerificationError> errors = new ArrayList<>();
		for (int i = 0; i != parent.size(); ++i) {
			SyntacticItem item = parent.getSyntacticItem(i);
			if (item instanceof WyalFile.Declaration.Assert) {
				WyalFile.Declaration.Assert ast = (WyalFile.Declaration.Assert) item;
				if (!check(ast)) {
					throw new SyntaxError(ast.getMessage(), originalSource, item);
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
		formula = Formulae.simplifyFormula(formula, types);
		// Allocate initial formula to the heap
		formula = heap.allocate(SyntacticHeaps.clone(formula));
//		println(formula);
		// Create initial state
		BitSetProof proof = new BitSetProof(null, heap, formula);
		State state = proof.getStep(0);
		//
		boolean r = checkUnsat(state, 0, FALSE);
//		System.out.println("******************* PROOF (" + formula.getIndex() + ") ******************");
//		print(proof);
		return r;
	}

	private static final int MAX_DEPTH = 100;

	private boolean checkUnsat(State state, int depth, Formula.Truth FALSE) {
		//
		if (depth >= MAX_DEPTH) {
			throw new IllegalArgumentException("Max depth reached");
			//return false;
		} else {
			State original;
			// The following loop is *very* primitive in nature. Basically it
			// keeps going in a "fair" fashion ensuring that all rules get a
			// chance to be activated.
			int trip = 10;

			do {
				original = state;
				int innerTrip = 5;
				State local;
				do {
					local = state;
					// Apply transitive closure over inequalities
					state = closeOverInequalities(state, FALSE);
					// Apply all simple linear rules
					for (int i = 0; i != original.size() && !state.contains(FALSE); ++i) {
						Formula truth = state.getActive(i);
						state = applyLinearRules(truth, state);
					}
				} while(local != state && !state.contains(FALSE) && --innerTrip > 0);
				//
				// Apply split rule for disjuncts. Do this after linear rules
				// because splitting is potentially expensive.
				for (int i = 0; i != state.size() && !state.contains(FALSE); ++i) {
					Formula truth = state.getActive(i);
					if (truth instanceof Formula.Disjunct) {
						return applySplitDisjunct((Formula.Disjunct) truth, state, depth, FALSE);
					}
				}
				// Apply quantifier instantiation. We do this after the other
				// options because it is really expensive.
				for (int i = 0; i != local.size() && !state.contains(FALSE); ++i) {
					Formula truth = state.getActive(i);
					if (truth instanceof Formula.Quantifier) {
						state = applyQuantifierInstantiation((Formula.Quantifier) truth, state);
					}
				}
			} while (original != state && !state.contains(FALSE) && --trip > 0);
			//
			return state.contains(FALSE);
		}
	}

	private State applyLinearRules(Formula truth, State state) {
		if (truth == null) {
			return state;
		} else {
			switch (truth.getOpcode()) {
			case EXPR_or:
				// disjunctions are a special case because they are non-linear.
				return state;
			case EXPR_and:
				state = applyFlatternConjunct((Formula.Conjunct) truth, state);
				break;
			case EXPR_forall:
			case EXPR_exists:
				//state = applyQuantifierInstantiation((Formula.Quantifier) truth, state);
				return state;
				//break;
			case EXPR_invoke:
				state = applyExpandInvocation((Formula.Invoke) truth, state);
				break;
			case EXPR_eq:
				state = applyCongruenceClosure((Formula.Equality) truth, state);
				break;
			}
			// Apply generic rules
			state = applyImplicitAxioms(truth, state);
			return applyCaseSplitters(truth, state);
		}
	}

	// ===========================================================================
	// Apply split disjunct
	// ===========================================================================

	private boolean applySplitDisjunct(Formula.Disjunct disjunct, State state, int depth, Formula.Truth FALSE) {
		// Split the disjunct into multiple states where, on each, exactly one
		// of the clauses is asserted.
		State[] splits = state.split(disjunct);
		// Now, try to find a contradiction for each case
		for (int j = 0; j != splits.length; ++j) {
			State split = splits[j];
			if (!checkUnsat(split, depth + splits.length, FALSE)) {
				// Unable to find a proof down this branch, therefore done.
				return false;
			} else {
				// We did find a proof for this branch. At this point, we need
				// to analyse the proof and see whether or not this disjunct
				// actually had a part to play or not. If not, then we can
				// terminate this disjunct early (which can lead to significant
				// reductions in the state space).
				BitSet cone = split.getDependencyCone();
				//
				if(cone.get(disjunct.getIndex()) == false) {
					// The disjunct is not relevant to this proof. Therefore, we
					// can bypass the remainder.

					// FIXME: implement actual bypass!

//					System.out.print("FOUND BYPASS: ");
//					println(disjunct);
					break;
				}
			}
		}
		return true;
	}

	// ===========================================================================
	// Apply flatten conjunct
	// ===========================================================================

	private State applyFlatternConjunct(Formula.Conjunct conjunct, State state) {
		return state.subsume("and", conjunct, conjunct.getOperands());
	}

	// ===========================================================================
	// Apply case splitters
	// ===========================================================================

	/**
	 * "Case splitters" are situations where we can reduce a given formula to a
	 * number of distinct cases to explore. We can think these (in some sense)
	 * as being like applying "guesses" to make further progress. As an example,
	 * the formula <code>[1,2][i] >= 0</code> leads to a "case split",
	 * corresponding to <code>(i == 0 && 1 >= 0) || (i == 1 && 2 >= 0)</code>.
	 * In some sense, a case split occurs when we've narrowed the options down
	 * so much that there is a finite number of choices remaining. Therefore, we
	 * can make progress simply by enumerating these choices.
	 *
	 * @param truth
	 * @param state
	 * @return
	 */
	private State applyCaseSplitters(Formula truth, State state) {
		Expr split = findSplitPoint(truth);
		if (split != null) {
			Formula[] cases = generateSplitCases(split, truth);
			Formula disjunct = state.allocate(Formulae.simplifyDisjunct(new Formula.Disjunct(cases), types));
			state = state.subsume("reduct", truth, disjunct);
		}
		return state;
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
			} else if (e.getOperand(0).getOpcode() == Opcode.EXPR_arrinit) {
				return e;
			}
		}
		case EXPR_forall:
			// Don't extract case splitters from quantified formulae. There's
			// no point until they are instantiated!
			return null;
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
		switch (split.getOpcode()) {
		case EXPR_arridx: {
			Expr.Operator src = (Expr.Operator) split.getOperand(0);
			Expr.Polynomial j = (Expr.Polynomial) split.getOperand(1);
			if (src.getOpcode() == Opcode.EXPR_arrupdt) {
				// xs[i:=v][j]
				Expr xs = src.getOperand(0);
				Expr.Polynomial i = (Expr.Polynomial) src.getOperand(1);
				Expr v = src.getOperand(2);
				result = new Formula[2];
				Formula case1 = (Formula) Formulae.substitute(split, v, truth);
				Formula case2 = (Formula) Formulae.substitute(split, new Expr.Operator(Opcode.EXPR_arridx, xs, j),
						truth);
				result[0] = Formulae.and(new Formula.ArithmeticEquality(true, i, j), case1);
				result[1] = Formulae.and(new Formula.ArithmeticEquality(false, i, j), case2);
				break;
			} else if (src.getOpcode() == Opcode.EXPR_arrinit) {
				// [a,b,c][j] >= 0
				result = new Formula[src.size()];
				for (int i = 0; i != src.size(); ++i) {
					// a >= 0 && j == 0
					Formula lhs = (Formula) Formulae.substitute(split, src.getOperand(i), truth);
					Formula rhs = new Formula.ArithmeticEquality(true, j, Formulae.toPolynomial(i));
					result[i] = Formulae.and(lhs, rhs);
				}
				break;
			}
		}
		default:
			throw new IllegalArgumentException("unknown split kind encountered");
		}
		return result;
	}

	// ===========================================================================
	// Apply implicit axioms
	// ===========================================================================

	/**
	 * <p>
	 * For a given truth, search for and apply any implicit axioms that may
	 * exist. For example, in the formula <code>A[i] >= 0</code> there is an
	 * implicit axiom that <code>0 <= i && i < |A|</code>. Likewise, in the
	 * division <code>x / y</code>, there is an implicit axiom that
	 * <code>y != 0</code>.
	 * </p>
	 * <p>
	 * Implicit axioms are necessary in some cases for proving a contradiction.
	 * For example, <code>i < 0 && A[i] == 1</code> should yield a
	 * contradiction.
	 * </p>
	 *
	 * @param truth
	 *            The formula in which to look for and apply any implicit axioms
	 * @param state
	 *            The current prover state
	 * @return
	 */
	private State applyImplicitAxioms(Formula truth, State state) {
		// First, recursively search for any implicit axioms
		Formula axiom = generateImplicitAxioms(truth);

		if (axiom != null) {
			// Such an axiom was indeed found and we simply need to apply it.
			axiom = state.allocate(Formulae.simplifyFormula(axiom, types));
			state = state.set("implicit", axiom, truth);
		}
		return state;
	}

	/**
	 * Recursively explore a given expression looking for sub-expressions which
	 * give rise to implicit axioms.
	 *
	 * @param e
	 * @return
	 */
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
			if (decl instanceof Declaration.Named.Function) {
				Declaration.Named.Function md = (Declaration.Named.Function) decl;
				VariableDeclaration[] params = md.getParameters().getOperands();
				VariableDeclaration[] returns = md.getReturns().getOperands();
				if (returns.length > 1) {
					throw new IllegalArgumentException("problem");
				} else {
					axiom = Formulae.extractTypeInvariant(returns[0].getType(), e, types);
				}
			}
			break;
		}
		case EXPR_arridx: {
			Expr.Operator idx = (Expr.Operator) e;
			Expr src = idx.getOperand(0);
			Polynomial index = Formulae.toPolynomial(idx.getOperand(1));
			Polynomial srclen = Formulae.toPolynomial(new Expr.Operator(Opcode.EXPR_arrlen, src));
			Formula.Inequality lb = Formulae.lessThan(index, srclen);
			Formula.Inequality gb = Formulae.greaterOrEqual(index, new Polynomial(BigInteger.ZERO));
			axiom = new Formula.Conjunct(lb, gb);
			break;
		}
		case EXPR_div: {
			Expr.Operator op = (Expr.Operator) e;
			axiom = new Formula.Equality(false, op.getOperand(1), new Expr.Constant(new Value.Int(0)));
			break;
		}
		case EXPR_arrlen: {
			Expr.Operator op = (Expr.Operator) e;
			Polynomial len = Formulae.toPolynomial(op);
			Polynomial zero = Formulae.toPolynomial(0);
			axiom = Formulae.greaterOrEqual(len, zero);
			break;
		}
		case EXPR_or:
			// Don't extract implicit axioms from disjuncts as we can be sure
			// they hold for all cases.
			return null;
		case EXPR_exists:
		case EXPR_forall:
			// Don't extract implicit axioms from quantified formulae. There's
			// no point until they are instantiated.
			return null;
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

	// ===========================================================================
	// Expand macros / type invariants
	// ===========================================================================

	private State applyExpandInvocation(Formula.Invoke ivk, State state) {
		// FIXME: this is broken in the case of recursive macros.
		// The reason for this is simply that it will expand forever
		// :)

		// Determine the type declaration in question
		Type.AbstractFunction af = ivk.getSignatureType();
		// FIXME: this resolution should have already been performed
		// elsewhere
		Declaration.Named decl = types.resolveAsDeclaration(ivk.getName());
		// Calculate the invariant
		Formula invariant = extractDeclarationInvariant(decl, ivk.getArguments());
		if(invariant == null) {
			invariant = new Formula.Truth(true);
		}
		if (invariant != null) {
			if (!ivk.getSign()) {
				invariant = Formulae.simplifyFormula(Formulae.invert(invariant), types);
			}
			// Update the state
			state = state.subsume("expand", ivk, state.allocate(invariant));
		}
		return state;
	}

	private Formula extractDeclarationInvariant(Declaration.Named decl, Tuple<Expr> arguments) {
		if (decl instanceof Declaration.Named.Type) {
			// This is a type invariant macro call. In such case, we
			// need to first determine what the invariant actually is.
			Declaration.Named.Type td = (Declaration.Named.Type) decl;
			// Expand the corresponding type invariant
			return expandTypeInvariant(td, arguments.getOperand(0));
		} else if (decl instanceof Declaration.Named.Macro) {
			Declaration.Named.Macro md = (Declaration.Named.Macro) decl;
			// Expand the macro body with appropriate substitutions
			return expandMacroBody(md, arguments.getOperands());
		} else {
			return null;
		}
	}

	private Formula expandMacroBody(Declaration.Named.Macro md, Expr[] arguments) {
		VariableDeclaration[] parameters = md.getParameters().getOperands();
		// Initialise the map with the identity for parameters to ensure they
		// are preserved as is, and can then be substituted.
		Map<SyntacticItem, SyntacticItem> map = new IdentityHashMap<>();
		for (int i = 0; i != parameters.length; ++i) {
			map.put(parameters[i], parameters[i]);
		}
		// Clone is required at this point to ensure that any variable
		// declarations are distinguished appropriately.
		WyalFile.Stmt.Block block = SyntacticHeaps.cloneOnly(md.getBody(), map, WyalFile.VariableDeclaration.class);
		Formula body = Formulae.toFormula(block, types);
		for (int i = 0; i != arguments.length; ++i) {
			// At this point, we must substitute the parameter name used in
			// the type declaration for the name used as the invocation
			// argument.
			Expr.VariableAccess parameter = new Expr.VariableAccess(parameters[i]);
			body = (Formula) Formulae.substitute(parameter, arguments[i], body);
		}
		return Formulae.simplifyFormula(body, types);
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
			return Formulae.simplifyFormula(result, types);
		}
	}

	// ===========================================================================
	// Congruence Closure
	// ===========================================================================

	private State closeOverCongruence(State state, Formula.Truth FALSE) {
		// Observe, we must always use the most up-to-date version of state
		// here. This is because, once a substitution is applied, we must ensure
		// that only ever use the substituted terms.
		//
		// I believe that this loop should now terminate. I don't think it's
		// possible for us to witness the counting problem here.
		for (int i = 0; i < state.size() && !state.contains(FALSE); ++i) {
			Formula ith = state.getActive(i);
			if (ith instanceof Formula.Equality) {
				Formula.Equality eq = (Formula.Equality) ith;
				if (eq.getSign()) {
					state = applyCongruenceClosure(eq, state);
				}
			}
		}
		return state;
	}

	/**
	 * <p>
	 * Congruence closure is the act of simplifying formula using equalities.
	 * For example, consider <code>i==(j+1) && A[i] >= 0 && A[j+1] < 0</code>.
	 * To obtain the contradiction we substitute <code>i</code> for
	 * <code>j+1</code> in all formulae (except the equality itself). This gives
	 * <code>i==(j+1) && A[j+1] >= 0 && A[j+1] < 0</code> and from there the
	 * contradiction is easy to obtain.
	 * </p>
	 * <p>
	 * An important point when applying congruence closure is to make a decision
	 * over which way to normalise. For example, in the expression
	 * <code>i==(j+1)</code> we can substitute through for either <code>i</code>
	 * or <code>j</code> (after rearranging). There are benefits in exploiting a
	 * fixed order of terms to determine which to choose in any given situation.
	 * </p>
	 *
	 *
	 * @param eq
	 * @param state
	 * @return
	 */
	private State applyCongruenceClosure(Formula.Equality eq, State state) {
		// COUNTING. this is possible in congruence closure when you have
		// recursive predicates. For example, x == f(x) can ultimately give rise
		// to a sequence of applications end up with f(f(f(f(x)))), etc.
		Pair<Expr, Expr> substitution = Formulae.rearrangeForSubstitution(eq);
		if (eq.getSign() && substitution != null) {
			// We've found a suitable substitution
			State original = state;
			int size = original.size();
			for (int j = 0; j < size; ++j) {
				Formula before = original.getActive(j);
				if (before != eq && before != null) {
					Formula after = (Formula) Formulae.substitute(substitution.getFirst(), substitution.getSecond(),
							before);
					//
					if (before != after) {
						after = Formulae.simplifyFormula(after, types);
						// The following is needed because substitution can
						// produce a different looking term which, after
						// simplification, is the same. To avoid this, we need
						// to avoid "recursive substitutions" somehow.
						if (!before.equals(after)) {
							after = state.allocate(after);
							state = state.subsume("substitution", before, after, eq);
						}
					}
				}
			}
		}
		return state;
	}

	// ===========================================================================
	// Inequality Closure
	// ===========================================================================

	private State closeOverInequalities(State state, Formula.Truth FALSE) {
		int size = state.size();
		//
		State nState = state;
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
							inferred = nState.allocate(inferred);
							nState = nState.set("closure", inferred, ith_ieq, jth_ieq);
						}
					}
				}
			}
		}
		return nState;
	}

	// ===========================================================================
	// Quantifier Instantiation
	// ===========================================================================

	private State instantiateUniversalQuantifiers(State state) {
		Expr[] grounds = determineGroundTerms(state);
		for (int i = 0; i != state.size(); ++i) {
			Formula ith = state.getActive(i);
			if (ith instanceof Formula.Quantifier) {
				Formula.Quantifier qf = (Formula.Quantifier) ith;
				if (qf.getSign()) {
					// This is a universal quantifier
					state = instantiateUniversalQuantifier(qf, new Expr[0], grounds, state);
				}
			}
		}
		return state;
	}

	private State applyQuantifierInstantiation(Formula.Quantifier qf, State state) {
		//
		if (qf.getSign()) {
			// Universal Quantifier
			//
			// In principle, thinking more carefully about which ground terms to
			// instantiation would be helpful.
			Expr[] grounds = determineGroundTerms(state);
			return instantiateUniversalQuantifier(qf, new Expr[0], grounds, state);
		} else {
			// Existential Quantifier
			//
			// FIXME: there might be a problem here when instantiation
			// existentials nested in universal quantifiers.
			return state.subsume("exists", qf, qf.getBody());
		}
	}

	private Expr[] determineGroundTerms(State state) {
		HashSet<Expr> grounds = new HashSet<>();
		for (int i = 0; i != state.size(); ++i) {
			Formula ith = state.getActive(i);
			// The reason we restrict the search here is to focus only on things
			// which could potentially lead to a contradiction. The choice of
			// what to instantiate is critically important and certainly
			// requires further thought.
			if (ith instanceof Formula.Equality || ith instanceof Formula.Inequality) {
			//if (ith instanceof Formula.Inequality) {
				Expr lhs = (Expr) ith.getOperand(0);
				Expr rhs = (Expr) ith.getOperand(1);
				extractGrounds(lhs, grounds);
				extractGrounds(rhs, grounds);
			}
		}
		Expr[] terms = grounds.toArray(new Expr[grounds.size()]);
		Arrays.sort(terms);
		return terms;
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

	private State instantiateUniversalQuantifier(Formula.Quantifier qf, Expr[] binding, Expr[] grounds, State state) {
		VariableDeclaration[] parameters = qf.getParameters().getOperands();
		if (parameters.length == binding.length) {
			// Binding now complete, so proceed to instantiate quantifier.
			// First, substitute body through for the binding obtained for each
			// parameter.
			Formula body = qf.getBody();
			// FIXME: there is a bug of sorts here related to skolems
			for (int i = 0; i != parameters.length; ++i) {
				VariableDeclaration parameter = parameters[i];
				Expr.VariableAccess access = new Expr.VariableAccess(parameter);
				body = (Formula) Formulae.substitute(access, binding[i], body);
			}
			// Second, instantiate the ground body
			body = state.allocate(Formulae.simplifyFormula(body, types));
			Expr[] dependencies = Arrays.copyOf(binding, binding.length + 1);
			dependencies[binding.length] = qf;
			state = state.set("instantiate", body, dependencies);
		} else {
			// Exhaustively instantiate this variable with all possible ground
			// terms.
			Type pt = parameters[binding.length].getType();
			//
			for (int i = 0; i != grounds.length; ++i) {
				Type gt = grounds[i].getReturnType(types);
				// Make sure ground term is compatible with parameter in
				// question. If not, then it's not a valid substitution and
				// should be skipped.
				if(types.isSubtype(pt, gt)) {
					Expr[] nBinding = Arrays.copyOf(binding, binding.length + 1);
					nBinding[binding.length] = grounds[i];
					state = instantiateUniversalQuantifier(qf, nBinding, grounds, state);
				}
			}
		}
		return state;
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
				System.out.print("[" + i + "] ");
				println(indent, ith);
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
			tab(indent);
			for (int i = 0; i != disjunct.size(); ++i) {
				if (i != 0) {
					System.out.print(" || ");
				}
				print(disjunct.getOperand(i));
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

	public static void print(Proof proof) {
		ProofPrinter printer = new ProofPrinter(System.out);
		printer.print(proof);
		printer.flush();
	}

	public static void tab(int indent) {
		for (int i = 0; i != indent; ++i) {
			System.out.print("  ");
		}
	}
}
