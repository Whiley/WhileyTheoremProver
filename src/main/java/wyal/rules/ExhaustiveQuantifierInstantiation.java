package wyal.rules;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import wyal.lang.Formula;
import wyal.lang.Proof;
import wyal.lang.SyntacticItem;
import wyal.lang.WyalFile;
import wyal.lang.Formula.Disjunct;
import wyal.lang.NameResolver.ResolutionError;
import wyal.lang.Proof.State;
import wyal.lang.WyalFile.Expr;
import wyal.lang.WyalFile.Expr.Polynomial;
import wyal.lang.WyalFile.Opcode;
import wyal.lang.WyalFile.Tuple;
import wyal.lang.WyalFile.Type;
import wyal.lang.WyalFile.VariableDeclaration;
import wyal.util.Formulae;
import wyal.util.TypeSystem;

public class ExhaustiveQuantifierInstantiation implements Proof.LinearRule {
	private final TypeSystem types;

	public ExhaustiveQuantifierInstantiation(TypeSystem types) {
		this.types = types;
	}

	@Override
	public String getName() {
		return "Forall-I";
	}

	@Override
	public State apply(Proof.State state, Formula newTruth) throws ResolutionError {

		if (newTruth instanceof Formula.Equation) {
			Formula.Equation ground = (Formula.Equation) newTruth;
			return instantiateQuantifiers(ground, state);
		} else if (newTruth instanceof Formula.Quantifier) {
			Formula.Quantifier quantifier = (Formula.Quantifier) newTruth;
			return instantiateQuantifiers(quantifier, state);
		}
		// No change in the normal case
		return state;
	}

	/**
	 * Attempt to match a given quantifier against any appropriate ground terms.
	 * This may fail if no suitable bindings can be found.
	 *
	 * @param quantifier
	 * @param state
	 * @return
	 */
	private State instantiateQuantifiers(Formula.Quantifier quantifier, State state) throws ResolutionError {
		if (quantifier.getSign()) {
			// At this point, we have a quantifier which has not been seen
			// before (for example, it was hiding inside a macro invocation
			// somewhere). Therefore, we need to search the history looking for
			// suitable opportunities to instantiate it.
			Proof.Delta history = state.getDelta(null);
			Proof.Delta.Set additions = history.getAdditions();
			for (int i = 0; i != additions.size(); ++i) {
				Formula truth = additions.get(i);
				if (truth instanceof Formula.ArithmeticEquation) {
					Formula.ArithmeticEquation ground = (Formula.ArithmeticEquation) truth;
					// Yes, this is a universal quantifier
					state = applyQuantifierInstantiation(quantifier, ground, state);
				} else {
					// FIXME: we need to handle Assignment here
				}
			}
		}
		//
		return state;
	}

	/**
	 * Attempt to match a given ground term against any active quantifiers in an
	 * effort to instantiate them one or more times. This may fail if no
	 * suitable bindings can be found.
	 *
	 * @param groundTerm
	 * @param state
	 * @return
	 */
	private State instantiateQuantifiers(Formula.Equation groundTerm, State state) throws ResolutionError {
		// At this point, we have an equality or inequality which potentially
		// could be used to instantiate one or more existing (universal)
		// quantifiers. Therefore, we need to look back through the history to
		// determine any cases where this can be applied.
		Proof.Delta history = state.getDelta(null);
		Proof.Delta.Set additions = history.getAdditions();
		for (int i = 0; i != additions.size(); ++i) {
			Formula truth = additions.get(i);
			if (truth instanceof Formula.Quantifier) {
				Formula.Quantifier qf = (Formula.Quantifier) truth;
				if (qf.getSign()) {
					// Yes, this is a universal quantifier
					state = applyQuantifierInstantiation(qf, groundTerm, state);
				}
			}
		}
		//
		return state;
	}

	private State applyQuantifierInstantiation(Formula.Quantifier quantifier, Formula.Equation groundTerm,
			State state) throws ResolutionError {

		// FIXME: I believe there is a bug here in the (unlikely?) situation
		// that we can in fact match *multiple* variables in the same quantifier
		// against the same ground term.

		VariableDeclaration[] parameters = quantifier.getParameters().getOperands();
		for (int i = 0; i != parameters.length; ++i) {
			VariableDeclaration variable = parameters[i];
			state = attemptQuantifierInstantiation(quantifier, variable, groundTerm, state);
		}
		return state;
	}

	/**
	 * Attempt to instantiate a given variable of a universal quantifier. This
	 * searches a given ground term for appropriate bindings for the variable in
	 * question. If any are found, then the quantifier is instantiated
	 * separately for each.
	 *
	 * @param quantifier
	 *            --- The universal quantifier to be instantiated.
	 * @param variable
	 *            --- The quantified variable declared in the universal
	 *            quantifier to be instantiated.
	 * @param groundTerm
	 *            --- The term with which we will attempt to bind the quantified
	 *            variable against, thereby producing appropriate bindings for
	 *            the instantiation (or not, if none exist).
	 * @param state
	 *            --- The state in which the instantiated quantifier will be
	 *            asserted.
	 * @return
	 */
	private State attemptQuantifierInstantiation(Formula.Quantifier quantifier, VariableDeclaration variable,
			Formula.Equation groundTerm, State state) throws ResolutionError {
		// Exhaustively instantiate this variable with all possible ground
		// terms.
		List<Expr> grounds = bind(state, variable, quantifier.getBody(), groundTerm);
		//
		for (int i = 0; i != grounds.size(); ++i) {
			Expr ground = grounds.get(i);
			// NOTE: we don't bother checking the type of the term being
			// instantiated here. That's because (at the moment) this is only
			// matching integer terms anyway. In the future, if we relax this,
			// then we might need a different approach.
			state = instantiateQuantifier(quantifier, variable, groundTerm, ground, state);
		}
		return state;
	}

	/**
	 * <p>
	 * Instantiate the body of a universal quantifier using a binding for a
	 * given quantified variable. For example, instantiating
	 * <code>forall(int i).(xs[i] >= 0)</code> with the binding <code>i=1</code>
	 * would produce the ground term <code>xs[1] >= 0</code>.
	 * </p>
	 * <p>
	 * Note that this procedure does not always eliminate the quantifier itself.
	 * For example, instantiating <code>forall(int i, int j).(xs[i] >= j)</code>
	 * with the binding <code>i=1</code> would produce the quantified term
	 * <code>forall(int j).(xs[1] >= j)</code>.
	 * </p>
	 *
	 * @param quantifier
	 *            --- The universal quantifier to be instantiated.
	 * @param variable
	 *            --- The quantified variable declared in the universal
	 *            quantifier to be instantiated.
	 * @param binding
	 *            --- The binding to be used to instantiated the quantified
	 *            variable with. In other words, all occurences of the
	 *            quantified variable are replaced with this expression.
	 * @param state
	 *            --- The state in which the instantiated quantifier will be
	 *            asserted.
	 * @return
	 */
	private State instantiateQuantifier(Formula.Quantifier quantifier, VariableDeclaration variable,
			Formula.Equation groundTerm, Expr binding, State state) throws ResolutionError {
		VariableDeclaration[] parameters = quantifier.getParameters().getOperands();
		// Substitute body through for the binding obtained the given parameter
		Formula grounded = quantifier.getBody();
		Expr.VariableAccess access = new Expr.VariableAccess(variable);
		grounded = (Formula) state.substitute(access, binding, grounded, types);
		// Expand any type invariant associated with this variable
		Formula invariant = Formulae.expandTypeInvariant(variable, types);
		// Add type invariants (if appropriate)
		if (invariant != null) {
			grounded = new Disjunct(Formulae.invert(invariant), grounded);
		}
		// Determine whether quantified variables still exist.
		if (parameters.length > 1) {
			// This does not represent a complete instantiation of this
			// quantifier. Therefore, we need to retain all quantified variables
			// except that which was instantiated.
			parameters = stripInstantiatedParameter(parameters, variable);
			// Re-quantify remaining variables
			grounded = new Formula.Quantifier(true, parameters, grounded);
		}
		// Finally, assert the newly instantiated quantifier in the current
		// state.
		grounded = state.allocate(Formulae.simplifyFormula(grounded, types));
		return state.infer(this, grounded, quantifier, groundTerm);
	}

	/**
	 * Remove a given parameter declaration from an array of parameter
	 * declarations, producing an array of length exactly one less than the
	 * original.
	 *
	 * @param parameters
	 * @param variable
	 * @return
	 */
	private VariableDeclaration[] stripInstantiatedParameter(VariableDeclaration[] parameters,
			VariableDeclaration variable) {
		VariableDeclaration[] result = new VariableDeclaration[parameters.length - 1];
		for (int i = 0, j = 0; i != parameters.length; ++i) {
			VariableDeclaration parameter = parameters[i];
			if (parameter != variable) {
				result[j++] = parameter;
			}
		}
		return result;
	}

	/**
	 * Match a given term quantified over a given variable against a ground
	 * term. For example, if "i" is a quantified variable then we might try
	 * matching "A[i] < 0" against "0 < A[1]". In this case, our list of matches
	 * would contain just "1". Observe that the key here is that the matches are
	 * occurring on opposite "sides" of the equation. This is important for
	 * being "goal driven" in that we are looking for potential contradictions.
	 *
	 * @param variable
	 * @return
	 */
	private List<Expr> bind(Proof.State state, VariableDeclaration variable, Formula quantified, Formula.Equation ground) throws ResolutionError {
		ArrayList<Expr> result = new ArrayList<>();
		//
		if (quantified instanceof Formula.Inequality && ground instanceof Formula.Inequality) {
			Formula.Inequality ieq = (Formula.Inequality) quantified;
			// Positive (Quantified) versus Negative (Ground)
			List<Expr> posNegMatches = bind(state, variable, ieq.getOperand(0), ground.getOperand(1), Match.NEGATIVE);
			// Negative (Quantified) versus Positive (Ground)
			List<Expr> negPosMatches = bind(state, variable, ieq.getOperand(1), ground.getOperand(0), Match.POSITIVE);
			//
			result.addAll(posNegMatches);
			result.addAll(negPosMatches);
		} else if (quantified instanceof Formula.Equation) {
			Formula.Equation ieq = (Formula.Equation) quantified;
			Match leftSign = getSign(ieq,ground,0);
			Match rightSign = getSign(ieq,ground,1);
			List<Expr> posPosMatches = bind(state, variable, ieq.getOperand(0), ground.getOperand(0), leftSign);
			List<Expr> posNegMatches = bind(state, variable, ieq.getOperand(0), ground.getOperand(1), rightSign);
			List<Expr> negPosMatches = bind(state, variable, ieq.getOperand(1), ground.getOperand(0), leftSign);
			List<Expr> negNegMatches = bind(state, variable, ieq.getOperand(1), ground.getOperand(1), rightSign);
			//
			result.addAll(posPosMatches);
			result.addAll(posNegMatches);
			result.addAll(negPosMatches);
			result.addAll(negNegMatches);
		} else if (quantified instanceof Formula.Conjunct) {
			Formula.Conjunct c = (Formula.Conjunct) quantified;
			for (int i = 0; i != c.size(); ++i) {
				result.addAll(bind(state, variable, c.getOperand(i), ground));
			}
		} else if (quantified instanceof Formula.Disjunct) {
			Formula.Disjunct c = (Formula.Disjunct) quantified;
			for (int i = 0; i != c.size(); ++i) {
				result.addAll(bind(state, variable, c.getOperand(i), ground));
			}
		}
		return result;
	}

	private Match getSign(Formula.Equation quantified, Formula.Equation ground, int operand) {
		if (quantified instanceof Formula.Equality && ground instanceof Formula.Equality) {
			return Match.EXACT;
		} else if (operand == 0) {
			return Match.POSITIVE;
		} else {
			return Match.NEGATIVE;
		}
	}

	private enum Match {
		EXACT,
		POSITIVE, // >= 0
		NEGATIVE  // <= 0
	}

	/**
	 * <p>
	 * Here, we have a quantified expression (e.g. A[k]) and a ground expression
	 * (e.g. A[0]). Our goal is to "guess" an appropriate instantiation of k
	 * which gives A[0]. Instead of trying to be too clever (e.g. some kind of
	 * matching), we're going to take a more "exhaustive" approach. That is,
	 * given some set of ground terms, we're just going to substitute *every*
	 * ground term for the quantified variable and see whether the result is a
	 * match. There are lots of reasons why this turns out to be quite a good
	 * idea.
	 * </p>
	 * <p>
	 * The important question is from where we derive our set of ground terms to
	 * try. If this set is too small, we may not be able to figure out what we
	 * need. For example, consider matching A[k-1] against A[0]. The ground term
	 * we need is -1 here.
	 * </p>
	 *
	 * @param variable
	 * @param quantified
	 * @param ground
	 * @return
	 */
	private List<Expr> bind(Proof.State state, VariableDeclaration variable, Expr quantified, Expr ground, Match kind) throws ResolutionError {
		//
		if (containsTrigger(quantified)) {
			Expr.VariableAccess access = new Expr.VariableAccess(variable);
			List<Expr> candidates = determineGroundTerms(ground, new ArrayList<>());
			List<Expr> result = new ArrayList<>();
			for (int i = 0; i != candidates.size(); ++i) {
				Expr candidate = candidates.get(i);
				Expr attempt = (Expr) substitute(access, candidate, quantified, types);
				attempt = Formulae.simplify(attempt, types);
				// Attempt the match
				if (match(attempt,ground,kind)) {
					// Awesome, we made a correct guess!!!
					result.add(candidate);
				}
			}
			return result;
		} else {
			return Collections.EMPTY_LIST;
		}
	}

	private boolean match(Expr attempt, Expr ground, Match kind) {
		if(!(ground instanceof Polynomial)) {
			ground = Formulae.toPolynomial(ground);
		}
		if(!(attempt instanceof Polynomial)) {
			attempt = Formulae.toPolynomial(attempt);
		}
		//
		Polynomial lhs = (Polynomial) attempt;
		Polynomial rhs = (Polynomial) ground;
		Polynomial difference = lhs.subtract(rhs);
		if (difference.isConstant()) {
			BigInteger diff = difference.toConstant().get();
			if(kind == Match.EXACT) {
				return diff.compareTo(BigInteger.ZERO) == 0;
			} else if (kind == Match.POSITIVE) {
				return diff.compareTo(BigInteger.ZERO) >= 0;
			} else {
				return diff.compareTo(BigInteger.ZERO) <= 0;
			}
		} else {
			return false;
		}
	}

	private List<Expr> determineGroundTerms(Expr e, List<Expr> grounds) {
		for (int i = 0; i != e.size(); ++i) {
			SyntacticItem child = e.getOperand(i);
			if (child instanceof Expr) {
				determineGroundTerms((Expr) child, grounds);
			} else if(child instanceof WyalFile.Tuple) {
				// FIXME: this can occur for the parameters of a function
				// invocation. Perhaps not ideal actually.
				Tuple<?> t = (Tuple<?>) child;
				for(SyntacticItem p : t.getOperands()) {
					if (p instanceof Expr) {
						determineGroundTerms((Expr) p, grounds);
					}
				}
			}
		}
		grounds.add(e);
		return grounds;
	}

	/**
	 * Determine whether a given expression contains a "trigger" or not. That
	 * is, a special term which we are using to signal that an instantiation
	 * makes sense.
	 *
	 * @param ground
	 * @return
	 */
	private boolean containsTrigger(Expr e) {
		if(isTrigger(e)) {
			return true;
		} else {
			for (int i = 0; i != e.size(); ++i) {
				SyntacticItem child = e.getOperand(i);
				if (child instanceof Expr) {
					if(containsTrigger((Expr) child)) {
						return true;
					}
				} else if(child instanceof WyalFile.Tuple) {
					// FIXME: this can occur for the parameters of a function
					// invocation. Perhaps not ideal actually.
					Tuple<?> t = (Tuple<?>) child;
					for(SyntacticItem p : t.getOperands()) {
						if (p instanceof Expr) {
							if(containsTrigger((Expr) p)) {
								return true;
							}
						}
					}
				}
			}
			return false;
		}
	}

	private boolean isTrigger(Expr e) {
		return e.getOpcode() == Opcode.EXPR_arridx;
	}

	private static SyntacticItem substitute(SyntacticItem from, SyntacticItem to, SyntacticItem item, TypeSystem types) {
		if (item.equals(from)) {
			// Yes, we made a substitution!
			return to;
		} else {
			// No immediate substitution possible. Instead, recursively traverse
			// term looking for substitution.
			SyntacticItem[] children = item.getOperands();
			SyntacticItem[] nChildren = children;
			if(children != null) {
				for (int i = 0; i != children.length; ++i) {
					SyntacticItem child = children[i];
					if(child != null) {
						SyntacticItem nChild = substitute(from, to, child, types);
						if (child != nChild && nChildren == children) {
							// Clone the new children array to avoid interfering with
							// original item.
							nChildren = Arrays.copyOf(children, children.length);
						}
						nChildren[i] = nChild;
					}
				}
			}
			if (nChildren == children) {
				// No children were updated, hence simply return the original
				// item.
				return item;
			} else {
				// At least one child was changed, therefore clone the original
				// item with the new children.
				return item.clone(nChildren);
			}
		}
	}
}
