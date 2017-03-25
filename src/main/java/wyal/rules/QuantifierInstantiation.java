package wyal.rules;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

import wyal.lang.Formula;
import wyal.lang.Proof;
import wyal.lang.WyalFile;
import wyal.lang.Formula.Disjunct;
import wyal.lang.Proof.State;
import wyal.lang.WyalFile.Expr;
import wyal.lang.WyalFile.Expr.Polynomial;
import wyal.lang.WyalFile.Opcode;
import wyal.lang.WyalFile.Type;
import wyal.lang.WyalFile.VariableDeclaration;
import wyal.util.Formulae;
import wyal.util.TypeSystem;

public class QuantifierInstantiation implements Proof.LinearRule {
	private final TypeSystem types;

	public QuantifierInstantiation(TypeSystem types) {
		this.types = types;
	}

	@Override
	public String getName() {
		return "Forall-I";
	}

	@Override
	public State apply(Proof.State state, Formula newTruth) {

		if(newTruth instanceof Formula.ArithmeticEquation) {
			Formula.ArithmeticEquation ground = (Formula.ArithmeticEquation) newTruth;
			return instantiateQuantifiers(ground,state);
		} else if(newTruth instanceof Formula.Quantifier) {
			Formula.Quantifier quantifier = (Formula.Quantifier) newTruth;
			return instantiateQuantifiers(quantifier,state);
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
	private State instantiateQuantifiers(Formula.Quantifier quantifier, State state) {
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
	private State instantiateQuantifiers(Formula.ArithmeticEquation groundTerm, State state) {
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

	private State applyQuantifierInstantiation(Formula.Quantifier quantifier, Formula.ArithmeticEquation groundTerm, State state) {

		// FIXME: I believe there is a bug here in the (unlikely?) situation
		// that we can in fact match *multiple* variables in the same quantifier
		// against the same ground term.

		VariableDeclaration[] parameters = quantifier.getParameters().getOperands();
		for(int i=0;i!=parameters.length;++i) {
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
			Formula.ArithmeticEquation groundTerm, State state) {
		// Exhaustively instantiate this variable with all possible ground
		// terms.
		List<Expr> grounds = bind(variable, quantifier.getBody(), groundTerm);
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
	private State instantiateQuantifier(Formula.Quantifier quantifier, VariableDeclaration variable, Formula.ArithmeticEquation groundTerm, Expr binding, State state) {
		VariableDeclaration[] parameters = quantifier.getParameters().getOperands();
		// Substitute body through for the binding obtained the given parameter
		Formula grounded = quantifier.getBody();
		Expr.VariableAccess access = new Expr.VariableAccess(variable);
		grounded = (Formula) Formulae.substitute(access, binding, grounded);
		// Expand any type invariant associated with this variable
		Formula invariant = Formulae.expandTypeInvariant(variable,types);
		// Add type invariants (if appropriate)
		if (invariant != null) {
			grounded = new Disjunct(Formulae.invert(invariant), grounded);
		}
		// Determine whether quantified variables still exist.
		if (parameters.length > 1) {
			// This does not represent a complete instantiation of this
			// quantifier. Therefore, we need to retain all quantified variables
			// except that which was instantiated.
			parameters = stripInstantiatedParameter(parameters,variable);
			// Re-quantify remaining variables
			grounded = new Formula.Quantifier(true,parameters,grounded);
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
	private List<Expr> bind(VariableDeclaration variable, Formula quantified, Formula.ArithmeticEquation ground) {
		ArrayList<Expr> result = new ArrayList<>();
		//
		if (quantified instanceof Formula.Inequality) {
			Formula.Inequality ieq = (Formula.Inequality) quantified;
			// Positive (Quantified) versus Negative (Ground)
			List<Expr> posNegMatches = bindPolynomial(variable, ieq.getOperand(0), ground.getOperand(1));
			// Negative (Quantified) versus Positive (Ground)
			List<Expr> negPosMatches = bindPolynomial(variable, ieq.getOperand(1), ground.getOperand(0));
			//
			result.addAll(posNegMatches);
			result.addAll(negPosMatches);
		} else if (quantified instanceof Formula.ArithmeticEquality) {
			Formula.ArithmeticEquality ieq = (Formula.ArithmeticEquality) quantified;
			List<Expr> posPosMatches = bindPolynomial(variable, ieq.getOperand(0), ground.getOperand(0));
			List<Expr> posNegMatches = bindPolynomial(variable, ieq.getOperand(0), ground.getOperand(1));
			List<Expr> negPosMatches = bindPolynomial(variable, ieq.getOperand(1), ground.getOperand(0));
			List<Expr> negNegMatches = bindPolynomial(variable, ieq.getOperand(1), ground.getOperand(1));
			//
			result.addAll(posPosMatches);
			result.addAll(posNegMatches);
			result.addAll(negPosMatches);
			result.addAll(negNegMatches);
		} else if(quantified instanceof Formula.Conjunct){
			Formula.Conjunct c = (Formula.Conjunct) quantified;
			for(int i=0;i!=c.size();++i) {
				result.addAll(bind(variable,c.getOperand(i),ground));
			}
		} else if(quantified instanceof Formula.Disjunct){
			Formula.Disjunct c = (Formula.Disjunct) quantified;
			for(int i=0;i!=c.size();++i) {
				result.addAll(bind(variable,c.getOperand(i),ground));
			}
		}
		return result;
	}

	private List<Expr> bindPolynomial(VariableDeclaration variable, Expr.Polynomial quantified, Expr.Polynomial ground) {
		//
		List<Expr> result = new ArrayList<>();
		// Perform exhaustive search through possible combinations of terms
		// looking for matches.
		for(int i=0;i!=quantified.size();++i) {
			Polynomial.Term quantifiedTerm = quantified.getOperand(i);
			if(isTrigger(quantifiedTerm)) {
				for(int j=0;j!=ground.size();++j) {
					Polynomial.Term groundTerm = ground.getOperand(j);
					List<Expr> matches = equatePolynomialTerm(variable,quantifiedTerm,groundTerm);
					if(matches != null) {
						// NOTE: unlike for equatePolynomiall we don't attempt to
						// balance things here. That's because we can accept some
						// differences in this case.
						//
						// FIXME: could do something similar to balancing whereby we
						// ensure the difference is acceptable. Something like
						// negative differences are OK, but positive ones are not.
						result.addAll(matches);
					}
				}
			}
		}
		// If we get here and result == null then we didn't find any suitable
		// matches and, hence, overall we failed to equate these. Observe that
		// we can assume the quantified expression and the ground expression
		// differ, since equateExpression() ensures this.
		return result;
	}

	/**
	 * Determine whether a given ground term is a suitable trigger or not. In
	 * the default case, only array access expressions are considered suitable
	 * triggers.
	 *
	 * @param ground
	 * @return
	 */
	private boolean isTrigger(Polynomial.Term ground) {
		Expr[] atoms = ground.getAtoms();
		return atoms.length == 1 && atoms[0].getOpcode() == Opcode.EXPR_arridx;
	}

	private List<Expr> equateExpression(VariableDeclaration variable, Expr quantified, Expr ground) {
//		System.out.print("EQUATING: ");
//		WyalFile.print(quantified);
//		System.out.print(" AGAINST: ");
//		WyalFile.println(ground);
		//
		WyalFile.Opcode quantifiedOpcode = quantified.getOpcode();
		WyalFile.Opcode groundOpcode = ground.getOpcode();
		if (quantified.equals(ground)) {
			return Collections.EMPTY_LIST;
		} else if (quantifiedOpcode == Opcode.EXPR_var) {
			return equateQuantifiedVariable(variable, (Expr.VariableAccess) quantified, ground);
		} else if (quantifiedOpcode == groundOpcode) {
			switch (quantifiedOpcode) {
			case EXPR_arridx:
				return equateArrayAccess(variable, (Expr.Operator) quantified, (Expr.Operator) ground);
			case EXPR_add:
				return equatePolynomial(variable, (Expr.Polynomial) quantified, (Expr.Polynomial) ground);
			}
		}
		// Failed to equate
		return null;
	}

	private List<Expr> equateQuantifiedVariable(VariableDeclaration variable, Expr.VariableAccess quantified, Expr ground) {
		if (quantified.getVariableDeclaration().equals(variable)) {
			// Yes, this is the quantified variable we're looking for.
			// Therefore, we can now (finally) extract an actual match.
			ArrayList<Expr> matches = new ArrayList<>();
			matches.add(ground);
			return matches;
		}
		// Failed to equate
		return null;
	}

	private List<Expr> equatePolynomial(VariableDeclaration variable, Expr.Polynomial quantified, Expr.Polynomial ground) {
		//
		List<Expr> result = null;
		// Perform exhaustive search through possible combinations of terms
		// looking for matches. If we find them, then we need to try and balance
		// any outstanding differences.
		for(int i=0;i!=quantified.size();++i) {
			Polynomial.Term quantifiedTerm = quantified.getOperand(i);
			for(int j=0;j!=ground.size();++j) {
				Polynomial.Term groundTerm = ground.getOperand(j);
				List<Expr> matches = equatePolynomialTerm(variable,quantifiedTerm,groundTerm);
				if(matches != null) {
					// We found some matches, now try to balance things out.
					result = balance(matches,quantified,ground,i,j,result);
				}
			}
		}
		// If we get here and result == null then we didn't find any suitable
		// matches and, hence, overall we failed to equate these. Observe that
		// we can assume the quantified expression and the ground expression
		// differ, since equateExpression() ensures this.
		return result;
	}

	private List<Expr> balance(List<Expr> matches, Expr.Polynomial quantified, Expr.Polynomial ground, int i, int j, List<Expr> result) {
		//
		Polynomial.Term quantifiedTerm = quantified.getOperand(i);
		Polynomial.Term groundTerm = ground.getOperand(j);
		quantified = quantified.subtract(quantifiedTerm);
		ground = ground.subtract(groundTerm);
		if(!quantified.equals(ground)) {
			// No, this did not balance out
			return result;
		} else if(result == null){
			return matches;
		} else {
			result.addAll(matches);
			return result;
		}
	}

	private List<Expr> equatePolynomialTerm(VariableDeclaration variable, Polynomial.Term quantified,
			Polynomial.Term ground) {
		Expr[] quantifiedAtoms = quantified.getAtoms();
		Expr[] groundAtoms = ground.getAtoms();
		// FIXME: this is something of a simplification, as we could potentially
		// handle more complex cases here.
		if (quantifiedAtoms.length == 1 && quantified.getCoefficient().get().equals(BigInteger.ONE)) {
			Expr quantifiedAtom = quantifiedAtoms[0];
			if(groundAtoms.length == 1 && ground.getCoefficient().get().equals(BigInteger.ONE)) {
				return equateExpression(variable, quantifiedAtoms[0], groundAtoms[0]);
			} else if(quantifiedAtom instanceof Expr.VariableAccess) {
				return equateQuantifiedVariable(variable,(Expr.VariableAccess) quantifiedAtom,ground);
			}
		}
		// Failed to equate
		return null;
	}

	private List<Expr> equateArrayAccess(VariableDeclaration variable, Expr.Operator quantified, Expr.Operator ground) {
		Expr quantifiedSource = quantified.getOperand(0);
		Expr quantifiedIndex = quantified.getOperand(1);
		Expr groundSource = ground.getOperand(0);
		Expr groundIndex = ground.getOperand(1);
		List<Expr> sourceMatches = equateExpression(variable,quantifiedSource, groundSource);
		List<Expr> indexMatches = equateExpression(variable,quantifiedIndex, groundIndex);
		if(sourceMatches == null || indexMatches == null) {
			// this indicates we failed to equate
			return null;
		} else {
			// Immutable data structures would be preferred here!
			ArrayList<Expr> result = new ArrayList<>();
			result.addAll(sourceMatches);
			result.addAll(indexMatches);
			return result;
		}
	}
}
