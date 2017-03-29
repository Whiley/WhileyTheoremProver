package wyal.rules;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

import wyal.lang.Formula;
import wyal.lang.NameResolver;
import wyal.lang.NameResolver.ResolutionError;
import wyal.lang.Proof;
import wyal.lang.Proof.State;
import wyal.lang.SyntacticItem;
import wyal.lang.WyalFile.Expr;
import wyal.lang.WyalFile.Opcode;
import wyal.lang.WyalFile.Tuple;
import wyal.lang.WyalFile.Expr.Polynomial;
import wyal.util.Formulae;
import wyal.util.TypeSystem;
import wyal.lang.WyalFile;

/**
 * <p>
 * Responsible for inferring that a given <i>array index expression</i> (e.g.
 * |xs|) is within bounds (i.e. for <code>A[i]</code> we have
 * <code>(0 <= i) && (i < |A|)</code>) at appropriate moments to help find a
 * contradiction. In otherwords, this rule implements the axiom that <i>array
 * accesses</i> should always be within bounds. For example, consider a simple
 * assertion such as the following:
 * </p>
 *
 * <pre>
 * assert:
 *  forall(int[] xs):
 *      if:
 *          xs[0] == 0
 *      then:
 *          |xs| > 0
 * </pre>
 * <p>
 * This assertion should be easily proven. To do this following
 * proof-by-contradiction requires showing that <code>|xs| <= 0</code> leads to
 * a contradiction. This rule essentially looks for such situations and would
 * implicitly infers <code>0 < |xs|</code> in which case, which gives the
 * contradiction.
 * </p>
 * <p>
 * <b>NOTE:</b> An important aspect of this rule is when it should and should
 * not fire. A simple (expensive) strategy is to fire whenever an array index
 * expression is encountered --- but this is wasteful. For example, in
 * <code>f(xs[i]) >= 0</code> there is no point inferring <code>i >= 0</code> as
 * this cannot lead to a contradiction.
 * </p>
 *
 */
public class ArrayIndexAxiom extends AbstractProofRule implements Proof.LinearRule {
	public ArrayIndexAxiom(TypeSystem types) {
		super(types);
	}

	@Override
	public String getName() {
		return "ArrIdx-I";
	}

	@Override
	public State apply(Proof.State state, Formula truth) throws ResolutionError {
		Proof.Delta history = state.getDelta(null);
		state = attemptInstantiationByArrayAccess(truth,history,state);
		state = attemptInstantiationByEquation(truth,history,state);
		return state;
	}

	public State attemptInstantiationByEquation(Formula truth, Proof.Delta history, Proof.State state) throws ResolutionError {
		Proof.Delta.Set additions = history.getAdditions();
		for (int j = 0; j != additions.size(); ++j) {
			Formula existing = additions.get(j);
			if(existing != truth) {
				List<Expr.Operator> matches = extractDefinedTerms(existing,Opcode.EXPR_arridx);
				state = attemptInstantiation(existing,matches,truth,state);
			}
		}
		return state;
	}

	public State attemptInstantiationByArrayAccess(Formula truth, Proof.Delta history, Proof.State state) throws ResolutionError {
		List<Expr.Operator> matches = extractDefinedTerms(truth,Opcode.EXPR_arridx);
		// At this point, we have one or more array access expressions which
		// potentially could be introduce some useful facts. Therefore, we need to look
		// back through the history to determine any cases where this can be applied.
		Proof.Delta.Set additions = history.getAdditions();
		for (int j = 0; j != additions.size(); ++j) {
			Formula existing = additions.get(j);
			if(existing != truth) {
				state = attemptInstantiation(truth,matches,existing,state);
			}
		}
		return state;
	}

	public State attemptInstantiation(Formula source, List<Expr.Operator> matches, Formula target, Proof.State state) throws ResolutionError {
		//
		for (int i = 0; i != matches.size(); ++i) {
			Expr.Operator match = matches.get(i);
			Polynomial index = Formulae.toPolynomial(match.getOperand(1));
			// NOTE: we must call construct here since we are creating a new
			// term from scratch.
			Polynomial length = Formulae
					.toPolynomial(state.construct(new Expr.Operator(Opcode.EXPR_arrlen, match.getOperand(0)),types));
			// Now, try to match!
			if (target instanceof Formula.Inequality) {
				Formula.Inequality ieq = (Formula.Inequality) target;
				//
				if(match(ieq.getOperand(1), index, Match.NONNEGATIVE)) {
					// A[i] ~ e && 0 >= i+1
					state = instantiateIndexAxiom(index,state,target,source);
				}
				//
				if (match(ieq.getOperand(0), index, Match.NEGATIVE)
						&& match(ieq.getOperand(1), length, Match.NONNEGATIVE)) {
					// A[i] ~ e && i-1 >= |A|+1 ==> i < |A|
					state = instantiateLengthAxiom(index, length, state, target, source);
				}
			} else if(target instanceof Formula.Equation) {
				Formula.Equation ieq = (Formula.Equation) target;
				// A[i] ~ e && |A| == c ==> i < |A|
				if (match(ieq.getOperand(0), length, Match.NONNEGATIVE)
						|| match(ieq.getOperand(1), length, Match.NONNEGATIVE)) {
					// A[i] ~ e && 0 >= i+1
					state = instantiateLengthAxiom(index,length,state,target,source);
				}
			}

		}
		return state;
	}

	private State instantiateIndexAxiom(Polynomial index, Proof.State state, Formula... dependencies) throws ResolutionError {
		Polynomial zero = new Polynomial(BigInteger.ZERO);
		Formula axiom = Formulae.simplifyFormula(Formulae.greaterOrEqual(index, zero), types);
		return state.infer(this, state.allocate(axiom), dependencies);
	}

	private State instantiateLengthAxiom(Polynomial index, Polynomial length, Proof.State state, Formula... dependencies) throws ResolutionError {
		Formula axiom = Formulae.simplifyFormula(Formulae.lessThan(index, length), types);
		return state.infer(this, state.allocate(axiom), dependencies);
	}


	private enum Match {
		EXACT,
		NONNEGATIVE, // >= 0
		NEGATIVE  // < 0
	}

	private boolean match(Expr attempt, Expr ground, Match kind) {
		if (kind == Match.EXACT || !(attempt instanceof Expr.Polynomial) || !(ground instanceof Polynomial)) {
			return attempt.equals(ground);
		}
		Polynomial lhs = (Polynomial) attempt;
		Polynomial rhs = (Polynomial) ground;
		Polynomial difference = lhs.subtract(rhs);
		if (difference.isConstant()) {
			BigInteger diff = difference.toConstant().get();
			if (kind == Match.NONNEGATIVE) {
				return diff.compareTo(BigInteger.ZERO) >= 0;
			} else {
				return diff.compareTo(BigInteger.ZERO) < 0;
			}
		} else {
			return false;
		}
	}
}
