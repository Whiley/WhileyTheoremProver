package wyal.rules;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

import wyal.lang.Formula;
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
public class ArrayIndexAxiom implements Proof.LinearRule {
	private final TypeSystem types;

	public ArrayIndexAxiom(TypeSystem types) {
		this.types = types;
	}

	@Override
	public String getName() {
		return "ArrIdx-I";
	}

	@Override
	public State apply(Proof.State state, Formula truth) {
		Proof.Delta history = state.getDelta(null);
		state = attemptInstantiationByArrayAccess(truth,history,state);
		state = attemptInstantiationByEquation(truth,history,state);
		return state;
	}

	public State attemptInstantiationByEquation(Formula truth, Proof.Delta history, Proof.State state) {
		Proof.Delta.Set additions = history.getAdditions();
		for (int j = 0; j != additions.size(); ++j) {
			Formula existing = additions.get(j);
			if(existing != truth) {
				List<Expr.Operator> matches = findArrayAccesses(existing);
				state = attemptInstantiation(existing,matches,truth,state);
			}
		}
		return state;
	}

	public State attemptInstantiationByArrayAccess(Formula truth, Proof.Delta history, Proof.State state) {
		List<Expr.Operator> matches = findArrayAccesses(truth);
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

	public State attemptInstantiation(Formula source, List<Expr.Operator> matches, Formula target, Proof.State state) {
		//
		for (int i = 0; i != matches.size(); ++i) {
			Expr.Operator match = matches.get(i);
			Polynomial index = Formulae.toPolynomial(match.getOperand(1));
			// NOTE: we must call construct here since we are creating a new
			// term from scratch.
			Polynomial length = Formulae
					.toPolynomial(state.construct(new Expr.Operator(Opcode.EXPR_arrlen, match.getOperand(0)),types));

			if (target instanceof Formula.Inequality) {

				// FIXME: in the following formula, the correct signage is a
				// little unclear to me.

				Formula.Inequality ieq = (Formula.Inequality) target;
				// Only look for index on negative side, as this is where it
				// is useful.
				if(hasPositiveMatchingAtom(ieq.getOperand(1), index)) {
					state = instantiateIndexAxiom(index,state,target,source);
				}
				// Only look for length on positive side, as this is where
				// it is useful.
				if (hasPositiveMatchingAtom(ieq.getOperand(0), index)
						&& hasPositiveMatchingAtom(ieq.getOperand(1), length)) {
					state = instantiateLengthAxiom(index, length, state, target, source);
				}
			}
		}
		return state;
	}

	private State instantiateIndexAxiom(Polynomial index, Proof.State state, Formula... dependencies) {
		Polynomial zero = new Polynomial(BigInteger.ZERO);
		Formula axiom = Formulae.simplifyFormula(Formulae.greaterOrEqual(index, zero), types);
		return state.infer(this, state.allocate(axiom), dependencies);
	}

	private State instantiateLengthAxiom(Polynomial index, Polynomial length, Proof.State state, Formula... dependencies) {
		Formula axiom = Formulae.simplifyFormula(Formulae.lessThan(index, length), types);
		return state.infer(this, state.allocate(axiom), dependencies);
	}

	/**
	 * <p>
	 * Find matches which can be used to instantiate the axiom. A match is
	 * simply an occurrence of an array access expression as any part of a
	 * truth.
	 * </p>
	 *
	 * @param poly
	 * @return
	 */
	private List<Expr.Operator> findArrayAccesses(Expr e) {
		ArrayList<Expr.Operator> matches = new ArrayList<>();
		switch(e.getOpcode()) {
		case EXPR_arridx:
			matches.add((Expr.Operator) e);
			break;
		case EXPR_and:
		case EXPR_or:
		case EXPR_forall:
		case EXPR_exists:
			// We don't explore these constructs as we either cannot reliably
			// pull stuff out of them or (for conjuncts), there's no point yet.
			return Collections.EMPTY_LIST;
		}
		for (int i = 0; i != e.size(); ++i) {
			SyntacticItem child = e.getOperand(i);
			if (child instanceof Expr) {
				matches.addAll(findArrayAccesses((Expr) child));
			} else if(child instanceof Tuple) {
				// FIXME: this can occur for the parameters of a function
				// invocation. Perhaps not ideal actually.
				Tuple<?> t = (Tuple<?>) child;
				for(SyntacticItem p : t.getOperands()) {
					if (p instanceof Expr) {
						matches.addAll(findArrayAccesses((Expr) p));
					}
				}
			}
		}
		return matches;
	}

	private boolean hasPositiveMatchingAtom(Polynomial lhs, Polynomial rhs) {
		Polynomial result = lhs.subtract(rhs);
		if(result.isConstant()) {
			BigInteger val = result.toConstant().get();
			return val.compareTo(BigInteger.ZERO) >= 0;
		} else {
			return false;
		}
	}

	private boolean hasNegativeMatchingAtom(Polynomial lhs, Polynomial rhs) {
		Polynomial result = lhs.subtract(rhs);
		if(result.isConstant()) {
			BigInteger val = result.toConstant().get();
			return val.compareTo(BigInteger.ZERO) <= 0;
		} else {
			return false;
		}
	}

	private boolean hasExactMatchingAtom(Polynomial lhs, Polynomial rhs) {
		Polynomial result = lhs.subtract(rhs);
		if(result.isConstant()) {
			BigInteger val = result.toConstant().get();
			return val.compareTo(BigInteger.ZERO) == 0;
		} else {
			return false;
		}
	}
}
