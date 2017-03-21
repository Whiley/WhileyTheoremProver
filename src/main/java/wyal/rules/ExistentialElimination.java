package wyal.rules;

import wyal.lang.Formula;
import wyal.lang.Proof;
import wyal.lang.Proof.State;

/**
 * <p>
 * Responsible for eliminating an existential quantifier through
 * <i>skolemisation</i>. For example, if we encounter
 * <code>exists(int i).(i >= 0)</code> then we replace this with the ground term
 * <code>i >= 0</code>, where <code>i</code> is now a <i>skolem</i> (that is, an
 * unknown constant).
 * </p>
 * <p>
 * <b>NOTE:</b> This rule current exploits the underlying structure of a
 * syntactic heap for ensuring that a given variable remains a skolem. This is
 * problematic in the case of existentials nested within universal quantifiers
 * and could be improved somewhat.
 * </p>
 *
 * @author David J. Pearce
 *
 */
public class ExistentialElimination implements Proof.LinearRule {

	@Override
	public String getName() {
		return "Exists-E";
	}

	@Override
	public State apply(Proof.State state, Formula truth) {
		if(truth instanceof Formula.Quantifier) {
			Formula.Quantifier qf = (Formula.Quantifier) truth;
			if(!qf.getSign()) {
				state = state.subsume(this, qf, qf.getBody());
			}
		}
		// No change in the normal case
		return state;
	}
}
