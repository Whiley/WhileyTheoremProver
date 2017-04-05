package wytp.proof.rules;

import wytp.proof.Formula;
import wytp.proof.Proof;
import wytp.proof.Proof.State;

/**
 * <p>
 * Responsible for breaking conjuncts down into their individual terms. This is
 * perhaps the most simple implementation of a <code>Proof.Rule</code> which is
 * also useful. For example, consider this simple assertion:
 * </p>
 * <pre>
 * assert:
 *   forall(int x):
 *       if:
 *           x > 0
 *       then:
 *           x >= 0
 * </pre>
 * <p>
 * To prove this by contradiction, we invert the term and look for a
 * contradiction. Eventually, we will encounter the conjunct
 * <code>(x > 0) && (x < 0)</code> and, in order to proceed, this is broken down
 * (by this rule) into the atomic truths <code>x > 0</code> and
 * <code>x < 0</code>. From there a separate rule shows the final contradiction.
 * </p>
 *
 * @author David J. Pearce
 *
 */
public class AndElimination implements Proof.LinearRule {

	@Override
	public String getName() {
		return "And-E";
	}

	@Override
	public State apply(Proof.State state, Formula truth) {
		if (truth instanceof Formula.Conjunct) {
			Formula.Conjunct conjunct = (Formula.Conjunct) truth;
			state = state.subsume(this, new Formula[]{conjunct}, conjunct.getOperands());
			return state;
		}
		// No change in the normal case
		return state;
	}

}
