package wyal.rules;

import wyal.lang.Formula;
import wyal.lang.Proof;
import wyal.lang.Proof.State;

public class AndElimination implements Proof.LinearRule {

	@Override
	public String getName() {
		return "And-E";
	}

	@Override
	public State apply(Proof.State state, Formula truth) {
		if(truth instanceof Formula.Conjunct) {
			Formula.Conjunct conjunct = (Formula.Conjunct) truth;
			state = state.subsume(this, conjunct, conjunct.getOperands());
			return state;
		}
		// No change in the normal case
		return state;
	}


}
