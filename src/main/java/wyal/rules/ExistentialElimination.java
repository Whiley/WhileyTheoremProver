package wyal.rules;

import wyal.lang.Formula;
import wyal.lang.Proof;
import wyal.lang.Proof.State;

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
