package wyal.rules;

import wyal.lang.Formula;
import wyal.lang.Proof;
import wyal.lang.Proof.State;

public class OrElimination implements Proof.NonLinearRule {

	@Override
	public String getName() {
		return "Or-E";
	}

	@Override
	public State[] apply(Proof.State state, Formula truth) {
		if(truth instanceof Formula.Disjunct) {
			Formula.Disjunct disjunct = (Formula.Disjunct) truth;
			Formula[] cases = disjunct.getOperands();
			State[] result = new State[cases.length];
			for (int i = 0; i != cases.length; ++i) {
				result[i] = state.subsume(this,disjunct,cases[i]);
			}
			return result;
		} else {
			// No change in the normal case
			return new Proof.State[]{state};
		}
	}
}
