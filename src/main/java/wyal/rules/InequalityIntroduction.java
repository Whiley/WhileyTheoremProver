package wyal.rules;

import wyal.lang.Formula;
import wyal.lang.Proof;
import wyal.lang.Proof.State;
import wyal.util.Formulae;
import wyal.util.TypeSystem;

public class InequalityIntroduction implements Proof.LinearRule {
	private final TypeSystem types;

	public InequalityIntroduction(TypeSystem types) {
		this.types = types;
	}

	@Override
	public String getName() {
		return "Ineq-I";
	}

	@Override
	public State apply(Proof.State state, Formula newTruth) {

		if(newTruth instanceof Formula.Inequality) {
			Formula.Inequality inequality = (Formula.Inequality) newTruth;
			// At this point, we have an inequality which potentially could be
			// closed with one or more other inequalities. Therefore, we need to
			// look back through the history to determine any inequalities which
			// are currently "active".
			Proof.Delta history = state.getDelta(null);
			Proof.Delta.Set additions = history.getAdditions();
			for(int i=0;i!=additions.size();++i) {
				Formula existingTruth = additions.get(i);
				if(existingTruth != newTruth && existingTruth instanceof Formula.Inequality) {
					state = closeOver(inequality,(Formula.Inequality)existingTruth,state);
				}
			}
		}
		// No change in the normal case
		return state;
	}

	private State closeOver(Formula.Inequality ith, Formula.Inequality jth, State state) {
		Formula inferred = Formulae.closeOver(ith, jth, types);
		if (inferred != null) {
			inferred = state.allocate(inferred);
			state = state.infer(this, inferred, ith, jth);
		}
		return state;
	}

}
