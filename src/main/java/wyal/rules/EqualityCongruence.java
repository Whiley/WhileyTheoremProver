package wyal.rules;

import wyal.lang.Formula;
import wyal.lang.Proof;
import wyal.lang.Proof.State;
import wyal.lang.WyalFile.Expr;
import wyal.lang.WyalFile.Pair;
import wyal.util.Formulae;
import wyal.util.TypeSystem;

public class EqualityCongruence implements Proof.LinearRule {
	private final TypeSystem types;

	public EqualityCongruence(TypeSystem types) {
		this.types = types;
	}

	@Override
	public String getName() {
		return "Eq-C";
	}

	@Override
	public State apply(Proof.State state, Formula newTruth) {

		if(newTruth instanceof Formula.Equality) {
			Formula.Equality equality = (Formula.Equality) newTruth;
			// COUNTING. this is possible in congruence closure when you have
			// recursive predicates. For example, x == f(x) can ultimately give rise
			// to a sequence of applications end up with f(f(f(f(x)))), etc.
			Pair<Expr, Expr> substitution = Formulae.rearrangeForSubstitution(equality);
			if(equality.getSign() && substitution != null) {
				// At this point, we have an equality which potentially could be
				// used to subsume one or more existing facts. Therefore, we need to
				// look back through the history to determine any cases where this
				// can be applied.
				Proof.Delta history = state.getDelta(null);
				Proof.Delta.Set additions = history.getAdditions();
				for(int i=0;i!=additions.size();++i) {
					Formula existingTruth = additions.get(i);
					if(existingTruth != newTruth) {
						Formula updatedTruth = (Formula) Formulae.substitute(substitution.getFirst(),
								substitution.getSecond(), existingTruth);
						if (existingTruth != updatedTruth) {
							updatedTruth = Formulae.simplifyFormula(updatedTruth, types);
							// The following is needed because substitution can
							// produce a different looking term which, after
							// simplification, is the same. To avoid this, we need
							// to avoid "recursive substitutions" somehow.
							if (!existingTruth.equals(updatedTruth)) {
								updatedTruth = state.allocate(updatedTruth);
								state = state.subsume(this, existingTruth, updatedTruth, equality);
							}
						}
					}
				}
			}
		}
		// No change in the normal case
		return state;
	}
}
