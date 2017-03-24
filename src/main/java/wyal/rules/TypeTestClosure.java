package wyal.rules;

import wyal.lang.Formula;
import wyal.lang.Proof;
import wyal.lang.Proof.State;
import wyal.lang.WyalFile.Type;
import wyal.util.Formulae;
import wyal.util.TypeSystem;

public class TypeTestClosure implements Proof.LinearRule {
	private final TypeSystem types;

	public TypeTestClosure(TypeSystem types) {
		this.types = types;
	}

	@Override
	public String getName() {
		return "Type-I";
	}

	@Override
	public State apply(State state, Formula newTruth) {
		if(newTruth instanceof Formula.Is) {
			Formula.Is test = (Formula.Is) newTruth;
			// At this point, we have a type test which potentially could be
			// closed with one or more other type tests. Therefore, we need to
			// look back through the history to determine any inequalities which
			// are currently "active".
			Proof.Delta history = state.getDelta(null);
			Proof.Delta.Set additions = history.getAdditions();
			for(int i=0;i!=additions.size();++i) {
				Formula existingTruth = additions.get(i);
				if(existingTruth != newTruth && existingTruth instanceof Formula.Is) {
					state = closeOver(test,(Formula.Is)existingTruth,state);
				}
			}
		}
		return state;
	}

	private State closeOver(Formula.Is lhs, Formula.Is rhs, Proof.State state) {
		if (lhs.getExpr().equals(rhs.getExpr())) {
			Type lhsT = lhs.getTypeTest();
			Type rhsT = rhs.getTypeTest();
			Type type = types.intersect(lhsT, rhsT);
			Formula inferred = Formulae.simplifyFormula(new Formula.Is(lhs.getExpr(), type), types);
			// FIXME: without proper simplification this could presumably
			// runaway.
			state = state.infer(this, state.allocate(inferred), lhs, rhs);
		}
		return state;
	}
}
