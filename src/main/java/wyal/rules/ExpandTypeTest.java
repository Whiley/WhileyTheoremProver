package wyal.rules;

import wyal.lang.Formula;
import wyal.lang.Proof;
import wyal.lang.Proof.State;
import wyal.lang.WyalFile;
import wyal.lang.WyalFile.Type;
import wyal.util.Formulae;
import wyal.util.TypeSystem;

public class ExpandTypeTest implements Proof.LinearRule {
	private final TypeSystem types;

	public ExpandTypeTest(TypeSystem types) {
		this.types = types;
	}

	@Override
	public String getName() {
		return "Is-I";
	}

	@Override
	public State apply(State state, Formula truth) {
		if(truth instanceof Formula.Is) {
			Formula nTruth = expand((Formula.Is) truth);
			if(nTruth != truth) {
				nTruth = state.allocate(nTruth);
				return state.subsume(this, truth, nTruth);
			}
		}
		return state;
	}

	private Formula expand(Formula.Is e) {
		WyalFile.Expr nLhs = e.getExpr();
		Formula invariant = Formulae.extractTypeInvariant(e.getTypeTest(), nLhs, types);
		// FIXME: could reduce this expression to true or false in some cases.
		// For example, if lhs is a constant.
		boolean isSubtype = types.isSubtype(e.getTypeTest(),nLhs.getReturnType(types));
		boolean isNotSubtype = types.isSubtype(new Type.Negation(e.getTypeTest()),nLhs.getReturnType(types));
		if (isSubtype && invariant != null) {
			return Formulae.simplifyFormula(invariant,types);
		} else if (isSubtype) {
			return new Formula.Truth(true);
		} else if (isNotSubtype && invariant != null) {
			// FIXME: I think this is broken in the general case. The essential
			// problem boils down to what the subtype test is really telling us.
			// For example, is it saying that the underlying type of the lhs is not
			// a subtype of the negated rhs? I don't think so.
			return Formulae.simplifyFormula(invariant,types);
		} else if(isNotSubtype) {
			return new Formula.Truth(false);
		}
		// At this point, we're stuck with a type test of some sort.
		if(invariant != null) {
			return Formulae.and(Formulae.simplifyFormula(invariant,types),e);
		} else {
			return e;
		}
	}
}
