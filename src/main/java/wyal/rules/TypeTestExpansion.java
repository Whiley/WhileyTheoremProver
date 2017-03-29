package wyal.rules;

import wyal.lang.Formula;
import wyal.lang.Proof;
import wyal.lang.Proof.State;
import wyal.lang.WyalFile;
import wyal.lang.NameResolver.ResolutionError;
import wyal.lang.WyalFile.Type;
import wyal.util.Formulae;
import wyal.util.TypeSystem;

public class TypeTestExpansion implements Proof.LinearRule {
	private final TypeSystem types;

	public TypeTestExpansion(TypeSystem types) {
		this.types = types;
	}

	@Override
	public String getName() {
		return "Is-Ib";
	}

	@Override
	public State apply(State state, Formula truth) throws ResolutionError {
		if (truth instanceof Formula.Is) {
			Formula nTruth = expand((Formula.Is) truth);
			if (nTruth != truth) {
				nTruth = state.allocate(Formulae.simplifyFormula(nTruth, types));
				return state.subsume(this, truth, nTruth);
			}
		}
		return state;
	}

	private Formula expand(Formula.Is e) throws ResolutionError {
		WyalFile.Expr nLhs = e.getExpr();
		Type lhsT = nLhs.getReturnType(types);
		if (lhsT == null) {
			// NOTE: this can arise in a situation where some other type test
			// has yet to be applied. As a result, the given expression cannot
			// currently be typed. Therefore, we have to wait for that other
			// type to be applied before we can proceed.
			return e;
		} else {
			Formula invariant = Formulae.extractTypeInvariant(e.getTypeTest(), nLhs, types);
			// See whether we can do anything useful with this type test.
			boolean isSubtype = types.isSubtype(e.getTypeTest(), lhsT);
			boolean isNotSubtype = types.isSubtype(TypeSystem.negate(e.getTypeTest()), lhsT);
			if (isSubtype && invariant != null) {
				return invariant;
			} else if (isSubtype) {
				return new Formula.Truth(true);
			} else if (isNotSubtype && invariant != null) {
				// FIXME: I think this is broken in the general case. The
				// essential
				// problem boils down to what the subtype test is really telling
				// us.
				// For example, is it saying that the underlying type of the lhs
				// is not
				// a subtype of the negated rhs? I don't think so.
				return invariant;
			} else if (isNotSubtype) {
				return new Formula.Truth(false);
			}
			// At this point, we're stuck with a type test of some sort.
			if (invariant != null) {
				return Formulae.and(invariant, e);
			} else {
				return e;
			}
		}
	}
}
