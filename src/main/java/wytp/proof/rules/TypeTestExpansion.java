package wytp.proof.rules;

import wyal.lang.WyalFile;
import wyal.lang.NameResolver.ResolutionError;
import wyal.lang.WyalFile.Type;
import wytp.proof.Formula;
import wytp.proof.Proof;
import wytp.proof.Proof.State;
import wytp.proof.util.Formulae;
import wytp.types.TypeSystem;

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
				nTruth = Formulae.simplifyFormula(nTruth, types);
				return state.subsume(this, truth, nTruth);
			}
		}
		return state;
	}

	private Formula expand(Formula.Is e) throws ResolutionError {
		System.out.print("EXPANDING: ");
		WyalFile.println(e);
		WyalFile.Expr nLhs = e.getExpr();
		Type lhsT = nLhs.getReturnType(types);
		if (lhsT == null) {
			// NOTE: this can arise in a situation where some other type test
			// has yet to be applied. As a result, the given expression cannot
			// currently be typed. Therefore, we have to wait for that other
			// type to be applied before we can proceed.);
			return e;
		} else {
			Formula invariant = types.extractInvariant(e.getTypeTest(), nLhs);
			// See whether we can do anything useful with this type test.

			// x : int|null && x is nat

			boolean isSubtype = types.isRawSubtype(lhsT, e.getTypeTest());
			boolean isNotSubtype = types.isRawSubtype(lhsT, new Type.Negation(e.getTypeTest()));
			if (isSubtype && invariant != null) {
				return invariant;
			} else if (isSubtype) {
				// int|null x ; x is nat
				return new Formula.Truth(true);
			} else if (isNotSubtype && invariant == null) {
				return new Formula.Truth(false);
			}
			// FIXME: There is a problem here as we really want to replace the
			// type test with a non-constrained version.

			// At this point, we're stuck with a type test of some sort.
			if (invariant != null) {
				return Formulae.and(invariant, e);
			} else {
				return e;
			}
		}
	}
}
