// Copyright 2011 The Whiley Project Developers
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//    http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.
package wytp.proof.rules;

import wyal.lang.WyalFile;
import wyal.lang.WyalFile.*;
import wyal.util.NameResolver;
import wyal.util.NameResolver.ResolutionError;
import wytp.proof.Formula;
import wytp.proof.Proof;
import wytp.proof.Formula.ArithmeticEquality;
import wytp.proof.Formula.Conjunct;
import wytp.proof.Formula.Inequality;
import wytp.proof.Formula.Quantifier;
import wytp.proof.Proof.State;
import wytp.proof.util.AbstractProofRule;
import wytp.proof.util.Formulae;
import wytp.types.TypeSystem;

public class EqualityCaseAnalysis extends AbstractProofRule implements Proof.LinearRule {

	public EqualityCaseAnalysis(Simplification simplify,TypeSystem types) {
		super(simplify,types);
	}

	@Override
	public String getName() {
		return "Neq-C";
	}

	@Override
	public State apply(State state, Formula truth) throws ResolutionError {
		if (truth instanceof Formula.ArithmeticEquality) {
			Formula.ArithmeticEquality eq = (Formula.ArithmeticEquality) truth;
			if (!eq.getSign()) {
				Expr lhs = eq.get(0);
				Expr rhs = eq.get(1);
				// For an arithmetic equality of the form x != y, we return a
				// disjunction of the form (x < y) || (x > y). This is not
				// necessarily the most efficient thing to do. However, for our
				// purposes, this works well enough for now.
				Inequality lt = Formulae.lessThan(lhs, rhs);
				Inequality gt = Formulae.lessThan(rhs, lhs);
				Formula disjunct = new Formula.Disjunct(lt, gt);
				return state.subsume(this, truth, disjunct);
			}
		} else if (truth instanceof Formula.Equality) {
			Formula.Equality eq = (Formula.Equality) truth;
			Expr lhs = eq.get(0);
			Expr rhs = eq.get(1);
			Type lhsT = types.inferType(state.getTypeEnvironment(), lhs);
			Type rhsT = types.inferType(state.getTypeEnvironment(), rhs);
			if (lhsT != null && rhsT != null) {
				Type intersection = new Type.Intersection(new Type[]{lhsT, rhsT});
				//
				if (types.isRawSubtype(new Type.Void(), intersection)) {
					// In this case, no possible intersection exists between the
					// lhs and rhs. Therefore, we're done as this equality
					// cannot ever be true.
					return state.subsume(this, truth, new Formula.Truth(true));
				} else if (types.isRawSubtype(new Type.Bool(), lhsT) && types.isRawSubtype(new Type.Bool(), rhsT)) {
					return expandBooleanEquality(eq, state);
				}
			} else {
				// NOTE: it is possible to get here in some situations. This can
				// happen as a result of type test which has not yet been
				// properly processed.
			}
		}

		return state;
	}

	private State expandBooleanEquality(Formula.Equality eq, Proof.State state) throws ResolutionError {
		Expr lhs = eq.get(0);
		Expr rhs = eq.get(1);
		//
		Formula lhs_f = Formulae.toFormula(lhs, types);
		Formula rhs_f = Formulae.toFormula(rhs, types);
		//
		// FIXME: I have a feeling we can do better here. Especially, in the
		// case of an equality I don't think we want to do anything. In the case
		// of an inequality (e.g. x==y), I think we want to generate an equality
		// (x == !y) or similar.
		//
		if(eq.getSign()) {
			Formula l = new Conjunct(lhs_f, rhs_f);
			Formula r = new Conjunct(Formulae.invert(lhs_f), Formulae.invert(rhs_f));
			Formula disjunct = new Formula.Disjunct(l, r);
			return state.subsume(this, eq, disjunct);
		} else {
			Formula l = new Conjunct(Formulae.invert(lhs_f),rhs_f);
			Formula r = new Conjunct(lhs_f,Formulae.invert(rhs_f));
			Formula disjunct = new Formula.Disjunct(l, r);
			// NOTE: at the moment, we can't do a subsume here because we can
			// end up losing critical information.
			return state.infer(this, simp.simplify(disjunct), eq);
		}
	}
}
