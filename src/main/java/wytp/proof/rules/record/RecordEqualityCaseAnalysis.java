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
package wytp.proof.rules.record;

import wyal.lang.WyalFile.Expr;
import wyal.lang.WyalFile.FieldDeclaration;
import wyal.util.NameResolver;
import wyal.util.NameResolver.ResolutionError;

import static wyal.lang.WyalFile.*;
import wytp.proof.Formula;
import wytp.proof.Proof;
import wytp.proof.Proof.State;
import wytp.proof.rules.Simplification;
import wytp.proof.util.AbstractProofRule;
import wytp.proof.util.Formulae;
import wytp.types.TypeSystem;

/**
 * <p>
 * Handle (non-)equality between expressions of record type. There are two main
 * cases to consider:
 * </p>
 * <ul>
 * <li>
 * <p>
 * <b>Record Equality.</b> The equality case is relatively straightforward.
 * Since we can already rely on congruence closure to handle the general case,
 * we need only consider the specific case of initialiser equality.
 * Specifically, the case when e.g.
 * "<code>{f1:e1, f2:e2, ...} == {f1:e'1, f2:e'2, ...}</code>" which reduces to
 * <code>n</code> assertions of the form "<code>e1 == e'1</code>",
 * "<code>e2 == e'2</code>", etc. Of course, if the set of fields is not a match
 * then the equality fails immediately.
 * </p>
 * </li>
 * <li>
 * <p>
 * <b>Record Non-Equality.</b> This is the more complex case. For a non-equality
 * of the form "<code>e1 != e2</code>" over a record type
 * <code>{T1 f, T2 g, ...}</code> we generate an n-clause disjunct of the form
 * "<code>(e1.f != e'1.f) || (e1.g != e'1.g) || ...</code>". One of the
 * difficulties here is how to handle the case of an open record.
 * </p>
 * </li>
 * </ul>
 *
 * @author David J. Pearce
 *
 */
public class RecordEqualityCaseAnalysis extends AbstractProofRule implements Proof.LinearRule {

	public RecordEqualityCaseAnalysis(Simplification simplify, TypeSystem types) {
		super(simplify, types);
	}

	@Override
	public String getName() {
		return "Req-C";
	}

	@Override
	public State apply(State state, Formula truth) throws ResolutionError {
		if (truth instanceof Formula.Equality) {
			Formula.Equality eq = (Formula.Equality) truth;
			Expr lhs = eq.get(0);
			Expr rhs = eq.get(1);
			Type lhsT = types.inferType(state.getTypeEnvironment(), lhs);
			Type rhsT = types.inferType(state.getTypeEnvironment(), rhs);
			if (lhsT != null && rhsT != null) {
				Type.Record lhsRecord = types.extractReadableRecord(lhsT);
				Type.Record rhsRecord = types.extractReadableRecord(rhsT);
				if (lhsRecord != null && rhsRecord != null) {
					return expandRecordEquality(eq, state);
				}
			} else {
				// NOTE: it is possible to get here in some situations. This can
				// happen as a result of type test which has not yet been
				// properly processed.
			}
		}

		return state;
	}

	private State expandRecordEquality(Formula.Equality eq, Proof.State state) throws ResolutionError {
		Expr lhs = eq.get(0);
		Expr rhs = eq.get(1);
		if (eq.getSign()) {
			// Equality
			if (lhs instanceof Expr.RecordInitialiser && rhs instanceof Expr.RecordInitialiser) {
				return expandRecordInitialiserEquality(eq, (Expr.RecordInitialiser) lhs, (Expr.RecordInitialiser) rhs,
						state);
			}
		} else {
			// Non-Equality
			return expandRecordNonEquality(eq, lhs, rhs, state);
		}
		return state;
	}

	private State expandRecordNonEquality(Formula.Equality eq, Expr lhs, Expr rhs, Proof.State state)
			throws ResolutionError {
		Type lhs_t = types.inferType(state.getTypeEnvironment(), lhs);
		Type.Record lhs_r = types.extractReadableRecord(lhs_t);
		FieldDeclaration[] fields = lhs_r.getFields();
		Formula[] clauses = new Formula[fields.length];
		for (int i = 0; i != fields.length; ++i) {
			Expr lf = new Expr.RecordAccess(lhs, fields[i].getVariableName());
			Expr rf = new Expr.RecordAccess(rhs, fields[i].getVariableName());
			clauses[i] = Formulae.toFormula(new Expr.NotEqual(lf, rf), types);
		}
		// FIXME: what to do for open records?
		Formula disjunct = new Formula.Disjunct(clauses);
		return state.subsume(this, eq, disjunct);
	}

	private State expandRecordInitialiserEquality(Formula.Equality eq, Expr.RecordInitialiser lhs,
			Expr.RecordInitialiser rhs, Proof.State state) throws ResolutionError {
		if (lhs.size() != rhs.size()) {
			// FIXME: for open records this could be possible
			return state.infer(this, new Formula.Truth(false), eq);
		} else {
			Pair<Identifier, Expr>[] lhsFields = lhs.getFields();
			Pair<Identifier, Expr>[] rhsFields = rhs.getFields();
			Formula[] clauses = new Formula[lhsFields.length];
			for (int i = 0; i != lhsFields.length; ++i) {
				Pair<Identifier, Expr> lhsField = lhsFields[i];
				Pair<Identifier, Expr> rhsField = rhsFields[i];
				if (!lhsField.getFirst().equals(rhsField.getFirst())) {
					// FIXME: could do more here --- esp to handle out-of-order
					// field declarations.
					return state.infer(this, new Formula.Truth(false), eq);
				}
				Expr lf = lhsField.getSecond();
				Expr rf = rhsField.getSecond();
				// NOTE: don't need to call construct here, since generating a
				// formula.
				clauses[i] = Formulae.toFormula(new Expr.Equal(lf, rf), types);
			}
			Formula disjunct = new Formula.Conjunct(clauses);
			return state.subsume(this, eq, disjunct);
		}
	}
}
