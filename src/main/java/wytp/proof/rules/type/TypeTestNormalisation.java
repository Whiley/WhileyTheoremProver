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
package wytp.proof.rules.type;

import wyal.lang.WyalFile.Expr;
import wyal.lang.WyalFile.FieldDeclaration;
import wyal.lang.WyalFile.Type;
import wyal.util.NameResolver;
import wyal.util.NameResolver.ResolutionError;
import wytp.proof.Formula;
import wytp.proof.Proof;
import wytp.proof.Proof.State;
import wytp.proof.rules.Simplification;
import wytp.proof.util.AbstractClosureRule;
import wytp.types.TypeSystem;

/**
 * <p>
 * Responsible for normalising type tests involving record accesses. For
 * example, consider the following assertion:
 * </p>
 *
 * <pre>
 * type Point is {null|int x, null|int y}
 *
 * assert:
 *    forall(Point p):
 *       if:
 *          p.x is !null
 *       then:
 *          p.x is int
 * </pre>
 * <p>
 * In solving this, we end up with truths <code>p.x is !null</code> and
 * <code>p.x is int</code>. These are then refined by this rule to be
 * <code>p is {!null x, ...}</code> and <code>p is {int x, ...}</code>. Doing
 * this allows the variable to be exposed which, in turn, enables a retyping of
 * that variable to give the contradiction.
 * </p>
 *
 * @author David J. Pearce
 *
 */
public class TypeTestNormalisation extends AbstractClosureRule implements Proof.LinearRule {

	public TypeTestNormalisation(Simplification simplify,TypeSystem types) {
		super(simplify,types);
	}

	@Override
	public String getName() {
		return "Is-N";
	}

	@Override
	public State apply(Proof.Delta.Set existingTruths, Proof.State head, Formula newTruth) throws ResolutionError {
		if (newTruth instanceof Formula.Is) {
			Formula.Is test = (Formula.Is) newTruth;
			// Attempt to normalise this type test by expanding record accesses.
			Formula.Is normalisedTest = normalise(test);
			// Check whether or not we managed to expand it.
			if (normalisedTest != test) {
				// Yes, we succeeded in normalising this test ... therefore, we
				// subsume the original test and replace it with the
				// generalisation.
				head = head.subsume(this, test, normalisedTest);
			}
		}
		return head;
	}

	/**
	 * Normalise a given type test of the form <code>p.x is T</code> to
	 * <code>p is {T x, ...}</code>.
	 *
	 * @param test
	 *            The test to be normalised
	 * @return
	 * @throws ResolutionError
	 */
	private Formula.Is normalise(Formula.Is test) throws ResolutionError {
		Expr lhs = test.getTestExpr();
		if (lhs instanceof Expr.RecordAccess) {
			Expr.RecordAccess ra = (Expr.RecordAccess) lhs;
			Type type = test.getTestType();
			// Type lhsT = types.inferType(state.getTypeEnvironment(), lhs);
			// if(lhsT instanceof Type.Record) {
			// Type.Record rec = (Type.Record) lhsT;
			// // FIXME: could potentially perform an extraction here.
			// FieldDeclaration[] fields = rec.getFields();
			// FieldDeclaration[] nFields = Arrays.copyOf(fields,fields.length);
			//
			// }
			FieldDeclaration[] fields = new FieldDeclaration[1];
			fields[0] = new FieldDeclaration(type, ra.getField());
			return normalise(new Formula.Is(ra.getSource(), new Type.Record(true, fields)));
		} else {
			return test;
		}
	}
}
