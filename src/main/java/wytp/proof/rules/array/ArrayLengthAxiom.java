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
package wytp.proof.rules.array;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

import wyal.lang.WyalFile.Expr;
import wyal.util.NameResolver;
import wyal.util.NameResolver.ResolutionError;
import wytp.proof.Formula;
import wytp.proof.Proof;
import wytp.proof.Proof.State;
import wytp.proof.rules.Simplification;
import wytp.proof.util.AbstractProofRule;
import wytp.proof.util.Formulae;
import wytp.types.TypeSystem;
import wyal.lang.WyalFile;

/**
 * <p>
 * Responsible for inferring that a given <i>array length expression</i> (e.g.
 * |xs|) is non-negative (i.e. <code>|xs| >= 0</code>) at appropriate moments to
 * help find a contradiction. In otherwords, this rule implements the axiom that
 * <i>arrays</i> cannot have negative length. For example, consider a simple
 * assertion such as the following:
 * </p>
 *
 * <pre>
 * assert:
 *  forall(int[] xs):
 *      |xs| >= 0
 * </pre>
 * <p>
 * This assertion shoud be easily proven. To do this following
 * proof-by-contradiction requires showing that <code>|xs| < 0</code> leads to a
 * contradiction. This rule essentially looks for such situations and implicitly
 * infers <code>|xs| >= 0</code> which then gives rise to the contradiction.
 * </p>
 * <p>
 * <b>NOTE:</b> An important aspect of this rule is when it should and should
 * not fire. A simple (expensive) strategy is to fire whenever an array length
 * expression is encountered --- but this is wasteful. For example, in
 * <code>f(xs) >= 0</code> there is no point inferring <code>|xs| >= 0</code> as
 * this cannot lead to a contradiction. Likewise, in <code>|xs| > 0</code> there
 * is equally no point in inferring <code>|xs| >= 0</code> as this is already
 * implied. This rule therefore fires only when <code>|xs|</code> is a positive
 * top-level term on an inequality. In fact, this matching scheme could be
 * further improved to reduce unnecessary firings. For example, there is no
 * point in matching "xs" in "1 < |xs|" since we cannot reach a contradiction.
 * </p>
 *
 * @param poly
 * @return
 */
public class ArrayLengthAxiom extends AbstractProofRule implements Proof.LinearRule {

	public ArrayLengthAxiom(Simplification simplify,TypeSystem types) {
		super(simplify,types);
	}

	@Override
	public String getName() {
		return "ArrLen-I";
	}

	@Override
	public State apply(Proof.State state, Formula truth) throws ResolutionError {
		// FIXME: there is a bug here because we might not find an array length
		// expression; rather we might find only the representative from its
		// equivalence class.
		if (truth instanceof Formula.Inequality) {
			Formula.Inequality inequality = (Formula.Inequality) truth;
			List<WyalFile.Expr> matches = findMatches(inequality.get(1));
			for (int i = 0; i != matches.size(); ++i) {
				WyalFile.Expr match = matches.get(i);
				Expr len = match;
				Expr zero = new Expr.Constant(new WyalFile.Value.Int(0));
				Formula axiom = Formulae.greaterOrEqual(len, zero);
				state = state.infer(this, simp.simplify(axiom), inequality);
			}
			return state;
		}
		// No change in the normal case
		return state;
	}

	/**
	 * <p>
	 * Find matches which can be used to instantiate the axiom. A match is
	 * simply an occurrence of an array length expression in a given polynomial.
	 * The is that it has to be on the positive side of an inequality. For
	 * example, "|xs|" matches in "0 < |xs|". In contrast, "|xs|" does not match
	 * in "|xs| > 0". The reason for this simply that the instantiated axiom
	 * cannot benefit the latter case.
	 * </p>
	 *
	 * @param poly
	 * @return
	 */
	private List<WyalFile.Expr> findMatches(Expr poly) {
		if (poly instanceof Expr.Operator) {
			ArrayList<WyalFile.Expr> matches = new ArrayList<>();
			Expr.Operator op = (Expr.Operator) poly;
			switch (op.getOpcode()) {
			case WyalFile.EXPR_arrlen:
				matches.add(poly);
				break;
			case WyalFile.EXPR_add:
			case WyalFile.EXPR_sub:
			case WyalFile.EXPR_mul:
			case WyalFile.EXPR_div:
			case WyalFile.EXPR_rem:
				for (int i = 0; i != poly.size(); ++i) {
					Expr term = op.get(i);
					matches.addAll(findMatches(term));
				}
			}
			return matches;
		} else {
			return Collections.EMPTY_LIST;
		}
	}
}
