// Copyright 2017 David J. Pearce
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

import java.util.Arrays;

import wyal.lang.WyalFile;
import wyal.lang.NameResolver.ResolutionError;
import wyal.lang.WyalFile.Expr;
import wyal.lang.WyalFile.Pair;
import wyal.lang.WyalFile.Expr.Polynomial;
import wytp.proof.Formula;
import wytp.proof.Proof;
import wytp.proof.Proof.State;
import wytp.proof.util.Formulae;
import wytp.types.TypeSystem;

/**
 * Responsible for emplying a form of <i>transitive closure</i> over
 * inequalities. For example, if <code>x < y</code> and <code>y < z</code> then
 * this rule might infer that <code>x < z</code>. To reduce the number of
 * unnecessary inferences, the rule is selective about how to determine new
 * inequalities. Specifically, it relies on a lexiographic ordering of terms and
 * will only produce inferences for the least ordered term in any given pair of
 * inequualities.
 *
 * @author David J. Pearce
 *
 */
public class InequalityIntroduction implements Proof.LinearRule {
	private final TypeSystem types;

	public InequalityIntroduction(TypeSystem types) {
		this.types = types;
	}

	@Override
	public String getName() {
		return "Ieq-I";
	}

	@Override
	public State apply(Proof.State state, Formula newTruth) throws ResolutionError {

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

	private State closeOver(Formula.Inequality ith, Formula.Inequality jth, State state) throws ResolutionError {
		//
		Formula inferred = closeOver(ith, jth);
		if (inferred != null) {
			state = state.infer(this, inferred, ith, jth);
		}
		return state;
	}


	/**
	 * Close over two inequalities. This may or may not produce a new inequality
	 * as a result. For example, closing over <code>3 < x</code> and
	 * <code>x < y</code> gives <code>3 < y</code>. Observe that, for this
	 * operation to succeed, there must exist a term common to both
	 * inequalities. In the case that multiple candidate terms exist, then the
	 * lexiographically least is selected.
	 *
	 * <b>NOTE:</b> this currently assumes that the inequalities are balanced.
	 *
	 * @param ith
	 * @param jth
	 * @return
	 */
	public Formula closeOver(Formula.Inequality ith, Formula.Inequality jth) throws ResolutionError {
		Polynomial ithLowerBound = extractBound(false, ith);
		Polynomial ithUpperBound = extractBound(true, ith);
		Polynomial jthLowerBound = extractBound(false, jth);
		Polynomial jthUpperBound = extractBound(true, jth);

		Pair<Polynomial.Term, Polynomial.Term> lCandidate = selectCandidateTerm(ithLowerBound, jthUpperBound);
		Pair<Polynomial.Term, Polynomial.Term> rCandidate = selectCandidateTerm(jthLowerBound, ithUpperBound);
		Polynomial.Term lhsCandidate;
		Polynomial lower;
		Polynomial upper;
		if (lCandidate != null && rCandidate == null) {
			lower = rearrangeForLowerBound(ithLowerBound, ithUpperBound, lCandidate.getFirst());
			upper = rearrangeForUpperBound(jthLowerBound, jthUpperBound, lCandidate.getSecond());
			lhsCandidate = lCandidate.getFirst();
		} else if (lCandidate == null && rCandidate != null) {
			lower = rearrangeForLowerBound(ithLowerBound, ithUpperBound, rCandidate.getSecond());
			upper = rearrangeForUpperBound(jthLowerBound, jthUpperBound, rCandidate.getFirst());
			lhsCandidate = rCandidate.getSecond();
		} else if(lCandidate == null && rCandidate == null) {
			return null;
		} else if(lessThan(lCandidate.getFirst(),rCandidate.getFirst())) {
			lower = rearrangeForLowerBound(ithLowerBound, ithUpperBound, lCandidate.getFirst());
			upper = rearrangeForUpperBound(jthLowerBound, jthUpperBound, lCandidate.getSecond());
			lhsCandidate = lCandidate.getFirst();
		} else {
			lower = rearrangeForLowerBound(ithLowerBound, ithUpperBound, rCandidate.getSecond());
			upper = rearrangeForUpperBound(jthLowerBound, jthUpperBound, rCandidate.getFirst());
			lhsCandidate = rCandidate.getSecond();
		}
		if(lower.equals(upper)) {
			return new Formula.ArithmeticEquality(true, Formulae.toPolynomial(lhsCandidate), lower);
		} else {
			// Result is not-strict as had something like ... <= x <= ...
			return Formulae.greaterOrEqual(upper,lower);
		}
	}

	private static boolean lessThan(Polynomial.Term lhs, Polynomial.Term rhs) {
		return lhs.getIndex() < rhs.getIndex();
	}

	/**
	 * Extract a given bound from the inequality. Here, true is upper and false
	 * is lower.
	 *
	 * @param sign
	 * @param inequality
	 * @return
	 */
	private static Polynomial extractBound(boolean sign, Formula.Inequality inequality) {
		int i = sign ? 0 : 1;
		return (Polynomial) inequality.getOperand(i);
	}


	/**
	 * <p>
	 * Determine a suitable term (if one exists) for rearranging the two
	 * inequalities. A candidate term must be common to both and involve at
	 * least one variable, and should appear on opposite sides of the
	 * inequalities. The selected candidate then has the lowest ordering of any
	 * possible term. For example, consider these two options:
	 * </p>
	 *
	 * <pre>
	 * x < y + z
	 * x + y > z
	 * </pre>
	 *
	 * <p>
	 * For these two equations, the candidate terms are <code>x</code> and
	 * <code>z</code>. Since <code>y</code> is an upper bound on both, it is not
	 * considered. Then, <code>x</code> is selected as the actual term for
	 * rearranging since it is lexiographically lower than <code>z</code>.
	 * </p>
	 *
	 * @param ith
	 * @param jth
	 * @return
	 */
	private static Pair<Polynomial.Term, Polynomial.Term> selectCandidateTerm(Polynomial lower, Polynomial upper) {
		for (int i = 0; i != lower.size(); ++i) {
			Polynomial.Term ith = lower.getOperand(i);
			Expr[] ithAtoms = ith.getAtoms();
			if (ithAtoms.length > 0) {
				for (int j = 0; j != upper.size(); ++j) {
					Polynomial.Term jth = upper.getOperand(j);
					Expr[] jthAtoms = jth.getAtoms();
					if (Arrays.equals(ithAtoms, jthAtoms)) {
						// Select lexicographically least term
						return new Pair<>(min(ith, jth),max(ith,jth));
					}
				}
			}
		}
		//
		return null;
	}

	private static Polynomial.Term min(Polynomial.Term lhs, Polynomial.Term rhs) {
		if(lhs.getIndex() < rhs.getIndex()) {
			return lhs;
		} else {
			return rhs;
		}
	}

	private static Polynomial.Term max(Polynomial.Term lhs, Polynomial.Term rhs) {
		if(lhs.getIndex() > rhs.getIndex()) {
			return lhs;
		} else {
			return rhs;
		}
	}

	/**
	 * Rearrange a given equation such that the given term appears on the
	 * right-hand side, and everything else is moved on to the left side. For
	 * example, consider rearranging these for <code>x</code>:
	 *
	 * <pre>
	 * 1 < x + y
	 * </pre>
	 *
	 * The resulting polynomial represents the "left-hand side" which (in this
	 * case) is 1-y. Thus, the rearranged inequality would be 1 - y < x.
	 *
	 * @param lhs
	 *            The "left-hand side" of the equation.
	 * @param rhs
	 *            The "right-hand side" of the equation.
	 * @param term
	 *            the given term being rearranged for.
	 */
	private static Polynomial rearrangeForLowerBound(Polynomial lhs, Polynomial rhs, Polynomial.Term term) {
		rhs = rhs.subtract(term);
		return lhs.add(rhs.negate());
	}

	/**
	 * Rearrange a given equation such that the given term appears on the
	 * left-hand side, and everything else is moved on to the right side. For
	 * example, consider rearranging these for <code>x</code>:
	 *
	 * <pre>
	 * x + y < 1
	 * </pre>
	 *
	 * The resulting polynomial represents the "right-hand side" which (in this
	 * case) is 1-y. Thus, the rearranged inequality would be x < 1 - y.
	 *
	 * @param lhs
	 *            The "left-hand side" of the equation.
	 * @param rhs
	 *            The "right-hand side" of the equation.
	 * @param term
	 *            the given term being rearranged for.
	 */
	private static Polynomial rearrangeForUpperBound(Polynomial lhs, Polynomial rhs, Polynomial.Term term) {
		lhs = lhs.subtract(term);
		return rhs.add(lhs.negate());
	}
}
