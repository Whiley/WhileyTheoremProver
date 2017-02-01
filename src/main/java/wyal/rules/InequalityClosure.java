package wyal.rules;

import java.util.ArrayList;

import wyal.lang.WyalFile.Expr;
import wyal.lang.WyalFile.Expr.Polynomial;
import wyal.lang.WyalFile.Formula;
import wyal.lang.WyalFile.Pair;
import wyal.lang.WyalFile.Tuple;
import wyal.util.AutomatedTheoremProver;
import wyal.util.AutomatedTheoremProver.RewriteRule;

public class InequalityClosure implements RewriteRule {

	@Override
	public Formula rewrite(Formula item) {
		if (item instanceof Formula.Conjunct) {
			// We've found a conjunct of terms. Therefore, we want to look
			// through and pick out all inequalities and close over them.
			Formula.Conjunct conjunct = (Formula.Conjunct) item;
			ArrayList<Formula> inferred = new ArrayList<>();
			for (int i = 0; i != conjunct.size(); ++i) {
				Formula ith = conjunct.getOperand(i);
				if (ith instanceof Formula.Inequality) {
					for (int j = i + 1; j != conjunct.size(); ++j) {
						Formula jth = conjunct.getOperand(j);
						if (jth instanceof Formula.Inequality) {
							infer((Formula.Inequality) ith, (Formula.Inequality) jth, inferred);
						}
					}
				}
			}
			if (inferred.size() > 0) {
				// We have inferred some new inequalities. Therefore, update the
				// conjunct to reflect this.
				for(int i=0;i!=conjunct.size();++i) {
					inferred.add(conjunct.getOperand(i));
				}
				System.out.println("INFERRING: ");
				Formula[] items = inferred.toArray(new Formula[inferred.size()]);
				item = Formula.and(items);
				AutomatedTheoremProver.print(conjunct);
				// FIXME: this test is rather inefficient, isn't it?
				if (item.equals(conjunct)) {
					return item;
				} else {
					return item;
				}
			}
		}
		// For the moment, do nothing
		return item;
	}

	private static void infer(Formula.Inequality ith, Formula.Inequality jth, ArrayList<Formula> inferred) {
		//
		Formula op = closeOverInequalities(ith, jth);
		if (op != null) {
			inferred.add(op);
		}
	}

	/**
	 * Close over two inequalities.
	 *
	 * @param ith
	 * @param jth
	 * @return
	 */
	private static Formula closeOverInequalities(Formula.Inequality ith, Formula.Inequality jth) {
		Polynomial ithLowerBound = extractBound(false, ith);
		Polynomial ithUpperBound = extractBound(true, ith);
		Polynomial jthLowerBound = extractBound(false, jth);
		Polynomial jthUpperBound = extractBound(true, jth);

		Pair<Polynomial.Term, Polynomial.Term> lCandidate = selectCandidateTerm(ithLowerBound, jthUpperBound);
		Pair<Polynomial.Term, Polynomial.Term> rCandidate = selectCandidateTerm(jthLowerBound, ithUpperBound);
		Polynomial lhs;
		Polynomial rhs;
		if (lCandidate != null) {
			// FIXME: should be selecting the least candidate
			lhs = rearrangeToRight(ithLowerBound, ithUpperBound, lCandidate.getFirst());
			rhs = rearrangeToLeft(jthLowerBound, jthUpperBound, lCandidate.getSecond());
		} else if (rCandidate != null) {
			lhs = rearrangeToRight(jthLowerBound, jthUpperBound, rCandidate.getFirst());
			rhs = rearrangeToLeft(ithLowerBound, ithUpperBound, rCandidate.getSecond());
		} else {
			return null;
		}

		// FIXME: need to properly construct inequality here.
		// FIXME: also need to check for inequality which can be evaluated to
		// true. This is necessary to prevent repeat applications of this rule
		// which infer true and this is then removed, etc.
		return Formula.lessThan(lhs, rhs);
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
		int i;
		switch (inequality.getOpcode()) {
		case EXPR_lt:
			i = sign ? 1 : 0;
			break;
		case EXPR_gteq:
			i = sign ? 0 : 1;
			break;
		default:
			throw new IllegalArgumentException("Invalid inequality");
		}
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
			Tuple<Expr> ithAtoms = ith.getAtoms();
			if (ithAtoms.size() > 0) {
				for (int j = 0; j != upper.size(); ++j) {
					Polynomial.Term jth = lower.getOperand(j);
					Tuple<Expr> jthAtoms = jth.getAtoms();
					if (jthAtoms.equals(ithAtoms)) {
						// FIXME: we should be selecting the lexiographically
						// least candidate here.
						// FIXME: sign of the constant is also potentially an
						// issue
						return new Pair<>(ith, jth);
					}
				}
			}
		}
		//
		return null;
	}

	private static Polynomial rearrangeToLeft(Polynomial left, Polynomial right, Polynomial.Term term) {
		return rearrange(true, left, right, term);
	}

	private static Polynomial rearrangeToRight(Polynomial left, Polynomial right, Polynomial.Term term) {
		return rearrange(false, left, right, term);
	}

	/**
	 * Rearrange a given inequality such that a given term appears on a given
	 * side, and everything else is moved on to the right side . For example,
	 * consider rearranging these for <code>x</code>:
	 *
	 * <pre>
	 * x + y < 1
	 * </pre>
	 *
	 * The resulting polynomial represents the "right-hand side" which (in this
	 * case) is 1-y. Thus, the resulting inequality would be x < 1 - y.
	 *
	 * @param inequality
	 * @param term
	 */
	private static Polynomial rearrange(boolean toLeft, Polynomial left, Polynomial right, Polynomial.Term term) {
		if (toLeft) {
			right = right.subtract(term);
			return left.add(right.negate());
		} else {
			left = left.subtract(term);
			return right.add(left.negate());
		}
	}
}
