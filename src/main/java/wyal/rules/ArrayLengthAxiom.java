package wyal.rules;

import java.util.ArrayList;
import java.util.List;

import wyal.lang.Formula;
import wyal.lang.Proof;
import wyal.lang.Proof.State;
import wyal.lang.WyalFile.Expr;
import wyal.lang.WyalFile.Opcode;
import wyal.lang.WyalFile.Expr.Polynomial;
import wyal.util.Formulae;
import wyal.util.TypeSystem;
import wyal.lang.WyalFile;
import wyal.lang.NameResolver.ResolutionError;

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
public class ArrayLengthAxiom implements Proof.LinearRule {
	private final TypeSystem types;

	public ArrayLengthAxiom(TypeSystem types) {
		this.types = types;
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
			List<WyalFile.Expr> matches = findMatches(inequality.getOperand(1));
			for (int i = 0; i != matches.size(); ++i) {
				WyalFile.Expr match = matches.get(i);
				Polynomial len = Formulae.toPolynomial(match);
				Polynomial zero = Formulae.toPolynomial(0);
				Formula axiom = Formulae.simplifyFormula(Formulae.greaterOrEqual(len, zero),types);
				state = state.infer(this, state.allocate(axiom), inequality);
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
	private List<WyalFile.Expr> findMatches(Expr.Polynomial poly) {
		ArrayList<WyalFile.Expr> matches = new ArrayList<>();
		for (int i = 0; i != poly.size(); ++i) {
			Polynomial.Term term = poly.getOperand(i);
			Expr[] atoms = term.getAtoms();
			for (int j = 0; j != atoms.length; ++j) {
				Expr atom = atoms[j];
				if (atom.getOpcode() == Opcode.EXPR_arrlen) {
					matches.add(atom);
				}
			}
		}
		return matches;
	}
}
