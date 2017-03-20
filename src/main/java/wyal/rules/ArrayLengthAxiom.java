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
import wyal.lang.WyalFile;

public class ArrayLengthAxiom implements Proof.LinearRule {

	@Override
	public String getName() {
		return "ArrLen-I";
	}

	@Override
	public State apply(Proof.State state, Formula truth) {
		if (truth instanceof Formula.Inequality) {
			Formula.Inequality inequality = (Formula.Inequality) truth;
			List<WyalFile.Expr> matches = findMatches(inequality.getOperand(1));
			for (int i = 0; i != matches.size(); ++i) {
				WyalFile.Expr match = matches.get(i);
				Polynomial len = Formulae.toPolynomial(match);
				Polynomial zero = Formulae.toPolynomial(0);
				Formula axiom = state.allocate(Formulae.greaterOrEqual(len, zero));
				state = state.infer(this, axiom, inequality);
			}
			return state;
		}
		// No change in the normal case
		return state;
	}

	/**
	 * <p>
	 * Find matches which can be used to instantiate the axiom. A match is
	 * simply an occurence of an array length expression in a given polynomial.
	 * The is that it has to be on the positive side of an inequality. For
	 * example, "|xs|" matches in "0 < |xs|". In contrast, "|xs|" does not match
	 * in "|xs| > 0". The reason for this simply that the instantiated axiom
	 * cannot benefit the latter case.
	 * </p>
	 * <p>
	 * <b>NOTE:</b> In fact, this matching scheme is relatively primitive and
	 * could be adjusted further to reduce unnecessary firings. For example,
	 * there is no point in matching "xs" in "1 < |xs|" since we cannot reach a
	 * contradiction.
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
