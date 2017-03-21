package wyal.rules;

import wyal.lang.Formula;
import wyal.lang.Proof;
import wyal.lang.SyntacticItem;
import wyal.lang.Proof.State;
import wyal.lang.WyalFile.Expr;
import wyal.lang.WyalFile.Opcode;
import wyal.util.Formulae;
import wyal.util.TypeSystem;

public class ArrayIndexCaseAnalysis implements Proof.LinearRule {
	private final TypeSystem types;

	public ArrayIndexCaseAnalysis(TypeSystem types) {
		this.types = types;
	}
	@Override
	public String getName() {
		return "ArrInd-C";
	}

	@Override
	public State apply(State state, Formula truth) {
		Expr split = findCaseAnalysis(truth);
		if (split != null) {
			Formula[] cases = generateCaseAnalysis(split, truth);
			Formula disjunct = state.allocate(Formulae.simplifyDisjunct(new Formula.Disjunct(cases), types));
			state = state.subsume(this, truth, disjunct);
		}
		return state;
	}

	/**
	 * A split point is a subexpression which can be divided into two or more
	 * "options". For example, the expression <code>xs[i:=0][j] >= 0</code> is
	 * broken down into
	 * <code>(j == i && 0 >= 0) || (j != i && xs[j] >= 0)</code>.
	 *
	 * @param e
	 * @return
	 */
	private Expr findCaseAnalysis(Expr e) {
		switch (e.getOpcode()) {
		case EXPR_arridx: {
			if (e.getOperand(0).getOpcode() == Opcode.EXPR_arrupdt) {
				// This represents a split point.
				return e;
			} else if (e.getOperand(0).getOpcode() == Opcode.EXPR_arrinit) {
				return e;
			}
		}
		case EXPR_forall:
			// Don't extract case splitters from quantified formulae. There's
			// no point until they are instantiated!
			return null;
		}
		// Generic traversal, returning first split point encountered.
		for (int i = 0; i != e.size(); ++i) {
			SyntacticItem item = e.getOperand(i);
			if (item instanceof Expr) {
				Expr cf = findCaseAnalysis((Expr) item);
				if (cf != null) {
					return cf;
				}
			}
		}
		// No split points found
		return null;
	}

	private Formula[] generateCaseAnalysis(Expr split, Formula truth) {
		Formula[] result;
		switch (split.getOpcode()) {
		case EXPR_arridx: {
			Expr.Operator src = (Expr.Operator) split.getOperand(0);
			Expr.Polynomial j = (Expr.Polynomial) split.getOperand(1);
			if (src.getOpcode() == Opcode.EXPR_arrupdt) {
				// xs[i:=v][j]
				Expr xs = src.getOperand(0);
				Expr.Polynomial i = (Expr.Polynomial) src.getOperand(1);
				Expr v = src.getOperand(2);
				result = new Formula[2];
				Formula case1 = (Formula) Formulae.substitute(split, v, truth);
				Formula case2 = (Formula) Formulae.substitute(split, new Expr.Operator(Opcode.EXPR_arridx, xs, j),
						truth);
				result[0] = Formulae.and(new Formula.ArithmeticEquality(true, i, j), case1);
				result[1] = Formulae.and(new Formula.ArithmeticEquality(false, i, j), case2);
				break;
			} else if (src.getOpcode() == Opcode.EXPR_arrinit) {
				// [a,b,c][j] >= 0
				result = new Formula[src.size()];
				for (int i = 0; i != src.size(); ++i) {
					// a >= 0 && j == 0
					Formula lhs = (Formula) Formulae.substitute(split, src.getOperand(i), truth);
					Formula rhs = new Formula.ArithmeticEquality(true, j, Formulae.toPolynomial(i));
					result[i] = Formulae.and(lhs, rhs);
				}
				break;
			}
		}
		default:
			throw new IllegalArgumentException("unknown split kind encountered");
		}
		return result;
	}
}
