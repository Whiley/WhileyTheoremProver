package wyal.rules;

import java.util.List;

import wyal.lang.Formula;
import wyal.lang.Proof;
import wyal.lang.SyntacticItem;
import wyal.lang.WyalFile;
import wyal.lang.Proof.State;
import wyal.lang.WyalFile.Expr;
import wyal.lang.WyalFile.Opcode;
import wyal.lang.WyalFile.Tuple;
import wyal.util.Formulae;
import wyal.util.TypeSystem;

public class ArrayIndexCaseAnalysis extends AbstractProofRule implements Proof.LinearRule {

	public ArrayIndexCaseAnalysis(TypeSystem types) {
		super(types);
	}

	@Override
	public String getName() {
		return "ArrInd-C";
	}

	@Override
	public State apply(State state, Formula truth) {
		List<Expr.Operator> matches = extractDefinedTerms(truth,Opcode.EXPR_arridx);
		if (matches.size() > 0) {
			for(int i=0;i!=matches.size();++i) {
				Expr.Operator match = matches.get(i);
				Formula[] cases = generateCaseAnalysis(match, truth, state);
				Formula disjunct = state.allocate(Formulae.simplifyDisjunct(new Formula.Disjunct(cases), types));
				state = state.subsume(this, truth, disjunct);
			}
		}
		return state;
	}

	private Formula[] generateCaseAnalysis(Expr.Operator split, Formula truth, Proof.State state) {
		Formula[] result;
		switch (split.getOpcode()) {
		case EXPR_arridx: {
			Expr src = split.getOperand(0);
			Expr.Polynomial j = (Expr.Polynomial) split.getOperand(1);
			if (src.getOpcode() == Opcode.EXPR_arrupdt) {
				// xs[i:=v][j]
				Expr xs = (Expr) src.getOperand(0);
				Expr.Polynomial i = (Expr.Polynomial) src.getOperand(1);
				Expr v = (Expr) src.getOperand(2);
				result = new Formula[2];
				Formula case1 = (Formula) state.substitute(split, v, truth, types);
				// NOTE: we must call construct here since we are creating a new
				// term from scratch.
				WyalFile.Expr arridx = state.construct(new Expr.Operator(Opcode.EXPR_arridx, xs, j), types);
				Formula case2 = (Formula) state.substitute(split, arridx, truth, types);
				result[0] = Formulae.and(new Formula.ArithmeticEquality(true, i, j), case1);
				result[1] = Formulae.and(new Formula.ArithmeticEquality(false, i, j), case2);
				break;
			} else if (src.getOpcode() == Opcode.EXPR_arrinit) {
				// [a,b,c][j] >= 0
				result = new Formula[src.size()];
				for (int i = 0; i != src.size(); ++i) {
					// a >= 0 && j == 0
					Formula lhs = (Formula) state.substitute(split, src.getOperand(i), truth, types);
					Formula rhs = new Formula.ArithmeticEquality(true, j, Formulae.toPolynomial(i));
					result[i] = Formulae.and(lhs, rhs);
				}
				break;
			}
		}
		default:
			// NOTE: we can arrive here if we extracted a defined term that
			// didn't meet our criteria above.
			return new Formula[0];
		}
		return result;
	}
}
