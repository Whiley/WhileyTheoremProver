package wyal.rules;

import java.util.ArrayList;
import java.util.List;

import wyal.lang.SyntacticItem;
import wyal.lang.WyalFile.Expr;
import wyal.lang.WyalFile.Opcode;
import wyal.util.AutomatedTheoremProver.RewriteRule;

public class InequalityClosure implements RewriteRule {

	@Override
	public SyntacticItem rewrite(SyntacticItem item) {
		if(item.getOpcode() == Opcode.EXPR_and) {
			// We've found a conjunct of terms. Therefore, we want to look
			// through and pick out all inequalities and close over them.
			Expr.Operator conjunct = (Expr.Operator) item;
			ArrayList<Expr.Operator> inferred = new ArrayList<>();
			for(int i=0;i!=conjunct.size();++i) {
				Expr ith = conjunct.getOperand(i);
				if(isInequality(ith)) {
					for(int j=i+1;j!=conjunct.size();++j) {
						Expr jth = conjunct.getOperand(j);
						if(isInequality(jth)) {
							infer(ith,jth,inferred);
						}
					}
				}
			}
		}
	}

	private static boolean isInequality(Expr term) {
		switch (term.getOpcode()) {
		case EXPR_lt:
		case EXPR_lteq:
		case EXPR_gt:
		case EXPR_gteq:
			return true;
		}
		return false;
	}

}
