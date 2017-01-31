package wyal.rules;

import wyal.lang.SyntacticItem;
import wyal.lang.WyalFile.Expr;
import wyal.lang.WyalFile.Opcode;
import wyal.util.AutomatedTheoremProver.RewriteRule;

public class QuantifierElimination implements RewriteRule {

	@Override
	public SyntacticItem rewrite(SyntacticItem item) {
		if(item instanceof Expr.Quantifier) {
			return rewrite((Expr.Quantifier) item);
		} else {
			return item;
		}
	}

	private SyntacticItem rewrite(Expr.Quantifier e) {
		if(e.getBody().getOpcode() == Opcode.EXPR_const) {
			// This is a very simple case wherethe body of the quantifier has
			// been reduced to a constant.
			return e.getBody();
		} else {
			return e;
		}
	}
}
