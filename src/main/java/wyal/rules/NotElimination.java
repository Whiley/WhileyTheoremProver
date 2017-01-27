package wyal.rules;

import wyal.lang.SyntacticItem;
import wyal.lang.WyalFile.Expr;
import wyal.lang.WyalFile.Opcode;
import wyal.util.AutomatedTheoremProver.RewriteRule;

public class NotElimination implements RewriteRule {

	@Override
	public SyntacticItem rewrite(SyntacticItem item) {
		if(item.getOpcode() == Opcode.EXPR_not) {
			// Matched not(...)
			Expr child = (Expr) item.getOperand(0);
			Opcode opcode = child.getOpcode();
			switch(opcode) {
			case EXPR_not:
				// !!x ---> x
				return child.getOperand(0);
			case EXPR_and:
			case EXPR_or: {
				// (1) !(x1 && ... && xn) ---> (!x1) || ... || !(xn)
				// (2) !(x1 || ... || xn)  ---> (!x1) && ... && !(xn)
				Expr[] nChildren = new Expr[child.size()];
				for(int i=0;i!=nChildren.length;++i) {
					nChildren[i] = not((Expr) child.getOperand(i));
				}
				return new Expr.Operator(invert(opcode), nChildren);
			}
			case EXPR_forall:
			case EXPR_exists: {
				// (1) forall(...).e ---> exists(...).!e
				// (2) exists(...).e ---> forall(...).!e
				Expr.Quantifier q = (Expr.Quantifier) child;
				Expr body = not(q.getBody());
				return new Expr.Quantifier(invert(opcode), q.getParameters(), body);
			}
			case EXPR_implies: {
				// !(A ==> B) ---> A && !B
				Expr.Operator operator = (Expr.Operator) child;
				Expr lhs = operator.getOperand(0);
				Expr rhs = operator.getOperand(0);
				return new Expr.Operator(Opcode.EXPR_and, lhs, not(rhs));
			}
			case EXPR_eq:
			case EXPR_neq:
			case EXPR_lt:
			case EXPR_lteq:
			case EXPR_gt:
			case EXPR_gteq: {
				Expr.Operator operator = (Expr.Operator) child;
				return new Expr.Operator(invert(opcode), operator.getOperands());
			}
			default:
			}
		}
		// Default case, no rewrite applied
		return item;
	}

	private Expr not(Expr e) {
		return new Expr.Operator(Opcode.EXPR_not, e);
	}

	private Opcode invert(Opcode opcode) {
		switch(opcode) {
		case EXPR_or:
			return Opcode.EXPR_and;
		case EXPR_and:
			return Opcode.EXPR_or;
		case EXPR_forall:
			return Opcode.EXPR_exists;
		case EXPR_exists:
			return Opcode.EXPR_forall;
		case EXPR_eq:
			return Opcode.EXPR_neq;
		case EXPR_neq:
			return Opcode.EXPR_eq;
		case EXPR_lt:
			return Opcode.EXPR_gteq;
		case EXPR_lteq:
			return Opcode.EXPR_gt;
		case EXPR_gt:
			return Opcode.EXPR_lteq;
		case EXPR_gteq:
			return Opcode.EXPR_lt;
		default:
			throw new IllegalArgumentException("Cannot invert opcode: " + opcode);
		}
	}
}