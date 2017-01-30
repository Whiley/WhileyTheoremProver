package wyal.rules;

import java.util.Arrays;

import wyal.lang.SyntacticItem;
import wyal.lang.WyalFile.Expr;
import wyal.lang.WyalFile.Expr.Polynomial;
import wyal.lang.WyalFile.Opcode;
import wyal.util.AutomatedTheoremProver.RewriteRule;

public class ArithmeticSimplification implements RewriteRule {
	// TODO:
	// Evaluate constant expressions
	// combine constants
	// Normalise substraction
	// Flatten sums
	// Distribute multiplication over addition
	// GCD

	@Override
	public SyntacticItem rewrite(SyntacticItem item) {
		switch(item.getOpcode()) {
		case EXPR_lt: {
			return simplify((Expr.Operator) item);
		}
		}
	}

	private Expr simplify(Expr.Operator expr) {
		Expr[] children = expr.getOperands();
		Expr[] nChildren = children;

		for(int i=0;i!=nChildren.length;++i) {
			Expr child = children[i];
			Expr nChild = simplify(child);
			if(child != nChild && children == nChildren) {
				nChildren = Arrays.copyOf(children, children.length);
			}
			nChildren[i] = nChild;
		}

		return expr.clone(nChildren);
	}

	/**
	 * Convert an arbitrary expression to a polynomial.
	 *
	 * @param e
	 * @return
	 */
	private Polynomial toPolynomial(Expr e) {
		switch(e.getOpcode()) {
		case EXPR_add:
		case EXPR_mul:
		case EXPR_sub:{
			Expr.Operator op = (Expr.Operator) e;
			return toPolynomial(e.getOpcode(),op.getOperands());
		}
		default:
			// For all other cases, no simplification is performed. For example,
			// a variable access remains as a variable access, etc.
			return e;
		}
	}

	private Polynomial toPolynomial(Opcode opcode, Expr...children) {
		Polynomial[] nChildren = toPolynomial(children);
		Polynomial result = nChildren[0];
		for(int i=1;i!=nChildren.length;++i) {
			result = add(result(nChildren[i]));
		}
		return result;
	}

	/**
	 * Recursively simplify a sequence of zero or more expressions. If no
	 * simplifications occur, then the original array is returned untouched.
	 *
	 * @param children
	 * @return
	 */
	private Polynomial[] toPolynomial(Expr... children) {
		Expr[] nChildren = children;

		for (int i = 0; i != nChildren.length; ++i) {
			Expr child = children[i];
			Expr nChild = simplify(child);
			if (child != nChild && children == nChildren) {
				nChildren = Arrays.copyOf(children, children.length);
			}
			nChildren[i] = nChild;
		}
		//
		return nChildren;
	}

	private Polynomial add(Polynomial lhs, Polynomial rhs) {

	}
}
