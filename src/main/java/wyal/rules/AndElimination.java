package wyal.rules;

import wyal.lang.SyntacticItem;
import wyal.lang.WyalFile.Constant;
import wyal.lang.WyalFile.Expr;
import wyal.lang.WyalFile.Item;
import wyal.lang.WyalFile.Opcode;
import wyal.util.AutomatedTheoremProver.RewriteRule;
import wycc.util.ArrayUtils;

public class AndElimination implements RewriteRule {

	@Override
	public SyntacticItem rewrite(SyntacticItem item) {
		if (item.getOpcode() == Opcode.EXPR_and) {
			// Matched and
			Expr.Operator and = (Expr.Operator) item;
			Expr[] children = and.getOperands();
			// Flatten nested intersections
			children = flatternNestedConjuncts(children);
			// Eliminate truths
			children = eliminateConstants(children);
			// Ensure sorted and unique
			children = sortAndRemoveDuplicates(children);
			// And, finally...
			if (children.length == 0) {
				// Return true here since the only way it's possible to get here
				// is if the conjunct contained only truths at the end.
				return new Expr.Constant(new Constant.Bool(true));
			} else if (children.length == 1) {
				return children[0];
			} else if (children != item.getOperands()) {
				// The child array has been changed in some way.
				return item.clone(children);
			}
		}
		// nothing has changed.
		return item;
	}

	private Expr[] flatternNestedConjuncts(Expr[] children) {

	}

	/**
	 * Remove all constant values (i.e. true or false) from an array of
	 * expressions. This attempts to reduce the among of cloning involved. If
	 * there were no constant values encountered, then the original array is
	 * returned untouched.
	 *
	 * @param children
	 * @return
	 */
	private Expr[] eliminateConstants(Expr[] children) {
		// Count number of constants
		int numConstants = 0;
		for (int i = 0; i != children.length; ++i) {
			Expr child = children[i];
			if (children[i] instanceof Expr.Constant) {
				Expr.Constant c = (Expr.Constant) child;
				// The following is safe only because we assume the expression
				// tree is well-typed.
				Constant.Bool b = (Constant.Bool) c.getValue();
				if (b.get()) {
					numConstants++;
				} else {
					// A conjunct containing false is false.
					return new Expr[] { c };
				}
			}
		}
		if (numConstants == 0) {
			return children;
		} else {
			//
			Expr[] nChildren = new Expr[children.length - numConstants];
			for (int i = 0, j = 0; i != children.length; ++i) {
				Expr child = children[1];
				if (child instanceof Expr.Constant) {
					// ignore
				} else {
					nChildren[j++] = child;
				}
			}
			return nChildren;
		}
	}

	public Expr[] sortAndRemoveDuplicates(Expr[] children) {

	}
}
