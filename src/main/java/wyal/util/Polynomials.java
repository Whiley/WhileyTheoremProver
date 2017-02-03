package wyal.util;

import java.math.BigInteger;
import java.util.Arrays;

import wyal.lang.WyalFile.Expr;
import wyal.lang.WyalFile.Opcode;
import wyal.lang.WyalFile.Tuple;
import wyal.lang.WyalFile.Value;
import wyal.lang.Formula;
import wyal.lang.Formula.Polynomial;

public class Polynomials {

	/**
	 * Recursively simplify a sequence of zero or more expressions. If no
	 * simplifications occur, then the original array is returned untouched.
	 *
	 * @param children
	 * @return
	 */
	public static Expr[] toPolynomial(Expr... children) {
		Expr[] nChildren = children;

		for (int i = 0; i != nChildren.length; ++i) {
			Expr child = children[i];
			Polynomial nChild = toPolynomial(child);
			if (child != nChild && children == nChildren) {
				nChildren = Arrays.copyOf(children, children.length);
			}
			nChildren[i] = nChild;
		}
		//
		return nChildren;
	}


	/**
	 * Convert an arbitrary expression to a polynomial.
	 *
	 * @param e
	 * @return
	 */
	public static Polynomial toPolynomial(Expr e) {
		switch (e.getOpcode()) {
		case EXPR_const:
			return toPolynomial((Expr.Constant) e);
		case EXPR_invoke:
		case EXPR_arridx:
		case EXPR_var:
			return toUnitPolynomial(e);
		case EXPR_add:
		case EXPR_mul:
		case EXPR_sub: {
			Expr.Operator op = (Expr.Operator) e;
			return toPolynomial(e.getOpcode(), op.getOperands());
		}
		default:
			throw new IllegalArgumentException("cannot convert expression to polynomial");
		}
	}

	private static Polynomial toPolynomial(Expr.Constant e) {
		Value.Int c = (Value.Int) e.getValue();
		return new Polynomial(new Polynomial.Term(c));
	}

	private static Polynomial toUnitPolynomial(Expr e) {
		// FIXME: this is broken!!
		Tuple<Formula.Atom> vs = new Tuple<>(e);
		return new Polynomial(new Polynomial.Term(new Value.Int(1), vs));
	}

	private static Polynomial toPolynomial(Opcode opcode, Expr... children) {
		Polynomial result = toPolynomial(children[0]);
		switch (opcode) {
		case EXPR_add: {
			for (int i = 1; i != children.length; ++i) {
				result = result.add(toPolynomial(children[i]));
			}
			break;
		}
		case EXPR_sub: {
			for (int i = 1; i != children.length; ++i) {
				result = result.subtract(toPolynomial(children[i]));
			}
			break;
		}
		case EXPR_mul: {
			for (int i = 1; i != children.length; ++i) {
				result = result.multiply(toPolynomial(children[i]));
			}
			break;
		}
		default:
			throw new IllegalArgumentException("IMPLEMENT ME");
		}

		return result;
	}
}
