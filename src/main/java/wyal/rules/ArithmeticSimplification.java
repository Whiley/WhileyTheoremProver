package wyal.rules;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Arrays;

import wyal.lang.SyntacticItem;
import wyal.lang.WyalFile.Value;
import wyal.lang.WyalFile.Expr;
import wyal.lang.WyalFile.Expr.Polynomial;
import wyal.lang.WyalFile.Opcode;
import wyal.lang.WyalFile.Tuple;
import wyal.util.AutomatedTheoremProver.RewriteRule;
import wyal.util.Polynomials;

public class ArithmeticSimplification implements RewriteRule {

	@Override
	public SyntacticItem rewrite(SyntacticItem item) {
		switch (item.getOpcode()) {
		case EXPR_eq:
		case EXPR_neq:
			// FIXME: above two cases broken as need to know if integer
			// comparison or not.
		case EXPR_lt:
		case EXPR_lteq:
		case EXPR_gt:
		case EXPR_gteq: {
			return simplifyEquation((Expr.Operator) item);
		}
		}
		return item;
	}

	private Expr simplifyEquation(Expr.Operator expr) {
		Expr[] children = expr.getOperands();
		Expr[] nChildren = toPolynomial(children);
		Polynomial lhs = (Polynomial) nChildren[0];
		Polynomial rhs = (Polynomial) nChildren[1];
		if (isConstant(lhs) && isConstant(rhs)) {
			return evaluateEquation(expr.getOpcode(), asConstant(lhs), asConstant(rhs));
		} else if ((isZero(lhs) || isZero(rhs)) && children == nChildren) {
			// Equation already in normal form, and cannot be reduced further.
			// Therefore, no need to do anything else
			return expr;
		} else {
			int lhsSigns = countSigns(lhs);
			int rhsSigns = countSigns(rhs);
			if(lhsSigns < rhsSigns) {
				rhs = rhs.subtract(lhs);
				lhs = new Polynomial(BigInteger.ZERO);
			} else {
				lhs = lhs.subtract(rhs);
				rhs = new Polynomial(BigInteger.ZERO);
			}
			return expr.clone(new Expr[]{lhs, rhs});
		}
	}

	private int countSigns(Polynomial p) {
		int signs = 0;
		for(int i=0;i!=p.size();++i) {
			Polynomial.Term term = p.getOperand(i);
			BigInteger b = term.getCoefficient().get();
			int c = b.compareTo(BigInteger.ZERO);
			if(c < 0) {
				signs = signs - 1;
			} else {
				signs = signs + 1;
			}
		}
		return signs;
	}

	/**
	 * Check whether a polynomial is a constant or not.
	 *
	 * @param p
	 * @return
	 */
	private boolean isConstant(Polynomial p) {
		return p.size() == 1 && p.getOperand(0).getAtoms().size() == 0;
	}

	/**
	 * Check whether a polynomial is a constant or not.
	 *
	 * @param p
	 * @return
	 */
	private boolean isZero(Polynomial p) {
		if (p.size() == 1) {
			Polynomial.Term term = p.getOperand(0);
			if (term.getAtoms().size() == 0) {
				BigInteger coefficient = term.getCoefficient().get();
				return coefficient.equals(BigInteger.ZERO);
			}
		}
		return false;
	}

	/**
	 * Check whether a polynomial is a constant or not.
	 *
	 * @param p
	 * @return
	 */
	private BigInteger asConstant(Polynomial p) {
		if (p.size() == 1) {
			Polynomial.Term term = p.getOperand(0);
			if (term.getAtoms().size() == 0) {
				return term.getCoefficient().get();
			}
		}
		throw new IllegalArgumentException("polynomial is not constant");
	}

	private Expr.Constant evaluateEquation(Opcode opcode, BigInteger lhs, BigInteger rhs) {
		boolean result;
		switch (opcode) {
		case EXPR_eq:
			result = lhs.equals(rhs);
			break;
		case EXPR_neq:
			result = !(lhs.equals(rhs));
			break;
		case EXPR_lt:
			result = lhs.compareTo(rhs) < 0;
			break;
		case EXPR_lteq:
			result = lhs.compareTo(rhs) <= 0;
			break;
		case EXPR_gt:
			result = lhs.compareTo(rhs) > 0;
			break;
		case EXPR_gteq:
			result = lhs.compareTo(rhs) >= 0;
			break;
		default:
			throw new IllegalArgumentException("Invalid equation opcode: " + opcode);
		}
		return new Expr.Constant(new Value.Bool(result));
	}

	/**
	 * Recursively simplify a sequence of zero or more expressions. If no
	 * simplifications occur, then the original array is returned untouched.
	 *
	 * @param children
	 * @return
	 */
	private Expr[] toPolynomial(Expr... children) {
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
	private Polynomial toPolynomial(Expr e) {
		switch (e.getOpcode()) {
		case EXPR_poly:
			return (Polynomial) e;
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

	private Polynomial toPolynomial(Expr.Constant e) {
		Value.Int c = (Value.Int) e.getValue();
		return new Polynomial(new Polynomial.Term(c));
	}

	private Polynomial toUnitPolynomial(Expr e) {
		Tuple<Expr> vs = new Tuple<>(e);
		return new Polynomial(new Polynomial.Term(new Value.Int(1), vs));
	}

	private Polynomial toPolynomial(Opcode opcode, Expr... children) {
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

	private Polynomial.Term[] factorise(Polynomial.Term... terms) {
		BigInteger factor = terms[0].getCoefficient().get();
		for (int i = 1; i != terms.length; ++i) {
			factor = factor.gcd(terms[1].getCoefficient().get());
		}
		if (!factor.equals(BigInteger.ONE)) {
			// Found a non-trivial factor, therefore divide each term by it.
			for (int i = 0; i != terms.length; ++i) {
				Polynomial.Term term = terms[i];
				BigInteger coefficient = term.getCoefficient().get().divide(factor);
				terms[i] = new Polynomial.Term(new Value.Int(coefficient), term.getAtoms());
			}
		}
		// FIXME: we should ideally sort terms here!!!
		return terms;
	}
}
