package wyal.rules;

import java.math.BigInteger;
import java.util.Arrays;

import wyal.lang.SyntacticItem;
import wyal.lang.WyalFile;
import wyal.lang.WyalFile.Value;
import wyal.lang.WyalFile.Expr;
import wyal.lang.WyalFile.Expr.Polynomial;
import wyal.lang.WyalFile.Opcode;
import wyal.lang.WyalFile.Tuple;
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
		case EXPR_lt:
		case EXPR_lteq:
		case EXPR_gt:
		case EXPR_gteq:{
			return simplify((Expr.Operator) item);
		}
		}
		return item;
	}

	private Expr simplify(Expr.Operator expr) {
		Expr[] children = expr.getOperands();
		Expr[] nChildren = children;

		for (int i = 0; i != nChildren.length; ++i) {
			Expr child = children[i];
			Polynomial nChild = toPolynomial(child);
			if (child != nChild && children == nChildren) {
				nChildren = Arrays.copyOf(children, children.length);
			}
			nChildren[i] = nChild;
		}

		if(children != nChildren) {
			return expr.clone(nChildren);
		} else {
			return expr;
		}
	}

	/**
	 * Convert an arbitrary expression to a polynomial.
	 *
	 * @param e
	 * @return
	 */
	private Polynomial toPolynomial(Expr e) {
		switch(e.getOpcode()) {
		case EXPR_poly:
			return (Polynomial) e;
		case EXPR_const:
			return toPolynomial((Expr.Constant)e);
		case EXPR_invoke:
		case EXPR_arridx:
		case EXPR_var:
			return toUnitPolynomial(e);
		case EXPR_add:
		case EXPR_mul:
		case EXPR_sub:{
			Expr.Operator op = (Expr.Operator) e;
			return toPolynomial(e.getOpcode(),op.getOperands());
		}
		default:
			throw new IllegalArgumentException("cannot convert expression to polynomial");
		}
	}

	private Polynomial toPolynomial(Expr.Constant e) {
		Value.Int c = (Value.Int) e.getValue();
		return new Polynomial(new Polynomial.Term(c, new Tuple<>()));
	}

	private Polynomial toUnitPolynomial(Expr e) {
		Tuple<Expr> vs = new Tuple<>(e);
		return new Polynomial(new Polynomial.Term(new Value.Int(1), vs));
	}

	private Polynomial toPolynomial(Opcode opcode, Expr...children) {
		Polynomial[] nChildren = toPolynomial(children);
		Polynomial result = nChildren[0];
		switch(opcode) {
		case EXPR_add:
			for(int i=1;i!=nChildren.length;++i) {
				result = add(result,nChildren[i]);
			}
			break;
		case EXPR_sub:
			for(int i=1;i!=nChildren.length;++i) {
				result = subtract(result,nChildren[i]);
			}
			break;
		default:
			throw new IllegalArgumentException("IMPLEMENT ME");
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
		Polynomial[] nChildren = new Polynomial[children.length];

		for (int i = 0; i != nChildren.length; ++i) {
			nChildren[i] = toPolynomial(children[i]);
		}
		//
		return nChildren;
	}

	private Polynomial add(Polynomial lhs, Polynomial rhs) {
		Polynomial.Term[] terms = new Polynomial.Term[countTerms(lhs,rhs)];
		int i = 0;
		int j = 0;
		int k = 0;
		while (i < lhs.size() && j < rhs.size()) {
			Polynomial.Term l = lhs.getOperand(i);
			Polynomial.Term r = rhs.getOperand(i);
			int l_index = l.getSecond().getIndex();
			int r_index = r.getSecond().getIndex();
			if (l_index < r_index) {
				terms[k] = l;
				i = i + 1;
			} else if (l_index > r_index) {
				terms[k] = r;
				j = j + 1;
			} else {
				BigInteger c = l.getFirst().get().add(r.getFirst().get());
				terms[k] = new Polynomial.Term(new Value.Int(c), l.getSecond());
				i = i + 1;
				j = j + 1;
			}
			k = k + 1;
		}
		Arrays.sort(terms);
		return new Polynomial(terms);
	}

	private int countTerms(Polynomial lhs, Polynomial rhs) {
		int count = 0;
		int i = 0;
		int j = 0;
		while(i < lhs.size() && j < rhs.size()) {
			int l_index = lhs.getOperand(i).getSecond().getIndex();
			int r_index = rhs.getOperand(j).getSecond().getIndex();
			if(l_index < r_index) {
				i = i + 1;
			} else if(l_index > r_index) {
				j = j + 1;
			} else {
				i = i + 1;
				j = j + 1;
			}
			count = count + 1;
		}
		//
		return count + (lhs.size()-i) + (rhs.size()-j);
	}
}
