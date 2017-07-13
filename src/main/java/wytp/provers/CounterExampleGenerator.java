package wytp.provers;

import java.util.Map;

import wyal.lang.WyalFile;
import wyal.lang.WyalFile.Expr;
import wytp.proof.Formula;

public class CounterExampleGenerator {
	public boolean evaluate(Formula f,Map<Integer,Object> environment) {
		if(f instanceof Formula.Conjunct) {
			return evaluateConjunct((Formula.Conjunct) f,environment);
		} else if (f instanceof Formula.Disjunct) {
			return evaluateDisjunct((Formula.Disjunct) f,environment);
		} else if(f instanceof Formula.Equality) {
			return evaluateEquality((Formula.Equality) f,environment);
		} else if(f instanceof Formula.Inequality) {
			return evaluateInequality((Formula.Inequality) f,environment);
		} else if(f instanceof Formula.Invoke) {
			return evaluateInvoke((Formula.Invoke) f,environment);
		} else if(f instanceof Formula.Is) {
			return evaluateIs((Formula.Is) f,environment);
		} else {
			throw new RuntimeException("Unknown formula encountered: " + f.getClass().getName());
		}
	}

	protected boolean evaluateConjunct(Formula.Conjunct conjunct, Map<Integer, Object> environment) {
		Formula[] children = conjunct.getOperands();
		for(int i=0;i!=children.length;++i) {
			if(!evaluate(children[i],environment)) {
				return false;
			}
		}
		return true;
	}

	protected boolean evaluateDisjunct(Formula.Disjunct disjunct, Map<Integer, Object> environment) {
		Formula[] children = disjunct.getOperands();
		for(int i=0;i!=children.length;++i) {
			if(evaluate(children[i],environment)) {
				return true;
			}
		}
		return false;
	}

	protected boolean evaluateEquality(Formula.Equality equality, Map<Integer, Object> environment) {
		Object lhs = evaluateExpression(equality.getOperand(0), environment);
		Object rhs = evaluateExpression(equality.getOperand(1), environment);
		return lhs.equals(rhs);
	}

	protected boolean evaluateInequality(Formula.Inequality f,Map<Integer,Object> environment) {
		throw new RuntimeException("implement me!");
	}

	protected boolean evaluateInvoke(Formula.Invoke f,Map<Integer,Object> environment) {
		throw new RuntimeException("implement me!");
	}

	protected boolean evaluateIs(Formula.Is f,Map<Integer,Object> environment) {
		throw new RuntimeException("implement me!");
	}

	protected Object evaluateExpression(WyalFile.Expr expr, Map<Integer,Object> environment) {
		switch (expr.getOpcode()) {
		// Ignored
		case EXPR_const:
			return evaluateConstant((Expr.Constant) expr, environment);
		case EXPR_var:
			return evaluateVariable((Expr.VariableAccess) expr, environment);
		default:
			throw new RuntimeException("unknown expression encountered");
		}
	}

	protected Object evaluateConstant(Expr.Constant expr, Map<Integer,Object> environment) {

	}

	protected Object evaluateConstant(Expr.VariableAccess expr, Map<Integer,Object> environment) {

	}
}
