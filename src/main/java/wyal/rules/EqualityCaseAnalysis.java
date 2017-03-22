package wyal.rules;

import wyal.lang.Formula;
import wyal.lang.Proof;
import wyal.lang.Formula.ArithmeticEquality;
import wyal.lang.Formula.Inequality;
import wyal.lang.Formula.Quantifier;
import wyal.lang.Proof.State;
import wyal.lang.WyalFile;
import wyal.lang.WyalFile.*;
import wyal.lang.WyalFile.Expr.Polynomial;
import wyal.util.Formulae;
import wyal.util.TypeSystem;

public class EqualityCaseAnalysis implements Proof.LinearRule {
	private final TypeSystem types;

	public EqualityCaseAnalysis(TypeSystem types) {
		this.types = types;
	}

	@Override
	public String getName() {
		return "Neq-C";
	}

	@Override
	public State apply(State state, Formula truth) {
		if(truth instanceof Formula.ArithmeticEquality) {
			Formula.ArithmeticEquality eq = (Formula.ArithmeticEquality) truth;
			if(!eq.getSign()) {
				Polynomial lhs = eq.getOperand(0);
				Polynomial rhs = eq.getOperand(1);
				// For an arithmetic equality of the form x != y, we return a
				// disjunction of the form (x < y) || (x > y). This is not
				// necessarily the most efficient thing to do. However, for our
				// purposes, this works well enough for now.
				Inequality lt = Formulae.lessThan(lhs,rhs);
				Inequality gt = Formulae.lessThan(rhs,lhs);
				Formula disjunct = state.allocate(new Formula.Disjunct(lt, gt));
				return state.subsume(this, truth, disjunct);
			}
		} else if(truth instanceof Formula.Equality) {
			Formula.Equality eq = (Formula.Equality) truth;
			Expr lhs = eq.getOperand(0);
			Expr rhs = eq.getOperand(1);
			Type lhs_t = lhs.getReturnType(types);
			Type rhs_t = rhs.getReturnType(types);
			if(types.isReadableRecord(lhs_t) || types.isReadableRecord(rhs_t)) {
				return expandRecordEquality(eq,state);
			} else if(types.isReadableArray(lhs_t) || types.isReadableArray(rhs_t)) {
				return expandArrayEquality(eq,state);
			}
		}

		return state;
	}

	private State expandRecordEquality(Formula.Equality eq, Proof.State state) {
		Expr lhs = eq.getOperand(0);
		Expr rhs = eq.getOperand(1);
		Type lhs_t = lhs.getReturnType(types);
		Type rhs_t = rhs.getReturnType(types);
		if (eq.getSign()) {
			if (lhs instanceof Expr.RecordInitialiser && rhs instanceof Expr.RecordInitialiser) {
				return expandRecordInitialiserEquality(eq, (Expr.RecordInitialiser) lhs, (Expr.RecordInitialiser) rhs,
						state);
			}
		} else {
			if (types.isReadableRecord(lhs_t)) {
				return expandRecordNonEquality(eq, lhs, rhs, state);
			} else if (types.isReadableRecord(rhs_t)) {
				return expandRecordNonEquality(eq, rhs, lhs, state);
			}
		}
		return state;
	}

	private State expandRecordNonEquality(Formula.Equality eq, Expr lhs, Expr rhs, Proof.State state) {
		Type lhs_t = lhs.getReturnType(types);
		Type.Record lhs_r = types.expandAsReadableRecordType(lhs_t);
		FieldDeclaration[] fields = lhs_r.getFields();
		Formula[] clauses = new Formula[fields.length];
		for (int i = 0; i != fields.length; ++i) {
			Expr lf = new Expr.RecordAccess(lhs, fields[i].getVariableName());
			Expr rf = new Expr.RecordAccess(rhs, fields[i].getVariableName());
			clauses[i] = Formulae.toFormula(new Expr.Operator(WyalFile.Opcode.EXPR_neq, lf, rf), types);
		}
		Formula disjunct = state.allocate(Formulae.simplifyFormula(new Formula.Disjunct(clauses), types));
		return state.subsume(this, eq, disjunct);
	}

	private State expandRecordInitialiserEquality(Formula.Equality eq, Expr.RecordInitialiser lhs,
			Expr.RecordInitialiser rhs, Proof.State state) {
		if (lhs.size() != rhs.size()) {
			// FIXME: for open records this could be possible
			return state.infer(this, new Formula.Truth(false), eq);
		} else {
			Pair<Identifier, Expr>[] lhsFields = lhs.getFields();
			Pair<Identifier, Expr>[] rhsFields = rhs.getFields();
			Formula[] clauses = new Formula[lhsFields.length];
			for (int i = 0; i != lhsFields.length; ++i) {
				Pair<Identifier, Expr> lhsField = lhsFields[i];
				Pair<Identifier, Expr> rhsField = rhsFields[i];
				if (!lhsField.getFirst().equals(rhsField.getFirst())) {
					// FIXME: could do more here --- esp to handle out-of-order
					// field declarations.
					return state.infer(this, new Formula.Truth(false), eq);
				}
				Expr lf = lhsField.getSecond();
				Expr rf = rhsField.getSecond();
				clauses[i] = Formulae.toFormula(new Expr.Operator(WyalFile.Opcode.EXPR_eq, lf, rf), types);
			}
			Formula disjunct = state.allocate(Formulae.simplifyFormula(new Formula.Conjunct(clauses), types));
			return state.subsume(this, eq, disjunct);
		}
	}

	private State expandArrayEquality(Formula.Equality eq, Proof.State state) {
		Expr lhs = eq.getOperand(0);
		Expr rhs = eq.getOperand(1);
		if (lhs.getOpcode() == Opcode.EXPR_arrinit && rhs.getOpcode() == Opcode.EXPR_arrinit) {
			return expandArrayInitialiserInitialiserEquality(eq, (Expr.Operator) lhs, (Expr.Operator) rhs,
					state);
		} else if(lhs.getOpcode() == Opcode.EXPR_arrgen && rhs.getOpcode() == Opcode.EXPR_arrinit) {
			return expandArrayGeneratorInitialiserEquality(eq, (Expr.Operator) lhs, (Expr.Operator) rhs,
					state);
		} else if(lhs.getOpcode() == Opcode.EXPR_arrinit && rhs.getOpcode() == Opcode.EXPR_arrgen) {
			return expandArrayGeneratorInitialiserEquality(eq, (Expr.Operator) rhs, (Expr.Operator) lhs,
					state);
		} else if(lhs.getOpcode() == Opcode.EXPR_arrgen && rhs.getOpcode() == Opcode.EXPR_arrgen) {
			return expandArrayGeneratorGeneratorEquality(eq, (Expr.Operator) lhs, (Expr.Operator) rhs,
					state);
		} else if(!eq.getSign() && lhs.getOpcode() == Opcode.EXPR_arrinit){
			return expandArrayInitialiserNonEquality(eq,(Expr.Operator)lhs,rhs,state);
		} else if(!eq.getSign() && rhs.getOpcode() == Opcode.EXPR_arrinit){
			return expandArrayInitialiserNonEquality(eq,(Expr.Operator)rhs,lhs,state);
		} else if(!eq.getSign()) {
			return expandArrayArrayNonEquality(eq, lhs, rhs, state);
		}
		return state;
	}

	private State expandArrayInitialiserInitialiserEquality(Formula.Equality eq, Expr.Operator lhs, Expr.Operator rhs,
			Proof.State state) {
		if (lhs.size() != rhs.size()) {
			return state.subsume(this, new Formula.Truth(!eq.getSign()), eq);
		} else {
			Expr[] lhsOperands = lhs.getOperands();
			Expr[] rhsOperands = rhs.getOperands();
			Formula[] clauses = new Formula[lhsOperands.length];
			for (int i = 0; i != lhsOperands.length; ++i) {
				Expr lhsOperand = lhsOperands[i];
				Expr rhsOperand = rhsOperands[i];
				WyalFile.Opcode opcode = eq.getSign() ? Opcode.EXPR_eq : Opcode.EXPR_neq;
				clauses[i] = Formulae.toFormula(new Expr.Operator(opcode, lhsOperand, rhsOperand), types);
			}
			//
			Formula f = eq.getSign() ? new Formula.Conjunct(clauses) : new Formula.Disjunct(clauses);
			return state.subsume(this, eq, state.allocate(Formulae.simplifyFormula(f, types)));
		}
	}

	private State expandArrayGeneratorInitialiserEquality(Formula.Equality eq, Expr.Operator lhs, Expr.Operator rhs,
			Proof.State state) {
		Expr lhsValue = lhs.getOperand(0);
		Expr lhsSize = lhs.getOperand(1);
		Expr rhsSize = new Expr.Constant(new Value.Int(rhs.size()));
		Expr[] rhsOperands = rhs.getOperands();
		Formula[] clauses = new Formula[rhsOperands.length + 1];
		for (int i = 0; i != rhsOperands.length; ++i) {
			Expr rhsOperand = rhsOperands[i];
			WyalFile.Opcode opcode = eq.getSign() ? Opcode.EXPR_eq : Opcode.EXPR_neq;
			clauses[i] = Formulae.toFormula(new Expr.Operator(opcode, lhsValue, rhsOperand), types);
		}
		WyalFile.Opcode opcode = eq.getSign() ? Opcode.EXPR_eq : Opcode.EXPR_neq;
		clauses[rhsOperands.length] = Formulae.toFormula(new Expr.Operator(opcode, lhsSize, rhsSize), types);
		//
		Formula f = eq.getSign() ? new Formula.Conjunct(clauses) : new Formula.Disjunct(clauses);
		return state.subsume(this, eq, state.allocate(Formulae.simplifyFormula(f, types)));
	}

	private State expandArrayGeneratorGeneratorEquality(Formula.Equality eq, Expr.Operator lhs, Expr.Operator rhs,
			Proof.State state) {
		Expr lhsValue = lhs.getOperand(0);
		Expr lhsSize = lhs.getOperand(1);
		Expr rhsValue = rhs.getOperand(0);
		Expr rhsSize = rhs.getOperand(1);

		WyalFile.Opcode opcode = eq.getSign() ? Opcode.EXPR_eq : Opcode.EXPR_neq;
		Formula c1 = Formulae.toFormula(new Expr.Operator(opcode, lhsSize, rhsSize), types);
		Formula c2 = Formulae.toFormula(new Expr.Operator(opcode, lhsValue, rhsValue), types);
		//
		Formula f = eq.getSign() ? new Formula.Conjunct(c1, c2) : new Formula.Disjunct(c1, c2);
		return state.subsume(this, eq, state.allocate(Formulae.simplifyFormula(f, types)));
	}

	private State expandArrayInitialiserNonEquality(Formula.Equality eq, Expr.Operator lhs, Expr rhs,
			Proof.State state) {
		Expr lhsSize = new Expr.Constant(new Value.Int(lhs.size()));
		Expr rhsSize = new Expr.Operator(Opcode.EXPR_arrlen, rhs);
		Expr[] lhsOperands = lhs.getOperands();
		Formula[] clauses = new Formula[lhsOperands.length + 1];
		for (int i = 0; i != lhsOperands.length; ++i) {
			Expr index = new Expr.Constant(new Value.Int(i));
			Expr lhsOperand = lhsOperands[i];
			Expr rhsOperand = new Expr.Operator(Opcode.EXPR_arridx, rhs, index);
			clauses[i] = Formulae.toFormula(new Expr.Operator(Opcode.EXPR_neq, lhsOperand, rhsOperand), types);
		}
		clauses[lhsOperands.length] = Formulae.toFormula(new Expr.Operator(Opcode.EXPR_neq, lhsSize, rhsSize), types);
		Formula f = new Formula.Disjunct(clauses);
		return state.subsume(this, eq, state.allocate(Formulae.simplifyFormula(f, types)));
	}

	private State expandArrayArrayNonEquality(Formula.Equality eq, Expr lhs, Expr rhs, Proof.State state) {
		WyalFile.VariableDeclaration var = new WyalFile.VariableDeclaration(new Type.Int(),
				new Identifier("i:" + Formulae.skolem++));
		Polynomial va = Formulae.toPolynomial(new Expr.VariableAccess(var));
		Expr lhsAccess = new Expr.Operator(Opcode.EXPR_arridx, lhs, va);
		Expr rhsAccess = new Expr.Operator(Opcode.EXPR_arridx, rhs, va);
		Formula body = Formulae.notEquals(lhsAccess, rhsAccess, types);
		Polynomial lhsLen = Formulae.toPolynomial(new Expr.Operator(Opcode.EXPR_arrlen, lhs));
		Polynomial rhsLen = Formulae.toPolynomial(new Expr.Operator(Opcode.EXPR_arrlen, rhs));
		// The following axiom simply states that the length of every array
		// type is greater than or equal to zero.
		Formula axiom = new ArithmeticEquality(false, lhsLen, rhsLen);
		axiom = Formulae.or(axiom, new Quantifier(false, var, body));
		axiom = Formulae.simplifyFormula(axiom, types);
		//
		return state.subsume(this, eq, state.allocate(axiom));
	}
}
