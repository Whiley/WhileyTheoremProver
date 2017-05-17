// Copyright 2017 David J. Pearce
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//    http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.
package wytp.proof.rules;

import wyal.lang.NameResolver.ResolutionError;
import wyal.lang.WyalFile;
import wyal.lang.WyalFile.*;
import wytp.proof.Formula;
import wytp.proof.Proof;
import wytp.proof.Formula.ArithmeticEquality;
import wytp.proof.Formula.Conjunct;
import wytp.proof.Formula.Inequality;
import wytp.proof.Formula.Quantifier;
import wytp.proof.Proof.State;
import wytp.proof.util.AbstractProofRule;
import wytp.proof.util.Formulae;
import wytp.types.TypeSystem;

public class EqualityCaseAnalysis extends AbstractProofRule implements Proof.LinearRule {
	private int skolem = 0;

	public EqualityCaseAnalysis(TypeSystem types) {
		super(types);
	}

	@Override
	public String getName() {
		return "Neq-C";
	}

	@Override
	public State apply(State state, Formula truth) throws ResolutionError {
		if(truth instanceof Formula.ArithmeticEquality) {
			Formula.ArithmeticEquality eq = (Formula.ArithmeticEquality) truth;
			if(!eq.getSign()) {
				Expr lhs = eq.getOperand(0);
				Expr rhs = eq.getOperand(1);
				// For an arithmetic equality of the form x != y, we return a
				// disjunction of the form (x < y) || (x > y). This is not
				// necessarily the most efficient thing to do. However, for our
				// purposes, this works well enough for now.
				Inequality lt = Formulae.lessThan(lhs,rhs);
				Inequality gt = Formulae.lessThan(rhs,lhs);
				Formula disjunct = new Formula.Disjunct(lt, gt);
				return state.subsume(this, truth, disjunct);
			}
		} else if(truth instanceof Formula.Equality) {
			Formula.Equality eq = (Formula.Equality) truth;
			Expr lhs = eq.getOperand(0);
			Expr rhs = eq.getOperand(1);
			Type lhsT = types.inferType(state.getTypeEnvironment(),lhs);
			Type rhsT = types.inferType(state.getTypeEnvironment(),rhs);
			if (lhsT != null && rhsT != null) {
				Type intersection = new Type.Intersection(lhsT, rhsT);
				//
				if (types.isRawSubtype(new Type.Void(), intersection)) {
					// In this case, no possible intersection exists between the
					// lhs and rhs. Therefore, we're done as this equality
					// cannot ever be true.
					return state.subsume(this, truth, new Formula.Truth(true));
				} else if (types.isRawSubtype(new Type.Bool(), lhsT) && types.isRawSubtype(new Type.Bool(), rhsT)) {
					return expandBooleanEquality(eq, state);
				}
				Type.Record lhsRecord = types.extractReadableRecord(lhsT);
				Type.Record rhsRecord = types.extractReadableRecord(rhsT);
				if(lhsRecord != null && rhsRecord != null) {
					return expandRecordEquality(eq, state);
				}
				Type.Array lhsArray = types.extractReadableArray(lhsT);
				Type.Array rhsArray = types.extractReadableArray(rhsT);
				if(lhsArray != null && rhsArray != null) {
					return expandArrayEquality(eq, state);
				}
			} else {
				// NOTE: it is possible to get here in some situations. This can
				// happen as a result of type test which has not yet been
				// properly processed.
			}
		}

		return state;
	}

	private State expandBooleanEquality(Formula.Equality eq, Proof.State state) throws ResolutionError {
		Expr lhs = eq.getOperand(0);
		Expr rhs = eq.getOperand(1);
		//
		Formula lhs_f = Formulae.toFormula(lhs, types);
		Formula rhs_f = Formulae.toFormula(rhs, types);
		//
		// FIXME: I have a feeling we can do better here. Especially, in the
		// case of an equality I don't think we want to do anything. In the case
		// of an inequality (e.g. x==y), I think we want to generate an equality
		// (x == !y) or similar.
		//
		if(eq.getSign()) {
			Formula l = new Conjunct(lhs_f, rhs_f);
			Formula r = new Conjunct(Formulae.invert(lhs_f), Formulae.invert(rhs_f));
			Formula disjunct = new Formula.Disjunct(l, r);
			return state.subsume(this, eq, disjunct);
		} else {
			Formula l = new Conjunct(Formulae.invert(lhs_f),rhs_f);
			Formula r = new Conjunct(lhs_f,Formulae.invert(rhs_f));
			Formula disjunct = new Formula.Disjunct(l, r);
			// NOTE: at the moment, we can't do a subsume here because we can
			// end up losing critical information.
			return state.infer(this, disjunct, eq);
		}
	}

	private State expandRecordEquality(Formula.Equality eq, Proof.State state) throws ResolutionError {
		Expr lhs = eq.getOperand(0);
		Expr rhs = eq.getOperand(1);
		if (eq.getSign()) {
			if (lhs instanceof Expr.RecordInitialiser && rhs instanceof Expr.RecordInitialiser) {
				return expandRecordInitialiserEquality(eq, (Expr.RecordInitialiser) lhs, (Expr.RecordInitialiser) rhs,
						state);
			}
		} else {
			return expandRecordNonEquality(eq, lhs, rhs, state);
		}
		return state;
	}

	private State expandRecordNonEquality(Formula.Equality eq, Expr lhs, Expr rhs, Proof.State state) throws ResolutionError {
		Type lhs_t = types.inferType(state.getTypeEnvironment(),lhs);
		Type.Record lhs_r = types.extractReadableRecord(lhs_t);
		FieldDeclaration[] fields = lhs_r.getFields();
		Formula[] clauses = new Formula[fields.length];
		for (int i = 0; i != fields.length; ++i) {
			Expr lf = new Expr.RecordAccess(lhs, fields[i].getVariableName());
			Expr rf = new Expr.RecordAccess(rhs, fields[i].getVariableName());
			clauses[i] = Formulae.toFormula(new Expr.NotEqual(lf, rf), types);
		}
		Formula disjunct = new Formula.Disjunct(clauses);
		return state.subsume(this, eq, disjunct);
	}

	private State expandRecordInitialiserEquality(Formula.Equality eq, Expr.RecordInitialiser lhs,
			Expr.RecordInitialiser rhs, Proof.State state) throws ResolutionError {
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
				// NOTE: don't need to call construct here, since generating a
				// formula.
				clauses[i] = Formulae.toFormula(new Expr.Equal(lf, rf), types);
			}
			Formula disjunct = new Formula.Conjunct(clauses);
			return state.subsume(this, eq, disjunct);
		}
	}

	private State expandArrayEquality(Formula.Equality eq, Proof.State state) throws ResolutionError {
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
			Proof.State state) throws ResolutionError {
		if (lhs.size() != rhs.size()) {
			return state.subsume(this, new Formula.Truth(!eq.getSign()), eq);
		} else {
			Expr[] lhsOperands = lhs.getOperands();
			Expr[] rhsOperands = rhs.getOperands();
			Formula[] clauses = new Formula[lhsOperands.length];
			for (int i = 0; i != lhsOperands.length; ++i) {
				Expr lhsOperand = lhsOperands[i];
				Expr rhsOperand = rhsOperands[i];
				clauses[i] = Formulae.toFormula(equal(eq.getSign(),lhsOperand, rhsOperand), types);
			}
			//
			Formula f = eq.getSign() ? new Formula.Conjunct(clauses) : new Formula.Disjunct(clauses);
			return state.subsume(this, eq, f);
		}
	}

	private State expandArrayGeneratorInitialiserEquality(Formula.Equality eq, Expr.Operator lhs, Expr.Operator rhs,
			Proof.State state) throws ResolutionError {
		Expr lhsValue = lhs.getOperand(0);
		Expr lhsSize = lhs.getOperand(1);
		Expr rhsSize = new Expr.Constant(new Value.Int(rhs.size()));
		Expr[] rhsOperands = rhs.getOperands();
		Formula[] clauses = new Formula[rhsOperands.length + 1];
		for (int i = 0; i != rhsOperands.length; ++i) {
			Expr rhsOperand = rhsOperands[i];
			clauses[i] = Formulae.toFormula(equal(eq.getSign(),lhsValue, rhsOperand), types);
		}
		clauses[rhsOperands.length] = Formulae.toFormula(equal(eq.getSign(),lhsSize,rhsSize), types);
		//
		Formula f = eq.getSign() ? new Formula.Conjunct(clauses) : new Formula.Disjunct(clauses);
		return state.subsume(this, eq, f);
	}

	private State expandArrayGeneratorGeneratorEquality(Formula.Equality eq, Expr.Operator lhs, Expr.Operator rhs,
			Proof.State state) throws ResolutionError {
		Expr lhsValue = lhs.getOperand(0);
		Expr lhsSize = lhs.getOperand(1);
		Expr rhsValue = rhs.getOperand(0);
		Expr rhsSize = rhs.getOperand(1);
		Formula c1 = Formulae.toFormula(equal(eq.getSign(), lhsSize, rhsSize), types);
		Formula c2 = Formulae.toFormula(equal(eq.getSign(), lhsValue, rhsValue), types);
		//
		Formula f = eq.getSign() ? new Formula.Conjunct(c1, c2) : new Formula.Disjunct(c1, c2);
		return state.subsume(this, eq, f);
	}

	private State expandArrayInitialiserNonEquality(Formula.Equality eq, Expr.Operator lhs, Expr rhs,
			Proof.State state) throws ResolutionError {
		Expr lhsSize = new Expr.Constant(new Value.Int(lhs.size()));
		Expr rhsSize = new Expr.ArrayLength(rhs);
		Expr[] lhsOperands = lhs.getOperands();
		Formula[] clauses = new Formula[lhsOperands.length + 1];
		for (int i = 0; i != lhsOperands.length; ++i) {
			Expr index = new Expr.Constant(new Value.Int(i));
			Expr lhsOperand = lhsOperands[i];
			Expr rhsOperand = new Expr.ArrayAccess(rhs, index);
			clauses[i] = Formulae.toFormula(new Expr.NotEqual(lhsOperand, rhsOperand), types);
		}
		clauses[lhsOperands.length] = Formulae.toFormula(new Expr.NotEqual(lhsSize, rhsSize), types);
		Formula f = new Formula.Disjunct(clauses);
		return state.subsume(this, eq, f);
	}

	private State expandArrayArrayNonEquality(Formula.Equality eq, Expr lhs, Expr rhs, Proof.State state) throws ResolutionError {
		WyalFile.VariableDeclaration var = new WyalFile.VariableDeclaration(new Type.Int(),
				new Identifier("i:" + skolem++));
		Expr va = new Expr.VariableAccess(var);
		Expr lhsAccess = new Expr.ArrayAccess(lhs, va);
		Expr rhsAccess = new Expr.ArrayAccess(rhs, va);
		Formula body = notEquals(state, lhsAccess, rhsAccess, types);
		Expr lhsLen = new Expr.ArrayLength(lhs);
		Expr rhsLen = new Expr.ArrayLength(rhs);
		// The following axiom simply states that the length of every array
		// type is greater than or equal to zero.
		Formula axiom = new ArithmeticEquality(false, lhsLen, rhsLen);
		axiom = Formulae.or(axiom, new Quantifier(false, var, body));
		//
		return state.subsume(this, eq, axiom);
	}

	private static Formula notEquals(State state, Expr lhs, Expr rhs, TypeSystem types) throws ResolutionError {
		Type lhs_t = types.inferType(state.getTypeEnvironment(),lhs);
		Type rhs_t = types.inferType(state.getTypeEnvironment(),rhs);
		if (types.isRawSubtype(new Type.Int(), lhs_t) || types.isRawSubtype(new Type.Int(), rhs_t)) {
			return new ArithmeticEquality(false, lhs, rhs);
		} else {
			return new Formula.Equality(false, lhs, rhs);
		}
	}

	private static Expr equal(boolean sign, Expr lhs, Expr rhs) {
		if (sign) {
			return new Expr.Equal(lhs,rhs);
		} else {
			return new Expr.NotEqual(lhs,rhs);
		}
	}
}
