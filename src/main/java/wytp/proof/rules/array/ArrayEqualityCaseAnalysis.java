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
package wytp.proof.rules.array;

import wyal.lang.WyalFile;
import wybs.lang.NameResolver.ResolutionError;

import static wyal.lang.WyalFile.*;

import wytp.proof.Formula;
import wytp.proof.Proof;
import wytp.proof.Formula.ArithmeticEquality;
import wytp.proof.Formula.Quantifier;
import wytp.proof.Proof.State;
import wytp.proof.rules.Simplification;
import wytp.proof.util.AbstractProofRule;
import wytp.proof.util.Formulae;
import wytp.types.TypeSystem;

/**
 * <p>
 * Handle (non-)equality between expressions of array type. There are six main
 * cases to consider:
 * </p>
 * <ul>
 * <li>
 * <p>
 * <b>Initialiser-Initialiser (Non-)Equality</b>. For a case of the form
 * <code>[e1,e2,...] == [e'1,e'2,...]</code> we produce <code>false</code> (if
 * the number of elements differs) or a conjunction of the form
 * <code>(e1 == e'1) && (e2 == e'2) && ...</code>. Similarly for the
 * non-equality case, either <code>true</code> (if number of elements differs)
 * or a disjunction is produced.
 * </p>
 * </li>
 *
 * <li>
 * <p>
 * <b>Initialiser-Generator (Non-)Equality.</b> For a case of the form
 * <code>[e1,e2,...] == [e'val; e'len]</code> we produce <code>n == e'len</code>
 * and a conjunction of the form
 * <code>(e1 == e'val) && (e2 == e'val) && ...</code>. Similarly for the
 * non-equality case, we produce <code>n != e'len</code> disjuncted against a
 * disjunction of the form <code>(e1 != e'val) || (e2 != e'val) || ...</code>.
 * </p>
 * </li>
 *
 * <li>
 * <p>
 * <b>Generator-Generator (Non-)Equality.</b> For a case of the form
 * <code>[e1'val; e1'len] == [e2'val; e2'len]</code> we produce
 * <code>(e1'len == e2'len) && (e1'val == e2'val)</code>. Similarly for the
 * non-equality case, we produce
 * <code>(e1'len != e2'len) || (e1'val != e2'val)</code>.
 * </p>
 * </li>
 *
 * <li>
 * <p>
 * <b>Initialiser Non-Equality.</b> For a case of the form
 * <code>[e1,e2,...] != e</code> we produce
 * <code>(n != |e|) || (e1 != e[0]) || (e2 != e[1]) || ...</code>. This is a
 * case analysis only because we have a finite number of elements from the
 * intialiser.
 * </p>
 * </li>
 *
 * <li>
 * <p>
 * <b>General Non-Equality.</b> For an equalty of the form <code>e1 != e2</code>
 * of array type we produce
 * <code>(|e1| != |e2|) || some i.(e1[i] != e2[i])</code>.
 * </p>
 * </li>
 * </ul>
 *
 * @author David J. Pearce
 *
 */
public class ArrayEqualityCaseAnalysis extends AbstractProofRule implements Proof.LinearRule {
	private int skolem = 0;

	public ArrayEqualityCaseAnalysis(Simplification simplify, TypeSystem types) {
		super(simplify, types);
	}

	@Override
	public String getName() {
		return "Aeq-C";
	}

	@Override
	public State apply(State state, Formula truth) throws ResolutionError {
		if (truth instanceof Formula.Equality) {
			Formula.Equality eq = (Formula.Equality) truth;
			Expr lhs = eq.getOperand(0);
			Expr rhs = eq.getOperand(1);
			Type lhsT = types.inferType(state.getTypeEnvironment(), lhs);
			Type rhsT = types.inferType(state.getTypeEnvironment(), rhs);
			if (lhsT != null && rhsT != null) {
				Type.Array lhsArray = types.extractReadableArray(lhsT);
				Type.Array rhsArray = types.extractReadableArray(rhsT);
				if (lhsArray != null && rhsArray != null) {
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

	private State expandArrayEquality(Formula.Equality eq, Proof.State state) throws ResolutionError {
		Expr lhs = eq.getOperand(0);
		Expr rhs = eq.getOperand(1);
		if (lhs.getOpcode() == WyalFile.EXPR_arrinit && rhs.getOpcode() == WyalFile.EXPR_arrinit) {
			return expandArrayInitialiserInitialiserEquality(eq, (Expr.Operator) lhs, (Expr.Operator) rhs, state);
		} else if (lhs.getOpcode() == WyalFile.EXPR_arrgen && rhs.getOpcode() == WyalFile.EXPR_arrinit) {
			return expandArrayGeneratorInitialiserEquality(eq, (Expr.Operator) lhs, (Expr.Operator) rhs, state);
		} else if (lhs.getOpcode() == WyalFile.EXPR_arrinit && rhs.getOpcode() == WyalFile.EXPR_arrgen) {
			return expandArrayGeneratorInitialiserEquality(eq, (Expr.Operator) rhs, (Expr.Operator) lhs, state);
		} else if (lhs.getOpcode() == WyalFile.EXPR_arrgen && rhs.getOpcode() == WyalFile.EXPR_arrgen) {
			return expandArrayGeneratorGeneratorEquality(eq, (Expr.Operator) lhs, (Expr.Operator) rhs, state);
		} else if (!eq.getSign() && lhs.getOpcode() == WyalFile.EXPR_arrinit) {
			return expandArrayInitialiserNonEquality(eq, (Expr.Operator) lhs, rhs, state);
		} else if (!eq.getSign() && rhs.getOpcode() == WyalFile.EXPR_arrinit) {
			return expandArrayInitialiserNonEquality(eq, (Expr.Operator) rhs, lhs, state);
		} else if (!eq.getSign()) {
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
				clauses[i] = Formulae.toFormula(equal(eq.getSign(), lhsOperand, rhsOperand), types);
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
			clauses[i] = Formulae.toFormula(equal(eq.getSign(), lhsValue, rhsOperand), types);
		}
		clauses[rhsOperands.length] = Formulae.toFormula(equal(eq.getSign(), lhsSize, rhsSize), types);
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

	private State expandArrayInitialiserNonEquality(Formula.Equality eq, Expr.Operator lhs, Expr rhs, Proof.State state)
			throws ResolutionError {
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

	private State expandArrayArrayNonEquality(Formula.Equality eq, Expr lhs, Expr rhs, Proof.State state)
			throws ResolutionError {
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
		Type lhs_t = types.inferType(state.getTypeEnvironment(), lhs);
		Type rhs_t = types.inferType(state.getTypeEnvironment(), rhs);
		if (types.isRawSubtype(new Type.Int(), lhs_t) || types.isRawSubtype(new Type.Int(), rhs_t)) {
			return new ArithmeticEquality(false, lhs, rhs);
		} else {
			return new Formula.Equality(false, lhs, rhs);
		}
	}

	private static Expr equal(boolean sign, Expr lhs, Expr rhs) {
		if (sign) {
			return new Expr.Equal(lhs, rhs);
		} else {
			return new Expr.NotEqual(lhs, rhs);
		}
	}
}
