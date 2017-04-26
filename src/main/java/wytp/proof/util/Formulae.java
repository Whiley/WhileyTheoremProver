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
package wytp.proof.util;

import java.math.BigInteger;
import java.util.Arrays;
import java.util.BitSet;

import wyal.lang.WyalFile;
import wyal.lang.WyalFile.*;
import wyal.lang.WyalFile.Declaration.Named;
import wyal.lang.NameResolver.ResolutionError;
import wycc.util.ArrayUtils;
import wytp.proof.Formula;
import wytp.proof.Formula.*;
import wytp.types.TypeSystem;

/**
 * <p>
 * Provides a range of different algorithms for manipulating formula. The idea
 * is that these provide the building blocks on which different automated
 * theorem provers can be built and experimented with. Each of the algorithms
 * contained here attempts to perform a single task and to do it with at least
 * moderate efficiency (though there is room for improvement there).
 * </p>
 *
 * @author David J. Pearce
 *
 */
public class Formulae {

	// ========================================================================
	// Conversions
	// ========================================================================

	/**
	 * <p>
	 * Take a tree of statements and expressions, and return a formula. This is
	 * the first part of the process in discharging a given assertion. The
	 * purpose of a formula is just to provide a more "structured" form of the
	 * logical expression. The interface Formula also provides useful functions
	 * form manipulating formulae.
	 * </p>
	 * <p>
	 * Observe that after this conversion the resulting formula is not
	 * necessarily in simplified form. For example, conjuncts may contain nested
	 * conjuncts or equations may be unbalanced.
	 * </p>
	 *
	 * @param stmt
	 *            The statement being converted into a formula
	 * @param types
	 *            The type system is required for the translation, as some
	 *            aspects depend upon the types of expressions involved.
	 * @return
	 * @throws AmbiguousNameError
	 * @throws NameNotFoundError
	 */
	public static Formula toFormula(WyalFile.Stmt stmt, TypeSystem types) throws ResolutionError {
		switch (stmt.getOpcode()) {
		case STMT_block: {
			WyalFile.Stmt.Block b = (WyalFile.Stmt.Block) stmt;
			Formula[] operands = toFormulae(b.getOperands(), types);
			return new Formula.Conjunct(operands);
		}
		case STMT_caseof: {
			WyalFile.Stmt.CaseOf b = (WyalFile.Stmt.CaseOf) stmt;
			Formula[] operands = toFormulae(b.getOperands(), types);
			return new Formula.Disjunct(operands);
		}
		case STMT_ifthen: {
			WyalFile.Stmt.IfThen it = (WyalFile.Stmt.IfThen) stmt;
			Formula lhs = toFormula(it.getIfBody(), types);
			Formula rhs = toFormula(it.getThenBody(), types);
			return new Formula.Disjunct(invert(lhs), rhs);
		}
		case STMT_forall: {
			Stmt.Quantifier q = (WyalFile.Stmt.Quantifier) stmt;
			// Convert body of quantifier
			Formula body = toFormula(q.getBody(), types);
			// Done
			return new Formula.Quantifier(true, q.getParameters(), body);
		}
		case STMT_exists: {
			Stmt.Quantifier q = (WyalFile.Stmt.Quantifier) stmt;
			// Convert body of quantifier
			Formula body = toFormula(q.getBody(), types);
			// Done
			return new Formula.Quantifier(false, q.getParameters(), body);
		}
		case EXPR_forall: {
			Expr.Quantifier q = (WyalFile.Expr.Quantifier) stmt;
			// Convert body of quantifier
			Formula body = toFormula(q.getBody(), types);
			// Done
			return new Formula.Quantifier(true, q.getParameters(), body);
		}
		case EXPR_exists: {
			Expr.Quantifier q = (WyalFile.Expr.Quantifier) stmt;
			// Convert body of quantifier
			Formula body = toFormula(q.getBody(), types);
			// Done
			return new Formula.Quantifier(false, q.getParameters(), body);
		}
		case EXPR_and: {
			Expr.Operator b = (Expr.Operator) stmt;
			Formula[] operands = toFormulae(b.getOperands(), types);
			return new Formula.Conjunct(operands);
		}
		case EXPR_or: {
			Expr.Operator b = (Expr.Operator) stmt;
			Formula[] operands = toFormulae(b.getOperands(), types);
			return new Formula.Disjunct(operands);
		}
		case EXPR_implies: {
			WyalFile.Expr.Operator it = (Expr.Operator) stmt;
			Formula lhs = toFormula(it.getOperand(0), types);
			Formula rhs = toFormula(it.getOperand(1), types);
			return new Formula.Disjunct(invert(lhs), rhs);
		}
		case EXPR_eq: {
			Expr.Operator operator = (Expr.Operator) stmt;
			Expr lhs = operator.getOperand(0);
			Expr rhs = operator.getOperand(1);
			Type lhs_t = types.inferType(lhs);
			Type rhs_t = types.inferType(rhs);
			if (types.isRawSubtype(new Type.Int(), lhs_t) && types.isRawSubtype(new Type.Int(), rhs_t)) {
				// Force arithmetic equality
				return new Formula.ArithmeticEquality(true, lhs, rhs);
			} else {
				return new Formula.Equality(true, lhs, rhs);
			}
		}
		case EXPR_neq: {
			Expr.Operator operator = (Expr.Operator) stmt;
			Expr lhs = operator.getOperand(0);
			Expr rhs = operator.getOperand(1);
			Type lhs_t = types.inferType(lhs);
			Type rhs_t = types.inferType(rhs);
			if (types.isRawSubtype(new Type.Int(), lhs_t) && types.isRawSubtype(new Type.Int(), rhs_t)) {
				// Force arithmetic equality
				return new Formula.ArithmeticEquality(false, lhs, rhs);
			} else {
				return new Formula.Equality(false, lhs, rhs);
			}
		}
		case EXPR_lt: {
			Expr.Operator operator = (Expr.Operator) stmt;
			Expr lhs = operator.getOperand(0);
			Expr rhs = operator.getOperand(1);
			return lessThan(lhs,rhs);
		}
		case EXPR_lteq: {
			Expr.Operator operator = (Expr.Operator) stmt;
			Expr lhs = operator.getOperand(0);
			Expr rhs = operator.getOperand(1);
			return greaterOrEqual(rhs,lhs);
		}
		case EXPR_gt: {
			Expr.Operator operator = (Expr.Operator) stmt;
			Expr lhs = operator.getOperand(0);
			Expr rhs = operator.getOperand(1);
			// lhs > rhs ==> lhs+1 >= rhs
			return lessThan(rhs,lhs);
		}
		case EXPR_gteq: {
			Expr.Operator operator = (Expr.Operator) stmt;
			Expr lhs = operator.getOperand(0);
			Expr rhs = operator.getOperand(1);
			return greaterOrEqual(lhs,rhs);
		}
		case EXPR_not: {
			Expr.Operator operator = (Expr.Operator) stmt;
			Formula f = toFormula(operator.getOperand(0), types);
			return invert(f);
		}
		case EXPR_const: {
			Expr.Constant c = (Expr.Constant) stmt;
			Value.Bool b = (Value.Bool) c.getValue();
			return new Formula.Truth(b);
		}
		case EXPR_invoke: {
			Expr.Invoke ivk = (Expr.Invoke) stmt;
			if(ivk.getSignatureType() instanceof Type.Function) {
				Expr TRUE = new Formula.Truth(new Value.Bool(true));
				return new Formula.Equality(true, ivk, TRUE);
			} else {
				return new Formula.Invoke(true, ivk.getSignatureType(), ivk.getName(), ivk.getArguments());
			}
		}
		case EXPR_is: {
			Expr.Is operator = (Expr.Is) stmt;
			Expr lhs = operator.getExpr();
			Type lhs_t = types.inferType(lhs);
			if(lhs_t != null && types.isRawSubtype(new Type.Bool(), lhs_t)) {
				lhs = toFormula(lhs,types);
			}
			return new Formula.Is(lhs,operator.getTypeTest());
		}
		default:
			if (stmt instanceof WyalFile.Expr) {
				Expr expr = (WyalFile.Expr) stmt;
				Expr TRUE = new Formula.Truth(new Value.Bool(true));
				return new Formula.Equality(true, expr, TRUE);
			} else {
				throw new IllegalArgumentException("unknown statement encountered: " + stmt.getOpcode());
			}
		}
	}

	/**
	 * Convert an array of statements into an array of (equivalent) formulae.
	 *
	 * @param stmts
	 * @return
	 * @throws AmbiguousNameError
	 * @throws NameNotFoundError
	 */
	public static Formula[] toFormulae(WyalFile.Stmt[] stmts, TypeSystem types) throws ResolutionError {
		Formula[] exprs = new Formula[stmts.length];
		for (int i = 0; i != exprs.length; ++i) {
			exprs[i] = toFormula(stmts[i], types);
		}
		return exprs;
	}

	public static Formula.Inequality lessThan(Expr lhs, Expr rhs) {
		// lhs < rhs ===> rhs >= (lhs+1)
		Expr one = new Expr.Constant(new Value.Int(1));
		Expr lhsP1 = new Expr.Operator(Opcode.EXPR_add, lhs, one);
		return new Formula.Inequality(rhs, lhsP1);
	}

	public static Formula.Inequality greaterOrEqual(Expr lhs, Expr rhs) {
		return new Formula.Inequality(lhs, rhs);
	}

	public static Formula implies(Formula lhs, Formula rhs) {
		return new Formula.Disjunct(invert(lhs),rhs);
	}

	public static Formula and(Formula lhs, Formula rhs) {
		return new Formula.Conjunct(lhs,rhs);
	}

	public static Formula or(Formula lhs, Formula rhs) {
		return new Formula.Disjunct(lhs,rhs);
	}

	// ========================================================================
	// Inversion
	// ========================================================================

	/**
	 * Logically invert a given formula. This pushes through all inversions as
	 * far as possible. For example, <code>!(x == 0 && y < x)</code> becomes
	 * <code>x != 0 || y >= x</code>. This method is useful (amongst other
	 * things) for beginning a proof-by-contradiction. In such a proof, we first
	 * invert the formula in question and then establish that this reduces to a
	 * contradiction.
	 *
	 * @param f
	 * @return
	 */
	public static Formula invert(Formula f) {
		switch (f.getOpcode()) {
		case EXPR_const: {
			Formula.Truth truth = (Formula.Truth) f;
			return new Formula.Truth(!truth.holds());
		}
		case EXPR_and: {
			Formula.Conjunct c = (Formula.Conjunct) f;
			return new Disjunct(invert(c.getOperands()));
		}
		case EXPR_or: {
			Formula.Disjunct c = (Formula.Disjunct) f;
			return new Conjunct(invert(c.getOperands()));
		}
		case EXPR_exists:
		case EXPR_forall: {
			Formula.Quantifier q = (Formula.Quantifier) f;
			// FIXME: it's perhaps a little strange that we invert the body
			// here?
			return new Formula.Quantifier(!q.getSign(), q.getParameters(), invert(q.getBody()));
		}
		case EXPR_eq:
		case EXPR_neq: {
			if (f instanceof ArithmeticEquality) {
				ArithmeticEquality e = (ArithmeticEquality) f;
				return new ArithmeticEquality(!e.getSign(), e.getOperand(0), e.getOperand(1));
			} else {
				Equality e = (Equality) f;
				return new Equality(!e.getSign(), e.getOperand(0), e.getOperand(1));
			}
		}
		case EXPR_gteq: {
			// !(lhs >= rhs) => lhs < rhs
			Inequality e = (Inequality) f;
			Expr lhs = e.getOperand(0);
			Expr rhs = e.getOperand(1);
			return lessThan(lhs,rhs);
		}
		case EXPR_invoke: {
			Invoke e = (Invoke) f;
			return new Formula.Invoke(!e.getSign(),e.getSignatureType(),e.getName(),e.getArguments());
		}
		case EXPR_is: {
			Formula.Is c = (Formula.Is) f;
			// FIXME: could simplify the type here I think
			return new Is(c.getExpr(), new Type.Negation(c.getTypeTest()));
		}
		default:
			throw new IllegalArgumentException("invalid formula opcode: " + f.getOpcode());
		}
	}

	private static Formula[] invert(Formula[] children) {
		Formula[] nChildren = new Formula[children.length];
		for (int i = 0; i != children.length; ++i) {
			nChildren[i] = invert(children[i]);
		}
		return nChildren;
	}

	// ========================================================================
	// Simplifications
	// ========================================================================

}
