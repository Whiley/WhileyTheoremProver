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
package wyal.util;

import java.util.List;

import wyal.lang.*;
import wyal.lang.NameResolver.ResolutionError;
import wyal.lang.WyalFile.Declaration.Named;
import wycc.util.ArrayUtils;
import wycc.util.Pair;
import wytp.types.TypeInferer.Environment;
import wytp.types.util.NullTypeEnvironment;
import wytp.types.TypeSystem;
import wyal.lang.WyalFile.Expr;
import wyal.lang.WyalFile.FieldDeclaration;
import wyal.lang.WyalFile.Identifier;
import wyal.lang.WyalFile.Name;
import wyal.lang.WyalFile.Stmt;
import wyal.lang.WyalFile.Tuple;
import wyal.lang.WyalFile.Type;
import wyal.lang.WyalFile.Value;
import wyal.lang.WyalFile.VariableDeclaration;
import wybs.lang.SyntacticElement;
import wybs.lang.SyntaxError;

/**
 * <p>
 * Implements a <i>flow-sensitive</i> type checker for WyAL source files which
 * performs various tasks: firstly, it checks that the various kinds of
 * expression are used correctly using flow typing to help; secondly, it checks
 * that declarations are "sensible"; finally, it resolves function and macro
 * invocations based on their type signature. Let's consider each of these in
 * turn.
 * </p>
 *
 * <p>
 * <b>Type checking expressions</b>. The primary function of the type checker is
 * to check that expressions are used correctly. For example, we expect
 * arithmetic operators to operator on integer types. Likewise, we cannot
 * perform an "array access" on an integer. The following illustrates such an
 * incorrect program:
 *
 * <pre>
 * assert:
 *   forall(int i, int j):
 *     i[j] == i[j]
 * </pre>
 *
 * The above program is not "type safe" because variable <code>i</code> is used
 * in a position where an array is expected. Another similar example is the
 * following:
 *
 * <pre>
 * assert:
 *   forall(int[] xs, bool i):
 *     xs[i] == xs[i]
 * </pre>
 *
 * Arrays can only be accessed using integer values and, hence, the above fails
 * because we are attempting to access array <code>xs</code> using a bool.
 * </p>
 * <p>
 * To illustrate flow-sensitive typing (a.k.a <i>flow typing</i>), consider the
 * following
 *
 * <pre>
 * forall(int|null x):
 *     if:
 *        x is int
 *        x &gt; 0
 *     then:
 *        x &gt;= 0
 * </pre>
 *
 * If the type checker only considered the declated type of <code>x</code> when
 * typing the expression <code>x gt; 0</code> then it would report an error
 * (i.e. because <code>int|null</code> is not of the expected type
 * <code>int</code>). To resolve this, the type checker maintains a typing
 * environment at each point in the program which includes any "refinements"
 * which are known to be true at that point (for example, that
 * <code>x is int</code> above). The current environment is used when type
 * checking a given expression, meaning that the above does indeed type check.
 * </p>
 *
 * <p>
 * <b>Sanity checking declarations</b>. When declaring a type, function, macro
 * or variable, it is possible to use a type which simply doesn't make sense. In
 * such case, we want the type checker to report a problem (as we might not have
 * been aware of this). The following illustrates such a case:
 *
 * <pre>
 * type empty is ((int&!int) x)
 * </pre>
 *
 * Here, the type <code>empty</code> defines a type which is equivalent to
 * <code>void</code> and, as such, it is impossible to use this type! The type
 * checker simply reports an error for any such types it encounters.
 * </p>
 *
 * <p>
 * <b>Resolving function or macro invocations</b>. The WyAL language supports
 * <i>overloading</i> of functions and macros. It does this primarily because
 * the Whiley language (for which WyAL is designed) supports this feature and we
 * wish WyAL programs to "look like" whiley programs as much as possible. A
 * simple example of this would be:
 *
 * <pre>
 * function id(int x) -> (int r)
 * function id(bool b) -> (bool r)
 *
 * assert:
 *   forall(int x, int y, int[] arr):
 *      if:
 *         id(x) == id(y)
 *      then:
 *         arr[id(x)] == arr[id(y)]
 * </pre>
 *
 * We can see here that the correct type for <code>id()</code> must be
 * determined in order of the expression <code>arr[id(x)]</code> to type check.
 * When deciding which is the appropriate type signature for an invocation,
 * there are several factors. Firstly, any candidates which are obviously
 * nonsense must be discarded (e.g. <code>id(bool)</code> above, since
 * <code>x</code> has type <code>int</code>). However, it is possible that there
 * are multiple candidates and the type checker will always choose the "most
 * precise" (or give up with an error if none exists). The following
 * illustrates:
 *
 * <pre>
 * function id(int x) -> (int r)
 * function id(int|null xn) -> (bool r)
 *
 * assert:
 *   forall(int x, int y, int[] arr):
 *      if:
 *         id(x) == id(y)
 *      then:
 *         arr[id(x)] == arr[id(y)]
 * </pre>
 *
 * In this example, the type checker will determine the signature
 * <code>id(int)</code> for the invocation. This is because that is the most
 * precise type which matches the given arguments.
 * </p>
 *
 * @author David J. Pearce
 *
 */
public class TypeChecker {
	/**
	 * The enclosing WyAL file being checked.
	 */
	private final WyalFile parent;

	/**
	 * The type system encapsulates the core algorithms for type simplification
	 * and subtyping testing.
	 */
	private TypeSystem types;

	public TypeChecker(TypeSystem typeSystem, WyalFile parent) {
		this.parent = parent;
		this.types = typeSystem;
	}

	public void check() {
		for (int i = 0; i != parent.size(); ++i) {
			SyntacticItem item = parent.getSyntacticItem(i);
			if (item instanceof WyalFile.Declaration) {
				check((WyalFile.Declaration) item);
			}
		}
	}

	private void check(WyalFile.Declaration decl) {
		if (decl instanceof WyalFile.Declaration.Assert) {
			check((WyalFile.Declaration.Assert) decl);
		} else if (decl instanceof WyalFile.Declaration.Named) {
			check((WyalFile.Declaration.Named) decl);
		} else if (decl instanceof WyalFile.Declaration.Import) {
			// nothing to do here
		} else {
			throw new IllegalArgumentException("unknown declaration: " + decl);
		}
	}

	private void check(WyalFile.Declaration.Assert decl) {
		checkStatement(TypeSystem.NULL_ENVIRONMENT, true, decl.getBody());
	}

	private void check(WyalFile.Declaration.Named decl) {
		if (decl instanceof WyalFile.Declaration.Named.FunctionOrMacro) {
			check((WyalFile.Declaration.Named.FunctionOrMacro) decl);
		} else if (decl instanceof WyalFile.Declaration.Named.Type) {
			check((WyalFile.Declaration.Named.Type) decl);
		} else {
			throw new IllegalArgumentException("unknown named declaration: " + decl);
		}
	}

	private void check(WyalFile.Declaration.Named.FunctionOrMacro decl) {
		checkNonEmpty(decl.getParameters());
		//
		if (decl instanceof WyalFile.Declaration.Named.Function) {
			check((WyalFile.Declaration.Named.Function) decl);
		} else {
			check((WyalFile.Declaration.Named.Macro) decl);
		}
	}

	private void check(WyalFile.Declaration.Named.Function decl) {
		checkNonEmpty(decl.getReturns());
	}

	private void check(WyalFile.Declaration.Named.Macro decl) {
		checkStatement(TypeSystem.NULL_ENVIRONMENT, true, decl.getBody());
	}

	private void check(WyalFile.Declaration.Named.Type decl) {
		checkNonEmpty(decl.getVariableDeclaration());
		//
		WyalFile.Tuple<Stmt.Block> invariant = decl.getInvariant();
		Environment env = TypeSystem.NULL_ENVIRONMENT;
		for (int i = 0; i != invariant.size(); ++i) {
			Stmt.Block clause = invariant.getOperand(i);
			env = checkStatement(env, true, clause);
		}
	}

	/**
	 * <p>
	 * Type check a given statement in a given environment with a given sign.
	 * The simplest possible example is the following:
	 * </p>
	 *
	 * <pre>
	 * forall(int x):
	 *     if:
	 *        x &gt; 0
	 *     then:
	 *        x &gt;= 0
	 * </pre>
	 *
	 * <p>
	 * When (for example) typing <code>x &gt; 0</code> here, the environment
	 * would simply map <code>x</code> to its declared type <code>int</code>.
	 * However, because WyAL supports "flow typing", it's not always the case
	 * that the declared type of a variable is the right one to use. Consider a
	 * more complex case.
	 * </p>
	 *
	 * <pre>
	 * forall(int|null x):
	 *     if:
	 *        x is int
	 *        x &gt; 0
	 *     then:
	 *        x &gt;= 0
	 * </pre>
	 *
	 * <p>
	 * This time, when typing (for example) typing <code>x &gt; 0</code>, we
	 * need to account for the fact that <code>x is int</code> is known. As
	 * such, the calculated type for <code>x</code> would be
	 * <code>(int|null)&int</code> when typing <code>x &gt; 0</code>.
	 * </p>
	 * <p>
	 * The purpose of the "sign" is to aid flow typing in the presence of
	 * negations. In essence, the sign indicates whether the statement being
	 * type checked is positive (i.e. sign=<code>true</code>) or negated (i.e.
	 * sign=<code>false</code>). In the latter case, the application of any type
	 * tests will be inverted. The following illustrates an interesting example:
	 * </p>
	 *
	 * <pre>
	 * forall(int|null x):
	 *     if:
	 *        !(x is null || x &lt; 0)
	 *     then:
	 *        x &gt;= 0
	 * </pre>
	 *
	 * <p>
	 * To type check this example, the type checked needs to effectively "push"
	 * the logical negation through the disjunction to give
	 * <code>!(x is null) && x &gt;= 0</code>. The purpose of the sign is to
	 * enable this without actually rewriting the source code.
	 * </p>
	 *
	 * @param env
	 * @param sign
	 * @param stmt
	 * @return The (potentially updated) typing environment for this statement.
	 */
	protected Environment checkStatement(Environment env, boolean sign, Stmt stmt) {
		switch (stmt.getOpcode()) {
		case STMT_block:
			return checkBlock(env, sign, (Stmt.Block) stmt);
		case STMT_ifthen:
			return checkIfThen(env, sign, (Stmt.IfThen) stmt);
		case STMT_caseof:
			return checkCaseOf(env, sign, (Stmt.CaseOf) stmt);
		case STMT_forall:
		case STMT_exists:
			return checkQuantifier(env, sign, (Stmt.Quantifier) stmt);
		case EXPR_not:
			return checkLogicalNegation(env, sign, (Expr.Operator) stmt);
		case EXPR_and:
		case EXPR_or:
		case EXPR_implies:
		case EXPR_iff:
			return checkLogicalConnective(env, sign, (Expr.Operator) stmt);
		case EXPR_forall:
		case EXPR_exists:
			return checkQuantifier(env, sign, (Expr.Quantifier) stmt);
		case EXPR_is:
			return checkIsOperator(env, sign, (Expr.Is) stmt);
		default:
			Type t = checkExpression(env, (Expr) stmt);
			checkIsSubtype(new Type.Bool(), t, stmt);
			return env;
		}
	}

	private Environment checkBlock(Environment env, boolean sign, Stmt.Block stmt) {
		if (sign) {
			return conjunct(env, true, stmt.getOperands());
		} else {
			return disjunct(env, false, stmt.getOperands());
		}
	}

	private Environment checkCaseOf(Environment env, boolean sign, Stmt.CaseOf stmt) {
		for (Stmt child : stmt.getOperands()) {
			env = checkStatement(env, sign, child);
		}
		return env;
	}

	private Environment checkIfThen(Environment env, boolean sign, Stmt.IfThen stmt) {
		// To understand this, remember that A ==> B is equivalent to !A || B.
		if (sign) {
			// First case assumes the if body doesn't hold.
			Environment left = checkStatement(env, false, stmt.getIfBody());
			// Second case assumes the if body holds ...
			env = checkStatement(env, true, stmt.getIfBody());
			// ... and then passes this into the then body
			Environment right = checkStatement(env, true, stmt.getThenBody());
			//
			return union(left, right);
		} else {
			// Effectively, this is a conjunction now: A && !B
			env = checkStatement(env, true, stmt.getIfBody());
			env = checkStatement(env, false, stmt.getThenBody());
			return env;
		}
	}

	private Environment checkLogicalNegation(Environment env, boolean sign, Expr.Operator expr) {
		return checkStatement(env, !sign, expr.getOperand(0));
	}

	/**
	 * Check the type for a given logical operator. Such an operator has the
	 * type bool, and all children should also produce values of type bool.
	 *
	 * @param expr
	 * @return
	 */
	private Environment checkLogicalConnective(Environment env, boolean sign, Expr.Operator expr) {
		switch (expr.getOpcode()) {
		case EXPR_implies:
			return checkLogicalImplication(env, sign, expr);
		case EXPR_and:
			return checkLogicalConjunction(env, sign, expr);
		case EXPR_or:
			return checkLogicalDisjunction(env, sign, expr);
		default:
			throw new IllegalArgumentException("unknown logical connective: " + expr);
		}
	}

	private Environment checkLogicalImplication(Environment env, boolean sign, Expr.Operator expr) {
		// To understand this, remember that A ==> B is equivalent to !A || B.
		if (sign) {
			// First case assumes the if body doesn't hold.
			Environment left = checkStatement(env, false, expr.getOperand(0));
			// Second case assumes the if body holds ...
			env = checkStatement(env, true, expr.getOperand(0));
			// ... and then passes this into the then body
			Environment right = checkStatement(env, true, expr.getOperand(1));
			//
			return union(left, right);
		} else {
			// Effectively, this is a conjunction now: A && !B
			env = checkStatement(env, true, expr.getOperand(0));
			env = checkStatement(env, false, expr.getOperand(1));
			return env;
		}
	}

	private Environment checkLogicalDisjunction(Environment env, boolean sign, Expr.Operator expr) {
		if (sign) {
			return disjunct(env, true, expr.getOperands());
		} else {
			return conjunct(env, false, expr.getOperands());
		}
	}

	private Environment checkLogicalConjunction(Environment env, boolean sign, Expr.Operator expr) {
		if (sign) {
			return conjunct(env, true, expr.getOperands());
		} else {
			return disjunct(env, false, expr.getOperands());
		}
	}

	private Environment checkQuantifier(Environment env, boolean sign, Stmt.Quantifier stmt) {
		checkNonEmpty(stmt.getParameters());
		return checkStatement(env, sign, stmt.getBody());
	}

	private Environment checkQuantifier(Environment env, boolean sign, Expr.Quantifier stmt) {
		checkNonEmpty(stmt.getParameters());
		return checkStatement(env, sign, stmt.getBody());
	}

	private Environment checkIsOperator(Environment env, boolean sign, Expr.Is expr) {
		Expr lhs = expr.getTestExpr();
		Type rhs = expr.getTestType();
		// Account the case when this test is inverted
		rhs = sign ? rhs : negate(rhs);
		//
		Type lhsT = checkExpression(env, expr.getTestExpr());
		// TODO: implement a proper intersection test here to ensure lhsT and
		// rhs types make sense (i.e. have some intersection).
		Pair<WyalFile.VariableDeclaration, Type> extraction = extractTypeTest(lhs, rhs);
		if (extraction != null) {
			WyalFile.VariableDeclaration var = extraction.first();
			// Update the typing environment accordingly.
			env = env.refineType(var, extraction.second());
		}
		//
		return env;
	}

	/**
	 * <p>
	 * Extract the "true" test from a given type test in order that we might try
	 * to retype it. This does not always succeed if, for example, the
	 * expression being tested cannot be retyped. An example would be a test
	 * like <code>arr[i] is int</code> as, in this case, we cannot retype
	 * <code>arr[i]</code>.
	 * </p>
	 *
	 * <p>
	 * In the simple case of e.g. <code>x is int</code> we just extract
	 * <code>x</code> and type <code>int</code>. The more interesting case
	 * arises when there is at least one field access involved. For example,
	 * <code>x.f is int</code> extracts variable <code>x</code> with type
	 * <code>{int f, ...}</code> (which is a safe approximation).
	 * </p>
	 *
	 * @param expr
	 * @param type
	 * @return A pair on successful extraction, or null if possible extraction.
	 */
	private Pair<WyalFile.VariableDeclaration, Type> extractTypeTest(Expr expr, Type type) {
		if (expr instanceof Expr.VariableAccess) {
			Expr.VariableAccess var = (Expr.VariableAccess) expr;
			return new Pair<>(var.getVariableDeclaration(), type);
		} else if (expr instanceof Expr.RecordAccess) {
			Expr.RecordAccess ra = (Expr.RecordAccess) expr;
			FieldDeclaration field = new FieldDeclaration(type, ((Expr.RecordAccess) expr).getField());
			Type.Record recT = new Type.Record(true, field);
			return extractTypeTest(ra.getSource(), recT);
		} else {
			// no extraction is possible
			return null;
		}
	}

	private Type checkExpression(Environment env, Expr expr) {
		switch (expr.getOpcode()) {
		// Ignored
		case EXPR_const:
			return checkConstant(env, (Expr.Constant) expr);
		case EXPR_var:
			return checkVariable(env, (Expr.VariableAccess) expr);
		case EXPR_invoke:
			return checkInvocation(env, (Expr.Invoke) expr);
		case EXPR_iff:
		case EXPR_implies:
		case EXPR_and:
		case EXPR_or:
			checkLogicalConnective(env, true, (Expr.Operator) expr);
			return new Type.Bool();
		case EXPR_not:
			checkLogicalNegation(env, true, (Expr.Operator) expr);
			return new Type.Bool();
		case EXPR_eq:
		case EXPR_neq:
		case EXPR_lt:
		case EXPR_lteq:
		case EXPR_gt:
		case EXPR_gteq:
			return checkComparisonOperator(env, (Expr.Operator) expr);
		case EXPR_neg:
		case EXPR_add:
		case EXPR_sub:
		case EXPR_mul:
		case EXPR_div:
		case EXPR_rem:
			return checkArithmeticOperator(env, (Expr.Operator) expr);
		// Record expressions
		case EXPR_recinit:
			return checkRecordInitialiser(env, (Expr.RecordInitialiser) expr);
		case EXPR_recfield:
			return checkRecordAccess(env, (Expr.RecordAccess) expr);
		case EXPR_recupdt:
			return checkRecordUpdate(env, (Expr.RecordUpdate) expr);
		// Array expressions
		case EXPR_arrlen:
			return checkArrayLength(env, (Expr.ArrayLength) expr);
		case EXPR_arrinit:
			return checkArrayInitialiser(env, (Expr.ArrayInitialiser) expr);
		case EXPR_arrgen:
			return checkArrayGenerator(env, (Expr.ArrayGenerator) expr);
		case EXPR_arridx:
			return checkArrayAccess(env, (Expr.ArrayAccess) expr);
		case EXPR_arrupdt:
			return checkArrayUpdate(env, (Expr.ArrayUpdate) expr);
		// Reference expressions ?
		case EXPR_deref:
			return checkDereference(env, (Expr.Dereference) expr);
		default:
			throw new RuntimeException("unknown statement or expression: " + expr);
		}
	}

	/**
	 * Check the type of a given constant expression. This is straightforward
	 * since the determine is fully determined by the kind of constant we have.
	 *
	 * @param expr
	 * @return
	 */
	private Type checkConstant(Environment env, Expr.Constant expr) {
		Value item = expr.getValue();
		switch (item.getOpcode()) {
		case CONST_null:
			return new Type.Null();
		case CONST_bool:
			return new Type.Bool();
		case CONST_int:
			return new Type.Int();
		default:
			throw new RuntimeException("unknown constant encountered: " + expr);
		}
	}

	/**
	 * Check the type of a given variable access. This is straightforward since
	 * the determine is fully determined by the declared type for the variable
	 * in question.
	 *
	 * @param expr
	 * @return
	 */
	private Type checkVariable(Environment env, Expr.VariableAccess expr) {
		VariableDeclaration var = expr.getVariableDeclaration();
		return env.getType(var);
	}

	private Type checkInvocation(Environment env, Expr.Invoke expr) {
		// Determine the argument types
		WyalFile.Tuple<Expr> arguments = expr.getArguments();
		Type[] types = new Type[arguments.size()];
		for (int i = 0; i != arguments.size(); ++i) {
			types[i] = checkExpression(env, arguments.getOperand(i));
		}
		// Attempt to resolve the appropriate function type
		Named.FunctionOrMacro sig = resolveAsDeclaredFunctionOrMacro(expr.getName(), expr, types);
		Type.FunctionOrMacro type = sig.getSignatureType();
		// Replace old object with fully resolved object
		expr.setSignatureType(parent.allocate(type));
		// Finally, return the declared returns
		Value.Int selector = expr.getSelector();
		//
		if (selector == null && type.getReturns().size() != 1) {
			throw new SyntaxError("invalid number of returns", parent.getEntry(), expr);
		} else if(selector == null){
			return type.getReturns().getOperand(0);
		} else {
			return type.getReturns().getOperand(selector.get().intValue());
		}
	}

	private Type checkRecordAccess(Environment env, Expr.RecordAccess expr) {
		Type src = checkExpression(env, expr.getSource());
		Type.Record effectiveRecord = checkIsRecordType(src, expr.getSource());
		//
		FieldDeclaration[] fields = effectiveRecord.getFields();
		String actualFieldName = expr.getField().get();
		for (int i = 0; i != fields.length; ++i) {
			FieldDeclaration vd = fields[i];
			String declaredFieldName = vd.getVariableName().get();
			if (declaredFieldName.equals(actualFieldName)) {
				return vd.getType();
			}
		}
		//
		throw new SyntaxError("invalid field access", parent.getEntry(), expr.getField());
	}

	private Type checkRecordUpdate(Environment env, Expr.RecordUpdate expr) {
		Type src = checkExpression(env, expr.getSource());
		Type val = checkExpression(env, expr.getValue());
		Type.Record effectiveRecord = checkIsRecordType(src, expr.getSource());
		//
		FieldDeclaration[] fields = effectiveRecord.getFields();
		String actualFieldName = expr.getField().get();
		for (int i = 0; i != fields.length; ++i) {
			FieldDeclaration vd = fields[i];
			String declaredFieldName = vd.getVariableName().get();
			if (declaredFieldName.equals(actualFieldName)) {
				// Matched the field type
				checkIsSubtype(vd.getType(), val, expr.getValue());
				return src;
			}
		}
		//
		throw new SyntaxError("invalid field update", parent.getEntry(), expr.getField());
	}

	private Type checkRecordInitialiser(Environment env, Expr.RecordInitialiser expr) {
		WyalFile.Pair<Identifier, Expr>[] fields = expr.getFields();
		FieldDeclaration[] decls = new FieldDeclaration[fields.length];
		for (int i = 0; i != fields.length; ++i) {
			Identifier fieldName = fields[i].getFirst();
			Type fieldType = checkExpression(env, fields[i].getSecond());
			decls[i] = new FieldDeclaration(fieldType, fieldName);
		}
		//
		return new Type.Record(false, decls);
	}

	/**
	 * Check the type for a given arithmetic operator. Such an operator has the
	 * type int, and all children should also produce values of type int.
	 *
	 * @param expr
	 * @return
	 */
	private Type checkArithmeticOperator(Environment env, Expr.Operator expr) {
		checkOperands(env, expr, new Type.Int());
		return new Type.Int();
	}

	/**
	 * Check the type for a given arithmetic operator. Such an operator has the
	 * type bool, and all children should also produce values of type int.
	 *
	 * @param expr
	 * @return
	 */
	private Type checkComparisonOperator(Environment env, Expr.Operator expr) {
		switch (expr.getOpcode()) {
		case EXPR_eq:
		case EXPR_neq:
			return checkEqualityOperator(env, expr);
		default:
			return checkArithmeticComparator(env, expr);
		}
	}

	private Type checkEqualityOperator(Environment env, Expr.Operator expr) {
		// FIXME: we could be more selective here I think. For example, by
		// checking that the given operands actually overall.
		for (int i = 0; i != expr.size(); ++i) {
			checkExpression(env, expr.getOperand(i));
		}
		return new Type.Bool();
	}

	private Type checkArithmeticComparator(Environment env, Expr.Operator expr) {
		checkOperands(env, expr, new Type.Int());
		return new Type.Bool();
	}

	private void checkOperands(Environment env, Expr.Operator expr, Type type) {
		for (int i = 0; i != expr.size(); ++i) {
			Expr operand = expr.getOperand(i);
			checkIsSubtype(type, checkExpression(env, operand), operand);
		}
	}

	private Type checkArrayLength(Environment env, Expr.ArrayLength expr) {
		Type src = checkExpression(env, expr.getSource());
		checkIsArrayType(src, expr.getSource());
		return new Type.Int();
	}

	private Type checkArrayInitialiser(Environment env, Expr.ArrayInitialiser expr) {
		Type[] ts = new Type[expr.size()];
		for (int i = 0; i != ts.length; ++i) {
			ts[i] = checkExpression(env, expr.getOperand(i));
		}
		ts = ArrayUtils.removeDuplicates(ts);
		Type element = ts.length == 1 ? ts[0] : new Type.Union(ts);
		return new Type.Array(element);
	}

	private Type checkArrayGenerator(Environment env, Expr.ArrayGenerator expr) {
		Expr value = expr.getValue();
		Expr length = expr.getLength();
		//
		Type valueT = checkExpression(env, value);
		Type lengthT = checkExpression(env, length);
		//
		checkIsSubtype(new Type.Int(), lengthT, length);
		return new Type.Array(valueT);
	}

	private Type checkArrayAccess(Environment env, Expr.ArrayAccess expr) {
		Expr source = expr.getSource();
		Expr subscript = expr.getSubscript();
		//
		Type sourceT = checkExpression(env, source);
		Type subscriptT = checkExpression(env, subscript);
		//
		Type.Array sourceArrayT = checkIsArrayType(sourceT, source);
		checkIsSubtype(new Type.Int(), subscriptT, subscript);
		//
		return sourceArrayT.getElement();
	}

	private Type checkArrayUpdate(Environment env, Expr.ArrayUpdate expr) {
		Expr source = expr.getSource();
		Expr subscript = expr.getSubscript();
		Expr value = expr.getValue();
		//
		Type sourceT = checkExpression(env, source);
		Type subscriptT = checkExpression(env, subscript);
		Type valueT = checkExpression(env, value);
		//
		Type.Array sourceArrayT = checkIsArrayType(sourceT, source);
		checkIsSubtype(new Type.Int(), subscriptT, subscript);
		checkIsSubtype(sourceArrayT.getElement(), valueT, value);
		return sourceArrayT;
	}

	private Type checkDereference(Environment env, Expr.Dereference expr) {
		Type operandT = checkExpression(env, expr.getOperand());
		//
		Type.Reference refT = checkIsReferenceType(operandT, expr.getOperand());
		//
		return refT.getElement();
	}

	/**
	 * Check whether a given type is an array type of some sort.
	 *
	 * @param type
	 * @return
	 * @throws ResolutionError
	 */
	private Type.Array checkIsArrayType(Type type, SyntacticElement element) {
		try {
			Type.Array arrT = types.extractReadableArray(type);
			if (arrT == null) {
				throw new SyntaxError("expected array type", parent.getEntry(), element);
			}
			return arrT;
		} catch (NameResolver.ResolutionError e) {
			throw new SyntaxError(e.getMessage(), parent.getEntry(), e.getName(), e);
		}
	}

	/**
	 * Check whether a given type is a record type of some sort.
	 *
	 * @param type
	 * @return
	 */
	private Type.Record checkIsRecordType(Type type, SyntacticElement element) {
		try {
			Type.Record recT = types.extractReadableRecord(type);
			if (recT == null) {
				throw new SyntaxError("expected record type", parent.getEntry(), element);
			}
			return recT;
		} catch (NameResolver.ResolutionError e) {
			throw new SyntaxError(e.getMessage(), parent.getEntry(), e.getName(), e);
		}
	}

	/**
	 * Check whether a given type is a reference type of some sort.
	 *
	 * @param type
	 * @return
	 * @throws ResolutionError
	 */
	private Type.Reference checkIsReferenceType(Type type, SyntacticElement element) {
		// TODO: should consider whether it makes sense to think about readable
		// reference types.
		if(type instanceof Type.Reference){
			return (Type.Reference) type;
		} else {
			throw new SyntaxError("expected reference type", parent.getEntry(), element);
		}
	}

	/**
	 * Attempt to determine the declared function or macro to which a given
	 * invocation refers. To resolve this requires considering the name, along
	 * with the argument types as well.
	 *
	 * @param name
	 * @param args
	 * @return
	 */
	private Named.FunctionOrMacro resolveAsDeclaredFunctionOrMacro(Name name, SyntacticElement context, Type... args) {
		try {
			// Identify all function or macro declarations which should be
			// considered
			List<Named.FunctionOrMacro> candidates = types.resolveAll(name, Named.FunctionOrMacro.class);
			// Based on given argument types, select the most precise signature
			// from the candidates.
			Named.FunctionOrMacro selected = selectCandidateFunctionOrMacroDeclaration(candidates, args);
			return selected;
		} catch (ResolutionError e) {
			throw new SyntaxError(e.getMessage(), parent.getEntry(), context);
		}
	}

	/**
	 * Given a list of candidate function or macro declarations, determine the
	 * most precise match for the supplied argument types. The given argument
	 * types must be applicable to this function or macro declaration, and it
	 * must be a subtype of all other applicable candidates.
	 *
	 * @param candidates
	 * @param args
	 * @return
	 */
	private Named.FunctionOrMacro selectCandidateFunctionOrMacroDeclaration(List<Named.FunctionOrMacro> candidates,
			Type... args) {
		Named.FunctionOrMacro best = null;
		for (int i = 0; i != candidates.size(); ++i) {
			Named.FunctionOrMacro candidate = candidates.get(i);
			// Check whether the given candidate is a real candidate or not. A
			if (isApplicable(candidate, args)) {
				// Yes, this candidate is applicable.
				if (best == null) {
					// No other candidates are applicable so far. Hence, this
					// one is automatically promoted to the best seen so far.
					best = candidate;
				} else if (isSubtype(candidate, best)) {
					// This candidate is a subtype of the best seen so far.
					// Hence, it is now the best seen so far.
					best = candidate;
				} else if (isSubtype(best, candidate)) {
					// This best so far is a subtype of this candidate.
					// Therefore, we can simply discard this candidate from
					// consideration.
				} else {
					// This is the awkward case. Neither the best so far, nor
					// the candidate, are subtypes of each other. In this case,
					// we report an error.
					throw new IllegalArgumentException("unable to resolve function");
				}
			}
		}
		// Having considered each candidate in turn, do we now have a winner?
		if (best != null) {
			// Yes, we have a winner.
			return best;
		} else {
			// No, there was no winner. In fact, there must have been no
			// applicable candidates to get here.
			throw new IllegalArgumentException("unable to resolve function");
		}
	}

	/**
	 * Determine whether a given function or macro declaration is applicable to
	 * a given set of argument types. If there number of arguments differs, it's
	 * definitely not applicable. Otherwise, we need every argument type to be a
	 * subtype of its corresponding parameter type.
	 *
	 * @param candidate
	 * @param args
	 * @return
	 */
	private boolean isApplicable(Named.FunctionOrMacro candidate, Type... args) {
		WyalFile.Tuple<VariableDeclaration> parameters = candidate.getParameters();
		if (parameters.size() != args.length) {
			// Differing number of parameters / arguments. Since we don't
			// support variable-length argument lists (yet), there is nothing
			// more to consider.
			return false;
		}
		try {
			// Number of parameters matches number of arguments. Now, check that
			// each argument is a subtype of its corresponding parameter.
			for (int i = 0; i != args.length; ++i) {
				Type param = parameters.getOperand(i).getType();
				if (!types.isRawSubtype(param, args[i])) {
					return false;
				}
			}
			//
			return true;
		} catch (NameResolver.ResolutionError e) {
			throw new SyntaxError(e.getMessage(), parent.getEntry(), e.getName(), e);
		}
	}

	private void checkIsSubtype(Type lhs, Type rhs, SyntacticElement element) {
		try {
			if (!types.isRawSubtype(lhs, rhs)) {
				throw new SyntaxError("type " + rhs + " not subtype of " + lhs, parent.getEntry(), element);
			}
		} catch (NameResolver.ResolutionError e) {
			throw new SyntaxError(e.getMessage(), parent.getEntry(), e.getName(), e);
		}
	}

	/**
	 * Check whether the type signature for a given function declaration is a
	 * super type of a given child declaration.
	 *
	 * @param lhs
	 * @param rhs
	 * @return
	 */
	private boolean isSubtype(Named.FunctionOrMacro lhs, Named.FunctionOrMacro rhs) {
		WyalFile.Tuple<VariableDeclaration> parentParams = lhs.getParameters();
		WyalFile.Tuple<VariableDeclaration> childParams = rhs.getParameters();
		if (parentParams.size() != childParams.size()) {
			// Differing number of parameters / arguments. Since we don't
			// support variable-length argument lists (yet), there is nothing
			// more to consider.
			return false;
		}
		try {
			// Number of parameters matches number of arguments. Now, check that
			// each argument is a subtype of its corresponding parameter.
			for (int i = 0; i != parentParams.size(); ++i) {
				Type parentParam = parentParams.getOperand(i).getType();
				Type childParam = childParams.getOperand(i).getType();
				if (!types.isRawSubtype(parentParam, childParam)) {
					return false;
				}
			}
			//
			return true;
		} catch (NameResolver.ResolutionError e) {
			throw new SyntaxError(e.getMessage(), parent.getEntry(), e.getName(), e);
		}
	}

	private void checkNonEmpty(Tuple<WyalFile.VariableDeclaration> decls) {
		for(int i=0;i!=decls.size();++i) {
			checkNonEmpty(decls.getOperand(i));
		}
	}

	private void checkNonEmpty(WyalFile.VariableDeclaration d) {
		try {
			Type type = d.getType();
			if (types.isRawSubtype(new Type.Void(), type)) {
				throw new SyntaxError("empty type", parent.getEntry(), type);
			}
		} catch (NameResolver.ResolutionError e) {
			throw new SyntaxError(e.getMessage(), parent.getEntry(), e.getName(), e);
		}
	}

	/**
	 * In this case, we are threading each environment as is through to the next
	 * statement. For example, consider this example:
	 *
	 * <pre>
	 * forall(int|null x):
	 *   if:
	 *       x is int
	 *       x &gt; 0
	 *   then:
	 *       ...
	 * </pre>
	 *
	 * The environment going into <code>x is int</code> will be
	 * <code>{x->(int|null)}</code>. The environment coming out of this
	 * statement will be <code>{x-&gt;int}</code> and this is just threaded
	 * directly into the next statement <code>x &gt; 0</code>
	 *
	 * @param env
	 * @param sign
	 * @param operands
	 * @return
	 */
	private Environment conjunct(Environment env, boolean sign, Stmt[] operands) {
		for (int i = 0; i != operands.length; ++i) {
			env = checkStatement(env, sign, operands[i]);
		}
		return env;
	}

	/**
	 * In this case, we are assuming the environments are exclusive from each
	 * other (i.e. this is the opposite of threading them through). For example,
	 * consider this case:
	 *
	 * <pre>
	 * forall(int|null x):
	 *   either:
	 *       x is null
	 *   or:
	 *       x is int
	 * </pre>
	 *
	 * The environment produced by the <code>either</code> block
	 * <code>{x->null}</code>. We cannot thread this environment into the
	 * <code>or</code> block as, clearly, it's not correct. Instead, we want to
	 * thread through the environment which arises on the assumption the fist
	 * case is false. That would be <code>{x->!null}</code>. Finally, the
	 * resulting environment is simply the union of the two environments from
	 * each case.
	 *
	 * @param env
	 * @param sign
	 * @param operands
	 * @return
	 */
	private Environment disjunct(Environment env, boolean sign, Stmt[] operands) {
		Environment[] refinements = new Environment[operands.length];
		for (int i = 0; i != operands.length; ++i) {
			refinements[i] = checkStatement(env, sign, operands[i]);
			// This is the clever bit. We recalculate the whole thing assuming
			// the opposite sign.
			env = checkStatement(env, !sign, operands[i]);
		}
		// Done.
		return union(refinements);
	}

	protected Environment union(Environment... environments) {
		Environment result = environments[0];
		for (int i = 1; i != environments.length; ++i) {
			result = union(result, environments[i]);
		}
		//
		return result;
	}

	public Environment union(Environment left, Environment right) {
		if (left == right) {
			return left;
		} else {
			Environment result = new NullTypeEnvironment();

			for (WyalFile.VariableDeclaration var : left.getRefinedVariables()) {
				Type declT = var.getType();
				Type rightT = right.getType(var);
				if (rightT != declT) {
					// We have a refinement on both branches
					Type leftT = left.getType(var);
					result = result.refineType(var, union(leftT, rightT));
				}
			}
			return result;
		}
	}

	public Type negate(Type type) {
		// FIXME: a more comprehensive simplification strategy would make sense
		// here.
		if (type instanceof Type.Negation) {
			Type.Negation nt = (Type.Negation) type;
			return nt.getElement();
		} else {
			return new Type.Negation(type);
		}
	}

	public Type union(Type left, Type right) {
		// FIXME: a more comprehensive simplification strategy would make sense
		// here.
		if (left == right || left.equals(right)) {
			return left;
		} else {
			return new Type.Union(left, right);
		}
	}

}
