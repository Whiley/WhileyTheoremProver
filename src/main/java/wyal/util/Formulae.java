package wyal.util;

import java.math.BigInteger;
import java.util.Arrays;
import java.util.Set;

import wyal.lang.Formula;
import wyal.lang.SyntacticItem;
import wyal.lang.WyalFile;
import wyal.lang.WyalFile.*;
import wyal.lang.WyalFile.Expr.Polynomial;
import wyal.lang.Formula.*;
import wycc.util.ArrayUtils;

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
	 */
	public static Formula toFormula(WyalFile.Stmt stmt, TypeSystem types) {
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
			// Expand any type invariants
			Formula invariant = expandTypeInvariants(q.getParameters(),types);
			// Add type invariants (if appropriate)
			if (invariant != null) {
				body = new Disjunct(invert(invariant), body);
			}
			// Done
			return new Formula.Quantifier(true, q.getParameters(), body);
		}
		case STMT_exists: {
			Stmt.Quantifier q = (WyalFile.Stmt.Quantifier) stmt;
			// Convert body of quantifier
			Formula body = toFormula(q.getBody(), types);
			// Expand any type invariants
			Formula invariant = expandTypeInvariants(q.getParameters(),types);
			// Add type invariants (if appropriate)
			if (invariant != null) {
				body = new Conjunct(invariant, body);
			}
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
			Type lhs_t = lhs.getReturnType(types);
			if (types.isSubtype(new Type.Int(), lhs_t)) {
				Polynomial lhs_p = toPolynomial(lhs);
				Polynomial rhs_p = toPolynomial(rhs);
				// Force arithmetic equality
				return new Formula.ArithmeticEquality(true, lhs_p, rhs_p);
			} else {
				return new Formula.Equality(true, lhs, rhs);
			}
		}
		case EXPR_neq: {
			Expr.Operator operator = (Expr.Operator) stmt;
			Expr lhs = operator.getOperand(0);
			Expr rhs = operator.getOperand(1);
			Type lhs_t = lhs.getReturnType(types);
			if (types.isSubtype(new Type.Int(), lhs_t)) {
				Polynomial lhs_p = toPolynomial(lhs);
				Polynomial rhs_p = toPolynomial(rhs);
				// Force arithmetic equality
				return new Formula.ArithmeticEquality(false, lhs_p, rhs_p);
			} else {
				return new Formula.Equality(false, lhs, rhs);
			}
		}
		case EXPR_lt: {
			Expr.Operator operator = (Expr.Operator) stmt;
			Polynomial lhs = toPolynomial(operator.getOperand(0));
			Polynomial rhs = toPolynomial(operator.getOperand(1));
			return new Formula.Inequality(true, lhs, rhs);
		}
		case EXPR_lteq: {
			Expr.Operator operator = (Expr.Operator) stmt;
			Polynomial lhs = toPolynomial(operator.getOperand(0));
			Polynomial rhs = toPolynomial(operator.getOperand(1));
			return new Formula.Inequality(false, rhs, lhs);
		}
		case EXPR_gt: {
			Expr.Operator operator = (Expr.Operator) stmt;
			Polynomial lhs = toPolynomial(operator.getOperand(0));
			Polynomial rhs = toPolynomial(operator.getOperand(1));
			return new Formula.Inequality(true, rhs, lhs);
		}
		case EXPR_gteq: {
			Expr.Operator operator = (Expr.Operator) stmt;
			Polynomial lhs = toPolynomial(operator.getOperand(0));
			Polynomial rhs = toPolynomial(operator.getOperand(1));
			return new Formula.Inequality(false, lhs, rhs);
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
			return new Formula.Invoke(true, ivk.getSignatureType(), ivk.getName(), ivk.getArguments());
		}
		default:
			if (stmt instanceof WyalFile.Expr) {
				Expr expr = (WyalFile.Expr) stmt;
				Expr TRUE = new Formula.Truth(new Value.Bool(true));
				return new Formula.Equality(true, expr, TRUE);
			} else {
				throw new IllegalArgumentException("u)nknown statement encountered: " + stmt.getOpcode());
			}
		}
	}

	/**
	 * Convert an array of statements into an array of (equivalent) formulae.
	 *
	 * @param stmts
	 * @return
	 */
	public static Formula[] toFormulae(WyalFile.Stmt[] stmts, TypeSystem types) {
		Formula[] exprs = new Formula[stmts.length];
		for (int i = 0; i != exprs.length; ++i) {
			exprs[i] = toFormula(stmts[i], types);
		}
		return exprs;
	}

	/**
	 * Convert an arithmetic expression into a polynomial. A polynomial is a
	 * structured form of an arithmetic expression which is useful for reasoning
	 * about.
	 *
	 * @param e
	 *            The expression to be converted
	 * @return
	 */
	private static Polynomial toPolynomial(Expr e) {
		if (e instanceof Polynomial) {
			return (Polynomial) e;
		} else {
			Polynomial.Term term = new Polynomial.Term(e);
			return new Polynomial(term);
		}
	}

	/**
	 * For a given sequence of variable declarations expand their type
	 * invariants as appropriate. This expansion is done lazily, in that it
	 * produces invocations to the type invariants themselves. Such invocations
	 * must then be separately expanded (like macros) later on. As an example,
	 * consider this:
	 *
	 * <pre>
	 * type nat is (int x) where x >= 0
	 *
	 * assert:
	 *     forall(nat x):
	 *         x >= 0
	 * </pre>
	 *
	 * The type invariant given for <code>x</code> in the quantifier will be
	 * expanded, to give then body <code>nat(x) ==> x >= 0</code>. The call
	 * <code>nat(x)</code> will later be expanded during theorem proving to
	 * <code>x >= 0</code>. The reason this is done lazily is to properly
	 * support recursive types and their invariants.
	 *
	 * @param declarations
	 * @param types
	 * @return
	 */
	private static Formula expandTypeInvariants(Tuple<VariableDeclaration> declarations, TypeSystem types) {
		Formula result = null;
		for (int i = 0; i != declarations.size(); ++i) {
			VariableDeclaration decl = declarations.getOperand(i);
			Formula invariant = extractTypeInvariant(decl.getType(), new Expr.VariableAccess(decl), types);
			// FIXME: need to perform appropriate variable substitution here?
			if (invariant != null && result == null) {
				result = invariant;
			} else if (invariant != null) {
				result = new Conjunct(result, invariant);
			}
		}
		return result;
	}

	private static int skolem = 0;

	/**
	 * Expand the type invariant associated with a given type (if any). For
	 * example, primitive types have no invariant associated with them. In
	 * contrast, nominal types may have as the following example illustrates:
	 *
	 * <pre>
	 * type nat is (int x) where x >= 0
	 * </pre>
	 *
	 * Here, the resulting invariant produced is <code>nat(x)</code>. Another
	 * interesting example is that for a record:
	 *
	 * <pre>
	 * type Point is ({nat x, nat y} p)
	 * </pre>
	 *
	 * Here, the resulting invariant would be <code>nat(p.x) && nat(p.y)</code>.
	 *
	 * @param type
	 * @param types
	 * @return
	 */
	private static Formula extractTypeInvariant(Type type, Expr root, TypeSystem types) {
		switch(type.getOpcode()) {
		case TYPE_void:
		case TYPE_any:
		case TYPE_null:
		case TYPE_bool:
		case TYPE_int:
			return null; // no invariant
		case TYPE_nom: {
			Type.Nominal nom = (Type.Nominal) type;
			Declaration.Named.Type td = types.resolveAsDeclaredType(nom.getName());
			if(td.getInvariant() == null) {
				return null;
			} else {
				Type parameter = td.getVariableDeclaration().getType();
				Type.Invariant ft = new Type.Invariant(new Tuple<>(parameter));
				return new Formula.Invoke(true, ft, nom.getName(), root);
			}
		}
		case TYPE_rec: {
			Type.Record r = (Type.Record) type;
			VariableDeclaration[] fields = r.getFields();
			Formula inv = null;
			for(int i=0;i!=fields.length;++i) {
				VariableDeclaration fieldDecl = (VariableDeclaration) fields[i];
				Expr.RecordAccess access = new Expr.RecordAccess(root, fieldDecl.getVariableName());
				Formula fieldInv = extractTypeInvariant(fieldDecl.getType(), access, types);
				if(fieldInv != null) {
					if(inv == null) {
						inv = fieldInv;
					} else {
						inv = and(inv,fieldInv);
					}
				}
			}
			return inv;
		}
		case TYPE_arr: {
			Type.Array t = (Type.Array) type;
			Formula inv = extractTypeInvariant(t.getElement(), root, types);
			if (inv == null) {
				return null;
			} else {
				// forall i.(0 <= i && i <|root|) ==> inv
				WyalFile.VariableDeclaration var = new WyalFile.VariableDeclaration(new Type.Int(),
						new Identifier("i:" + skolem++));
				Polynomial va = toPolynomial(new Expr.VariableAccess(var));
				Polynomial zero = toPolynomial(0);
				Polynomial len = toPolynomial(new Expr.Operator(Opcode.EXPR_arrlen, root));
				Formula gt = greaterOrEqual(va, zero);
				Formula lt = lessThan(va, len);
				return new Quantifier(true, var, implies(and(gt, lt), inv));
			}
		}
		case TYPE_or: {
			Type.Union t = (Type.Union) type;
			Formula result = null;
			for(int i=0;i!=t.size();++i) {
				Formula inv = extractTypeInvariant(t.getOperand(i),root,types);
				if(inv != null && result == null) {
					result = inv;
				} else if(inv != null) {
					result = new Disjunct(result,inv);
				}
			}
			return result;
		}
		case TYPE_and: {
			Type.Intersection t = (Type.Intersection) type;
			Formula result = null;
			for(int i=0;i!=t.size();++i) {
				Formula inv = extractTypeInvariant(t.getOperand(i),root,types);
				if(inv != null && result == null) {
					result = inv;
				} else if(inv != null) {
					result = new Conjunct(result,inv);
				}
			}
			return result;
		}
		case TYPE_not: {
			Type.Negation t = (Type.Negation) type;
			Formula inv = extractTypeInvariant(t.getElement(),root,types);
			if(inv == null) {
				return null;
			} else {
				return invert(inv);
			}
		}
		case TYPE_ref:
		case TYPE_fun:
		case TYPE_macro:
		default:
			throw new IllegalArgumentException("invalid type opcode: " + type.getOpcode());
		}
	}

	private static Formula lessThan(Polynomial lhs, Polynomial rhs) {
		return new Formula.Inequality(true, lhs, rhs);
	}

	private static Formula greaterOrEqual(Polynomial lhs, Polynomial rhs) {
		return new Formula.Inequality(false, lhs, rhs);
	}

	private static Formula implies(Formula lhs, Formula rhs) {
		return new Formula.Disjunct(invert(lhs),rhs);
	}

	private static Formula and(Formula lhs, Formula rhs) {
		return new Formula.Conjunct(lhs,rhs);
	}

	public static Polynomial toPolynomial(int value) {
		return new Polynomial(new Polynomial.Term(BigInteger.valueOf(value)));
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
		case EXPR_lt:
		case EXPR_gteq: {
			Inequality e = (Inequality) f;
			return new Inequality(!e.getSign(), e.getOperand(0), e.getOperand(1));
		}
		case EXPR_invoke: {
			Invoke e = (Invoke) f;
			return new Formula.Invoke(!e.getSign(),e.getSignatureType(),e.getName(),e.getArguments());
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

	/**
	 * Recursively simplify a given formula by applying the "standard"
	 * simplifications for each kind. If no simplification is performed, this
	 * returns the original object in tact.
	 *
	 * @param f
	 * @return
	 */
	public static Formula simplify(Formula f) {
		switch (f.getOpcode()) {
		case EXPR_const: {
			return f;
		}
		case EXPR_and: {
			return simplify((Formula.Conjunct) f);
		}
		case EXPR_or: {
			return simplify((Formula.Disjunct) f);
		}
		case EXPR_exists:
		case EXPR_forall: {
			return simplify((Formula.Quantifier) f);
		}
		case EXPR_eq:
		case EXPR_neq: {
			if (f instanceof ArithmeticEquality) {
				return simplify((Formula.ArithmeticEquality) f);
			} else {
				return simplify((Formula.Equality) f);
			}
		}
		case EXPR_lt:
		case EXPR_gteq: {
			return simplify((Formula.Inequality) f);
		}
		case EXPR_invoke: {
			return simplify((Formula.Invoke) f);
		}
		default:
			throw new IllegalArgumentException("invalid formula opcode: " + f.getOpcode());
		}
	}

	/**
	 * Apply a range of simplifications to a given conjunct:
	 *
	 * <ol>
	 * <li><b>Eliminates boolean constants</b>. Conjuncts containing
	 * <code>false</code> are reduced to <code>false</code>. In contrast, any
	 * occurrences of <code>true</code> are simply removed.</li>
	 * <li><b>Flattens nested conjuncts</b>. All nested conjuncts are
	 * recursively flattened into a single conjunct. For example,
	 * <code> (x && (y && z))</code> is flattened to
	 * <code>(x && y && z)</code>.</li>
	 * <li><b>Eliminates singleton conjuncts</b>. A conjunct containing a single
	 * (non-conjunct) child is reduced to that child.</li>
	 * </ol>
	 *
	 * The implementation attempts to eliminate dynamic memory allocation in the
	 * case that no simplification is applied. Furthermore, this function is
	 * <b>recursive</b>. That is, it will simplify all children of this formula.
	 *
	 * @author David J. Pearce
	 *
	 */
	public static Formula simplify(Conjunct conjunct) {
		Formula[] children = conjunct.getOperands();
		Formula[] nChildren = children;
		// Flatten nested conjuncts
		nChildren = flattenNestedConjuncts(nChildren);
		// Simplify children
		nChildren = simplify(nChildren);
		// Eliminate truths
		nChildren = eliminateConstants(true, nChildren);
		// Ensure sorted and unique
		nChildren = sortAndRemoveDuplicates(nChildren);
		// And, finally...
		if (nChildren.length == 0) {
			// Return true here since the only way it's possible to get here
			// is if the conjunct contained only truths at the end.
			return new Truth(true);
		} else if (nChildren.length == 1) {
			return nChildren[0];
		} else if (children == nChildren) {
			// nothing has changed
			return conjunct;
		} else {
			return new Conjunct(nChildren);
		}
	}

	/**
	 * Apply a range of simplifications to a given disjunct:
	 *
	 * <ol>
	 * <li><b>Eliminates boolean constants</b>. Disjuncts containing
	 * <code>true</code> are reduced to <code>true</code>. In contrast, any
	 * occurrences of <code>false</code> are simply removed.</li>
	 * <li><b>Flattens nested disjuncts</b>. All nested disjuncts are
	 * recursively flattened into a single disjunct. For example,
	 * <code> (x || (y || z))</code> is flattened to
	 * <code>(x || y || z)</code>.</li>
	 * <li><b>Eliminates singleton disjuncts</b>. A disjunct containing a single
	 * (non-disjunct) child is reduced to that child.</li>
	 * </ol>
	 *
	 * The implementation attempts to eliminate dynamic memory allocation in the
	 * case that no simplification is applied. Furthermore, this function is
	 * <b>not recursive</b>. Furthermore, this function is <b>recursive</b>.
	 * That is, it will simplify all children of this formula.
	 *
	 */
	public static Formula simplify(Disjunct disjunct) {
		Formula[] children = disjunct.getOperands();
		Formula[] nChildren = children;
		// Flatten nested disjuncts
		nChildren = flattenNestedDisjuncts(nChildren);
		// Simplify children
		nChildren = simplify(nChildren);
		// Eliminate truths
		nChildren = eliminateConstants(false, nChildren);
		// Ensure sorted and unique
		nChildren = sortAndRemoveDuplicates(nChildren);
		// And, finally...
		if (nChildren.length == 0) {
			// Return false here since the only way it's possible to get
			// here is if the disjunct contained only falsehoods at the end.
			return new Truth(false);
		} else if (nChildren.length == 1) {
			return nChildren[0];
		} else if (children == nChildren) {
			// nothing has changed
			return disjunct;
		} else {
			return new Disjunct(nChildren);
		}
	}

	private static Formula[] simplify(Formula[] children) {
		Formula[] nChildren = children;
		for (int i = 0; i != nChildren.length; ++i) {
			Formula child = children[i];
			Formula nChild = simplify(child);
			if (child != nChild && children != nChildren) {
				nChildren = Arrays.copyOf(children, children.length);
			}
			nChildren[i] = nChild;
		}
		return nChildren;
	}

	/**
	 * Simplify a quantified formula. In essence, if the body is a truth value
	 * then that is returned. For example, <code>forall x.true</code> is simply
	 * <code>true</code>.
	 *
	 * @param quantifier
	 * @return
	 */
	public static Formula simplify(Quantifier quantifier) {
		Formula body = quantifier.getBody();
		Formula nBody = simplify(body);
		if (nBody instanceof Truth) {
			return nBody;
		} else if (nBody != body) {
			return new Quantifier(quantifier.getSign(), quantifier.getParameters(), nBody);
		} else {
			return quantifier;
		}
	}

	/**
	 * Simplify an inequality by canceling, evaluating and/or balancing:
	 * <ol>
	 * <li><b>Canceling</b> is the process of removing commons terms from both
	 * sides. For example, in <code>x+y < x</code> we can cancel <code>x</code>
	 * to give <code>y < 0</code>.</li>
	 * <li><b>Evaluating</b> is the process of reducing a constant inequality to
	 * either <code>true</code> or <code>false</code>. For example,
	 * <code>0 < 1</code> reduces to <code>true</code> whilst
	 * <code>1 >= 0</code> reduces to <code>false</code>.</li>
	 * <li><b>Balancing</b> is the process of eliminating negative terms and
	 * factorising. For example, <code>-x < 1</code> is balanced to
	 * <code>0 < 1 + x</code>. Likewise, <code>2*x < 6*y</code> is factorised to
	 * <code>x < 3*y</code>.</li>
	 * </ol>
	 *
	 * @param ieq
	 * @return
	 */
	public static Formula simplify(Inequality ieq) {
		Polynomial lhs = simplify(ieq.getOperand(0));
		Polynomial rhs = simplify(ieq.getOperand(1));
		Pair<Polynomial, Polynomial> bs = normaliseBounds(lhs, rhs);
		lhs = bs.getFirst();
		rhs = bs.getSecond();
		//
		if (lhs.isConstant() && rhs.isConstant()) {
			return evaluateInequality(ieq.getOpcode(), lhs.toConstant(), rhs.toConstant());
		} else if (lhs.equals(rhs)) {
			return new Formula.Truth(false);
		} else {
			// FIXME: need to ensure identical object returned if no
			// simplification applied.
			return new Inequality(ieq.getSign(), bs.getFirst(), bs.getSecond());
		}
	}

	/**
	 * Simplify an arithmetic equality by canceling, evaluating and/or
	 * balancing:
	 * <ol>
	 * <li><b>Canceling</b> is the process of removing commons terms from both
	 * sides. For example, in <code>x+y == x</code> we can cancel <code>x</code>
	 * to give <code>y == 0</code>.</li>
	 * <li><b>Evaluating</b> is the process of reducing a constant inequality to
	 * either <code>true</code> or <code>false</code>. For example,
	 * <code>0 == 0</code> reduces to <code>true</code> whilst
	 * <code>1 == 0</code> reduces to <code>false</code>.</li>
	 * <li><b>Balancing</b> is the process of eliminating negative terms and
	 * factorising. For example, <code>-x == 1</code> is balanced to
	 * <code>0 == 1 + x</code>. Likewise, <code>2*x == 6*y</code> is factorised
	 * to <code>x == 3*y</code>.</li>
	 * </ol>
	 *
	 * @param ieq
	 * @return
	 */
	public static Formula simplify(ArithmeticEquality eq) {
		Polynomial lhs = simplify(eq.getOperand(0));
		Polynomial rhs = simplify(eq.getOperand(1));
		Pair<Polynomial, Polynomial> bs = normaliseBounds(lhs, rhs);
		lhs = bs.getFirst();
		rhs = bs.getSecond();
		if (lhs.isConstant() && rhs.isConstant()) {
			Value lhs_v = lhs.toConstant();
			Value rhs_v = rhs.toConstant();
			return evaluateEquality(eq.getOpcode(), lhs_v, rhs_v);
		} else if (lhs.equals(rhs)) {
			return new Formula.Truth(eq.getSign());
		} else if (eq.getSign()) {
			// FIXME: need to ensure identical object returned if no
			// simplification applied.
			return new ArithmeticEquality(true, lhs, rhs);
		} else {
			// For an arithmetic equality of the form x != y, we return a
			// disjunction of the form (x < y) || (x > y). This is not
			// necessarily the most efficient thing to do. However, for our
			// purposes, this works well enough for now.
			Inequality lt = new Inequality(true, lhs, rhs);
			Inequality gt = new Inequality(true, rhs, lhs);
			return new Formula.Disjunct(lt, gt);
		}
	}

	/**
	 * Simplify a non-arithmetic equality by attempting to evaluate it. For
	 * example, <code>true == false</code> reduces to <code>false</code>. In the
	 * case that neither side is a constant, then the original equality is
	 * returned.
	 *
	 * @param eq
	 * @return
	 */
	public static Formula simplify(Equality eq) {
		Expr lhs = simplify(eq.getOperand(0));
		Expr rhs = simplify(eq.getOperand(1));
		if (lhs instanceof Expr.Constant && rhs instanceof Expr.Constant) {
			Value lhs_v = ((Expr.Constant) lhs).getValue();
			Value rhs_v = ((Expr.Constant) rhs).getValue();
			return evaluateEquality(eq.getOpcode(), lhs_v, rhs_v);
		} else if (lhs.equals(rhs)) {
			return new Formula.Truth(eq.getSign());
		} else {
			// FIXME: need to ensure new object returned if simplification
			// applied.
			return eq;
		}
	}

	public static Formula simplify(Invoke ivk) {
		Tuple<Expr> args = ivk.getArguments();
		Tuple<Expr> nArgs = simplify(args);
		if(args == nArgs) {
			return ivk;
		} else {
			return new Invoke(ivk.getSign(),ivk.getSignatureType(),ivk.getName(),nArgs);
		}
	}

	private static Tuple<Expr> simplify(Tuple<Expr> tuple) {
		Expr[] children = tuple.getOperands();
		Expr[] nChildren = simplify(children);
		if(children == nChildren) {
			return tuple;
		} else {
			return new Tuple<>(nChildren);
		}
	}

	private static Expr[] simplify(Expr[] children) {
		Expr[] nChildren = children;
		for (int i = 0; i != children.length; ++i) {
			Expr child = children[i];
			Expr nChild = simplify(child);
			if (child != nChild && children == nChildren) {
				nChildren = Arrays.copyOf(children, children.length);
			}
			nChildren[i] = nChild;
		}
		return nChildren;
	}

	/**
	 * Convert an arbitrary expression to an atom.
	 *
	 * @param e
	 * @return
	 */
	private static Expr simplify(Expr e) {
		switch (e.getOpcode()) {
		case EXPR_var:
			return e;
		case EXPR_const:
			return simplify((Expr.Constant) e);
		case EXPR_invoke:
			return simplify((Expr.Invoke) e);
		case EXPR_arridx:
			return simplifyArrayIndex((Expr.Operator) e);
		case EXPR_arrlen:
		case EXPR_arrinit:
		case EXPR_arrgen:
		case EXPR_rem: // temporary for now
			return simplifyNonArithmetic((Expr.Operator) e);
		case EXPR_neg:
		case EXPR_add:
		case EXPR_mul:
		case EXPR_sub: {
			return simplifyArithmetic((Expr.Operator) e);
		}
		case EXPR_recfield:
			return simplify((Expr.RecordAccess) e);
		default:
			throw new IllegalArgumentException("cannot convert expression to atom: " + e.getOpcode());
		}
	}

	private static Expr simplify(Expr.Constant e) {
		Value val = e.getValue();
		if (val instanceof Value.Int) {
			Value.Int c = (Value.Int) val;
			return new Polynomial(new Polynomial.Term(c));
		} else {
			Value.Bool b = (Value.Bool) val;
			return new Formula.Truth(b.get());
		}
	}

	private static Expr simplify(Expr.RecordAccess e) {
		Expr source = e.getSource();
		Expr nSource = simplify(source);
		if (source == nSource) {
			return e;
		} else {
			return new Expr.RecordAccess(source, e.getField());
		}
	}

	private static Expr simplify(Expr.Invoke ivk) {
		Tuple<Expr> args = ivk.getArguments();
		Tuple<Expr> nArgs = simplify(args);
		if(args == nArgs) {
			return ivk;
		} else {
			return new Expr.Invoke(ivk.getSignatureType(),ivk.getName(),nArgs);
		}
	}

	private static Expr simplifyArrayIndex(Expr.Operator e) {
		Expr[] children = e.getOperands();
		Expr[] nChildren = simplify(children);
		Expr source = nChildren[0];
		Expr index = nChildren[1];
		if (source instanceof Expr.Operator && index instanceof Expr.Polynomial) {
			// We may have a constant index value into a constant array
			Expr.Operator arr = (Expr.Operator) source;
			Expr.Polynomial idx = (Expr.Polynomial) index;
			if (arr.getOpcode() == Opcode.EXPR_arrinit && idx.isConstant()) {
				// We definitely have a constant index value into a constant
				// array
				BigInteger i = ((Value.Int) idx.toConstant()).get();
				if (i.compareTo(BigInteger.ZERO) >= 0 && i.compareTo(BigInteger.valueOf(arr.size())) < 0) {
					// The constant index is within bounds
					return arr.getOperand(i.intValue());
				}
			}
		}
		// If we get here, then no simplification of the array access expression
		// was possible.
		if (children == nChildren) {
			return e;
		} else {
			return e.clone(nChildren);
		}
	}

	private static Expr simplifyNonArithmetic(Expr.Operator e) {
		Expr[] children = e.getOperands();
		Expr[] nChildren = simplify(children);

		if (nChildren == children) {
			return e;
		} else {
			// FIXME: there are further simplifications that can be performed
			// here. For example, taking the field of a constant record;
			// likewise, taking a constant index into a constant array. Although
			// unlikely, they can arise through the use of e.g. configuration
			// constants, etc.
			return e.clone(nChildren);
		}
	}

	private static Expr simplifyArithmetic(Expr.Operator e) {
		if (e instanceof Polynomial) {
			return simplify((Polynomial) e);
		} else {
			Expr[] children = e.getOperands();
			Polynomial result = toPolynomial(simplify(children[0]));
			switch (e.getOpcode()) {
			case EXPR_add: {
				for (int i = 1; i != children.length; ++i) {
					result = result.add(toPolynomial(simplify(children[i])));
				}
				break;
			}
			case EXPR_sub: {
				for (int i = 1; i != children.length; ++i) {
					result = result.subtract(toPolynomial(simplify(children[i])));
				}
				break;
			}
			case EXPR_mul: {
				for (int i = 1; i != children.length; ++i) {
					result = result.multiply(toPolynomial(simplify(children[i])));
				}
				break;
			}
			case EXPR_neg: {
				result = result.negate();
				break;
			}
			default:
				throw new IllegalArgumentException("Unknown arithmetic opcode encountered");
			}
			return result;
		}
	}

	/**
	 * Simplify a polynomial. This ensures that all terms are simplified, and
	 * that there are no nested polynomials.
	 *
	 * @param p
	 * @return
	 */
	private static Polynomial simplify(Polynomial p) {
		Polynomial.Term[] children = p.getOperands();
		Expr[] nChildren = children;
		for (int i = 0; i != p.size(); ++i) {
			Polynomial.Term child = children[i];
			Expr nChild = simplify(child);
			if (nChild instanceof Polynomial && nChildren instanceof Polynomial.Term[]) {
				// At this point, we are now committed to constructing a new
				// polynomial. For now, we continue simplifying the children as
				// before. However, we downgrade the enclosing array to hold
				// only expressions in order that it can hold both terms and
				// polynomials.
				Expr[] oChildren = nChildren;
				nChildren = new Expr[nChildren.length];
				System.arraycopy(oChildren, 0, nChildren, 0, nChildren.length);
			} else if (child != nChild && children == nChildren) {
				nChildren = Arrays.copyOf(children, children.length);
			}
			nChildren[i] = nChild;
		}
		//
		if (children == nChildren) {
			// In this case, nothing changed anyway.
			return p;
		} else if (nChildren instanceof Polynomial.Term[]) {
			// FIXME: we need to do some other kinds of simplification here. For
			// example, coalescing terms.
			return Polynomials.toNormalForm((Polynomial.Term[]) nChildren);
		} else {
			Polynomial result = new Polynomial(BigInteger.ZERO);
			for (int i = 0; i != nChildren.length; ++i) {
				Expr nChild = nChildren[i];
				if (nChild instanceof Polynomial) {
					result = result.add((Polynomial) nChild);
				} else {
					result = result.add((Polynomial.Term) nChild);
				}
			}
			return result;
		}
	}

	private static Expr simplify(Polynomial.Term p) {
		final Expr[] children = p.getAtoms();
		Expr[] nChildren = children;
		int numPolynomials = 0;

		for (int i = 0; i != children.length; ++i) {
			Expr child = children[i];
			Expr nChild = simplify(child);
			if (nChild instanceof Polynomial) {
				numPolynomials = numPolynomials + 1;
			}
			if (child != nChild && children == nChildren) {
				nChildren = Arrays.copyOf(children, children.length);
			}
			nChildren[i] = nChild;
		}

		if (numPolynomials == 0) {
			// This is the easy case. No nested polynomials were found.
			if (nChildren == children) {
				return p;
			} else {
				return new Polynomial.Term(p.getCoefficient(), nChildren);
			}
		} else {
			// This is the harder case. At least one nested polynomial was
			// found. For now, we don't make much effort to be efficient.
			Polynomial result = new Polynomial(new Polynomial.Term(p.getCoefficient()));
			for (int i = 0; i != nChildren.length; ++i) {
				Expr nChild = nChildren[i];
				if (nChild instanceof Polynomial) {
					result = result.multiply((Polynomial) nChild);
				} else {
					Polynomial.Term term = new Polynomial.Term(nChild);
					result = result.multiply(term);
				}
			}

			return result;
		}
	}

	/**
	 * Close over two inequalities. This may or may not produce a new inequality
	 * as a result. For example, closing over <code>3 < x</code> and
	 * <code>x < y</code> gives <code>3 < y</code>. Observe that, for this
	 * operation to succeed, there must exist a term common to both
	 * inequalities. In the case that multiple candidate terms exist, then the
	 * lexiographically least is selected.
	 *
	 * <b>NOTE:</b> this currently assumes that the inequalities are balanced.
	 *
	 * @param ith
	 * @param jth
	 * @return
	 */
	public static Formula closeOver(Formula.Inequality ith, Formula.Inequality jth) {
		Polynomial ithLowerBound = extractBound(false, ith);
		Polynomial ithUpperBound = extractBound(true, ith);
		Polynomial jthLowerBound = extractBound(false, jth);
		Polynomial jthUpperBound = extractBound(true, jth);

		Pair<Polynomial.Term, Polynomial.Term> lCandidate = selectCandidateTerm(ithLowerBound, jthUpperBound);
		Pair<Polynomial.Term, Polynomial.Term> rCandidate = selectCandidateTerm(jthLowerBound, ithUpperBound);
		Polynomial lhs;
		Polynomial rhs;
		if (lCandidate != null) {
			// FIXME: should be selecting the least candidate
			lhs = rearrangeForLowerBound(ithLowerBound, ithUpperBound, lCandidate.getFirst());
			rhs = rearrangeForUpperBound(jthLowerBound, jthUpperBound, lCandidate.getSecond());
		} else if (rCandidate != null) {
			lhs = rearrangeForLowerBound(ithLowerBound, ithUpperBound, rCandidate.getSecond());
			rhs = rearrangeForUpperBound(jthLowerBound, jthUpperBound, rCandidate.getFirst());
		} else {
			return null;
		}
		if (ith.getSign() && jth.getSign()) {
			// Result is *very* strict as had something like ... < x < ...
			lhs = lhs.add(new Polynomial.Term(BigInteger.ONE));
			return simplify(new Formula.Inequality(true, lhs, rhs));
		} else if (ith.getSign() || jth.getSign()) {
			// Result is strict as had something like ... <= x < ...
			return simplify(new Formula.Inequality(true, lhs, rhs));
		} else {
			// Result is not-strict as had something like ... <= x <= ...
			return simplify(new Formula.Inequality(false, lhs, rhs));
		}
	}

	/**
	 * Extract a given bound from the inequality. Here, true is upper and false
	 * is lower.
	 *
	 * @param sign
	 * @param inequality
	 * @return
	 */
	private static Polynomial extractBound(boolean sign, Formula.Inequality inequality) {
		int i;
		switch (inequality.getOpcode()) {
		case EXPR_lt:
			i = sign ? 1 : 0;
			break;
		case EXPR_gteq:
			i = sign ? 0 : 1;
			break;
		default:
			throw new IllegalArgumentException("Invalid inequality");
		}
		return (Polynomial) inequality.getOperand(i);
	}

	/**
	 * <p>
	 * Determine a suitable term (if one exists) for rearranging the two
	 * inequalities. A candidate term must be common to both and involve at
	 * least one variable, and should appear on opposite sides of the
	 * inequalities. The selected candidate then has the lowest ordering of any
	 * possible term. For example, consider these two options:
	 * </p>
	 *
	 * <pre>
	 * x < y + z
	 * x + y > z
	 * </pre>
	 *
	 * <p>
	 * For these two equations, the candidate terms are <code>x</code> and
	 * <code>z</code>. Since <code>y</code> is an upper bound on both, it is not
	 * considered. Then, <code>x</code> is selected as the actual term for
	 * rearranging since it is lexiographically lower than <code>z</code>.
	 * </p>
	 *
	 * @param ith
	 * @param jth
	 * @return
	 */
	private static Pair<Polynomial.Term, Polynomial.Term> selectCandidateTerm(Polynomial lower, Polynomial upper) {
		for (int i = 0; i != lower.size(); ++i) {
			Polynomial.Term ith = lower.getOperand(i);
			Expr[] ithAtoms = ith.getAtoms();
			if (ithAtoms.length > 0) {
				for (int j = 0; j != upper.size(); ++j) {
					Polynomial.Term jth = upper.getOperand(j);
					Expr[] jthAtoms = jth.getAtoms();
					if (Arrays.equals(ithAtoms, jthAtoms)) {
						// FIXME: we should be selecting the lexiographically
						// least candidate here.
						return new Pair<>(ith, jth);
					}
				}
			}
		}
		//
		return null;
	}

	public static Pair<Expr, Expr> rearrangeForSubstitution(Formula.Equality f) {
		Expr candidate;
		Expr bound;
		if (f instanceof Formula.ArithmeticEquality) {
			// Arithmetic equalities are a special case because we can actually
			// rearrange them.
			Formula.ArithmeticEquality e = (Formula.ArithmeticEquality) f;
			Polynomial lhs = e.getOperand(0);
			Polynomial rhs = e.getOperand(1);
			Polynomial.Term lhsCandidate = selectCandidateForSubstitution(lhs,rhs);
			Polynomial.Term rhsCandidate = selectCandidateForSubstitution(rhs,lhs);
			if (lhsCandidate != null && rhsCandidate != null) {
				if (lhsCandidate.compareTo(rhsCandidate) < 0) {
					candidate = extractCandidate(lhsCandidate);
					bound = rhs.subtract(lhs.subtract(lhsCandidate));
				} else {
					candidate = extractCandidate(rhsCandidate);
					bound = lhs.subtract(rhs.subtract(rhsCandidate));
				}
			} else if (lhsCandidate != null) {
				candidate = extractCandidate(lhsCandidate);
				bound = rhs.subtract(lhs.subtract(lhsCandidate));
			} else if (rhsCandidate != null) {
				candidate = extractCandidate(rhsCandidate);
				bound = lhs.subtract(rhs.subtract(rhsCandidate));
			} else {
				return null;
			}
		} else {
			// For non-arithmetic equalities, we can't rearrange them.
			// Therefore, there are relatively few options.
			Expr lhs = f.getOperand(0);
			Expr rhs = f.getOperand(1);
			//
			if (lhs.compareTo(rhs) < 0) {
				candidate = lhs;
				bound = rhs;
			} else {
				candidate = rhs;
				bound = lhs;
			}
		}

		System.out.print("FOUND SUBSTITUTION: ");
		AutomatedTheoremProver.print(candidate);
		System.out.print(" ==> ");
		AutomatedTheoremProver.println(bound);
		return new Pair<>(candidate, bound);
	}

	private static Expr extractCandidate(Polynomial.Term term) {
		return term.getAtoms()[0];
	}

	/**
	 * Examine all terms in a polynomial to see whether any is a candidate for
	 * substitution or not. If one or more are found, then the least candidate
	 * is returned.
	 *
	 * @param p
	 * @return
	 */
	private static Polynomial.Term selectCandidateForSubstitution(Polynomial p, Polynomial other) {
		Expr candidateAtom = null;
		Polynomial.Term candidate = null;
		for (int i = 0; i != p.size(); ++i) {
			Polynomial.Term term = p.getOperand(i);
			Expr[] atoms = term.getAtoms();
			if (term.getAtoms().length == 1) {
				Expr atom = atoms[0];
				// FIXME: the problem here is thatthe given polynomial is not
				// taking into account the other side of the equation, which may
				// contain a recursive reference.
				if ((candidate == null || atom.compareTo(candidateAtom) < 0) && !recursive(atom, i, p) && !recursive(atom, -1, other)) {
					candidate = term;
					candidateAtom = atom;
				}
			}
		}
		return candidate;
	}

	private static boolean recursive(Expr atom, int i, Polynomial p) {
		for (int j = 0; j != p.size(); ++j) {
			if (i != j) {
				Polynomial.Term term = p.getOperand(j);
				if (isParentOf(term,atom)) {
					return true;
				}
			}
		}
		return false;
	}

	private static boolean isParentOf(Expr parent, Expr child) {
		if (parent.equals(child)) {
			return true;
		} else {
			for (int i = 0; i != parent.size(); ++i) {
				SyntacticItem pChild = parent.getOperand(i);
				if (pChild instanceof Expr && isParentOf((Expr) pChild, child)) {
					return true;
				}
			}
			return false;
		}
	}

	/**
	 * Rearrange a given equation such that the given term appears on the
	 * right-hand side, and everything else is moved on to the left side. For
	 * example, consider rearranging these for <code>x</code>:
	 *
	 * <pre>
	 * 1 < x + y
	 * </pre>
	 *
	 * The resulting polynomial represents the "left-hand side" which (in this
	 * case) is 1-y. Thus, the rearranged inequality would be 1 - y < x.
	 *
	 * @param lhs
	 *            The "left-hand side" of the equation.
	 * @param rhs
	 *            The "right-hand side" of the equation.
	 * @param term
	 *            the given term being rearranged for.
	 */
	private static Polynomial rearrangeForLowerBound(Polynomial lhs, Polynomial rhs, Polynomial.Term term) {
		rhs = rhs.subtract(term);
		return lhs.add(rhs.negate());
	}

	/**
	 * Rearrange a given equation such that the given term appears on the
	 * left-hand side, and everything else is moved on to the right side. For
	 * example, consider rearranging these for <code>x</code>:
	 *
	 * <pre>
	 * x + y < 1
	 * </pre>
	 *
	 * The resulting polynomial represents the "right-hand side" which (in this
	 * case) is 1-y. Thus, the rearranged inequality would be x < 1 - y.
	 *
	 * @param lhs
	 *            The "left-hand side" of the equation.
	 * @param rhs
	 *            The "right-hand side" of the equation.
	 * @param term
	 *            the given term being rearranged for.
	 */
	private static Polynomial rearrangeForUpperBound(Polynomial lhs, Polynomial rhs, Polynomial.Term term) {
		lhs = lhs.subtract(term);
		return rhs.add(lhs.negate());
	}

	/**
	 * <p>
	 * Substitute for a given variable within a given syntactic item.
	 * Specifically, this replaces all instances of VariableAccess which match
	 * the given declaration. Observe that the substitution is performed
	 * verbatim and (for example) without simplifying the underlying item.
	 * </p>
	 * <p>
	 * This function preserves the aliasing structure of the original item up to
	 * the substitution itself. Furthermore, if no substitution was performed
	 * then the original item is returned as is.
	 * </p>
	 *
	 * @param to
	 * @param item
	 * @return
	 */
	public static <T extends SyntacticItem> SyntacticItem substitute(T from, T to,
			SyntacticItem item) {
		// FIXME: this function is broken because it should not be using
		// identifiers for substitution. Instead, is should be using variable
		// declarations.
		if (item.equals(from)) {
			// Yes, we made a substitution!
			return to;
		} else {
			// No immediate substitution possible. Instead, recursively traverse
			// term looking for substitution.
			SyntacticItem[] children = item.getOperands();
			SyntacticItem[] nChildren = children;
			for (int i = 0; i != children.length; ++i) {
				SyntacticItem child = children[i];
				SyntacticItem nChild = substitute(from, to, child);
				if (child != nChild && nChildren == children) {
					// Clone the new children array to avoid interfering with
					// original item.
					nChildren = Arrays.copyOf(children, children.length);
				}
				nChildren[i] = nChild;
			}
			if (nChildren == children) {
				// No children were updated, hence simply return the original
				// item.
				return item;
			} else {
				// At least one child was changed, therefore clone the original
				// item with the new children.
				return item.clone(nChildren);
			}
		}
	}

	/**
	 * Recursively remove nested conjuncts. If no nested conjuncts are
	 * encountered, then the same array is returned. Otherwise, a new array
	 * containing all elements from both is returned. For example
	 * <code>[x, y && z]</code> is returned as <code>[x,y,z]</code>.
	 *
	 *
	 * @param children
	 * @return
	 */
	private static Formula[] flattenNestedConjuncts(Formula[] children) {
		return flattenNestedClauses(true, children);
	}

	/**
	 * Recursively remove nested disjuncts. If no nested disjuncts are
	 * encountered, then the same array is returned. Otherwise, a new array
	 * containing all elements from both is returned. For example
	 * <code>[x, y && z]</code> is returned as <code>[x,y,z]</code>.
	 *
	 *
	 * @param children
	 * @return
	 */
	private static Formula[] flattenNestedDisjuncts(Formula[] children) {
		return flattenNestedClauses(false, children);
	}

	private static Formula[] flattenNestedClauses(boolean sign, Formula[] children) {
		int count = nestedCount(sign, children);
		if (count == children.length) {
			// In this case, there are no nested expressions to include.
			// Therefore, we return the array as is without modification.
			return children;
		} else {
			// Yes, we have at least one nested expression to handle. This means
			// we are definitely returning a new array.
			Formula[] nChildren = new Formula[count];
			nestedCopy(sign, children, nChildren, 0);
			return nChildren;
		}
	}

	/**
	 * Count the total number of elements in this array which are not conjuncts.
	 * This recursively includes nested conjuncts in this count. For example,
	 * <code>[x, y && z]</code> returns a count of <code>3</code>.
	 *
	 * @param children
	 * @return
	 */
	private static int nestedCount(boolean flag, Formula[] children) {
		int count = 0;
		for (int i = 0; i != children.length; ++i) {
			Expr child = children[i];
			if (flag && child.getOpcode() == Opcode.EXPR_and) {
				Formula.Conjunct conjunct = (Formula.Conjunct) child;
				count += nestedCount(flag, conjunct.getOperands());
			} else if (!flag && child.getOpcode() == Opcode.EXPR_or) {
				Formula.Disjunct disjunct = (Formula.Disjunct) child;
				count += nestedCount(flag, disjunct.getOperands());
			} else {
				count = count + 1;
			}
		}
		return count;
	}

	/**
	 * Copy non-conjunct expressions from one array to another. This will
	 * recursively copy the children of conjunct expressions as well.
	 *
	 * @param from
	 *            The array to be copied from.
	 * @param to
	 *            The array to which non-conjuncts are copied.
	 * @param start
	 *            The starting point in the destination array into which
	 *            elements are copied. The underlying assumption is that the
	 *            destination array is always big enough to hold all items to be
	 *            copied.
	 * @return The total number of items copied. This is necessary so that
	 *         recursive calls can determine how much of the destination array
	 *         is now occupied.
	 */
	private static int nestedCopy(boolean flag, Formula[] from, Formula[] to, int start) {
		int j = start;
		for (int i = 0; i != from.length; ++i) {
			Expr child = from[i];
			if (flag && child.getOpcode() == Opcode.EXPR_and) {
				Formula.Conjunct conjunct = (Formula.Conjunct) child;
				j += nestedCopy(flag, conjunct.getOperands(), to, j);
			} else if (!flag && child.getOpcode() == Opcode.EXPR_or) {
				Formula.Disjunct disjunct = (Formula.Disjunct) child;
				j += nestedCopy(flag, disjunct.getOperands(), to, j);
			} else {
				to[j++] = from[i];
			}
		}
		return j - start;
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
	private static Formula[] eliminateConstants(boolean sign, Formula[] children) {
		// Count number of constants
		int numConstants = 0;
		for (int i = 0; i != children.length; ++i) {
			Formula child = children[i];
			if (children[i] instanceof Formula.Truth) {
				Formula.Truth c = (Formula.Truth) child;
				// The following is safe only because we assume the expression
				// tree is well-typed.
				if (c.holds() == sign) {
					numConstants++;
				} else {
					// A conjunct containing sign is sign
					return new Formula[] { c };
				}
			}
		}
		if (numConstants == 0) {
			return children;
		} else {
			//
			Formula[] nChildren = new Formula[children.length - numConstants];
			for (int i = 0, j = 0; i != children.length; ++i) {
				Formula child = children[i];
				if (child instanceof Expr.Constant) {
					// ignore
				} else {
					nChildren[j++] = child;
				}
			}
			return nChildren;
		}
	}

	/**
	 * Sort and remove duplicate expressions from the given array. The concept
	 * of a duplicate expression is based solely on the index of that expression
	 * in the contained syntactic heap. That is, two expressions with the same
	 * index are considered duplicates. Likewise, sorting is conducted based on
	 * heap index, with those with lower indices coming earlier in the resulting
	 * array.
	 *
	 * @param children
	 * @return
	 */
	private static <T extends SyntacticItem> T[] sortAndRemoveDuplicates(T[] children) {
		int r = isSortedAndUnique(children);
		switch (r) {
		case 0:
			// In this case, the array is already sorted and no duplicates were
			// found.
			return children;
		case 1:
			// In this case, the array is already sorted, but duplicates were
			// found
			return ArrayUtils.sortedRemoveDuplicates(children);
		default:
			// In this case, the array is not sorted and may or may not
			// contained duplicates.
			children = Arrays.copyOf(children, children.length);
			Arrays.sort(children);
			return ArrayUtils.sortedRemoveDuplicates(children);
		}
	}

	/**
	 * Normalise bounds of an equation to be positive. For example, consider the
	 * inequality <code>x < y - z</code>. In this case, the right-hand side is
	 * not normalised because it contains a negative term. The normalised
	 * version of this inequality would be <code>x + z < y</code>.
	 *
	 * @param lhs
	 * @param rhs
	 * @return
	 */
	private static Pair<Polynomial, Polynomial> normaliseBounds(Polynomial lhs, Polynomial rhs) {
		Polynomial bound = factorise(lhs.subtract(rhs));
		Polynomial pos = new Polynomial(BigInteger.ZERO);
		Polynomial neg = new Polynomial(BigInteger.ZERO);
		for (int i = 0; i != bound.size(); ++i) {
			Polynomial.Term t = bound.getOperand(i);
			BigInteger coeff = t.getCoefficient().get();
			if (coeff.compareTo(BigInteger.ZERO) >= 0) {
				pos = pos.add(t);
			} else {
				neg = neg.subtract(t);
			}
		}
		return new Pair<>(pos, neg);
	}

	// ========================================================================
	// Equalities / Inequalities
	// ========================================================================

	/**
	 * Evaluate a given inequality whose bounds are known to be constant integer
	 * values. For example, <code>1 < 0</code> evaluates to <code>false</code>,
	 * etc.
	 *
	 * @param opcode
	 * @param lhs
	 * @param rhs
	 * @return
	 */
	private static Formula.Truth evaluateInequality(Opcode opcode, Value.Int lhs, Value.Int rhs) {
		boolean result;
		switch (opcode) {
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
			throw new IllegalArgumentException("Invalid inequality opcode: " + opcode);
		}
		return new Formula.Truth(result);
	}

	/**
	 * Evaluate a given equality whose bounds are known to be constant values of
	 * some sort. For example, <code>true == false</code> evaluates to
	 * <code>false</code>, etc.
	 *
	 * @param opcode
	 * @param lhs
	 * @param rhs
	 * @return
	 */
	private static Formula.Truth evaluateEquality(Opcode opcode, Value lhs, Value rhs) {
		boolean result;
		switch (opcode) {
		case EXPR_eq:
			result = lhs.equals(rhs);
			break;
		case EXPR_neq:
			result = !(lhs.equals(rhs));
			break;
		default:
			throw new IllegalArgumentException("Invalid equality opcode: " + opcode);
		}
		return new Formula.Truth(result);
	}

	/**
	 * Factorise a given polynomial. For example, <code>2x+2</code> is
	 * factorised to be <code>x+1</code>. Observe that this does not preseve the
	 * result of the polynomial. However, it is safe to do when simplifying
	 * equations. For example, <code>2x == 2y</code> can be safely factorised to
	 * <code>x == y</code>.
	 *
	 * @param p
	 * @return
	 */
	private static Polynomial factorise(Polynomial p) {
		BigInteger factor = p.getOperand(0).getCoefficient().get();
		// In case of just one coefficient which is negative, we need to compute
		// abs() here.
		factor = factor.abs();
		//
		for (int i = 1; i != p.size(); ++i) {
			BigInteger c = p.getOperand(i).getCoefficient().get();
			factor = factor.gcd(c);
		}
		if (factor.equals(BigInteger.ZERO) || factor.equals(BigInteger.ONE)) {
			// No useful factor discovered
			return p;
		} else {
			// Yes, we found a useful factor. Therefore, divide all coefficients
			// by this.
			Polynomial r = new Polynomial(BigInteger.ZERO);
			for (int i = 0; i != p.size(); ++i) {
				Polynomial.Term t = p.getOperand(i);
				BigInteger c = t.getCoefficient().get();
				c = c.divide(factor);
				r = r.add(new Polynomial.Term(new Value.Int(c), t.getAtoms()));
			}
			return r;
		}
	}

	/**
	 * Check whether or not the children of this array are sorted according to
	 * syntactic heap index. And, if so, whether or not there are any duplicate
	 * elements encountered.
	 *
	 * @param children
	 * @return
	 */
	private static <T extends SyntacticItem> int isSortedAndUnique(T[] children) {
		int r = 0;
		for (int i = 1; i < children.length; ++i) {
			int c = children[i - 1].compareTo(children[i]);
			if (c == 0) {
				// Duplicate found, though still could be in sorted order.
				r = 1;
			} else if (c > 0) {
				// NOT in sorted order
				return -1;
			}
		}
		// All good
		return r;
	}
}
