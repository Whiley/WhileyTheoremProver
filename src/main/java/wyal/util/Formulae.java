package wyal.util;

import java.math.BigInteger;
import java.util.Arrays;

import wyal.lang.Formula;
import wyal.lang.SyntacticItem;
import wyal.lang.WyalFile;
import wyal.lang.WyalFile.*;
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
			Formula[] operands = toFormulae(b.getOperands(),types);
			return new Formula.Conjunct(operands);
		}
		case STMT_caseof: {
			WyalFile.Stmt.CaseOf b = (WyalFile.Stmt.CaseOf) stmt;
			Formula[] operands = toFormulae(b.getOperands(),types);
			return new Formula.Disjunct(operands);
		}
		case STMT_ifthen: {
			WyalFile.Stmt.IfThen it = (WyalFile.Stmt.IfThen) stmt;
			Formula lhs = toFormula(it.getIfBody(),types);
			Formula rhs = toFormula(it.getThenBody(),types);
			return new Formula.Disjunct(lhs.invert(),rhs);
		}
		case STMT_forall: {
			Stmt.Quantifier q = (WyalFile.Stmt.Quantifier) stmt;
			Formula body = toFormula(q.getBody(),types);
			return new Formula.Quantifier(true,q.getParameters(), body);
		}
		case STMT_exists: {
			Stmt.Quantifier q = (WyalFile.Stmt.Quantifier) stmt;
			Formula body = toFormula(q.getBody(),types);
			return new Formula.Quantifier(false,q.getParameters(), body);
		}
		case EXPR_implies: {
			WyalFile.Expr.Operator it = (Expr.Operator) stmt;
			Formula lhs = toFormula(it.getOperand(0),types);
			Formula rhs = toFormula(it.getOperand(1),types);
			return new Formula.Disjunct(lhs.invert(), rhs);
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
				Formula.Atom lhs_a = toAtom(lhs);
				Formula.Atom rhs_a = toAtom(rhs);
				return new Formula.Equality(true, lhs_a, rhs_a);
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
				Formula.Atom lhs_a = toAtom(lhs);
				Formula.Atom rhs_a = toAtom(rhs);
				return new Formula.Equality(false, lhs_a, rhs_a);
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
			return new Formula.Inequality(true, lhs, rhs);
		}
		case EXPR_gteq: {
			Expr.Operator operator = (Expr.Operator) stmt;
			Polynomial lhs = toPolynomial(operator.getOperand(0));
			Polynomial rhs = toPolynomial(operator.getOperand(1));
			return new Formula.Inequality(false, lhs, rhs);
		}
		case EXPR_not: {
			Expr.Operator operator = (Expr.Operator) stmt;
			Formula f = toFormula(operator.getOperand(0),types);
			return f.invert();
		}
		case EXPR_const: {
			Expr.Constant c = (Expr.Constant) stmt;
			Value.Bool b = (Value.Bool) c.getValue();
			return new Formula.Truth(b);
		}
		default:
			if (stmt instanceof WyalFile.Expr) {
				Formula.Atom atom = toAtom((WyalFile.Expr) stmt);
				Formula.Atom TRUE = new Formula.Truth(new Value.Bool(true));
				return new Formula.Equality(true, TRUE, atom);
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
		Formula.Atom atom = toAtom(e);
		if(atom instanceof Polynomial) {
			return (Polynomial) atom;
		} else {
			Polynomial.Term term = new Polynomial.Term(atom);
			return new Polynomial(term);
		}
	}

	/**
	 * Convert an arbitrary expression to an atom.
	 *
	 * @param e
	 * @return
	 */
	private static Formula.Atom toAtom(Expr e) {
		switch (e.getOpcode()) {
		case EXPR_const:
			return toAtom((Expr.Constant) e);
		//case EXPR_invoke:
		//case EXPR_arridx:
		case EXPR_var:
			return toAtom((Expr.VariableAccess) e);
		case EXPR_add:
		case EXPR_mul:
		case EXPR_sub: {
			return toAtom((Expr.Operator) e);
		}
		default:
			throw new IllegalArgumentException("cannot convert expression to polynomial");
		}
	}

	private static Formula.Atom toAtom(Expr.Constant e) {
		Value val = e.getValue();
		if(val instanceof Value.Int) {
			Value.Int c = (Value.Int) val;
			return new Polynomial(new Polynomial.Term(c));
		} else {
			Value.Bool b = (Value.Bool) val;
			return new Formula.Truth(b.get());
		}
	}

	private static Formula.Atom toAtom(Expr.VariableAccess e) {
		return new Formula.VariableAccess(e.getVariableDeclaration());
	}

	private static Formula.Atom toAtom(Expr.Operator e) {
		Expr[] children = e.getOperands();
		// FIXME: not all operators produce polynomials
		Polynomial result = toPolynomial(children[0]);
		switch (e.getOpcode()) {
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

	// ========================================================================
	// Simplifications
	// ========================================================================

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
	 * <b>not recursive</b>. That is, it does not attempt to simplify the
	 * children of this formula.
	 *
	 * @author David J. Pearce
	 *
	 */
	public static Formula simplify(Conjunct conjunct) {
		Formula[] children = conjunct.getOperands();
		Formula[] nChildren = children;
		// Flatten nested conjuncts
		nChildren = flattenNestedConjuncts(nChildren);
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
	 * <b>not recursive</b>. That is, it does not attempt to simplify the
	 * children of this formula.
	 *
	 */
	public static Formula simplify(Disjunct disjunct) {
		Formula[] children = disjunct.getOperands();
		Formula[] nChildren = children;
		// Flatten nested disjuncts
		nChildren = flattenNestedDisjuncts(nChildren);
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

	/**
	 * Simplify a quantifier expression. In essence, if the body is a truth
	 * value then that is returned. For example, <code>forall x.true</code> is
	 * simply <code>true</code>.
	 *
	 * @param quantifier
	 * @return
	 */
	public static Formula simplify(Quantifier quantifier) {
		Formula body = quantifier.getBody();
		if(body instanceof Truth) {
			return body;
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
		Polynomial lhs = ieq.getOperand(0);
		Polynomial rhs = ieq.getOperand(1);
		// FIXME: this doesn't cancel terms!
		if (lhs.isConstant() && rhs.isConstant()) {
			return evaluateInequality(ieq.getOpcode(), lhs.toConstant(), rhs.toConstant());
		} else if (lhs.equals(rhs)) {
			return new Formula.Truth(false);
		} else {
			Pair<Polynomial, Polynomial> bs = normaliseBounds(lhs, rhs);
			return new Inequality(true, bs.getFirst(), bs.getSecond());
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
		Polynomial lhs = eq.getOperand(0);
		Polynomial rhs = eq.getOperand(1);
		// FIXME: this doesn't cancel terms!
		if (lhs.isConstant() && rhs.isConstant()) {
			Value lhs_v = lhs.toConstant();
			Value rhs_v = rhs.toConstant();
			return evaluateEquality(eq.getOpcode(), lhs_v, rhs_v);
		} else if (lhs.equals(rhs)) {
			return new Formula.Truth(true);
		} else {
			Pair<Polynomial, Polynomial> bs = normaliseBounds(lhs, rhs);
			return new ArithmeticEquality(true, bs.getFirst(), bs.getSecond());
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
		Atom lhs = eq.getOperand(0);
		Atom rhs = eq.getOperand(1);
		if (lhs instanceof Expr.Constant && rhs instanceof Expr.Constant) {
			Value lhs_v = ((Expr.Constant) lhs).getValue();
			Value rhs_v = ((Expr.Constant) rhs).getValue();
			return evaluateEquality(eq.getOpcode(), lhs_v, rhs_v);
		} else if (lhs.equals(rhs)) {
			return new Formula.Truth(true);
		} else {
			return eq;
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
			lhs = rearrangeForUpperBound(ithLowerBound, ithUpperBound, lCandidate.getFirst());
			rhs = rearrangeForLowerBound(jthLowerBound, jthUpperBound, lCandidate.getSecond());
		} else if (rCandidate != null) {
			rhs = rearrangeForUpperBound(jthLowerBound, jthUpperBound, rCandidate.getFirst());
			lhs = rearrangeForLowerBound(ithLowerBound, ithUpperBound, rCandidate.getSecond());
		} else {
			return null;
		}
		if (ith.getSign() || jth.getSign()) {
			// Result is strict as had something like ... <= x < ...
			return new Formula.Inequality(true, lhs, rhs);
		} else {
			// Result is not-strict as had something like ... <= x <= ...
			return new Formula.Inequality(false, lhs, rhs);
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
			Formula.Atom[] ithAtoms = ith.getAtoms();
			if (ithAtoms.length > 0) {
				for (int j = 0; j != upper.size(); ++j) {
					Polynomial.Term jth = upper.getOperand(j);
					Formula.Atom[] jthAtoms = jth.getAtoms();
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
	 * @param substitution
	 * @param item
	 * @return
	 */
	public static <T extends SyntacticItem> SyntacticItem substitute(Pair<Identifier, T> substitution, SyntacticItem item) {
		// FIXME: this function is broken because it should not be using
		// identifiers for substitution. Instead, is should be using variable
		// declarations.
		if (item instanceof Expr.VariableAccess) {
			// In this case, we might be able to make a substitution.
			Expr.VariableAccess v = (Expr.VariableAccess) item;
			Identifier name = v.getVariableDeclaration().getVariableName();
			if (name.equals(substitution.getFirst())) {
				// Yes, we made a substitution!
				return substitution.getSecond();
			}
			return item;
		} else {
			// No immediate substitution possible. Instead, recursively traverse
			// term looking for substitution.
			SyntacticItem[] children = item.getOperands();
			SyntacticItem[] nChildren = children;
			for (int i = 0; i != children.length; ++i) {
				SyntacticItem child = children[i];
				SyntacticItem nChild = substitute(substitution, item);
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
		return flattenNestedClauses(true,children);
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
		return flattenNestedClauses(false,children);
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
		int count = 0;
		for (int i = 0, j = start; i != from.length; ++i) {
			Expr child = from[i];
			if (flag && child.getOpcode() == Opcode.EXPR_and) {
				Formula.Conjunct conjunct = (Formula.Conjunct) child;
				j += nestedCopy(flag,conjunct.getOperands(), to, j);
			} else if (!flag && child.getOpcode() == Opcode.EXPR_or) {
				Formula.Disjunct disjunct = (Formula.Disjunct) child;
				j += nestedCopy(flag,disjunct.getOperands(), to, j);
			} else {
				to[j++] = from[i];
				count = count + 1;
			}
		}
		return count;
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
		switch(r) {
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
		if (factor.equals(BigInteger.ONE)) {
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
