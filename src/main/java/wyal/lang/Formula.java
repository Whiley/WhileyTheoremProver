package wyal.lang;


import wyal.lang.WyalFile.Expr;
import wyal.lang.WyalFile.Opcode;
import wyal.lang.WyalFile.Tuple;
import wyal.lang.WyalFile.Value;
import wyal.lang.WyalFile.VariableDeclaration;
import wyal.util.Formulae;

/**
 * A special kind of expression which maintains a normal form
 * representation. As such, formulae are not suitable for representing
 * source-level syntax, as they do not faithfully retain relevant aspects,
 * such as ordering, etc. Instead, they are used with the automated theorem
 * prover for ensuring properties are correct.
 *
 * @author David J. Pearce
 *
 */
public interface Formula extends Expr {

	/**
	 * Invert a given formula.
	 * @return
	 */
	public Formula invert();

	@Override
	public Formula clone(SyntacticItem[] operands);

	/**
	 * Combine formulae together as conjuncts, whilst performing a range of
	 * simplifications:
	 *
	 * <ol>
	 * <li><b>Eliminates boolean constants</b>. Conjuncts containing
	 * <code>false</code> are reduced to <code>false</code>. In contrast,
	 * any occurrences of <code>true</code> are simply removed.</li>
	 * <li><b>Flattens nested conjuncts</b>. All nested conjuncts are
	 * recursively flattened into a single conjunct. For example,
	 * <code> (x && (y && z))</code> is flattened to
	 * <code>(x && y && z)</code>.</li>
	 * <li><b>Eliminates singleton conjuncts</b>. A conjunct containing a
	 * single (non-conjunct) child is reduced to that child.</li>
	 * </ol>
	 *
	 * The implementation attempts to eliminate dynamic memory allocation in
	 * the case that no reduction is applied.
	 *
	 * @author David J. Pearce
	 *
	 */
	public static Formula and(Formula... formulae) {
		// Flatten nested conjuncts
		formulae = Formulae.flattenNestedConjuncts(formulae);
		// Eliminate truths
		formulae = Formulae.eliminateConstants(false, formulae);
		// Ensure sorted and unique
		formulae = Formulae.sortAndRemoveDuplicates(formulae);
		// And, finally...
		if (formulae.length == 0) {
			// Return true here since the only way it's possible to get here
			// is if the conjunct contained only truths at the end.
			return new Truth(true);
		} else if (formulae.length == 1) {
			return formulae[0];
		} else {
			return new Conjunct(formulae);
		}
	}

	/**
	 * Combine formulae together as disjuncts, whilst performing a range of
	 * simplifications:
	 *
	 * <ol>
	 * <li><b>Eliminates boolean constants</b>. Disjuncts containing
	 * <code>true</code> are reduced to <code>true</code>. In contrast, any
	 * occurrences of <code>false</code> are simply removed.</li>
	 * <li><b>Flattens nested disjuncts</b>. All nested disjuncts are
	 * recursively flattened into a single disjunct. For example,
	 * <code> (x || (y || z))</code> is flattened to
	 * <code>(x || y || z)</code>.</li>
	 * <li><b>Eliminates singleton disjuncts</b>. A disjunct containing a
	 * single (non-disjunct) child is reduced to that child.</li>
	 * </ol>
	 *
	 * The implementation attempts to eliminate dynamic memory allocation in
	 * the case that no reduction is applied.
	 *
	 */
	public static Formula or(Formula... formulae) {
		// Flatten nested disjuncts
		formulae = Formulae.flattenNestedDisjuncts(formulae);
		// Eliminate truths
		formulae = Formulae.eliminateConstants(true, formulae);
		// Ensure sorted and unique
		formulae = Formulae.sortAndRemoveDuplicates(formulae);
		// And, finally...
		if (formulae.length == 0) {
			// Return false here since the only way it's possible to get
			// here is if the disjunct contained only falsehoods at the end.
			return new Truth(false);
		} else if (formulae.length == 1) {
			return formulae[0];
		} else {
			return new Disjunct(formulae);
		}
	}

	public static Formula lessThan(Expr.Polynomial lhs, Expr.Polynomial rhs) {
		if (lhs.isConstant() && rhs.isConstant()) {
			return Formulae.evaluateInequality(Opcode.EXPR_lt, lhs.toConstant(), rhs.toConstant());
		} else if(lhs.equals(rhs)) {
			return new Formula.Truth(false);
		} else {
			// FIXME: we need to normalise the left- and right-hand sides
			// here
			return new Inequality(true,lhs,rhs);
		}
	}

	public static Formula greaterThanOrEquals(Expr.Polynomial lhs, Expr.Polynomial rhs) {
		if (lhs.isConstant() && rhs.isConstant()) {
			return Formulae.evaluateInequality(Opcode.EXPR_gteq, lhs.toConstant(), rhs.toConstant());
		} else if(lhs.equals(rhs)) {
			return new Formula.Truth(true);
		} else {
			// FIXME: we need to normalise the left- and right-hand sides
			// here
			return new Inequality(false, lhs, rhs);
		}
	}

	public static Formula equals(Polynomial lhs, Polynomial rhs) {
		if (lhs.isConstant() && rhs.isConstant()) {
			Value lhs_v = lhs.toConstant();
			Value rhs_v = rhs.toConstant();
			return Formulae.evaluateEquality(Opcode.EXPR_eq, lhs_v, rhs_v);
		} else if(lhs.equals(rhs)) {
			return new Formula.Truth(true);
		} else {
			return new Equality(true,lhs,rhs);
		}
	}

	public static Formula notEquals(Polynomial lhs, Polynomial rhs) {
		if (lhs.isConstant() && rhs.isConstant()) {
			Value lhs_v = lhs.toConstant();
			Value rhs_v = rhs.toConstant();
			return Formulae.evaluateEquality(Opcode.EXPR_neq, lhs_v, rhs_v);
		} else if(lhs.equals(rhs)) {
			return new Formula.Truth(false);
		} else {
			return new Equality(false,lhs,rhs);
		}
	}

	public static Formula unify(Expr lhs, Expr rhs) {
		if (lhs instanceof Expr.Constant && rhs instanceof Expr.Constant) {
			Value lhs_v = ((Expr.Constant)lhs).getValue();
			Value rhs_v = ((Expr.Constant)rhs).getValue();
			return Formulae.evaluateEquality(Opcode.EXPR_eq, lhs_v, rhs_v);
		} else if(lhs.equals(rhs)) {
			return new Formula.Truth(true);
		} else {
			return new Equality(true,lhs,rhs);
		}
	}

	public static Formula notUnify(Expr lhs, Expr rhs) {
		if (lhs instanceof Expr.Constant && rhs instanceof Expr.Constant) {
			Value lhs_v = ((Expr.Constant)lhs).getValue();
			Value rhs_v = ((Expr.Constant)rhs).getValue();
			return Formulae.evaluateEquality(Opcode.EXPR_neq, lhs_v, rhs_v);
		} else if(lhs.equals(rhs)) {
			return new Formula.Truth(false);
		} else {
			return new Equality(false,lhs,rhs);
		}
	}

	public static Formula forall(Tuple<VariableDeclaration> parameters, Formula body) {
		if(body instanceof Truth) {
			return body;
		} else {
			return new Quantifier(true,parameters,body);
		}
	}

	public static Formula exists(Tuple<VariableDeclaration> parameters, Formula body) {
		if(body instanceof Truth) {
			return body;
		} else {
			return new Quantifier(false,parameters,body);
		}
	}

	public static class Truth extends Expr.Constant implements Formula {

		public Truth(boolean value) {
			super(new Value.Bool(value));
		}

		public Truth(Value.Bool value) {
			super(value);
		}

		public boolean holds() {
			return getValue().get();
		}

		@Override
		public Value.Bool getValue() {
			return (Value.Bool) super.getValue();
		}

		@Override
		public Formula invert() {
			return new Truth(!getValue().get());
		}

		@Override
		public Formula.Truth clone(SyntacticItem[] operands) {
			return new Truth((Value.Bool) operands[0]);
		}
	}

	public static class Conjunct extends Expr.Operator implements Formula {

		private Conjunct(Formula... operands) {
			super(Opcode.EXPR_and, operands);
		}

		@Override
		public Formula getOperand(int i) {
			return (Formula) super.getOperand(i);
		}

		@Override
		public Formula[] getOperands() {
			return (Formula[]) super.getOperands();
		}

		@Override
		public Formula invert() {
			Formula[] children = getOperands();
			Formula[] nChildren = new Formula[children.length];
			for(int i=0;i!=children.length;++i) {
				nChildren[i] = children[i].invert();
			}
			return or(nChildren);
		}

		@Override
		public Formula.Conjunct clone(SyntacticItem[] operands) {
			return new Conjunct((Formula[]) operands);
		}
	}

	public static class Disjunct extends Expr.Operator implements Formula {

		private Disjunct(Formula... operands) {
			super(Opcode.EXPR_or, operands);
		}

		@Override
		public Formula getOperand(int i) {
			return (Formula) super.getOperand(i);
		}

		@Override
		public Formula[] getOperands() {
			return (Formula[]) super.getOperands();
		}

		@Override
		public Formula invert() {
			Formula[] children = getOperands();
			Formula[] nChildren = new Formula[children.length];
			for(int i=0;i!=children.length;++i) {
				nChildren[i] = children[i].invert();
			}
			return and(nChildren);
		}
		@Override
		public Formula.Disjunct clone(SyntacticItem[] operands) {
			return new Disjunct((Formula[]) operands);
		}
	}

	public static class Quantifier extends Expr.Quantifier implements Formula {
		private Quantifier(boolean sign, VariableDeclaration[] parameters, Formula body) {
			super(sign ? Opcode.EXPR_forall : Opcode.EXPR_exists, new Tuple<>(parameters), body);
		}

		private  Quantifier(boolean sign, Tuple<VariableDeclaration> parameters, Formula body) {
			super(sign ? Opcode.EXPR_forall : Opcode.EXPR_exists, parameters, body);
		}

		public boolean getSign() {
			return getOpcode() == Opcode.EXPR_forall;
		}

		@Override
		public Tuple<VariableDeclaration> getParameters() {
			return (Tuple<VariableDeclaration>) getOperand(0);
		}

		@Override
		public Formula getBody() {
			return (Formula) getOperand(1);
		}

		@Override
		public Formula invert() {
			Formula body = getBody().invert();
			return new Formula.Quantifier(!getSign(),getParameters(),body);
		}

		@Override
		public Formula.Quantifier clone(SyntacticItem[] operands) {
			return new Formula.Quantifier(getSign(), (Tuple<VariableDeclaration>) operands[0],
					(Formula) operands[1]);
		}
	}

	public static class Inequality extends Expr.Operator implements Formula {

		private Inequality(boolean sign, Expr.Polynomial lhs, Expr.Polynomial rhs) {
			super(sign ? Opcode.EXPR_lt : Opcode.EXPR_gteq, lhs, rhs);
		}

		@Override
		public Expr.Polynomial getOperand(int i) {
			return (Expr.Polynomial) super.getOperand(i);
		}

		@Override
		public Expr.Polynomial[] getOperands() {
			return (Expr.Polynomial[]) super.getOperands();
		}

		@Override
		public Formula invert() {
			Expr.Polynomial lhs = getOperand(0);
			Expr.Polynomial rhs = getOperand(1);
			return new Inequality(getOpcode() != Opcode.EXPR_lt,lhs,rhs);
		}

		@Override
		public Formula.Inequality clone(SyntacticItem[] operands) {
			return new Inequality(getOpcode() == Opcode.EXPR_lt, (Expr.Polynomial) operands[0],
					(Expr.Polynomial) operands[1]);
		}
	}

	public static class Equality extends Expr.Operator implements Formula {
		private Equality(boolean sign, Expr lhs, Expr rhs) {
			super(sign ? Opcode.EXPR_eq : Opcode.EXPR_neq, lhs, rhs);
		}

		@Override
		public Formula.Equality clone(SyntacticItem[] operands) {
			return new Equality(getOpcode() == Opcode.EXPR_eq, (Expr) operands[0], (Expr) operands[1]);
		}

		@Override
		public Formula invert() {
			Expr lhs = getOperand(0);
			Expr rhs = getOperand(1);
			return new Equality(getOpcode() != Opcode.EXPR_eq,lhs,rhs);
		}
	}

	public static class Unifier extends Expr.Operator implements Formula {
		private Unifier(boolean sign, Expr lhs, Expr rhs) {
			super(sign ? Opcode.EXPR_eq : Opcode.EXPR_neq, lhs, rhs);
		}

		@Override
		public Formula.Unifier clone(SyntacticItem[] operands) {
			return new Unifier(getOpcode() == Opcode.EXPR_eq, (Expr) operands[0], (Expr) operands[1]);
		}

		@Override
		public Formula invert() {
			Expr lhs = getOperand(0);
			Expr rhs = getOperand(1);
			return new Unifier(getOpcode() != Opcode.EXPR_eq, lhs, rhs);
		}
	}
}