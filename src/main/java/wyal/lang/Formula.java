package wyal.lang;

import wyal.lang.WyalFile.Expr;
import wyal.lang.WyalFile.Name;
import wyal.lang.WyalFile.Opcode;
import wyal.lang.WyalFile.Tuple;
import wyal.lang.WyalFile.Type;
import wyal.lang.WyalFile.Value;
import wyal.lang.WyalFile.VariableDeclaration;

/**
 * A special kind of expression which maintains a normal form representation. As
 * such, formulae are not suitable for representing source-level syntax, as they
 * do not faithfully retain relevant aspects, such as ordering, etc. Instead,
 * they are used with the automated theorem prover for ensuring properties are
 * correct.
 *
 * @author David J. Pearce
 *
 */
public interface Formula extends Expr {

	@Override
	public Formula clone(SyntacticItem[] children);

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
		public Truth clone(SyntacticItem[] children) {
			return new Truth((Value.Bool) children[0]);
		}
	}

	public static class Conjunct extends Expr.Operator implements Formula {

		public Conjunct(Formula... operands) {
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
		public Conjunct clone(SyntacticItem[] children) {
			return new Conjunct((Formula[]) children);
		}
	}

	public static class Disjunct extends Expr.Operator implements Formula {

		public Disjunct(Formula... operands) {
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
		public Disjunct clone(SyntacticItem[] children) {
			return new Disjunct((Formula[]) children);
		}
	}

	public static class Quantifier extends Expr.Quantifier implements Formula {
		public Quantifier(boolean sign, VariableDeclaration parameter, Formula body) {
			super(sign ? Opcode.EXPR_forall : Opcode.EXPR_exists, new Tuple<>(parameter), body);
		}

		public Quantifier(boolean sign, VariableDeclaration[] parameters, Formula body) {
			super(sign ? Opcode.EXPR_forall : Opcode.EXPR_exists, new Tuple<>(parameters), body);
		}

		public Quantifier(boolean sign, Tuple<VariableDeclaration> parameters, Formula body) {
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
		public Formula.Quantifier clone(SyntacticItem[] children) {
			return new Formula.Quantifier(getSign(), (Tuple) children[0], (Formula) children[1]);
		}
	}

	public static class Inequality extends Expr.Operator implements Formula {

		public Inequality(boolean sign, Polynomial lhs, Polynomial rhs) {
			super(sign ? Opcode.EXPR_lt : Opcode.EXPR_gteq, new Polynomial[]{lhs, rhs});
		}

		public boolean getSign() {
			return getOpcode() == Opcode.EXPR_lt;
		}

		@Override
		public Polynomial getOperand(int i) {
			return (Polynomial) super.getOperand(i);
		}

		@Override
		public Polynomial[] getOperands() {
			return (Polynomial[]) super.getOperands();
		}

		@Override
		public Inequality clone(SyntacticItem[] children) {
			return new Inequality(getSign(),(Polynomial) children[0],(Polynomial) children[1]);
		}
	}

	public static class Equality extends Expr.Operator implements Formula {
		public Equality(boolean sign, Expr lhs, Expr rhs) {
			super(sign ? Opcode.EXPR_eq : Opcode.EXPR_neq, lhs, rhs);
		}

		public Equality(boolean sign, Polynomial[] arr) {
			super(sign ? Opcode.EXPR_eq : Opcode.EXPR_neq, arr);
		}

		public boolean getSign() {
			return getOpcode() == Opcode.EXPR_eq;
		}

		@Override
		public Equality clone(SyntacticItem[] children) {
			return new Equality(getSign(),(Expr) children[0],(Expr) children[1]);
		}
	}

	public static class ArithmeticEquality extends Equality implements Formula {
		public ArithmeticEquality(boolean sign, Polynomial lhs, Polynomial rhs) {
			super(sign, new Polynomial[]{lhs, rhs});
		}

		@Override
		public Polynomial getOperand(int i) {
			return (Polynomial) super.getOperand(i);
		}

		@Override
		public Polynomial[] getOperands() {
			return (Polynomial[]) super.getOperands();
		}

		@Override
		public ArithmeticEquality clone(SyntacticItem[] children) {
			return new ArithmeticEquality(getSign(),(Polynomial) children[0],(Polynomial) children[1]);
		}
	}

	public static class Invoke extends Expr.Invoke implements Formula {
		private boolean sign;

		public Invoke(boolean sign, Type.AbstractFunction type, Name name, Expr... arguments) {
			super(type, name, arguments);
			this.sign = sign;
		}

		public Invoke(boolean sign, Type.AbstractFunction type, Name name, Tuple<Expr> arguments) {
			super(type, name, arguments);
			this.sign = sign;
		}

		public boolean getSign() {
			return sign;
		}

		@Override
		public Boolean getData() {
			return sign;
		}

		@Override
		public boolean equals(Object o) {
			// FIXME: the need for this method is something of a hack.
			if(o instanceof Formula.Invoke) {
				Formula.Invoke i = (Formula.Invoke) o;
				return sign == i.sign && super.equals(o);
			}
			return false;
		}

		@Override
		public Formula.Invoke clone(SyntacticItem[] children) {
			return new Formula.Invoke(sign,(Type.AbstractFunction) children[0], (Name) children[1],
					(Tuple) children[2]);
		}
	}
}