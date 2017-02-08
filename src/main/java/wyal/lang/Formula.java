package wyal.lang;


import java.math.BigInteger;
import java.util.Arrays;

import wyal.lang.Formula.Polynomial;
import wyal.lang.WyalFile.Expr;
import wyal.lang.WyalFile.Opcode;
import wyal.lang.WyalFile.Pair;
import wyal.lang.WyalFile.Stmt;
import wyal.lang.WyalFile.Tuple;
import wyal.lang.WyalFile.Type;
import wyal.lang.WyalFile.Value;
import wyal.lang.WyalFile.VariableDeclaration;
import wyal.util.Formulae;
import wyal.util.Polynomials;
import wyal.util.TypeSystem;

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

	/**
	 * Invert a given formula.
	 *
	 * @return
	 */
	public Formula invert();

	@Override
	public Formula clone(SyntacticItem[] children);

	public static class Truth extends Expr.Constant implements Formula,Atom {

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
		public Truth clone(SyntacticItem[] children) {
			return new Truth(getValue());
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
		public Formula invert() {
			Formula[] children = getOperands();
			Formula[] nChildren = new Formula[children.length];
			for(int i=0;i!=children.length;++i) {
				nChildren[i] = children[i].invert();
			}
			return new Disjunct(nChildren);
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
		public Formula invert() {
			Formula[] children = getOperands();
			Formula[] nChildren = new Formula[children.length];
			for(int i=0;i!=children.length;++i) {
				nChildren[i] = children[i].invert();
			}
			return new Conjunct(nChildren);
		}

		@Override
		public Disjunct clone(SyntacticItem[] children) {
			return new Disjunct((Formula[]) children);
		}
	}

	public static class Quantifier extends Expr.Quantifier implements Formula {
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
		public Formula invert() {
			Formula body = getBody().invert();
			return new Formula.Quantifier(!getSign(),getParameters(),body);
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
		public Formula invert() {
			Polynomial lhs = getOperand(0);
			Polynomial rhs = getOperand(1);
			return new Inequality(!getSign(),lhs,rhs);
		}

		@Override
		public Inequality clone(SyntacticItem[] children) {
			return new Inequality(getSign(),(Polynomial) children[0],(Polynomial) children[1]);
		}
	}

	public static class Equality extends Expr.Operator implements Formula {
		public Equality(boolean sign, Atom lhs, Atom rhs) {
			super(sign ? Opcode.EXPR_eq : Opcode.EXPR_neq, lhs, rhs);
		}

		public Equality(boolean sign, Polynomial[] arr) {
			super(sign ? Opcode.EXPR_eq : Opcode.EXPR_neq, arr);
		}

		public boolean getSign() {
			return getOpcode() == Opcode.EXPR_eq;
		}

		@Override
		public Atom getOperand(int i) {
			return (Atom) super.getOperand(i);
		}

		@Override
		public Atom[] getOperands() {
			return (Atom[]) super.getOperands();
		}

		@Override
		public Formula invert() {
			Atom lhs = getOperand(0);
			Atom rhs = getOperand(1);
			return new Equality(!getSign(),lhs,rhs);
		}

		@Override
		public Equality clone(SyntacticItem[] children) {
			return new Equality(getSign(),(Atom) children[0],(Atom) children[1]);
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
		public Formula invert() {
			Polynomial lhs = getOperand(0);
			Polynomial rhs = getOperand(1);
			return new Equality(!getSign(), lhs, rhs);
		}

		@Override
		public ArithmeticEquality clone(SyntacticItem[] children) {
			return new ArithmeticEquality(getSign(),(Polynomial) children[0],(Polynomial) children[1]);
		}
	}

	public interface Atom extends Expr {
		@Override
		public Atom clone(SyntacticItem[] children);
	}

	public static class VariableAccess extends Expr.VariableAccess implements Atom {

		public VariableAccess(VariableDeclaration decl) {
			super(decl);
		}

		@Override
		public Formula.VariableAccess clone(SyntacticItem[] children) {
			return new Formula.VariableAccess((VariableDeclaration) children[0]);
		}
	}

	public final static class Polynomial extends Expr.Operator implements Atom {
		public Polynomial(BigInteger constant) {
			super(Opcode.EXPR_add,new Polynomial.Term[]{new Polynomial.Term(constant)});
		}
		public Polynomial(Term... terms) {
			super(Opcode.EXPR_add, terms);
		}

		@Override
		public Term getOperand(int i) {
			return (Term) super.getOperand(i);
		}

		@Override
		public Type getReturnType(TypeSystem types) {
			// FIXME: we could do better than this.
			return new Type.Int();
		}

		@Override
		public Polynomial.Term[] getOperands() {
			return (Polynomial.Term[]) super.getOperands();
		}

		/**
		 * Check whether a polynomial is a constant or not.
		 *
		 * @param p
		 * @return
		 */
		public boolean isConstant() {
			return size() == 1 && getOperand(0).getAtoms().length == 0;
		}

		/**
		 * Extract the constant that this polynomial represents (assuming it
		 * does).
		 *
		 * @param p
		 * @return
		 */
		public Value.Int toConstant() {
			if (size() == 1) {
				Polynomial.Term term = getOperand(0);
				if (term.getAtoms().length == 0) {
					return term.getCoefficient();
				}
			}
			throw new IllegalArgumentException("polynomial is not constant");
		}

		public Polynomial negate() {
			return Polynomials.negate(this);
		}

		public Polynomial add(Polynomial poly) {
			return Polynomials.add(this, poly);
		}

		public Polynomial add(Polynomial.Term term) {
			return Polynomials.add(this, term);
		}

		public Polynomial subtract(Polynomial p) {
			return add(p.negate());
		}

		public Polynomial subtract(Polynomial.Term term) {
			return Polynomials.add(this, Polynomials.negate(term));
		}

		public Polynomial multiply(Polynomial rhs) {
			return Polynomials.multiply(this, rhs);
		}

		@Override
		public Polynomial clone(SyntacticItem[] children) {
			return new Polynomial((Term[]) children);
		}

		public static class Term extends Expr.Operator {
			public Term(BigInteger constant) {
				this(new Value.Int(constant));
			}
			public Term(Value.Int constant) {
				super(Opcode.EXPR_mul,new Constant(constant));
			}
			public Term(Atom atom) {
				super(Opcode.EXPR_mul,append(new Value.Int(1),atom));
			}
			public Term(Value.Int coefficient, Atom... variables) {
				super(Opcode.EXPR_mul,append(coefficient,variables));
			}
			Term(Atom[] operands) {
				super(Opcode.EXPR_mul,operands);
			}
			public Value.Int getCoefficient() {
				Constant c = (Constant) getOperand(0);
				return (Value.Int) c.getValue();
			}

			public Atom[] getAtoms() {
				Expr[] children = getOperands();
				Atom[] atoms = new Atom[children.length-1];
				System.arraycopy(children, 1, atoms, 0, atoms.length);
				return atoms;
			}


			static Expr[] append(Value.Int i, Atom... variables) {
				Expr[] exprs = new Expr[variables.length+1];
				exprs[0] = new Expr.Constant(i);
				for(int k=0;k!=variables.length;++k) {
					exprs[k+1] = variables[k];
				}
				return exprs;
			}

			@Override
			public Term clone(SyntacticItem[] children) {
				Atom[] atoms = new Atom[children.length-1];
				System.arraycopy(children, 1, atoms, 0, atoms.length);
				return new Term((Value.Int) children[0], atoms);
			}

		}
	}
}