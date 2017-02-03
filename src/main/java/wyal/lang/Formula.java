package wyal.lang;


import java.math.BigInteger;
import java.util.Arrays;

import wyal.lang.WyalFile.Expr;
import wyal.lang.WyalFile.Opcode;
import wyal.lang.WyalFile.Pair;
import wyal.lang.WyalFile.Tuple;
import wyal.lang.WyalFile.Type;
import wyal.lang.WyalFile.Value;
import wyal.lang.WyalFile.VariableDeclaration;
import wyal.util.Formulae;
import wyal.util.TypeSystem;

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
	 *
	 * @return
	 */
	public Formula invert();

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
			return Formulae.or(nChildren);
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
			return Formulae.and(nChildren);
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
			if(getSign()) {
				return Formulae.notEqual(lhs,rhs);
			} else {
				return Formulae.equal(lhs,rhs);
			}
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
			if (getSign()) {
				return Formulae.notEqual(lhs,rhs);
			} else {
				return Formulae.equal(lhs,rhs);
			}
		}
	}

	public interface Atom extends Expr {

	}

	public static class VariableAccess extends Expr.VariableAccess implements Atom {

		public VariableAccess(VariableDeclaration decl) {
			super(decl);
		}


	}

	public static class Constant extends Expr.Constant implements Atom {

		public Constant(Value v) {
			super(v);
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
			return size() == 1 && getOperand(0).getAtoms().size() == 0;
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
				if (term.getAtoms().size() == 0) {
					return term.getCoefficient();
				}
			}
			throw new IllegalArgumentException("polynomial is not constant");
		}

		public Polynomial negate() {
			return Formulae.negate(this);
		}

		public Polynomial add(Polynomial poly) {
			return Formulae.add(this, poly);
		}

		public Polynomial subtract(Polynomial.Term p) {
			return Formulae.add(this,p.negate());
		}

		public Polynomial subtract(Polynomial p) {
			return add(p.negate());
		}

		public Polynomial multiply(Polynomial rhs) {
			return Formulae.multiply(this, rhs);
		}

		public static class Term extends Expr.Operator {
			public Term(BigInteger constant) {
				this(new Value.Int(constant));
			}
			public Term(Value.Int constant) {
				super(Opcode.EXPR_mul,new Constant(constant));
			}
			public Term(Value.Int v, Tuple<Atom> variables) {
				super(Opcode.EXPR_mul,append(v, variables));
			}
			Term(Atom[] operands) {
				super(Opcode.EXPR_mul,operands);
			}
			public Value.Int getCoefficient() {
				Constant c = (Constant) getOperand(0);
				return (Value.Int) c.getValue();
			}

			@Override
			public Atom[] getOperands() {
				return (Atom[]) super.getOperands();
			}

			public Tuple<Atom> getAtoms() {
				Atom[] atoms = getOperands();
				atoms = Arrays.copyOfRange(atoms, 1, atoms.length);
				return new Tuple<>(atoms);
			}

			public Polynomial.Term negate() {
				BigInteger coeff = getCoefficient().get();
				return new Polynomial.Term(new Value.Int(coeff.negate()), getAtoms());
			}

			public Polynomial.Term add(Polynomial.Term term) {
				BigInteger lhsCoeff = this.getCoefficient().get();
				BigInteger rhsCoeff = term.getCoefficient().get();
				BigInteger r = lhsCoeff.add(rhsCoeff);
				if (r.equals(BigInteger.ZERO)) {
					return null;
				} else {
					return new Polynomial.Term(new Value.Int(r), getAtoms());
				}
			}

			/**
			 * Multiply two polynomial terms together. For example, multiplying
			 * <code>4xy</code> by <code>2x</code> gives <code>8x^2y</code>.
			 *
			 * @param lhs
			 * @param rhs
			 * @return
			 */
			public Polynomial.Term multiply(Polynomial.Term rhs) {
				BigInteger lhsCoeff = this.getCoefficient().get();
				BigInteger rhsCoeff = rhs.getCoefficient().get();
				Tuple<Atom> lhsAtoms = this.getAtoms();
				Tuple<Atom> rhsAtoms = rhs.getAtoms();
				Atom[] atoms = new Atom[lhsAtoms.size() + rhsAtoms.size()];
				System.arraycopy(lhsAtoms.getOperands(), 0, atoms, 0, lhsAtoms.size());
				System.arraycopy(rhsAtoms.getOperands(), 0, atoms, lhsAtoms.size(), rhsAtoms.size());
				Arrays.sort(atoms);
				Value.Int coefficient = new Value.Int(lhsCoeff.multiply(rhsCoeff));
				return new Polynomial.Term(coefficient, new Tuple<>(atoms));
			}

			static Atom[] append(Value.Int i, Tuple<Atom> variables) {
				Atom[] exprs = new Atom[variables.size()+1];
				exprs[0] = new Formula.Constant(i);
				for(int k=0;k!=variables.size();++k) {
					exprs[k+1] = variables.getOperand(k);
				}
				return exprs;
			}
		}
	}
}