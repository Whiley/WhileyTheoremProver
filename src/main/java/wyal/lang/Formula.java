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
		formulae = Formulae.eliminateConstants(true, formulae);
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
		formulae = Formulae.eliminateConstants(false, formulae);
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

	public static Formula lessThan(Polynomial lhs, Polynomial rhs) {
		if (lhs.isConstant() && rhs.isConstant()) {
			return Formulae.evaluateInequality(Opcode.EXPR_lt, lhs.toConstant(), rhs.toConstant());
		} else if(lhs.equals(rhs)) {
			return new Formula.Truth(false);
		} else {
			Pair<Polynomial,Polynomial> bs = Formulae.normaliseBounds(lhs,rhs);
			return new Inequality(true,bs.getFirst(),bs.getSecond());
		}
	}

	public static Formula greaterThanOrEqual(Polynomial lhs, Polynomial rhs) {
		if (lhs.isConstant() && rhs.isConstant()) {
			return Formulae.evaluateInequality(Opcode.EXPR_gteq, lhs.toConstant(), rhs.toConstant());
		} else if(lhs.equals(rhs)) {
			return new Formula.Truth(true);
		} else {
			Pair<Polynomial,Polynomial> bs = Formulae.normaliseBounds(lhs,rhs);
			return new Inequality(false,bs.getFirst(),bs.getSecond());
		}
	}

	public static Formula equal(Polynomial lhs, Polynomial rhs) {
		if (lhs.isConstant() && rhs.isConstant()) {
			Value lhs_v = lhs.toConstant();
			Value rhs_v = rhs.toConstant();
			return Formulae.evaluateEquality(Opcode.EXPR_eq, lhs_v, rhs_v);
		} else if(lhs.equals(rhs)) {
			return new Formula.Truth(true);
		} else {
			Pair<Polynomial,Polynomial> bs = Formulae.normaliseBounds(lhs,rhs);
			return new ArithmeticEquality(true,bs.getFirst(),bs.getSecond());
		}
	}

	public static Formula notEqual(Polynomial lhs, Polynomial rhs) {
		if (lhs.isConstant() && rhs.isConstant()) {
			Value lhs_v = lhs.toConstant();
			Value rhs_v = rhs.toConstant();
			return Formulae.evaluateEquality(Opcode.EXPR_neq, lhs_v, rhs_v);
		} else if(lhs.equals(rhs)) {
			return new Formula.Truth(false);
		} else {
			Pair<Polynomial,Polynomial> bs = Formulae.normaliseBounds(lhs,rhs);
			return new ArithmeticEquality(false,bs.getFirst(),bs.getSecond());
		}
	}

	public static Formula equal(Atom lhs, Atom rhs) {
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

	public static Formula notEqual(Atom lhs, Atom rhs) {
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

	public static Polynomial sum(Polynomial.Term... terms) {
		Polynomial.Term[] nTerms = Arrays.copyOf(terms, terms.length);
		// FIXME: this is not the ideal way to do this.
		return toNormalForm(nTerms);
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
		public Formula clone(SyntacticItem[] operands) {
			return and((Formula[]) operands);
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
		public Formula clone(SyntacticItem[] operands) {
			return or((Formula[]) operands);
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
		public Formula clone(SyntacticItem[] operands) {
			if (getSign()) {
				return forall((Tuple<VariableDeclaration>) operands[0], (Formula) operands[1]);
			} else {
				return exists((Tuple<VariableDeclaration>) operands[0], (Formula) operands[1]);
			}
		}
	}

	public static class Inequality extends Expr.Operator implements Formula {

		private Inequality(boolean sign, Polynomial lhs, Polynomial rhs) {
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
		public Formula clone(SyntacticItem[] operands) {
			if (getSign()) {
				return lessThan((Polynomial) operands[0],(Polynomial) operands[1]);
			} else {
				return greaterThanOrEqual((Polynomial) operands[0],(Polynomial) operands[1]);
			}
		}
	}

	public static class Equality extends Expr.Operator implements Formula {
		private Equality(boolean sign, Expr lhs, Expr rhs) {
			super(sign ? Opcode.EXPR_eq : Opcode.EXPR_neq, lhs, rhs);
		}

		private Equality(boolean sign, Polynomial[] arr) {
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
		public Formula clone(SyntacticItem[] operands) {
			if (getSign()) {
				return equal((Atom)operands[0],(Atom)operands[1]);
			} else {
				return notEqual((Atom)operands[0],(Atom)operands[1]);
			}
		}

		@Override
		public Formula invert() {
			Atom lhs = getOperand(0);
			Atom rhs = getOperand(1);
			if(getSign()) {
				return notEqual(lhs,rhs);
			} else {
				return equal(lhs,rhs);
			}
		}
	}

	public static class ArithmeticEquality extends Equality implements Formula {
		private ArithmeticEquality(boolean sign, Polynomial lhs, Polynomial rhs) {
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
		public Formula clone(SyntacticItem[] operands) {
			Polynomial lhs = (Polynomial) operands[0];
			Polynomial rhs = (Polynomial) operands[1];
			if (getSign()) {
				return Formula.equal(lhs,rhs);
			} else {
				return notEqual(lhs,rhs);
			}
		}

		@Override
		public Formula invert() {
			Polynomial lhs = getOperand(0);
			Polynomial rhs = getOperand(1);
			if (getSign()) {
				return Formula.notEqual(lhs,rhs);
			} else {
				return equal(lhs,rhs);
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

		/**
		 * A simple implementation of polynomial negation. This simply negates the
		 * coefficient of each term.
		 *
		 * @param p
		 * @return
		 */
		public Polynomial negate() {
			Polynomial.Term[] terms = new Polynomial.Term[size()];

			for (int i = 0; i != terms.length; ++i) {
				terms[i] = getOperand(i).negate();
			}

			return new Polynomial(terms);
		}

		/**
		 * <p>
		 * Add two polynomials together, producing a polynomial in normal form.
		 * To do this, we must add the coefficients for terms which have the
		 * same set of atoms, whilst other terms are incorporated as is. For
		 * example, consider adding <code>2+2x</code> with <code>1+3x+4y</code>.
		 * In this case, we have some terms in common, so the result becomes
		 * <code>(2+1) + (2x+3x) + 4y</code> which is simplified to
		 * <code>3 + 5x + 4y</code>.
		 * </p>
		 *
		 * @param poly
		 * @return
		 */
		public Polynomial add(Polynomial poly) {
			Polynomial.Term[] terms = new Polynomial.Term[this.size() + poly.size()];
			int this_size = this.size();
			//
			for (int i = 0; i != this_size; ++i) {
				terms[i] = this.getOperand(i);
			}
			for (int j = 0; j != poly.size(); ++j) {
				terms[this_size + j] = poly.getOperand(j);
			}
			return toNormalForm(terms);
		}

		public Polynomial add(Polynomial.Term p) {
			Polynomial.Term[] terms = new Polynomial.Term[this.size() + 1];
			for (int i = 0; i != this.size(); ++i) {
				terms[i] = this.getOperand(i);
			}
			terms[this.size()] = p;
			return toNormalForm(terms);
		}

		public Polynomial subtract(Polynomial.Term p) {
			return add(p.negate());
		}

		public Polynomial subtract(Polynomial p) {
			return add(p.negate());
		}

		/**
		 * Multiply two polynomials together. This is done by reusing the add()
		 * function as much as possible, though this may not be the most efficient.
		 * In essence, to multiply one polynomial (e.g. <code>2+2x</code>) by
		 * another (e.g.<code>1+3x+4y</code>) it breaks it down into a series of
		 * multiplications over terms and additions. That is, we multiply each term
		 * from the first polynomial by the second (e.g. <code>2*(1+3x+4y)</code>
		 * and <code>2x*(1+3x+4y)</code>). Then, we add the results together (e.g.
		 * <code>(2+6x+8y) + (2x+6x2+8xy)</code>).
		 *
		 * @param p
		 * @return
		 */
		public Polynomial multiply(Polynomial rhs) {
			int lhs_size = this.size();
			int rhs_size = rhs.size();
			Polynomial.Term[] terms = new Polynomial.Term[lhs_size*rhs_size];

			for (int i = 0; i != lhs_size; ++i) {
				Polynomial.Term lhsTerm = this.getOperand(i);
				int j_base = i * rhs_size;
				for (int j = 0; j != rhs_size; ++j) {
					Polynomial.Term rhsTerm = rhs.getOperand(j);
					terms[j_base+j] = lhsTerm.multiply(rhsTerm);
				}
			}

			return toNormalForm(terms);
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
			private Term(Atom[] operands) {
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

			@Override
			public Term clone(SyntacticItem[] operands) {
				return new Term((Atom[]) operands);
			}

			private static Atom[] append(Value.Int i, Tuple<Atom> variables) {
				Atom[] exprs = new Atom[variables.size()+1];
				exprs[0] = new Formula.Constant(i);
				for(int k=0;k!=variables.size();++k) {
					exprs[k+1] = variables.getOperand(k);
				}
				return exprs;
			}
		}

		@Override
		public Polynomial clone(SyntacticItem[] operands) {
			return Formula.sum((Term[]) operands);
		}
	}

	// ======================================================================
	// Helpers
	// ======================================================================
	/**
	 * Given a list of unsorted and potentially overlapping terms, apply the
	 * necessary simplifications to produce a polynomial in normal form. For
	 * example, given <code>[2, 7x, 4y, -x]</code> we would end up with
	 * <code>[1, 3x, 2y]</code>.
	 *
	 * @param terms
	 * @return
	 */
	public static Polynomial toNormalForm(Polynomial.Term[] terms) {
		mergeTerms(terms);
		// Strip out null entries
		Polynomial.Term[] nTerms = removeNulls(terms);
		// Sort remaining terms
		Arrays.sort(nTerms);
		// Done
		return new Polynomial(nTerms);
	}

	static boolean isZero(Polynomial.Term term) {
		BigInteger coefficient = term.getCoefficient().get();
		return coefficient.equals(BigInteger.ZERO);
	}

	/**
	 * Combine all terms which have the same set of atoms by adding the
	 * coefficients together. For example, [x,2x] is combined into [null,3x].
	 *
	 * @param terms
	 */
	static void mergeTerms(Polynomial.Term[] terms) {
		for (int i = 0; i != terms.length; ++i) {
			Polynomial.Term ith = terms[i];
			if (ith != null) {
				if (isZero(ith)) {
					// Eliminate any zeros which may have arisen during the
					// calculation.
					terms[i] = null;
				} else {
					Tuple<Atom> ithAtoms = ith.getAtoms();
					for (int j = i + 1; j != terms.length; ++j) {
						Polynomial.Term jth = terms[j];
						if (jth != null && ithAtoms.equals(jth.getAtoms())) {
							// We have two overlapping terms, namely i and j.
							// Add them together and assign the result to the
							// jth position.
							terms[j] = ith.add(jth);
							terms[i] = null;
							break;
						}
					}
				}
			}
		}
	}

	/**
	 * This strips out any occurrence of null from the given list of terms.
	 *
	 * @param terms
	 * @return
	 */
	static Polynomial.Term[] removeNulls(Polynomial.Term[] terms) {
		int count = 0;
		for (int i = 0; i != terms.length; ++i) {
			if (terms[i] != null) {
				count = count + 1;
			}
		}
		if (count == 0) {
			return new Polynomial.Term[] { new Polynomial.Term(BigInteger.ZERO) };
		} else {
			//
			Polynomial.Term[] nTerms = new Polynomial.Term[count];
			for (int i = 0, j = 0; i != terms.length; ++i) {
				Polynomial.Term term = terms[i];
				if (term != null) {
					nTerms[j++] = term;
				}
			}
			//
			return nTerms;
		}
	}
}