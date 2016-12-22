package wyal.util;

import java.util.ArrayList;
import java.util.BitSet;

import wyal.lang.SyntacticItem;
import wyal.lang.WyalFile;
import wyal.lang.WyalFile.*;

public class AutomatedTheoremProver {
	/**
	 * The enclosing WyAL file being checked.
	 */
	private final WyalFile parent;

	public AutomatedTheoremProver(final WyalFile parent) {
		this.parent = parent;
	}

	public void check() {
		for (int i = 0; i != parent.size(); ++i) {
			SyntacticItem item = parent.getSyntacticItem(i);
			if (item instanceof WyalFile.Declaration.Assert) {
				check((WyalFile.Declaration.Assert) item);
			}
		}
	}

	private void check(WyalFile.Declaration.Assert decl) {

	}

	private class State {
		/**
		 * The list of declared variables in scope.
		 */
		private VariableDeclaration[] environment;
		/**
		 *
		 */
		private Heap heap;
		/**
		 * The set of terms which are cases; that is, disjunctions of terms.
		 * Each of these disjunctions corresponds to a split point.
		 */
		private BitSet cases;
		/**
		 * The set of universal (or non-ground) truths; that is, terms involving
		 * a non-ground variable. Each of these can be instantiated as necessary
		 * to establish a contradiction.
		 */
		private BitSet universalTruths;
		/**
		 * The set of ground truths. That is terms involving constants and/or
		 * ground variables. These are used to directly prove a contradiction.
		 */
		private BitSet groundTruths;

	}

	private class VariableDeclaration {
		private final boolean universal;
		private final Type type;
		private final Identifier name;
		private final VariableDeclaration[] scope;

		public VariableDeclaration(boolean universal, Type type, Identifier name, VariableDeclaration... scope) {
			this.universal = universal;
			this.type = type;
			this.name = name;
			this.scope = scope;
		}

		public VariableDeclaration[] getScope() {
			return scope;
		}

		public boolean isUniveral() {
			return universal;
		}

		public Type getType() {
			return type;
		}

		public Identifier getName() {
			return name;
		}

		/**
		 * Determine whether or not this corresponds to a ground variable
		 * declaration. That is, in effect, a named constant.
		 *
		 * @return
		 */
		public boolean isGround() {
			return !universal && scope.length == 0;
		}
	}

	private abstract class Item {
		/**
		 * Determine whether or not this expression is ground. That is, whether
		 * or not it (or a sub-expression) refers to a non-ground variable.
		 *
		 * @return
		 */
		abstract boolean isGround();
	}

	private abstract class Formula extends Item {

	}

	/**
	 * A conjunct is a sequence of one or more sub-formulas, all of which have
	 * to be true for the conjunct to be considered true.
	 *
	 * @author David J. Pearce
	 *
	 */
	private class Conjunct extends Formula {

		@Override
		boolean isGround() {
			// TODO Auto-generated method stub
			return false;
		}

	}

	/**
	 * A disjunct is a sequence of one or more sub-formulas, all of which have
	 * to be false for the conjunct to be considered false.
	 *
	 * @author David J. Pearce
	 *
	 */
	private class Disjunct extends Formula {

		@Override
		boolean isGround() {
			// TODO Auto-generated method stub
			return false;
		}

	}

	/**
	 * An inequality is of the form "0 <= P", where P is a polynomial.
	 *
	 * @author David J. Pearce
	 *
	 */
	private class Inequality extends Formula {

		@Override
		boolean isGround() {
			// TODO Auto-generated method stub
			return false;
		}
	}

	/**
	 * Terms represent expressions which evaluate to values of a given type.
	 *
	 * @author David J. Pearce
	 *
	 */
	private abstract class Term extends Item {

		/**
		 * Get the type to which this term evaluates
		 *
		 * @return
		 */
		public abstract Type[] getTypes();
	}

	private class Invoke extends Term {
		private final Type.Function type;

		@Override
		boolean isGround() {
			// TODO Auto-generated method stub
			return false;
		}

		@Override
		public Type[] getTypes() {
			return new Type[]{type.getReturns()};
		}
	}

	private class Polynomial extends Term {
		private final Type.Int type;

		public Polynomial(Type.Int type) {
			this.type = type;
		}

		@Override
		public boolean isGround() {
			return false;
		}

		@Override
		public Type[] getTypes() {
			return new Type[]{type};
		}
	}

	private class Heap {
		private Item[] items;
		private int size;
	}
}
