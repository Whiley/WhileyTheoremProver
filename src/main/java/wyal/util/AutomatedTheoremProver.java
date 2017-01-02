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
		Heap heap = new Heap();
		Formula result = translate(false, decl.getBody(), heap);
		print(0,result);
	}

	private Formula translate(boolean sign, Block blk, Heap heap) {
		Formula[] fs = new Formula[blk.size()];
		for (int i = 0; i != blk.size(); ++i) {
			fs[i] = translate(sign, blk.getOperand(i), heap);
		}
		if (sign) {
			return new Conjunct(fs);
		} else {
			return new Disjunct(fs);
		}
	}

	private Formula translate(boolean sign, Stmt stmt, Heap heap) {
		switch (stmt.getOpcode()) {
		case STMT_ifthen:
			// TODO: fix me!
		default:
			// An expression of some kind which cannot be represented directly
			// as a formula. Therefore, we need to convert it into an equality.
			Term t = translate((Expr) stmt, heap);
			if (sign) {
				return heap.add(new Equality(t, heap.TRUE));
			} else {
				return heap.add(new Equality(t, heap.FALSE));
			}
		}
	}

	private Term translate(Expr expr, Heap heap) {
		switch (expr.getOpcode()) {
		case EXPR_const:
			return translate((Expr.Constant) expr,heap);
		default:
			throw new RuntimeException("Unknown bytecode encountered: " + expr.getOpcode());
		}
	}

	private Term translate(Expr.Constant expr, Heap heap) {
		Constant val = (Constant) expr.getOperand(0);
		Object data = val.data;
		switch(val.getOpcode()) {
		case CONST_bool:
			boolean b = (Boolean) data;
			if (b) {
				return heap.TRUE;
			} else {
				return heap.FALSE;
			}
		default:
			throw new IllegalArgumentException("implement me --- " + expr);
		}
	}

	private enum Opcode {
		TRUE,
		FALSE,
		CONJUNCT,
		DISJUNCT,
		EQUALITY,
		INEQUALITY,
		POLYNOMIAL
	};

	/**
	 * A heap is a container for items which make up the state(s) required for
	 * solving a given assertion.
	 *
	 * @author David J. Pearce
	 *
	 */
	private class Heap {
		/**
		 * Represents the constant value true. This is always the first item in
		 * the heap.
		 */
		public final TruthValue TRUE;
		/**
		 * Represents the constant value false. This is always the second item
		 * in the heap.
		 */
		public final TruthValue FALSE;
		/**
		 * The list of declared variables over which terms of the heap are
		 * defined.
		 */
		private VariableDeclaration[] environment;

		/**
		 * The array of all items in the heap. Some of these may not be
		 * reachable from any given state and could, in principle, be garbage
		 * collected. However, all items are required to be distinct. That is,
		 * no two identical items are permitted to exist.
		 */
		private Item[] items;

		/**
		 * The number of elements in items currently in use. As more item are
		 * added, this increases accordingly. When the number matches the
		 * current size of items, then we must expand it accordingly.
		 */
		private int size;

		public Heap() {
			this.items = new Item[16];
			this.TRUE = add(new TruthValue(true));
			this.FALSE = add(new TruthValue(false));
		}

		/**
		 * Add a new item to the heap. This will ensure that the item is, in
		 * fact, unique. Otherwise, it will identify the existing representative
		 * for this item.
		 *
		 * @param item
		 * @return
		 */
		public <T extends Item> T add(T item) {
			// Check whether item already exists in this heap
			for(int i=0;i!=size;++i) {
				Item other = items[i];
				if(other.equivalent(item)) {
					// Yes, item already exists
					return (T) other;
				}
			}
			// No, item does not already exist
			int index = allocate(item);
			return (T) items[index];
		}

		/**
		 * Allocate a given item into this heap. The item cannot already have
		 * been allocated to a heap.
		 */
		private int allocate(Item item) {
			if (item.owner != null) {
				throw new IllegalArgumentException("item already seated");
			} else {
				int index = size;
				item.owner = this;
				item.index = index;
				items[index] = item;
				size = size + 1;
				return index;
			}
		}
	}

	private class State {
		/**
		 * The space in which the terms making up this and other states exist.
		 */
		private Heap heap;
		/**
		 * The set of heap terms which are cases; that is, disjunctions of
		 * terms. Each of these disjunctions corresponds to a split point.
		 */
		private BitSet cases;
		/**
		 * The set of universal (or non-ground) truths; that is, heap terms
		 * involving a non-ground variable. Each of these can be instantiated as
		 * necessary to establish a contradiction.
		 */
		private BitSet universalTruths;
		/**
		 * The set of ground truths. That is heap terms involving constants
		 * and/or ground variables. These are used to directly prove a
		 * contradiction.
		 */
		private BitSet groundTruths;

	}

	private class VariableDeclaration {
		/**
		 * Indicates whether this variable is universally or existentially
		 * quantified.
		 */
		private final boolean universal;
		/**
		 * The given type of this variable.
		 */
		private final Type type;
		/**
		 * The given name of this variable, which is primarily used for
		 * error-reporting and debugging purposes.
		 */
		private final Identifier name;
		/**
		 * Indicates the scope in which this variable is declared. That is, the
		 * set of universal variables in whose scope this variable is declated.
		 */
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

	private static abstract class Item {

		/**
		 * The owner identifies the heap in which this item resides.
		 */
		private Heap owner;

		/**
		 * The index identifiers the index within the heap where this item is
		 * allocated.
		 */
		private int index;

		/**
		 * The opcode defines the type of item we have.
		 */
		private final Opcode opcode;

		/**
		 * The sub-components of this item (if any)
		 */
		private final Item[] components;

		public Item(Opcode opcode, Item... children) {
			this.opcode = opcode;
			this.components = children;
		}

		public Opcode getOpcode() {
			return opcode;
		}

		public Item get(int i) {
			return components[i];
		}

		public int size() {
			return components.length;
		}

		/**
		 * Determine whether or not this expression is ground. That is, whether
		 * or not it (or a sub-expression) refers to a non-ground variable.
		 *
		 * @return
		 */
		public boolean isGround() {
			for (int i = 0; i < components.length; ++i) {
				if (!components[i].isGround()) {
					return false;
				}
			}
			return true;
		}

		/**
		 * Determine whether two items are equivalent or not.
		 *
		 * @param i
		 * @return
		 */
		public boolean equivalent(Item other) {
			Item[] other_components = other.components;
			if (opcode == other.opcode && components.length == other_components.length) {
				for (int i = 0; i != other_components.length; ++i) {
					Item my_child = components[i];
					Item f_child = other_components[i];
					if (my_child.index != f_child.index) {
						return false;
					}
				}
				return true;
			}
			return false;
		}
	}

	private static abstract class Formula extends Item {

		public Formula(Opcode opcode, Item... components) {
			super(opcode, components);
		}

	}

	/**
	 * A conjunct is a sequence of one or more sub-formulas, all of which have
	 * to be true for the conjunct to be considered true.
	 *
	 * @author David J. Pearce
	 *
	 */
	private static class Conjunct extends Formula {

		public Conjunct(Formula... children) {
			super(Opcode.CONJUNCT,children);
		}

		@Override
		public Formula get(int i) {
			return (Formula) super.get(i);
		}
	}

	/**
	 * A disjunct is a sequence of one or more sub-formulas, all of which have
	 * to be false for the conjunct to be considered false.
	 *
	 * @author David J. Pearce
	 *
	 */
	private static class Disjunct extends Formula {

		public Disjunct(Formula... children) {
			super(Opcode.DISJUNCT,children);
		}

		@Override
		public Formula get(int i) {
			return (Formula) super.get(i);
		}
	}

	private static class Equality extends Formula {

		public Equality(Term lhs, Term rhs) {
			super(Opcode.EQUALITY,lhs, rhs);
		}

	}

	/**
	 * An inequality is of the form "0 <= P", where P is a polynomial.
	 *
	 * @author David J. Pearce
	 *
	 */
	private static class Inequality extends Formula {

		public Inequality(Polynomial lhs) {
			super(Opcode.INEQUALITY,lhs);
		}

	}

	/**
	 * Terms represent expressions which evaluate to values of a given type.
	 *
	 * @author David J. Pearce
	 *
	 */
	private static abstract class Term extends Item {

		public Term(Opcode opcode, Item... components) {
			super(opcode,components);
		}

		/**
		 * Get the type to which this term evaluates
		 *
		 * @return
		 */
		public abstract Type[] getTypes();
	}

	private static class TruthValue extends Term {
		public TruthValue(boolean sign) {
			super(sign ? Opcode.TRUE : Opcode.FALSE);
		}

		@Override
		public Type[] getTypes() {
			return null;
		}

		@Override
		public boolean isGround() {
			return true;
		}
	}

	private static class Polynomial extends Term {
		private final Type.Int type;

		public Polynomial(Type.Int type) {
			super(Opcode.POLYNOMIAL);
			this.type = type;
		}

		@Override
		public Type[] getTypes() {
			return new Type[] { type };
		}

	}

	private void print(int indent, Formula formula) {
		switch(formula.getOpcode()) {
		case CONJUNCT: {
			for(int i=0;i!=formula.size();++i) {
				print(indent, (Formula) formula.get(i));
			}
			break;
		}
		case DISJUNCT: {
			for(int i=0;i!=formula.size();++i) {
				indent(indent);System.out.println("case:");
				print(indent+1,(Formula) formula.get(i));
			}
			break;
		}
		case EQUALITY: {
			indent(indent);
			print(formula.get(0));
			System.out.print(" == ");
			print(formula.get(1));
			System.out.println();
			break;
		}
		case INEQUALITY: {
			throw new IllegalArgumentException("implement me");
		}
		default:
			indent(indent);
			print(formula);
			System.out.println();
		}
	}

	private void print(Item item) {
		switch(item.getOpcode()) {
		case TRUE:
			System.out.print("true");
			break;
		case FALSE:
			System.out.print("false");
			break;
		default:
			throw new IllegalArgumentException("implement me --- " + item);
		}
	}

	private void indent(int amount) {
		amount = amount * 4;
		for(int i=0;i!=amount;++i) {
			System.out.print(" ");
		}
	}
}
