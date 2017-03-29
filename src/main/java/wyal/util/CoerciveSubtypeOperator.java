package wyal.util;

import java.util.ArrayList;
import java.util.BitSet;

import wyal.lang.NameResolver;
import wyal.lang.NameResolver.AmbiguousNameError;
import wyal.lang.NameResolver.NameNotFoundError;
import wyal.lang.SubtypeOperator;
import wyal.lang.WyalFile;
import wyal.lang.WyalFile.FieldDeclaration;
import wyal.lang.WyalFile.Opcode;
import wyal.lang.WyalFile.Tuple;
import wyal.lang.WyalFile.Type;
import wyal.lang.WyalFile.Declaration.Named;

public class CoerciveSubtypeOperator implements SubtypeOperator {
	private NameResolver resolver;

	public CoerciveSubtypeOperator(NameResolver resolver) {
		this.resolver = resolver;

	}

	@Override
	public boolean isSubtype(Type parent, Type child) throws NameNotFoundError, AmbiguousNameError {
		// A :> B iff (!A & B) == void
		return isVoid(false, parent, true, child, null);
	}

	private boolean isVoid(boolean t1sign, Type t1, boolean t2sign, Type t2, BitSet assumptions) throws NameNotFoundError, AmbiguousNameError {
		assumptions = createAssumptions(t1, t2, assumptions);
		//
		if (isAssumedVoid(t1sign, t1, t2sign, t2, assumptions)) {
			// This represents the "coinductive" case. That is, we have
			// encountered a pair of recursive types whose "voidness" depends
			// circularly on itself. In such case, we assume they are indeed
			// void.
			return true;
		} else {
			setAssumedVoid(t1sign, t1, t2sign, t2, assumptions);
			ArrayList<Atom> truths = new ArrayList<>();
			Worklist worklist = new Worklist();
			worklist.push(t1sign, t1);
			worklist.push(t2sign, t2);
			boolean r = isVoid(truths, worklist, assumptions);
			clearAssumedVoid(t1sign, t1, t2sign, t2, assumptions);
			return r;
		}
	}

	/**
	 * Determine whether or not the intersection of a given list of types (the
	 * worklist) reduces to void or not. This is performed in the context of a
	 * number of ground "atoms" which are known to hold. In essence, this
	 * algorithm exhaustively expands all items on the worklist to form atoms.
	 * The expanded atoms are then checked for consistency.
	 *
	 * is type is equivalent to void. This is a relatively complex operation
	 * which builds up a list of clauses known to hold.
	 *
	 * @param truths
	 *            The set of truths which have been established.
	 * @param worklist
	 *            The set of types currently being expanded
	 * @param assumptions
	 *            The set of assumed subtype relationships
	 * @return
	 * @throws AmbiguousNameError
	 * @throws NameNotFoundError
	 */
	private boolean isVoid(ArrayList<Atom> truths, Worklist worklist, BitSet assumptions) throws NameNotFoundError, AmbiguousNameError {

		// FIXME: there is a bug in the following case which needs to be
		// addressed:
		//
		// {int|null f} & !{int f} & !{null f}
		//
		// The problem is that we need the "pairwise consistency property" in
		// order for this algorithm to be complete. To get that, we must expand
		// records containing union types. Thus, the above should be expanded
		// to:
		//
		// ({int f} & !{int f} & !{null f}) || ({null f} & !{int f} & !{null f})
		//
		// This will now produce the correct result.

		if (worklist.size() == 0) {
			// At this point, we have run out of terms to expand further.
			// Therefore, we have accumulated the complete list of "truths" and
			// we must now attempt to establish whether or not this is
			// consistent. For example, "int & !bool & !int" is not consistent
			// because "int & !int" is not consistent.
			//
			// Therefore, we consider each possible pair of truths looking for
			// consistency.
			for (int i = 0; i != truths.size(); ++i) {
				for (int j = i + 1; j != truths.size(); ++j) {
					if (isVoid(truths.get(i), truths.get(j), assumptions)) {
						return true;
					}
				}
			}
			return false;
		} else {
			// In this case, we still have items on the worklist which need to
			// be processed. That is, broken down into "atomic" terms.
			Worklist.Item<Type> item = worklist.pop();
			Type t = item.type;
			boolean conjunct = item.sign;
			//
			switch (t.getOpcode()) {
			case TYPE_or:
				conjunct = !conjunct;
			case TYPE_and: {
				Type.UnionOrIntersection ut = (Type.UnionOrIntersection) t;
				Type[] operands = ut.getOperands();
				if (conjunct) {
					// Conjunction
					worklist.push(item.sign, operands);
				} else {
					// Disjunction
					for (int i = 0; i != operands.length; ++i) {
						Worklist tmp = (Worklist) worklist.clone();
						tmp.push(item.sign, operands[i]);
						if (!isVoid((ArrayList<Atom>) truths.clone(), tmp, assumptions)) {
							return false;
						}
					}
					return true;
				}
				break;
			}
			case TYPE_not: {
				Type.Negation nt = (Type.Negation) t;
				worklist.push(!conjunct, nt.getElement());
				break;
			}
			case TYPE_nom: {
				Type.Nominal nom = (Type.Nominal) t;
				Named.Type decl = resolver.resolveExactly(nom.getName(),Named.Type.class, nom);
				worklist.push(conjunct, decl.getVariableDeclaration().getType());
				break;
			}
			default:
				truths.add(new Atom(item.sign, (Type.Atom) item.type));
			}
			return isVoid(truths, worklist, assumptions);
		}
	}

	/**
	 * Determine whether the intersection of two arbitrary atoms results in void
	 * or not. Each atom is either a "positive" or "negative" term. The latter
	 * corresponds to negated terms, such as !int or !{int f}.
	 *
	 * @param a
	 * @param b
	 * @param assumptions
	 *            The set of assumed subtype relationships
	 * @return
	 * @throws AmbiguousNameError
	 * @throws NameNotFoundError
	 */
	private boolean isVoid(Atom a, Atom b, BitSet assumptions) throws NameNotFoundError, AmbiguousNameError {
		// At this point, we have several cases left to consider.
		boolean aSign = a.sign;
		boolean bSign = b.sign;
		WyalFile.Opcode aOpcode = a.type.getOpcode();
		WyalFile.Opcode bOpcode = b.type.getOpcode();
		//
		if (aOpcode == bOpcode) {
			// In this case, we are intersecting two atoms of the same kind, of
			// which at least one is positive. For primitive types, this reduces
			// to void is one of them is negative. For non-primitive types, it
			// requires further investigation.
			switch (aOpcode) {
			case TYPE_void:
				// void & void => void
				// !void & void => void
				return true;
			case TYPE_any:
			case TYPE_null:
			case TYPE_bool:
			case TYPE_int:
				// any & !any => void
				// int & !int => void
				return aSign != bSign;
			case TYPE_arr:
				return isVoidArray(aSign, (Type.Array) a.type, bSign, (Type.Array) b.type, assumptions);
			case TYPE_rec:
				return isVoidRecord(aSign, (Type.Record) a.type, bSign, (Type.Record) b.type, assumptions);
			case TYPE_ref:
				throw new RuntimeException("Implement me!");
			case TYPE_fun:
				return isVoidFunction(aSign, (Type.Function) a.type, bSign, (Type.Function) b.type, assumptions);
			default:
				throw new RuntimeException("invalid type encountered: " + aOpcode);
			}
		} else if (aSign && bSign) {
			// We have two positive atoms of different kind. For example, int
			// and {int f}, or int and !bool. This always reduces to void,
			// unless one of them is any.
			return aOpcode != Opcode.TYPE_any && bOpcode != Opcode.TYPE_any;
		} else if (aSign) {
			// We have a positive atom and a negative atom of different kinds.
			// For example, int and !bool or int and !(bool[]). This only
			// reduces to void in the case that one of them is equivalent to
			// void (i.e. is void or !any).
			return aOpcode == Opcode.TYPE_void || bOpcode == Opcode.TYPE_any;
		} else if (bSign) {
			// We have a negative atom and a positive atom of different kinds.
			// For example, !int and bool or !(int[]) and bool[]. This only
			// reduces to void in the case that one of them is equivalent to
			// void (i.e. is void or !any).
			return aOpcode == Opcode.TYPE_any || bOpcode == Opcode.TYPE_void;
		} else {
			// We have two negative atoms of different kinds. For example, !int
			// and !bool or !int[] and !bool. This only reduces to void in the
			// case that one of them is equivalent to void (i.e. is !any).
			return aOpcode == Opcode.TYPE_any || bOpcode == Opcode.TYPE_any;
		}
	}

	/**
	 * <p>
	 * Determine whether the intersection of two array types is void or not. For
	 * example, <code>int[]</code> intersecting with <code>bool[]</code> gives
	 * void. In contrast, intersecting <code>(int|null)[]</code> with
	 * <code>int[]</code> does not give void. Likewise, <code>int[]</code>
	 * intersecting with <code>!(int[])</code> gives void, whilst intersecting
	 * <code>int[]</code> with <code>!(bool[])</code> does not give void.
	 * </p>
	 *
	 * @param lhsSign
	 *            The sign of the first type being intersected. If true, we have
	 *            a positive atom. Otherwise, we have a negative atom.
	 * @param lhs.
	 *            The first type being intersected, referred to as the
	 *            "left-hand side".
	 * @param rhsSign
	 *            The sign of the second type being intersected. If true, we
	 *            have a positive atom. Otherwise, we have a negative atom.
	 * @param rhs
	 *            The second type being intersected, referred to as the
	 *            "right-hand side".
	 * @param assumptions
	 *            The set of assumed subtype relationships
	 * @return
	 * @throws AmbiguousNameError
	 * @throws NameNotFoundError
	 */
	private boolean isVoidArray(boolean lhsSign, Type.Array lhs, boolean rhsSign, Type.Array rhs, BitSet assumptions) throws NameNotFoundError, AmbiguousNameError {
		if (lhsSign != rhsSign) {
			// In this case, we are intersecting two array types, of which at
			// least one is positive. This is void only if there is no
			// intersection of the underlying element types. For example, int[]
			// and bool[] is void, whilst (int|null)[] and int[] is not.
			return isVoid(lhsSign, lhs.getElement(), rhsSign, rhs.getElement(), assumptions);
		} else {
			// In this case, we are intersecting two negative array types. For
			// example, !(int[]) and !(bool[]). This never reduces to void.
			return false;
		}
	}

	/**
	 * <p>
	 * Determine whether the intersection of two record types is void or not.
	 * For example, <code>{int f}</code> intersecting with <code>{int g}</code>
	 * gives void. In contrast, intersecting <code>{int|null f}</code> with
	 * <code>{int f}</code> does not give void. Likewise, <code>{int f}</code>
	 * intersecting with <code>!{int f}</code> gives void, whilst intersecting
	 * <code>{int f}</code> with <code>!{int g}</code> does not give void.
	 * </p>
	 *
	 * @param lhsSign
	 *            The sign of the first type being intersected. If true, we have
	 *            a positive atom. Otherwise, we have a negative atom.
	 * @param lhs.
	 *            The first type being intersected, referred to as the
	 *            "left-hand side".
	 * @param rhsSign
	 *            The sign of the second type being intersected. If true, we
	 *            have a positive atom. Otherwise, we have a negative atom.
	 * @param rhs
	 *            The second type being intersected, referred to as the
	 *            "right-hand side".
	 * @param assumptions
	 *            The set of assumed subtype relationships
	 * @return
	 * @throws AmbiguousNameError
	 * @throws NameNotFoundError
	 */
	private boolean isVoidRecord(boolean lhsSign, Type.Record lhs, boolean rhsSign, Type.Record rhs,
			BitSet assumptions) throws NameNotFoundError, AmbiguousNameError {
		FieldDeclaration[] lhsFields = lhs.getFields();
		FieldDeclaration[] rhsFields = rhs.getFields();
		//
		if (lhsSign || rhsSign) {
			// The sign indicates whether were in the pos-pos case, or in the
			// pos-neg case.
			boolean sign = lhsSign == rhsSign;
			// Attempt to match all fields In the positive-positive case this
			// reduces to void if the fields in either of these differ (e.g.
			// {int f} and {int g}), or if there is no intersection between the
			// same field in either (e.g. {int f} and {bool f}).
			int matches = 0;
			//
			for (int i = 0; i != lhsFields.length; ++i) {
				FieldDeclaration lhsField = lhsFields[i];
				for (int j = 0; j != rhsFields.length; ++j) {
					FieldDeclaration rhsField = rhsFields[j];
					if (!lhsField.getVariableName().equals(rhsField.getVariableName())) {
						continue;
					} else if (isVoid(lhsSign, lhsField.getType(), rhsSign, rhsField.getType(), assumptions) == sign) {
						// For pos-pos case, there is no intersection
						// between these fields and, hence, no intersection
						// overall; for pos-neg case, there is some
						// intersection between these fields which means
						// that some intersections
						// exists overall. For example, consider the case
						// {int f, int|null g} & !{int f, int g}. There is no
						// intersection for field f (i.e. since int & !int =
						// void), whilst there is an intersection for field g
						// (i.e. since int|null & !int = null). Hence, we can
						// conclude that there is an intersection between them
						// with {int f, null g}.
						return sign;
					} else {
						matches = matches + 1;
					}
				}
			}

			if (matches < lhsFields.length && !rhs.isOpen()) {
				// We have matched fewer fields than contained in the lhs.
				// However, if the rhs is an open record, then it can match the
				// remainder. Otherwise, there is no match here. In the pos-pos
				// case, this means there is no intersection. In the pos-neg
				// case, this means there is an intersection.
				return sign;
			} else if (matches < rhsFields.length && !lhs.isOpen()) {
				// We have matched fewer fields than contained in the rhs.
				// However, if the lhs is an open record, then it can match the
				// remainder. Otherwise, there is no match here. In the pos-pos
				// case, this means there is no intersection. In the pos-neg
				// case, this means there is an intersection.
				return sign;
			} else {
				// If we get here, then: for pos-pos case, all fields have
				// intersection; for pos-neg case, no fields have intersection.
				return !sign;
			}
		} else {
			// In this case, we are intersecting two negative record types. For
			// example, !({int f}) and !({int g}). This never reduces to void.
			return false;
		}
	}

	/**
	 * <p>
	 * Determine whether the intersection of two function types is void or not.
	 * For example, <code>function(int)->(int)</code> intersecting with
	 * <code>function(bool)->(int)</code> gives void. In contrast, intersecting
	 * <code>function(int|null)->(int)</code> with
	 * <code>function(int)->(int)</code> does not give void. Likewise,
	 * <code>function(int)->(int)</code> intersecting with
	 * <code>!function(int)->(int)</code> gives void, whilst intersecting
	 * <code>function(int)->(int)</code> with
	 * <code>!function(bool)->(int)</code> does not give void.
	 * </p>
	 *
	 *
	 * @param lhsSign
	 *            The sign of the first type being intersected. If true, we have
	 *            a positive atom. Otherwise, we have a negative atom.
	 * @param lhs.
	 *            The first type being intersected, referred to as the
	 *            "left-hand side".
	 * @param rhsSign
	 *            The sign of the second type being intersected. If true, we
	 *            have a positive atom. Otherwise, we have a negative atom.
	 * @param rhs
	 *            The second type being intersected, referred to as the
	 *            "right-hand side".
	 * @param assumptions
	 *            The set of assumed subtype relationships private boolean
	 * @throws AmbiguousNameError
	 * @throws NameNotFoundError
	 */
	public boolean isVoidFunction(boolean lhsSign, Type.Function lhs, boolean rhsSign, Type.Function rhs,
			BitSet assumptions) throws NameNotFoundError, AmbiguousNameError {
		if (lhsSign || rhsSign) {
			// The sign indicates whether were in the pos-pos case, or in the
			// pos-neg case.
			Tuple<Type> lhsParameters = lhs.getParameters();
			Tuple<Type> rhsParameters = rhs.getParameters();
			//
			if(isVoidParameters(!lhsSign, lhsParameters, !rhsSign, rhsParameters, assumptions)) {
				return true;
			} else if(isVoidParameters(lhsSign, lhsParameters, rhsSign, rhsParameters, assumptions)) {
				return true;
			} else {
				return false;
			}
		} else {
			// In this case, we are intersecting two negative function types.
			// For example, !(function(int)->(int)) and
			// !(function(bool)->(int)). This never reduces to void.
			return false;
		}
	}

	public boolean isVoidParameters(boolean lhsSign, Tuple<Type> lhs, boolean rhsSign, Tuple<Type> rhs,
			BitSet assumptions) throws NameNotFoundError, AmbiguousNameError {
		boolean sign = lhsSign == rhsSign;
		//
		if (lhs.size() != rhs.size()) {
			// Different number of parameters. In either pos-pos or neg-neg
			// cases, this reduces to void. Otherwise, it doesn't.
			return sign;
		} else {
			for (int i = 0; i != lhs.size(); ++i) {
				Type lhsParameter = lhs.getOperand(i);
				Type rhsParameter = rhs.getOperand(i);
				if (isVoid(lhsSign, lhsParameter, rhsSign, rhsParameter, assumptions) == sign) {
					// For pos-pos / neg-neg case, there is no intersection
					// between this parameterand, hence, no intersection
					// overall; for pos-neg case, there is some
					// intersection between these parameters which means
					// that some intersections exists overall. For example,
					// consider the case (int,int|null) & !(int,int). There is
					// no intersection for first parameter (i.e. since int &
					// !int = void), whilst there is an intersection for second
					// parameter (i.e. since int|null & !int = null). Hence, we
					// can conclude that there is an intersection between them
					// with (int,null).
					return sign;
				}
			}
			// If we get here, then: for pos-pos case, all parameters have
			// intersection; for pos-neg case, no parameters have intersection.
			return !sign;
		}
	}

	// ========================================================================
	// Helpers
	// ========================================================================

	private static class Worklist extends ArrayList<Worklist.Item<Type>> {

		/**
		 *
		 */
		private static final long serialVersionUID = 1L;

		private static class Item<T extends Type> {
			public final boolean sign;
			public final T type;

			public Item(boolean sign, T type) {
				this.type = type;
				this.sign = sign;
			}
		}

		public void push(boolean sign, Type type) {
			add(new Item(sign, type));
		}

		public void push(boolean sign, Type[] types) {
			for (int i = 0; i != types.length; ++i) {
				add(new Item(sign, types[i]));
			}
		}

		public Item<Type> pop() {
			Item<Type> i = get(size() - 1);
			remove(size() - 1);
			return i;
		}

		@Override
		public Worklist clone() {
			Worklist wl = new Worklist();
			wl.addAll(this);
			return wl;
		}
	}

	private static class Atom extends Worklist.Item<Type.Atom> {
		public Atom(boolean sign, Type.Atom type) {
			super(sign, type);
		}

		@Override
		public String toString() {
			if (sign) {
				return type.toString();
			} else {
				return "!" + type;
			}
		}
	}

	private boolean isAssumedVoid(boolean lhsSign, Type lhs, boolean rhsSign, Type rhs, BitSet assumptions) {
		if (assumptions != null) {
			return assumptions.get(indexOf(lhsSign, lhs, rhsSign, rhs));
		} else {
			return false;
		}
	}

	private void setAssumedVoid(boolean lhsSign, Type lhs, boolean rhsSign, Type rhs, BitSet assumptions) {
		if (assumptions != null) {
			assumptions.set(indexOf(lhsSign, lhs, rhsSign, rhs));
		}
	}

	private void clearAssumedVoid(boolean lhsSign, Type lhs, boolean rhsSign, Type rhs, BitSet assumptions) {
		if (assumptions != null) {
			assumptions.clear(indexOf(lhsSign, lhs, rhsSign, rhs));
		}
	}

	private int indexOf(boolean lhsSign, Type lhs, boolean rhsSign, Type rhs) {
		int lhsSize = lhs.getParent().size();
		int rhsSize = rhs.getParent().size();
		int lhsIndex = lhs.getIndex();
		int rhsIndex = rhs.getIndex();
		if (lhsSign) {
			lhsIndex += lhsSize;
		}
		if (rhsSign) {
			rhsIndex += rhsSize;
		}
		return (lhsIndex * rhsSize * 2) + rhsIndex;
	}

	private static BitSet createAssumptions(Type lhs, Type rhs, BitSet assumptions) {
		if (assumptions != null) {
			return assumptions;
		} else if (lhs.getParent() != null && rhs.getParent() != null) {
			// We multiply by 2 here because we want to encode both positive and
			// negative signs.
			int lhsSize = lhs.getParent().size() * 2;
			int rhsSize = rhs.getParent().size() * 2;
			return new BitSet(lhsSize * rhsSize);
		} else {
			return null;
		}
	}
}
