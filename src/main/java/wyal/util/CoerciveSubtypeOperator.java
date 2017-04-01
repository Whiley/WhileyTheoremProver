package wyal.util;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.BitSet;

import wyal.lang.NameResolver;
import wyal.lang.NameResolver.ResolutionError;
import wyal.lang.SubtypeOperator;
import wyal.lang.WyalFile;
import wyal.lang.WyalFile.FieldDeclaration;
import wyal.lang.WyalFile.Name;
import wyal.lang.WyalFile.Opcode;
import wyal.lang.WyalFile.Tuple;
import wyal.lang.WyalFile.Type;
import wyal.lang.WyalFile.Declaration.Named;

public class CoerciveSubtypeOperator implements SubtypeOperator {
	protected NameResolver resolver;

	public CoerciveSubtypeOperator(NameResolver resolver) {
		this.resolver = resolver;

	}

	@Override
	public Result isSubtype(Type parent, Type child) throws ResolutionError {
		// A :> B iff (!A & B) == void
		return isVoid(false, parent, true, child, null);
	}

	protected Result isVoid(boolean t1sign, Type t1, boolean t2sign, Type t2, BitSet assumptions) throws ResolutionError {
		assumptions = createAssumptions(t1, t2, assumptions);
		//
		if (isAssumedVoid(t1sign, t1, t2sign, t2, assumptions)) {
			// This represents the "coinductive" case. That is, we have
			// encountered a pair of recursive types whose "voidness" depends
			// circularly on itself. In such case, we assume they are indeed
			// void.
			return Result.True;
		} else {
			setAssumedVoid(t1sign, t1, t2sign, t2, assumptions);
			ArrayList<Atom> truths = new ArrayList<>();
			Worklist worklist = new Worklist();
			worklist.push(t1sign, t1, null);
			worklist.push(t2sign, t2, null);
			Result r = isVoid(truths, worklist, assumptions);
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
	 * @throws ResolutionError
	 */
	protected Result isVoid(ArrayList<Atom> truths, Worklist worklist, BitSet assumptions) throws ResolutionError {

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
			Result result = Result.False;

			for (int i = 0; i != truths.size(); ++i) {
				Atom ith = truths.get(i);
				for (int j = i + 1; j != truths.size(); ++j) {
					Atom jth = truths.get(j);
					Result r = isVoid(ith, jth, assumptions);
					if (r == Result.True) {
						return r;
					} else if (r == Result.Unknown) {
						result = Result.Unknown;
					}
				}
			}
			return result;
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
					worklist.push(item.sign, operands, item.constraints);
				} else {
					// Disjunction
					Result result = Result.True;
					//
					for (int i = 0; i != operands.length; ++i) {
						Worklist tmp = (Worklist) worklist.clone();
						tmp.push(item.sign, operands[i], item.constraints);
						Result r = isVoid((ArrayList<Atom>) truths.clone(), tmp, assumptions);
						if (r == Result.False) {
							// If a single clause of the disjunct is definitely
							// not void, then the whole thing is not void.
							return r;
						} else if(r == Result.Unknown) {
							// If a single clause of the disjunct is unknown,
							// then we cannot conclude that the whole thing is
							// void. However, we could still conclude that it
							// definitely isn't false if a subsequent clause is
							// determined to be false.
							result = Result.Unknown;
						}
					}
					return result;
				}
				break;
			}
			case TYPE_not: {
				Type.Negation nt = (Type.Negation) t;
				worklist.push(!conjunct, nt.getElement(), item.constraints);
				break;
			}
			case TYPE_nom: {
				Type.Nominal nom = (Type.Nominal) t;
				Named.Type decl = resolver.resolveExactly(nom.getName(), Named.Type.class);
				Name[] constraints = item.constraints;
				if(decl.getInvariant().size() > 0) {
					// Indicates a constrained type
					Name resolvedName = resolver.resolveFully(new Name(decl.getName()));
					constraints = append(constraints,resolvedName);
				}
				worklist.push(conjunct, decl.getVariableDeclaration().getType(), constraints);
				break;
			}

			default:
				truths.add(new Atom(item.sign, (Type.Atom) item.type, item.constraints));
			}
			return isVoid(truths, worklist, assumptions);
		}
	}

	protected Name[] append(Name[] lhs, Name rhs) {
		if(rhs == null) {
			return lhs;
		} else {
			lhs = Arrays.copyOf(lhs, lhs.length+1);
			lhs[lhs.length-1] = rhs;
			return lhs;
		}
	}

	protected Result isVoid(Atom a, Atom b, BitSet assumptions) throws ResolutionError {
		boolean aConstrained = a.constraints.length > 0;
		boolean bConstrained = b.constraints.length > 0;
		Result r = isRawVoid(a,b,assumptions);
		//
		if(Arrays.equals(a.constraints, b.constraints)) {
			// In this case, we are dealing with types from the same nominal
			// type. Therefore, we can treat this as being equivalent to the raw
			// case.
			return r;
		}
		if(a.sign == b.sign) {
			if(r == Result.True) {

			} else {

			}
		} else {
			if(r == Result.True) {

			} else {

			}
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
	 * @throws ResolutionError
	 */
	protected Result isRawVoid(Atom a, Atom b, BitSet assumptions) throws ResolutionError {
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
				return Result.True;
			case TYPE_any:
			case TYPE_null:
			case TYPE_bool:
			case TYPE_int:
				// any & !any => void
				// int & !int => void
				return (aSign != bSign) ? Result.True : Result.False;
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
			return (aOpcode != Opcode.TYPE_any && bOpcode != Opcode.TYPE_any) ? Result.True : Result.False;
		} else if (aSign) {
			// We have a positive atom and a negative atom of different kinds.
			// For example, int and !bool or int and !(bool[]). This only
			// reduces to void in the case that one of them is equivalent to
			// void (i.e. is void or !any).
			return (aOpcode == Opcode.TYPE_void || bOpcode == Opcode.TYPE_any) ? Result.True : Result.False;
		} else if (bSign) {
			// We have a negative atom and a positive atom of different kinds.
			// For example, !int and bool or !(int[]) and bool[]. This only
			// reduces to void in the case that one of them is equivalent to
			// void (i.e. is void or !any).
			return (aOpcode == Opcode.TYPE_any || bOpcode == Opcode.TYPE_void) ? Result.True : Result.False;
		} else {
			// We have two negative atoms of different kinds. For example, !int
			// and !bool or !int[] and !bool. This only reduces to void in the
			// case that one of them is equivalent to void (i.e. is !any).
			return (aOpcode == Opcode.TYPE_any || bOpcode == Opcode.TYPE_any) ? Result.True : Result.False;
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
	 * @throws ResolutionError
	 */
	protected Result isVoidArray(boolean lhsSign, Type.Array lhs, boolean rhsSign, Type.Array rhs, BitSet assumptions) throws ResolutionError {
		if (lhsSign || rhsSign) {
			// In this case, we are intersecting two array types, of which at
			// least one is positive. This is void only if there is no
			// intersection of the underlying element types. For example, int[]
			// and bool[] is void, whilst (int|null)[] and int[] is not.
			return isVoid(lhsSign, lhs.getElement(), rhsSign, rhs.getElement(), assumptions);
		} else {
			// In this case, we are intersecting two negative array types. For
			// example, !(int[]) and !(bool[]). This never reduces to void.
			return Result.False;
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
	 * @throws ResolutionError
	 */
	protected Result isVoidRecord(boolean lhsSign, Type.Record lhs, boolean rhsSign, Type.Record rhs,
			BitSet assumptions) throws ResolutionError {
		FieldDeclaration[] lhsFields = lhs.getFields();
		FieldDeclaration[] rhsFields = rhs.getFields();
		//
		if (lhsSign || rhsSign) {
			// The sign indicates whether were in the pos-pos case, or in the
			// pos-neg case.
			Result sign = lhsSign == rhsSign ? Result.True : Result.False;
			// Attempt to match all fields In the positive-positive case this
			// reduces to void if the fields in either of these differ (e.g.
			// {int f} and {int g}), or if there is no intersection between the
			// same field in either (e.g. {int f} and {bool f}).
			int matches = 0;
			boolean isUnknown = false;
			//
			for (int i = 0; i != lhsFields.length; ++i) {
				FieldDeclaration lhsField = lhsFields[i];
				for (int j = 0; j != rhsFields.length; ++j) {
					FieldDeclaration rhsField = rhsFields[j];
					if (!lhsField.getVariableName().equals(rhsField.getVariableName())) {
						continue;
					} else {
						Result r = isVoid(lhsSign, lhsField.getType(), rhsSign, rhsField.getType(), assumptions);
						if(r == sign) {
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
						} else if(r == Result.Unknown) {
							// In this case, the intersection of a field was
							// undetermined. We don't return unknown immediately
							// in this case, since its possible that a definite
							// case can still be made that an intersection
							// exists between some other field pairing.
							isUnknown = true;
						} else {
							matches = matches + 1;
						}
					}
				}
			}

			if(isUnknown) {
				return Result.Unknown;
			} else if (matches < lhsFields.length && !rhs.isOpen()) {
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
				return sign == Result.True ? Result.False : Result.True;
			}
		} else {
			// In this case, we are intersecting two negative record types. For
			// example, !({int f}) and !({int g}). This never reduces to void.
			return Result.False;
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
	 * @throws ResolutionError
	 */
	public Result isVoidFunction(boolean lhsSign, Type.Function lhs, boolean rhsSign, Type.Function rhs,
			BitSet assumptions) throws ResolutionError {
		if (lhsSign || rhsSign) {
			// The sign indicates whether were in the pos-pos case, or in the
			// pos-neg case.
			Tuple<Type> lhsParameters = lhs.getParameters();
			Tuple<Type> rhsParameters = rhs.getParameters();
			//
			Result pr = isVoidParameters(!lhsSign, lhsParameters, !rhsSign, rhsParameters, assumptions);
			Result rr = isVoidParameters(lhsSign, lhsParameters, rhsSign, rhsParameters, assumptions);
			if(pr == Result.True || rr == Result.True) {
				return Result.True;
			} else if(pr == Result.False && rr == Result.False) {
				return Result.False;
			} else {
				return Result.Unknown;
			}
		} else {
			// In this case, we are intersecting two negative function types.
			// For example, !(function(int)->(int)) and
			// !(function(bool)->(int)). This never reduces to void.
			return Result.False;
		}
	}

	public Result isVoidParameters(boolean lhsSign, Tuple<Type> lhs, boolean rhsSign, Tuple<Type> rhs,
			BitSet assumptions) throws ResolutionError {
		Result sign = lhsSign == rhsSign ? Result.True : Result.False;
		//
		if (lhs.size() != rhs.size()) {
			// Different number of parameters. In either pos-pos or neg-neg
			// cases, this reduces to void. Otherwise, it doesn't.
			return Result.False;
		} else {
			boolean isUnknown = false;
			//
			for (int i = 0; i != lhs.size(); ++i) {
				Type lhsParameter = lhs.getOperand(i);
				Type rhsParameter = rhs.getOperand(i);
				Result r = isVoid(lhsSign, lhsParameter, rhsSign, rhsParameter, assumptions);
				if (r == sign) {
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
				} else if(r == Result.Unknown) {
					isUnknown = true;
				}
			}
			if(isUnknown) {
				// Result in at least one case was undetermined. Hence, cannot
				// make any concrete determination here.
				return Result.Unknown;
			} else if(sign == Result.True) {
				// for pos-pos case, all parameters have intersection. Hence,
				// there is a possible intersection.
				return Result.False;
			} else {
				// for pos-neg case, no parameters have intersection. Hence, no
				// possible intersection.
				return Result.True;
			}
		}
	}

	// ========================================================================
	// Helpers
	// ========================================================================

	protected static class Worklist extends ArrayList<Worklist.Item<Type>> {

		/**
		 *
		 */
		private static final long serialVersionUID = 1L;

		protected static class Item<T extends Type> {
			public final boolean sign;
			public final T type;
			public final Name[] constraints;

			public Item(boolean sign, T type, Name[] constraints) {
				this.type = type;
				this.sign = sign;
				this.constraints = constraints;
			}
		}

		public Item<Type> top() {
			return get(size() - 1);
		}

		public void push(boolean sign, Type type, Name[] constraints) {
			add(new Item(sign, type, constraints));
		}

		public void push(boolean sign, Type[] types, Name[] constraints) {
			for (int i = 0; i != types.length; ++i) {
				add(new Item(sign, types[i], constraints));
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

	protected static class Atom extends Worklist.Item<Type.Atom> {
		public Atom(boolean sign, Type.Atom type, Name[] constraints) {
			super(sign, type, constraints);
		}

		@Override
		public String toString() {
			String r = type.toString();
			if (sign) {
				return r;
			} else {
				return "!" + r;
			}
		}
	}

	protected boolean isAssumedVoid(boolean lhsSign, Type lhs, boolean rhsSign, Type rhs, BitSet assumptions) {
		if (assumptions != null) {
			return assumptions.get(indexOf(lhsSign, lhs, rhsSign, rhs));
		} else {
			return false;
		}
	}

	protected void setAssumedVoid(boolean lhsSign, Type lhs, boolean rhsSign, Type rhs, BitSet assumptions) {
		if (assumptions != null) {
			assumptions.set(indexOf(lhsSign, lhs, rhsSign, rhs));
		}
	}

	protected void clearAssumedVoid(boolean lhsSign, Type lhs, boolean rhsSign, Type rhs, BitSet assumptions) {
		if (assumptions != null) {
			assumptions.clear(indexOf(lhsSign, lhs, rhsSign, rhs));
		}
	}

	protected int indexOf(boolean lhsSign, Type lhs, boolean rhsSign, Type rhs) {
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

	protected static BitSet createAssumptions(Type lhs, Type rhs, BitSet assumptions) {
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
