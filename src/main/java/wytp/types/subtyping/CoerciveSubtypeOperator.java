package wytp.types.subtyping;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.BitSet;

import wyal.lang.NameResolver;
import wyal.lang.NameResolver.ResolutionError;
import wyal.lang.SyntacticHeap;
import wyal.lang.WyalFile;
import wyal.lang.WyalFile.FieldDeclaration;
import wyal.lang.WyalFile.Name;
import wyal.lang.WyalFile.Opcode;
import wyal.lang.WyalFile.Tuple;
import wyal.lang.WyalFile.Type;
import wyal.lang.WyalFile.Declaration.Named;
import wytp.types.SubtypeOperator;
import wytp.types.SubtypeOperator.Result;

public class CoerciveSubtypeOperator implements SubtypeOperator {
	protected NameResolver resolver;

	public CoerciveSubtypeOperator(NameResolver resolver) {
		this.resolver = resolver;

	}

	@Override
	public Result isSubtype(Type parent, Type child) throws ResolutionError {
		// FIXME: we can do better in some situations here. For example, if we
		// have the same nominal types they can cancel each other.
		Term<?> lhsMaxTerm = new Term<>(false, parent, true);
		Term<?> rhsMaxTerm = new Term<>(true, child, true);
		boolean max = isVoid(lhsMaxTerm, rhsMaxTerm, null);
		// FIXME: I don't think this logic is correct yet for some reason.
		if(!max) {
			return Result.False;
		} else {
			Term<?> lhsMinTerm = new Term<>(false, parent, false);
			Term<?> rhsMinTerm = new Term<>(true, child, false);
			boolean min = isVoid(lhsMinTerm, rhsMinTerm, null);
			if(min) {
				return Result.True;
			} else {
				return Result.Unknown;
			}
		}
	}

	protected boolean isVoid(Term<?> lhs, Term<?> rhs, BitSet assumptions) throws ResolutionError {
		assumptions = createAssumptions(lhs, rhs, assumptions);
		//
		if (isAssumedVoid(lhs, rhs, assumptions)) {
			// This represents the "coinductive" case. That is, we have
			// encountered a pair of recursive types whose "voidness" depends
			// circularly on itself. In such case, we assume they are indeed
			// void.
			return true;
		} else {
			setAssumedVoid(lhs, rhs, assumptions);
			ArrayList<Atom<?>> truths = new ArrayList<>();
			Worklist worklist = new Worklist();
			worklist.push(lhs);
			worklist.push(rhs);
			boolean r = isVoid(truths, worklist, assumptions);
			clearAssumedVoid(lhs, rhs, assumptions);
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
	protected boolean isVoid(ArrayList<Atom<?>> truths, Worklist worklist, BitSet assumptions) throws ResolutionError {

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
				Atom<?> ith = truths.get(i);
				for (int j = i + 1; j != truths.size(); ++j) {
					Atom<?> jth = truths.get(j);
					if (isVoid(ith, jth, assumptions)) {
						return true;
					}
				}
			}
			return false;
		} else {
			// In this case, we still have items on the worklist which need to
			// be processed. That is, broken down into "atomic" terms.
			Term<Type> item = worklist.pop();
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
					worklist.push(item.sign, operands, item.maximise);
				} else {
					// Disjunction
					for (int i = 0; i != operands.length; ++i) {
						Worklist tmp = (Worklist) worklist.clone();
						tmp.push(item.sign, operands[i], item.maximise);
						if (!isVoid((ArrayList<Atom<?>>) truths.clone(), tmp, assumptions)) {
							// If a single clause of the disjunct is definitely
							// not void, then the whole thing is not void.
							return false;
						}
					}
					return true;
				}
				break;
			}
			case TYPE_not: {
				Type.Negation nt = (Type.Negation) t;
				worklist.push(!item.sign, nt.getElement(), !item.maximise);
				break;
			}
			case TYPE_nom: {
				Type.Nominal nom = (Type.Nominal) t;
				Named.Type decl = resolver.resolveExactly(nom.getName(), Named.Type.class);
				if (item.maximise || decl.getInvariant().size() == 0) {
					worklist.push(item.sign, decl.getVariableDeclaration().getType(), item.maximise);
				} else if (item.sign) {
					// Corresponds to void, so we're done on this path.
					return true;
				}
				break;
			}

			default:
				truths.add(new Atom(item.sign, (Type.Atom) item.type, item.maximise));
			}
			return isVoid(truths, worklist, assumptions);
		}
	}

	protected Name[] append(Name[] lhs, Name rhs) {
		if (rhs == null) {
			return lhs;
		} else {
			lhs = Arrays.copyOf(lhs, lhs.length + 1);
			lhs[lhs.length - 1] = rhs;
			return lhs;
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
	protected boolean isVoid(Atom a, Atom b, BitSet assumptions) throws ResolutionError {
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
				return (aSign != bSign) ? true : false;
			case TYPE_arr:
				return isVoidArray((Atom<Type.Array>) a, (Atom<Type.Array>) b, assumptions);
			case TYPE_rec:
				return isVoidRecord((Atom<Type.Record>) a, (Atom<Type.Record>) b, assumptions);
			case TYPE_ref:
				throw new RuntimeException("Implement me!");
			case TYPE_fun:
				return isVoidFunction((Atom<Type.Function>) a, (Atom<Type.Function>) b, assumptions);
			default:
				throw new RuntimeException("invalid type encountered: " + aOpcode);
			}
		} else if (aSign && bSign) {
			// We have two positive atoms of different kind. For example, int
			// and {int f}, or int and !bool. This always reduces to void,
			// unless one of them is any.
			return (aOpcode != Opcode.TYPE_any && bOpcode != Opcode.TYPE_any) ? true : false;
		} else if (aSign) {
			// We have a positive atom and a negative atom of different kinds.
			// For example, int and !bool or int and !(bool[]). This only
			// reduces to void in the case that one of them is equivalent to
			// void (i.e. is void or !any).
			return (aOpcode == Opcode.TYPE_void || bOpcode == Opcode.TYPE_any) ? true : false;
		} else if (bSign) {
			// We have a negative atom and a positive atom of different kinds.
			// For example, !int and bool or !(int[]) and bool[]. This only
			// reduces to void in the case that one of them is equivalent to
			// void (i.e. is void or !any).
			return (aOpcode == Opcode.TYPE_any || bOpcode == Opcode.TYPE_void) ? true : false;
		} else {
			// We have two negative atoms of different kinds. For example, !int
			// and !bool or !int[] and !bool. This only reduces to void in the
			// case that one of them is equivalent to void (i.e. is !any).
			return (aOpcode == Opcode.TYPE_any || bOpcode == Opcode.TYPE_any) ? true : false;
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
	protected boolean isVoidArray(Atom<Type.Array> lhs, Atom<Type.Array> rhs, BitSet assumptions)
			throws ResolutionError {
		if (lhs.sign || rhs.sign) {
			Term<?> lhsTerm = new Term<>(lhs.sign, lhs.type.getElement(), lhs.maximise);
			Term<?> rhsTerm = new Term<>(rhs.sign, rhs.type.getElement(), rhs.maximise);
			// In this case, we are intersecting two array types, of which at
			// least one is positive. This is void only if there is no
			// intersection of the underlying element types. For example, int[]
			// and bool[] is void, whilst (int|null)[] and int[] is not.
			return isVoid(lhsTerm, rhsTerm, assumptions);
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
	 * @throws ResolutionError
	 */
	protected boolean isVoidRecord(Atom<Type.Record> lhs, Atom<Type.Record> rhs, BitSet assumptions)
			throws ResolutionError {
		FieldDeclaration[] lhsFields = lhs.type.getFields();
		FieldDeclaration[] rhsFields = rhs.type.getFields();
		//
		if (lhs.sign || rhs.sign) {
			// The sign indicates whether were in the pos-pos case, or in the
			// pos-neg case.
			boolean sign = lhs.sign == rhs.sign;
			// Attempt to match all fields In the positive-positive case this
			// reduces to void if the fields in either of these differ (e.g.
			// {int f} and {int g}), or if there is no intersection between the
			// same field in either (e.g. {int f} and {bool f}).
			int matches = 0;
			//
			for (int i = 0; i != lhsFields.length; ++i) {
				FieldDeclaration lhsField = lhsFields[i];
				Term<?> lhsTerm = new Term<>(lhs.sign, lhsField.getType(), lhs.maximise);
				for (int j = 0; j != rhsFields.length; ++j) {
					FieldDeclaration rhsField = rhsFields[j];
					if (!lhsField.getVariableName().equals(rhsField.getVariableName())) {
						continue;
					} else {
						Term<?> rhsTerm = new Term<>(rhs.sign, rhsField.getType(), rhs.maximise);
						if (sign == isVoid(lhsTerm, rhsTerm, assumptions)) {
							// For pos-pos case, there is no intersection
							// between these fields and, hence, no intersection
							// overall; for pos-neg case, there is some
							// intersection between these fields which means
							// that some intersections
							// exists overall. For example, consider the case
							// {int f, int|null g} & !{int f, int g}. There is
							// no
							// intersection for field f (i.e. since int & !int =
							// void), whilst there is an intersection for field
							// g
							// (i.e. since int|null & !int = null). Hence, we
							// can
							// conclude that there is an intersection between
							// them
							// with {int f, null g}.
							return sign;
						} else {
							matches = matches + 1;
						}
					}
				}
			}

			if (matches < lhsFields.length && !rhs.type.isOpen()) {
				// We have matched fewer fields than contained in the lhs.
				// However, if the rhs is an open record, then it can match the
				// remainder. Otherwise, there is no match here. In the pos-pos
				// case, this means there is no intersection. In the pos-neg
				// case, this means there is an intersection.
				return sign;
			} else if (matches < rhsFields.length && !lhs.type.isOpen()) {
				// We have matched fewer fields than contained in the rhs.
				// However, if the lhs is an open record, then it can match the
				// remainder. Otherwise, there is no match here. In the pos-pos
				// case, this means there is no intersection. In the pos-neg
				// case, this means there is an intersection.
				return sign;
			} else {
				// If we get here, then: for pos-pos case, all fields have
				// intersection; for pos-neg case, no fields have intersection.
				return sign == true ? false : true;
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
	 * @throws ResolutionError
	 */
	public boolean isVoidFunction(Atom<Type.Function> lhs, Atom<Type.Function> rhs, BitSet assumptions)
			throws ResolutionError {
		if (lhs.sign || rhs.sign) {
			// The sign indicates whether were in the pos-pos case, or in the
			// pos-neg case.
			Tuple<Type> lhsParameters = lhs.type.getParameters();
			Tuple<Type> rhsParameters = rhs.type.getParameters();
			Tuple<Type> lhsReturns = lhs.type.getParameters();
			Tuple<Type> rhsReturns = rhs.type.getParameters();
			//
			// FIXME: should maximise be flipped for parameters as well?
			//
			boolean pr = isVoidParameters(!lhs.sign, lhs.maximise, lhsParameters, !rhs.sign, rhs.maximise,
					rhsParameters, assumptions);
			boolean rr = isVoidParameters(lhs.sign, lhs.maximise, lhsReturns, rhs.sign, rhs.maximise, rhsReturns,
					assumptions);
			return pr || rr;
		} else {
			// In this case, we are intersecting two negative function types.
			// For example, !(function(int)->(int)) and
			// !(function(bool)->(int)). This never reduces to void.
			return false;
		}
	}

	public boolean isVoidParameters(boolean lhsSign, boolean lhsMax, Tuple<Type> lhs, boolean rhsSign, boolean rhsMax,
			Tuple<Type> rhs, BitSet assumptions) throws ResolutionError {
		boolean sign = lhsSign == rhsSign;
		//
		if (lhs.size() != rhs.size()) {
			// Different number of parameters. In either pos-pos or neg-neg
			// cases, this reduces to void. Otherwise, it doesn't.
			return false;
		} else {
			//
			for (int i = 0; i != lhs.size(); ++i) {
				Type lhsParameter = lhs.getOperand(i);
				Type rhsParameter = rhs.getOperand(i);
				Term<?> lhsTerm = new Term<>(lhsSign, lhsParameter, lhsMax);
				Term<?> rhsTerm = new Term<>(rhsSign, rhsParameter, rhsMax);
				if (sign == isVoid(lhsTerm, rhsTerm, assumptions)) {
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
			if (sign == true) {
				// for pos-pos case, all parameters have intersection. Hence,
				// there is a possible intersection.
				return false;
			} else {
				// for pos-neg case, no parameters have intersection. Hence, no
				// possible intersection.
				return true;
			}
		}
	}

	// ========================================================================
	// Helpers
	// ========================================================================

	protected static class Worklist extends ArrayList<Term<Type>> {
		/**
		 *
		 */
		private static final long serialVersionUID = 1L;

		public Term<Type> top() {
			return get(size() - 1);
		}

		public void push(Term item) {
			add(item);
		}

		public void push(boolean sign, Type type, boolean maximise) {
			add(new Term(sign, type, maximise));
		}

		public void push(boolean sign, Type[] types, boolean maximise) {
			for (int i = 0; i != types.length; ++i) {
				add(new Term(sign, types[i], maximise));
			}
		}

		public Term<Type> pop() {
			Term<Type> i = get(size() - 1);
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

	protected static class Term<T extends Type> {
		public final boolean sign;
		public final T type;
		public final boolean maximise;

		public Term(boolean sign, T type, boolean maximise) {
			this.type = type;
			this.sign = sign;
			this.maximise = maximise;
		}
	}

	protected static class Atom<T extends Type.Atom> extends Term<T> {
		public Atom(boolean sign, T type, boolean maximise) {
			super(sign, type, maximise);
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

	protected boolean isAssumedVoid(Term<?> lhs, Term<?> rhs, BitSet assumptions) {
		if (assumptions != null) {
			return assumptions.get(indexOf(lhs.sign, lhs.type, rhs.sign, rhs.type));
		} else {
			return false;
		}
	}

	protected void setAssumedVoid(Term<?> lhs, Term<?> rhs, BitSet assumptions) {
		if (assumptions != null) {
			assumptions.set(indexOf(lhs.sign, lhs.type, rhs.sign, rhs.type));
		}
	}

	protected void clearAssumedVoid(Term<?> lhs, Term<?> rhs, BitSet assumptions) {
		if (assumptions != null) {
			assumptions.clear(indexOf(lhs.sign, lhs.type, rhs.sign, rhs.type));
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

	protected static BitSet createAssumptions(Term<?> lhs, Term<?> rhs, BitSet assumptions) {
		SyntacticHeap lhsHeap = lhs.type.getParent();
		SyntacticHeap rhsHeap = rhs.type.getParent();
		if (assumptions != null) {
			return assumptions;
		} else if (lhsHeap != null && rhsHeap != null) {
			// We multiply by 2 here because we want to encode both positive and
			// negative signs.
			int lhsSize = lhsHeap.size() * 2;
			int rhsSize = rhsHeap.size() * 2;
			return new BitSet(lhsSize * rhsSize);
		} else {
			return null;
		}
	}
}
