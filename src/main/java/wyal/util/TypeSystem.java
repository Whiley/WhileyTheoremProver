package wyal.util;

import java.io.IOException;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.BitSet;

import wyal.lang.SyntacticHeap;
import wyal.lang.SyntacticItem;
import wyal.lang.WyalFile;
import wyal.lang.WyalFile.Declaration;
import wyal.lang.WyalFile.Identifier;
import wyal.lang.WyalFile.Name;
import wyal.lang.WyalFile.Opcode;
import wyal.lang.WyalFile.Type;
import wyal.lang.WyalFile.Declaration.Named;
import wybs.util.ResolveError;
import wycc.util.ArrayUtils;
import wyal.lang.WyalFile.FieldDeclaration;

public class TypeSystem {
	private final WyalFile parent;

	public TypeSystem(WyalFile parent) {
		this.parent = parent;
	}

	public boolean isEffectiveRecord(Type type) {
		return expandAsEffectiveRecord(type) != null;
	}

	public boolean isEffectiveArray(Type type) {
		return expandAsEffectiveArray(type) != null;
	}

	/**
	 * For a given type, extract its effective record type. For example, the
	 * type <code>({int x, int y}|{int x, int z})</code> has effective record
	 * type <code>{int x, ...}</code>. The following illustrates some more
	 * cases:
	 *
	 * <pre>
	 * {int x, int y} | null    ==> null
	 * {int x, int y} | {int x} ==> null
	 * {int x, int y} | {int x, bool y} ==> {int x, int|bool y}
	 * {int x, int y} & null    ==> null
	 * {int x, int y} & {int x} ==> null
	 * {int x, int y} & {int x, int|bool y} ==> {int x, int y}
	 * </pre>
	 *
	 * @param type
	 * @return
	 */
	public Type.EffectiveRecord expandAsEffectiveRecord(Type type) {
		Type r = expandAsEffectiveType(true,type);
		if(r instanceof Type.EffectiveRecord) {
			return (Type.EffectiveRecord) r;
		} else {
			return null;
		}
	}

	/**
	 * Extract the readable array type from a given type. For example, the type
	 * <code>(int[])|(bool[])</code> has a readable array type of
	 * <code>(int|bool)[]</code>.
	 *
	 * @param type
	 * @return
	 */
	public Type.EffectiveArray expandAsEffectiveArray(Type type) {
		Type r = expandAsEffectiveType(true,type);
		if(r instanceof Type.EffectiveArray) {
			return (Type.EffectiveArray) r;
		} else {
			return null;
		}
	}

	/**
	 * Expand a given type by "exactly one level". The exact meaning of this
	 * subtle. Roughly speaking, the intuition is to expand a nominal type if
	 * its encountered into its underlying type. But, critically, we don't
	 * expand the underlying type itself. The reason for the latter is simply
	 * that, in the presence of recursive types, this could lead to an infinite
	 * expansion.
	 *
	 * The complicating factors here are the present of "type connectives". That
	 * is unions, intersections or negations. These are not counted as a "level"
	 * and, instead, their bounds are expanded. Given the following type
	 * declarations:
	 *
	 * <pre>
	 * type neg is (int x) where x < 0
	 * type pos is (int x) where x > 0
	 * </pre>
	 *
	 * Then, the following expansions are to be expected:
	 *
	 * <pre>
	 * neg            ==> int
	 * {neg x, pos y} ==> {neg x, pos y}
	 * !neg           ==> !int
	 * neg|pos        ==> int
	 * </pre>
	 *
	 * @param type
	 *            The type to be expanded by exactly one level
	 * @return
	 * @throws IOException
	 * @throws ResolveError
	 */
	public Type expandAsEffectiveType(boolean sign, Type type) {
		//
		switch(type.getOpcode()) {
		case TYPE_not: {
			Type.Negation neg = (Type.Negation) type;
			return expandAsEffectiveType(!sign,neg.getElement());
		}
		case TYPE_nom: {
			Type.Nominal nom = (Type.Nominal) type;
			Named.Type decl = resolveAsDeclaredType(nom.getName());
			return expandAsEffectiveType(sign,decl.getVariableDeclaration().getType());
		}
		case TYPE_and:
		case TYPE_or: {
			// Hmm, this is tasty line. It does exactly what I want though :)
			boolean union = sign == (type.getOpcode() == Opcode.TYPE_or);
			Type[] children = expandAsReadableTypes(sign,(Type[])type.getOperands());
			if(union) {
				return union(children);
			} else {
				return intersect(children);
			}
		}
		default:
			if(sign) {
				return type;
			} else {
				return new Type.Negation(type);
			}
		}
	}

	/**
	 * Expand a sequence of zero or more types by one level.
	 *
	 * @param sign
	 * @param types
	 * @return
	 */
	public Type[] expandAsReadableTypes(boolean sign, Type... types) {
		Type[] nTypes = new Type[types.length];
		for(int i=0;i!=types.length;++i) {
			nTypes[i] = expandAsEffectiveType(sign, types[i]);
		}
		return nTypes;
	}

	// ======================================================================
	// Negate
	// ======================================================================
	public static Type negate(Type type) {
		if(type instanceof Type.Negation){
			Type.Negation nt = (Type.Negation) type;
			return nt.getElement();
		} else if(type instanceof Type.Union) {
			Type.Union union = (Type.Union) type;
			return intersect(negate(union.getOperands()));
		} else if(type instanceof Type.Intersection) {
			Type.Intersection intersection = (Type.Intersection) type;
			return union(negate(intersection.getOperands()));
		} else {
			return new Type.Negation(type);
		}
	}

	public static Type[] negate(Type... types) {
		Type[] result = new Type[types.length];
		for(int i=0;i!=result.length;++i) {
			result[i] = negate(types[i]);
		}
		return result;
	}

	// ======================================================================
	// Union
	// ======================================================================

	/**
	 * Take a sequence of zero or more types and produce a minimal union of
	 * them.
	 *
	 * @param types
	 * @return
	 */
	public static Type union(Type... types) {
		//
		Type[] rs = Arrays.copyOf(types, types.length);
		// Any union containing any equals any
		int anyIndex = ArrayUtils.firstIndexOf(rs, new Type.Any());
		if(anyIndex >= 0) { return rs[anyIndex]; }
		// Any in an intersection can be dropped
		rs = ArrayUtils.removeAll(rs, new Type.Void());
		rs = ArrayUtils.removeAll(rs, null);
		// remove any duplicates
		rs = ArrayUtils.sortAndRemoveDuplicates(rs);
		//
		// FIXME: we can do better here by handling subsumed types.
		//
		// FIXME: we also need to flatten nest types properly
		//
		if(rs.length == 0) {
			return new Type.Void();
		} else if(rs.length == 1) {
			return rs[0];
		} else if(areInstances(types,Type.Record.class)){
			return new UnionOfRecords(rs);
		} else if(areInstances(types, Type.Array.class)){
			return new UnionOfArrays(rs);
		} else {
			return new Type.Union(rs);
		}
	}

	private static <T> boolean areInstances(T[] items, Class<? extends T> kind) {
		for(int i=0;i!=items.length;++i) {
			if(!kind.isInstance(items[i])) {
				return false;
			}
		}
		//
		return true;
	}

	private static class UnionOfRecords extends WyalFile.Type.Union implements Type.EffectiveRecord {

		public UnionOfRecords(Type...records) {
			super(records);
		}

		@Override
		public Type.Record getOperand(int i) {
			return (Type.Record) super.getOperand(i);
		}

		@Override
		public FieldDeclaration[] getFields() {
			Type.Record result = getOperand(0);
			for(int i=1;i!=size();++i) {
				result = unionReadableRecords(result,getOperand(i));
			}
			return result.getFields();
		}

		private static Type.Record unionReadableRecords(Type.Record lhs, Type.Record rhs) {
			ArrayList<FieldDeclaration> fields = new ArrayList<>();
			for (int i = 0; i != lhs.size(); ++i) {
				for (int j = 0; j != rhs.size(); ++j) {
					FieldDeclaration lhsField = lhs.getOperand(i);
					FieldDeclaration rhsField = rhs.getOperand(j);
					Identifier lhsFieldName = lhsField.getVariableName();
					Identifier rhsFieldName = rhsField.getVariableName();
					if (lhsFieldName.equals(rhsFieldName)) {
						Type type = union(lhsField.getType(), rhsField.getType());
						fields.add(new FieldDeclaration(type, lhsFieldName));
					}
				}
			}
			// FIXME: this should potentially create an open record in some
			// cases
			return new Type.Record(fields.toArray(new FieldDeclaration[fields.size()]));
		}
	}

	private static class UnionOfArrays extends WyalFile.Type.Union implements Type.EffectiveArray {

		public UnionOfArrays(Type...arrays) {
			super(arrays);
		}

		@Override
		public Type.Array getOperand(int i) {
			return (Type.Array) super.getOperand(i);
		}

		@Override
		public Type getReadableElement() {
			Type[] results = new Type[size()];
			for(int i=0;i!=size();++i) {
				results[i] = getOperand(i).getElement();

			}
			return union(results);
		}
	}

	// ======================================================================
	// Intersection
	// ======================================================================

	/**
	 * Take a sequence of zero or more types and produce a minimal union of
	 * them.
	 *
	 * @param types
	 * @return
	 */
	public static Type intersect(Type... types) {
		//
		Type[] rs = Arrays.copyOf(types, types.length);
		// At this point, we need to handle distribution of
		// intersections over negations.
		for(int i=0;i!=types.length;++i) {
			Type child = types[i];
			if(child instanceof Type.Union) {
				// Distribute outer intersection over this inner
				return distributeUnion(i,types);
			}
		}
		// intersect atoms
		for (int i = 0; i < rs.length; ++i) {
			for (int j = i + 1; j < rs.length; ++j) {
				intersectAtoms(i, j, rs);
			}
		}
		// Any intersection containing void equals void
		int voidIndex = ArrayUtils.firstIndexOf(rs, new Type.Void());
		if(voidIndex >= 0) { return rs[voidIndex]; }
		// Any in an intersection can be dropped
		rs = ArrayUtils.removeAll(rs, new Type.Any());
		rs = ArrayUtils.removeAll(rs, null);
		// remove any duplicates
		rs = ArrayUtils.sortAndRemoveDuplicates(rs);
		// intersect terms together
		//
		if(rs.length == 0) {
			return new Type.Any();
		} else if(rs.length == 1) {
			return rs[0];
		} else {
			return new Type.Intersection(rs);
		}
	}

	/**
	 * Assumes one or more children which are to be intersected together, where
	 * the ith is a union. Then distribute over the union.
	 *
	 * @param ith
	 *            The child at this point is the union we are distrubuting over.
	 * @param children
	 *            One or more types which should be intersected together
	 * @return
	 */
	private static Type distributeUnion(int ith, Type[] children) {
		Type.Union union = (Type.Union) children[ith];
		Type[] clauses = new Type[union.size()];
		for(int j=0;j!=union.size();++j) {
			Type[] nChildren = Arrays.copyOf(children, children.length);
			nChildren[ith] = union.getOperand(j);
			clauses[j] = intersect(nChildren);

		}
		// At this point, we recursively call expand one level again. This is
		// perhaps slightly inefficient, but is necessary to ensure that nested
		// unions are taken care of.
		return union(clauses);
	}

	private static void intersectAtoms(int i, int j, Type[] types) {
		Type ith = types[i];
		Type jth = types[j];
		boolean lhsNegative = ith instanceof Type.Negation;
		boolean rhsNegative = jth instanceof Type.Negation;
		if(lhsNegative && rhsNegative) {
			intersectNegativeNegative(i,j,types);
		} else if(lhsNegative) {
			intersectNegativePositive(i,j,types);
		} else if(rhsNegative) {
			intersectNegativePositive(j,i,types);
		} else {
			intersectPositivePositive(i,j,types);
		}
	}

	private static void intersectNegativeNegative(int i, int j, Type[] types) {
		// FIXME: could do more here
	}

	private static void intersectNegativePositive(int i, int j, Type[] types) {
		Type.Negation ith = (Type.Negation) types[i];
		Type ith_element = ith.getElement();
		Type jth = types[j];
		if(jth instanceof Type.Any) {
			types[i] = null;
			types[j] = ith;
		} else if(ith_element.equals(jth)) {
			// FIXME: should do more here as there are other cases where we
			// should reduce to void. For example, if jth element is
			// supertype of ith.
			types[i] = types[j] = new Type.Void();
		} else if(ith_element instanceof Type.Nominal || jth instanceof Type.Nominal) {
			// There's not much we can do here, since we can't be sure
			// whether or not the Nominal types having anything in common.
		} else {
			// ith is subsumed
			types[i] = new Type.Any();
		}
	}

	private static void intersectPositivePositive(int i, int j, Type[] types) {
		Type ith = types[i];
		Type jth = types[j];
		Opcode lhsKind = ith.getOpcode();
		Opcode rhsKind = jth.getOpcode();
		//
		if(lhsKind == Opcode.TYPE_any || rhsKind == Opcode.TYPE_any) {
			// In this case, there is nothing really to do. Basically
			// intersection something with any gives something. We don't remove
			// the any type from the array at this stage, since it will be
			// removed lated on.
		} else if(lhsKind == Opcode.TYPE_nom || rhsKind == Opcode.TYPE_nom) {
			// In this case, there is also nothing to do. That's because
			// we don't know what a nominal is, and hence we are
			// essentially treating it as being the same as any.
		} else if (lhsKind != rhsKind) {
			// There are no situations where this results in a positive
			// outcome. Therefore, set both parties to be void. This
			// guarantees the void will be caught at the earliest possible
			// moment,
			types[i] = types[j] = new Type.Void();
		} else {
			// Now check individual cases
			switch (lhsKind) {
			case TYPE_void:
			case TYPE_bool:
			case TYPE_int:
				// For primitives, it's enough to know that they have
				// the same kind.
				types[i] = null;
				break;
			case TYPE_arr:
				types[i] = null;
				types[j] = intersectArrays((Type.Array)ith,(Type.Array)jth);
				break;
			case TYPE_rec:
				types[i] = null;
				types[j] = intersectRecords((Type.Record)ith,(Type.Record)jth);
				break;
			}
			// FIXME: could do more here
		}
	}

	private static Type intersectArrays(Type.Array lhs, Type.Array rhs) {
		return new Type.Array(intersect(lhs.getElement(), rhs.getElement()));
	}

	private static Type intersectRecords(Type.Record lhs, Type.Record rhs) {
		//
		if (lhs == null) {
			return rhs;
		} else {
			FieldDeclaration[] lhsFields = lhs.getFields();
			FieldDeclaration[] rhsFields = rhs.getFields();
			if(lhsFields.length != rhsFields.length) {
				// FIXME: need support for open records here
				return new Type.Void();
			}
			ArrayList<FieldDeclaration> fields = new ArrayList<>();
			for (int i = 0; i != lhsFields.length; ++i) {
				for(int j=0; j != rhsFields.length; ++j) {
					FieldDeclaration lhsField = lhsFields[i];
					FieldDeclaration rhsField = rhsFields[j];
					Identifier lhsFieldName = lhsField.getVariableName();
					Identifier rhsFieldName = rhsField.getVariableName();
					if (lhsFieldName.equals(rhsFieldName)) {
						fields.add(new FieldDeclaration(intersect(lhsField.getType(), rhsField.getType()),
								lhsFieldName));
					}
				}
			}
			if (fields.size() != lhsFields.length) {
				// FIXME: support open records here
				return new Type.Void();
			} else {
				return new Type.Record(fields.toArray(new FieldDeclaration[fields.size()]));
			}
		}
	}

	/**
	 * Check whether a given "parent" type is indeed a supertype of a given
	 * "child". In the presence of arbitrary recursive types with unions,
	 * intersections and negations, this is a challenging operation.
	 *
	 * @param parent
	 * @param child
	 * @return
	 */
	public boolean isSubtype(Type parent, Type child) {
		// A :> B iff (!A & B) == void
		return isVoid(false, parent, true, child, null);
	}

	private boolean isVoid(boolean t1sign, Type t1, boolean t2sign, Type t2, BitSet assumptions) {
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
	 */
	private boolean isVoid(ArrayList<Atom> truths, Worklist worklist, BitSet assumptions) {

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
				Named.Type decl = resolveAsDeclaredType(nom.getName());
				// FIXME: this will cause infinite loops!!!
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
	 */
	private boolean isVoid(Atom a, Atom b, BitSet assumptions) {
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
				throw new RuntimeException("Implement me!");
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
	 */
	private boolean isVoidArray(boolean lhsSign, Type.Array lhs, boolean rhsSign, Type.Array rhs, BitSet assumptions) {
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
	 */
	private boolean isVoidRecord(boolean lhsSign, Type.Record lhs, boolean rhsSign, Type.Record rhs,
			BitSet assumptions) {
		FieldDeclaration[] lhsFields = lhs.getFields();
		FieldDeclaration[] rhsFields = rhs.getFields();
		// FIXME: We need to sort fields above by their name in order to
		// eliminate the order in which they are written as being relevant.
		if (lhsSign || rhsSign) {
			// The sign indicates whether were in the pos-pos case, or in the
			// pos-neg case.
			boolean sign = lhsSign == rhsSign;
			// In this case, we are intersecting two positive record types. This
			// reduces to void if the fields in either of these differ (e.g.
			// {int f} and {int g}), or if there is no intersection between the
			// same field in either (e.g. {int f} and {bool f}).
			if (lhsFields.length != rhsFields.length) {
				// We have a differing number of fields and, hence, no
				// intersection of underlying types is possible. In the pos-pos
				// case, this indicates no intersection is possible overall. In
				// the pos-neg case, then intersection exists.
				return sign;
			} else {
				// We have the same number of fields. Now, we need to check that
				// each field as the same name, and that their types intersect.
				for (int i = 0; i != lhsFields.length; ++i) {
					FieldDeclaration lhsField = lhsFields[i];
					FieldDeclaration rhsField = rhsFields[i];
					if (!lhsField.getVariableName().equals(rhsField.getVariableName())) {
						// The fields have different names. In the pos-pos
						// case, this indicates no intersection is possible. For
						// pos-neg case, intersection exists.
						return sign;
					} else if (isVoid(lhsSign, lhsField.getType(), rhsSign, rhsField.getType(), assumptions) == sign) {
						// For pos-pos case, there is no intersection between
						// these fields and, hence, no intersection overall; for
						// pos-neg case, there is some intersection between
						// these fields which means that some intersections
						// exists overall. For example, consider the case
						// {int f, int|null g} & !{int f, int g}. There is no
						// intersection for field f (i.e. since int & !int =
						// void), whilst there is an intersection for field g
						// (i.e. since int|null & !int = null). Hence, we can
						// conclude that there is an intersection between them
						// with {int f, null g}.
						return sign;
					}
				}
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

	// ========================================================================
	// Resolution
	// ========================================================================

	public <T extends Declaration.Named> T resolveAsDeclaration(Name name, Class<T> kind) {
		Identifier[] components = name.getComponents();
		// FIXME: need to handle case where more than one component
		Identifier last = components[components.length - 1];
		// Look through the enclosing file first!
		SyntacticHeap parent = name.getParent();
		for (int i = 0; i != parent.size(); ++i) {
			SyntacticItem item = parent.getSyntacticItem(i);
			if (item instanceof Declaration.Named) {
				Declaration.Named nd = (Declaration.Named) item;
				if (nd.getName().equals(last) && kind.isInstance(nd)) {
					return (T) nd;
				}
			}
		}
		return null;
	}

	public Declaration.Named resolveAsDeclaration(Name name) {
		Identifier[] components = name.getComponents();
		// FIXME: need to handle case where more than one component
		Identifier last = components[components.length - 1];
		// Look through the enclosing file first!
		SyntacticHeap parent = name.getParent();
		for (int i = 0; i != parent.size(); ++i) {
			SyntacticItem item = parent.getSyntacticItem(i);
			if (item instanceof Declaration.Named) {
				Declaration.Named nd = (Declaration.Named) item;
				if (nd.getName().equals(last)) {
					return nd;
				}
			}
		}
		// FIXME: consider imported files as well
		throw new IllegalArgumentException("unable to resolve " + Arrays.toString(name.getComponents()) + " as type");
	}

	/**
	 * Expand a given named declaration on the assumption that it is a type.
	 * This will initially look for the given name in the enclosing file, before
	 * considering those import statements included in the appropriate order.
	 *
	 * @param name
	 * @return
	 */
	public Declaration.Named.Type resolveAsDeclaredType(Name name) {
		Identifier[] components = name.getComponents();
		// FIXME: need to handle case where more than one component
		Identifier last = components[components.length - 1];
		// Look through the enclosing file first!
		SyntacticHeap parent = name.getParent();
		for (int i = 0; i != parent.size(); ++i) {
			SyntacticItem item = parent.getSyntacticItem(i);
			if (item instanceof Declaration.Named.Type) {
				Declaration.Named.Type nd = (Declaration.Named.Type) item;
				if (nd.getName().equals(last)) {
					return nd;
				}
			}
		}
		// FIXME: consider imported files as well
		throw new IllegalArgumentException("unable to resolve " + Arrays.toString(name.getComponents()) + " as type");
	}

	// ========================================================================
	// Helpers
	// ========================================================================

	private static class Worklist extends ArrayList<Worklist.Item<Type>> {

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
