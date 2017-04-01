package wyal.util;

import java.io.IOException;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.BitSet;
import java.util.List;

import wyal.lang.NameResolver;
import wyal.lang.NameResolver.AmbiguousNameError;
import wyal.lang.NameResolver.NameNotFoundError;
import wyal.lang.NameResolver.ResolutionError;
import wyal.lang.RawSubtypeOperator;
import wyal.lang.SyntacticHeap;
import wyal.lang.SyntacticItem;
import wyal.lang.WyalFile;
import wyal.lang.WyalFile.Declaration;
import wyal.lang.WyalFile.Identifier;
import wyal.lang.WyalFile.Name;
import wyal.lang.WyalFile.Opcode;
import wyal.lang.WyalFile.Tuple;
import wyal.lang.WyalFile.Type;
import wyal.lang.WyalFile.Declaration.Named;
import wyal.lang.WyalFile.Expr;
import wybs.lang.SyntacticElement;
import wybs.util.ResolveError;
import wycc.util.ArrayUtils;
import wyal.lang.WyalFile.FieldDeclaration;

public class TypeSystem {
	private final WyalFile parent;
	private final NameResolver resolver;
	private final RawSubtypeOperator coerciveRawSubtypeOperator;

	public TypeSystem(WyalFile parent) {
		this.parent = parent;
		this.resolver = new WyalFileResolver();
		this.coerciveRawSubtypeOperator = new CoerciveRawSubtypeOperator(resolver);
	}

	/**
	 * <p>
	 * Determine whether one type is a <i>raw subtype</i> of another.
	 * Specifically, whether the raw type of <code>rhs</code> is a subtype of
	 * <code>lhs</code>'s raw type (i.e.
	 * "<code>&lfloor;lhs&rfloor; :> &lfloor;rhs&rfloor;</code>"). The raw type
	 * is that which ignores any type invariants involved. Thus, one must be
	 * careful when interpreting the meaning of this operation. Specifically,
	 * "<code>&lfloor;lhs&rfloor; :> &lfloor;rhs&rfloor;</code>" <b>does not
	 * imply</b> that "<code>lhs :> rhs</code>" holds. However, if
	 * "<code>&lfloor;lhs&rfloor; :> &lfloor;rhs&rfloor;</code>" does not hold,
	 * then it <b>does follow</b> that "<code>lhs :> rhs</code>" also does not
	 * hold.
	 * </p>
	 *
	 * <p>
	 * Depending on the exact language of types involved, this can be a
	 * surprisingly complex operation. For example, in the presence of
	 * <i>union</i>, <i>intersection</i> and <i>negation</i> types, the subtype
	 * algorithm is surprisingly intricate.
	 * </p>
	 *
	 * @param lhs
	 *            The candidate "supertype". That is, lhs's raw type may be a
	 *            supertype of <code>rhs</code>'s raw type.
	 * @param rhs
	 *            The candidate "subtype". That is, rhs's raw type may be a
	 *            subtype of <code>lhs</code>'s raw type.
	 * @return
	 * @throws ResolutionError
	 *             Occurs when a nominal type is encountered whose name cannot
	 *             be resolved properly. For example, it resolves to more than
	 *             one possible matching declaration, or it cannot be resolved
	 *             to a corresponding type declaration.
	 */
	public boolean isRawSubtype(Type lhs, Type rhs) throws ResolutionError {
		return coerciveRawSubtypeOperator.isRawSubtype(lhs,rhs);
	}

	public boolean isEffectiveRecord(Type type) throws ResolutionError {
		return expandAsEffectiveRecord(type) != null;
	}

	public boolean isEffectiveArray(Type type) throws ResolutionError {
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
	 * @throws ResolutionError
	 */
	public Type.EffectiveRecord expandAsEffectiveRecord(Type type) throws ResolutionError {
		Type r = expandAsEffectiveType(true, type);
		if (r instanceof Type.EffectiveRecord) {
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
	 * @throws ResolutionError
	 */
	public Type.EffectiveArray expandAsEffectiveArray(Type type) throws ResolutionError {
		Type r = expandAsEffectiveType(true, type);
		if (r instanceof Type.EffectiveArray) {
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
	 * @throws ResolutionError
	 * @throws IOException
	 * @throws ResolveError
	 */
	public Type expandAsEffectiveType(boolean sign, Type type) throws ResolutionError {
		//
		switch (type.getOpcode()) {
		case TYPE_not: {
			Type.Negation neg = (Type.Negation) type;
			return expandAsEffectiveType(!sign, neg.getElement());
		}
		case TYPE_nom: {
			Type.Nominal nom = (Type.Nominal) type;
			Named.Type decl = resolveExactly(nom.getName(),Named.Type.class);
			return expandAsEffectiveType(sign, decl.getVariableDeclaration().getType());
		}
		case TYPE_and:
		case TYPE_or: {
			// Hmm, this is tasty line. It does exactly what I want though :)
			boolean union = sign == (type.getOpcode() == Opcode.TYPE_or);
			Type[] children = expandAsReadableTypes(sign, (Type[]) type.getOperands());
			if (union) {
				return union(children);
			} else {
				return intersect(children);
			}
		}
		default:
			if (sign) {
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
	 * @throws ResolutionError
	 */
	public Type[] expandAsReadableTypes(boolean sign, Type... types) throws ResolutionError {
		Type[] nTypes = new Type[types.length];
		for (int i = 0; i != types.length; ++i) {
			nTypes[i] = expandAsEffectiveType(sign, types[i]);
		}
		return nTypes;
	}

	// ======================================================================
	// Negate
	// ======================================================================
	public static Type negate(Type type) {
		if (type instanceof Type.Negation) {
			Type.Negation nt = (Type.Negation) type;
			return nt.getElement();
		} else if (type instanceof Type.Union) {
			Type.Union union = (Type.Union) type;
			return intersect(negate(union.getOperands()));
		} else if (type instanceof Type.Intersection) {
			Type.Intersection intersection = (Type.Intersection) type;
			return union(negate(intersection.getOperands()));
		} else {
			return new Type.Negation(type);
		}
	}

	public static Type[] negate(Type... types) {
		Type[] result = new Type[types.length];
		for (int i = 0; i != result.length; ++i) {
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
		if (anyIndex >= 0) {
			return rs[anyIndex];
		}
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
		if (rs.length == 0) {
			return new Type.Void();
		} else if (rs.length == 1) {
			return rs[0];
		} else if (areInstances(types, Type.Record.class)) {
			return new UnionOfRecords(rs);
		} else if (areInstances(types, Type.Array.class)) {
			return new UnionOfArrays(rs);
		} else {
			return new Type.Union(rs);
		}
	}

	private static <T> boolean areInstances(T[] items, Class<? extends T> kind) {
		for (int i = 0; i != items.length; ++i) {
			if (!kind.isInstance(items[i])) {
				return false;
			}
		}
		//
		return true;
	}

	private static class UnionOfRecords extends WyalFile.Type.Union implements Type.EffectiveRecord {

		public UnionOfRecords(Type... records) {
			super(records);
		}

		@Override
		public Type.Record getOperand(int i) {
			return (Type.Record) super.getOperand(i);
		}

		@Override
		public FieldDeclaration[] getFields() {
			Type.Record result = getOperand(0);
			for (int i = 1; i != size(); ++i) {
				result = unionReadableRecords(result, getOperand(i));
			}
			return result.getFields();
		}

		private static Type.Record unionReadableRecords(Type.Record lhs, Type.Record rhs) {
			ArrayList<FieldDeclaration> fields = new ArrayList<>();
			FieldDeclaration[] lhsFields = lhs.getFields();
			FieldDeclaration[] rhsFields = rhs.getFields();
			for (int i = 0; i != lhsFields.length; ++i) {
				for (int j = 0; j != rhsFields.length; ++j) {
					FieldDeclaration lhsField = lhsFields[i];
					FieldDeclaration rhsField = rhsFields[j];
					Identifier lhsFieldName = lhsField.getVariableName();
					Identifier rhsFieldName = rhsField.getVariableName();
					if (lhsFieldName.equals(rhsFieldName)) {
						Type type = union(lhsField.getType(), rhsField.getType());
						fields.add(new FieldDeclaration(type, lhsFieldName));
					}
				}
			}
			//
			boolean isOpenRecord = lhs.isOpen() || rhs.isOpen();
			//
			return new Type.Record(isOpenRecord, fields.toArray(new FieldDeclaration[fields.size()]));
		}
	}

	private static class UnionOfArrays extends WyalFile.Type.Union implements Type.EffectiveArray {

		public UnionOfArrays(Type... arrays) {
			super(arrays);
		}

		@Override
		public Type.Array getOperand(int i) {
			return (Type.Array) super.getOperand(i);
		}

		@Override
		public Type getReadableElement() {
			Type[] results = new Type[size()];
			for (int i = 0; i != size(); ++i) {
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
		for (int i = 0; i != types.length; ++i) {
			Type child = types[i];
			if (child instanceof Type.Union) {
				// Distribute outer intersection over this inner
				return distributeUnion(i, types);
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
		if (voidIndex >= 0) {
			return rs[voidIndex];
		}
		// Any in an intersection can be dropped
		rs = ArrayUtils.removeAll(rs, new Type.Any());
		rs = ArrayUtils.removeAll(rs, null);
		// remove any duplicates
		rs = ArrayUtils.sortAndRemoveDuplicates(rs);
		// intersect terms together
		//
		if (rs.length == 0) {
			return new Type.Any();
		} else if (rs.length == 1) {
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
		for (int j = 0; j != union.size(); ++j) {
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
		if (lhsNegative && rhsNegative) {
			intersectNegativeNegative(i, j, types);
		} else if (lhsNegative) {
			intersectNegativePositive(i, j, types);
		} else if (rhsNegative) {
			intersectNegativePositive(j, i, types);
		} else {
			intersectPositivePositive(i, j, types);
		}
	}

	private static void intersectNegativeNegative(int i, int j, Type[] types) {
		// FIXME: could do more here
	}

	private static void intersectNegativePositive(int i, int j, Type[] types) {
		Type.Negation ith = (Type.Negation) types[i];
		Type ith_element = ith.getElement();
		Type jth = types[j];
		if (jth instanceof Type.Any) {
			types[i] = null;
			types[j] = ith;
		} else if (ith_element.equals(jth)) {
			// FIXME: should do more here as there are other cases where we
			// should reduce to void. For example, if jth element is
			// supertype of ith.
			types[i] = types[j] = new Type.Void();
		} else if (ith_element instanceof Type.Nominal || jth instanceof Type.Nominal) {
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
		if (lhsKind == Opcode.TYPE_any || rhsKind == Opcode.TYPE_any) {
			// In this case, there is nothing really to do. Basically
			// intersection something with any gives something. We don't remove
			// the any type from the array at this stage, since it will be
			// removed lated on.
		} else if (lhsKind == Opcode.TYPE_nom || rhsKind == Opcode.TYPE_nom) {
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
				types[j] = intersectArrays((Type.Array) ith, (Type.Array) jth);
				break;
			case TYPE_rec:
				types[i] = null;
				types[j] = intersectRecords((Type.Record) ith, (Type.Record) jth);
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
			// Determine the number of matching fields. That is, fields with the
			// same name.
			int matches = countMatchingFields(lhsFields, rhsFields);
			// When intersecting two records, the number of fields is only
			// allowed to differ if one of them is an open record. Therefore, we
			// need to pay careful attention to the size of the resulting match
			// in comparison with the original records.
			if (matches < lhsFields.length && !rhs.isOpen()) {
				// Not enough matches made to meet the requirements of the lhs
				// type.
				return new Type.Void();
			} else if (matches < rhsFields.length && !lhs.isOpen()) {
				// Not enough matches made to meet the requirements of the rhs
				// type.
				return new Type.Void();
			} else {
				// At this point, we know the intersection succeeds. The next
				// job is to determine the final set of field declarations.
				int lhsRemainder = lhsFields.length - matches;
				int rhsRemainder = rhsFields.length - matches;
				FieldDeclaration[] fields = new FieldDeclaration[matches + lhsRemainder + rhsRemainder];
				// Extract all matching fields first
				int index = extractMatchingFields(lhsFields, rhsFields, fields);
				// Extract remaining lhs fields second
				index = extractNonMatchingFields(lhsFields, rhsFields, fields, index);
				// Extract remaining rhs fields last
				index = extractNonMatchingFields(rhsFields, lhsFields, fields, index);
				// The intersection of two records can only be open when both
				// are themselves open.
				boolean isOpen = lhs.isOpen() && rhs.isOpen();
				//
				return new Type.Record(isOpen, fields);
			}
		}
	}

	/**
	 * Count the number of matching fields. That is, fields with the same name.
	 *
	 * @param lhsFields
	 * @param rhsFields
	 * @return
	 */
	private static int countMatchingFields(FieldDeclaration[] lhsFields, FieldDeclaration[] rhsFields) {
		int count = 0;
		for (int i = 0; i != lhsFields.length; ++i) {
			for (int j = 0; j != rhsFields.length; ++j) {
				FieldDeclaration lhsField = lhsFields[i];
				FieldDeclaration rhsField = rhsFields[j];
				Identifier lhsFieldName = lhsField.getVariableName();
				Identifier rhsFieldName = rhsField.getVariableName();
				if (lhsFieldName.equals(rhsFieldName)) {
					count = count + 1;
				}
			}
		}
		return count;
	}

	/**
	 * Extract all matching fields (i.e. fields with the same name) into the
	 * result array.
	 *
	 * @param lhsFields
	 * @param rhsFields
	 * @param result
	 * @return
	 */
	private static int extractMatchingFields(FieldDeclaration[] lhsFields, FieldDeclaration[] rhsFields,
			FieldDeclaration[] result) {
		int index = 0;
		// Extract all matching fields first.
		for (int i = 0; i != lhsFields.length; ++i) {
			for (int j = 0; j != rhsFields.length; ++j) {
				FieldDeclaration lhsField = lhsFields[i];
				FieldDeclaration rhsField = rhsFields[j];
				Identifier lhsFieldName = lhsField.getVariableName();
				Identifier rhsFieldName = rhsField.getVariableName();
				if (lhsFieldName.equals(rhsFieldName)) {
					FieldDeclaration combined = new FieldDeclaration(intersect(lhsField.getType(), rhsField.getType()),
							lhsFieldName);
					result[index++] = combined;
				}
			}
		}
		return index;
	}

	/**
	 * Extract fields from lhs which do not match any field in the rhs. That is,
	 * there is no field in the rhs with the same name.
	 *
	 * @param lhsFields
	 * @param rhsFields
	 * @param result
	 * @param index
	 * @return
	 */
	private static int extractNonMatchingFields(FieldDeclaration[] lhsFields, FieldDeclaration[] rhsFields,
			FieldDeclaration[] result, int index) {
		outer: for (int i = 0; i != lhsFields.length; ++i) {
			for (int j = 0; j != rhsFields.length; ++j) {
				Identifier lhsFieldName = lhsFields[i].getVariableName();
				Identifier rhsFieldName = rhsFields[j].getVariableName();
				if (lhsFieldName.equals(rhsFieldName)) {
					// This is a matching field. Therefore, continue on to the
					// next lhs field
					continue outer;
				}
			}
			result[index++] = lhsFields[i];
		}
		return index;
	}



	// ========================================================================
	// Resolution
	// ========================================================================

	public <T extends Declaration.Named> T resolveExactly(Name name, Class<T> kind)
			throws ResolutionError {
		return resolver.resolveExactly(name,kind);
	}

	public <T extends Declaration.Named> List<T> resolveAll(Name name, Class<T> kind)
			throws ResolutionError {
		return resolver.resolveAll(name,kind);
	}

}
