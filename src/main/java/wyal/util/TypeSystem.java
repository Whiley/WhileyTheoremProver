package wyal.util;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.BitSet;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import wyal.lang.Formula;
import wyal.lang.SyntacticHeap;
import wyal.lang.SyntacticItem;
import wyal.lang.WyalFile;
import wyal.lang.Formula.Conjunct;
import wyal.lang.Formula.Disjunct;
import wyal.lang.WyalFile.Declaration;
import wyal.lang.WyalFile.Identifier;
import wyal.lang.WyalFile.Name;
import wyal.lang.WyalFile.Opcode;
import wyal.lang.WyalFile.Tuple;
import wyal.lang.WyalFile.Type;
import wyal.lang.WyalFile.VariableDeclaration;
import wyal.lang.WyalFile.Declaration.Named;

public class TypeSystem {
	private final WyalFile parent;
	private final ArrayList<Type> rewrites;

	public TypeSystem(WyalFile parent) {
		this.parent = parent;
		this.rewrites = new ArrayList<>();
	}

	/**
	 * For a given type, extract its effective record type. For example, the
	 * type <code>({int x, int y}|{int x, int z})</code> has effective record
	 * type <code>{int x,
	 * ...}</code>.
	 *
	 * @param type
	 * @return
	 */
	public Type.Record extractReadableRecordType(Type type) {

		// FIXME: this method is horribly broken. For example, it can't handle
		// any of these cases:
		// --> {int x} & {int x}
		// --> !!{int x}
		// --> ({int x}|null}&!null

		if (type instanceof Type.Record) {
			return (Type.Record) type;
		} else if (type instanceof Type.Union) {
			Type.Union union = (Type.Union) type;
			HashMap<String, Type> fields = null;
			for (int i = 0; i != union.size(); ++i) {
				Type.Record r = extractReadableRecordType(union.getOperand(i));
				merge(fields, r);
			}
			//
			return constructEffectiveRecord(fields);
		} else if (type instanceof Type.Nominal) {
			Type.Nominal nom = (Type.Nominal) type;
			Named.Type decl = resolveAsDeclaredType(nom.getName());
			return extractReadableRecordType(decl.getVariableDeclaration().getType());
		} else {
			throw new RuntimeException("expected record type, found: " + type);
		}
	}

	private void merge(HashMap<String, Type> fields, Type.Record r) {
		VariableDeclaration[] vds = r.getFields();
		for (Map.Entry<String, Type> e : fields.entrySet()) {
			String fieldName = e.getKey();
			Type fieldType = null;
			for (int i = 0; i != vds.length; ++i) {
				VariableDeclaration fd = vds[i];
				String name = fd.getVariableName().get();
				if (fieldName.equals(name)) {
					fieldType = union(e.getValue(), fd.getType());
				}
			}
			fields.put(fieldName, fieldType);
		}
	}

	private Type.Record constructEffectiveRecord(Map<String, Type> fields) {
		VariableDeclaration[] declarations = new VariableDeclaration[fields.size()];
		int index = 0;
		for (Map.Entry<String, Type> e : fields.entrySet()) {
			Identifier id = new Identifier(e.getKey());
			declarations[index++] = new VariableDeclaration(e.getValue(), id);
		}
		return new Type.Record(declarations);
	}

	/**
	 * Extract the readable array type from a given type. For example, the type
	 * <code>(int[])|(bool[])</code> has a readable array type of
	 * <code>(int|bool)[]</code>.
	 *
	 * @param type
	 * @return
	 */
	public Type.Array extractReadableArrayType(Type type) {
		if (type instanceof Type.Array) {
			return (Type.Array) type;
		} else if (type instanceof Type.Union) {
			Type.Union union = (Type.Union) type;
			Type[] elements = new Type[union.size()];
			for (int i = 0; i != union.size(); ++i) {
				Type.Array r = extractReadableArrayType(union.getOperand(i));
				elements[i] = r.getElement();
			}
			//
			return new Type.Array(union(elements));
		} else if (type instanceof Type.Nominal) {
			Type.Nominal nom = (Type.Nominal) type;
			Named.Type decl = resolveAsDeclaredType(nom.getName());
			return extractReadableArrayType(decl.getVariableDeclaration().getType());
		} else {
			throw new RuntimeException("expected array type, found: " + type);
		}
	}

	/**
	 * Take a sequence of zero or more types and produce a minimal union of
	 * them.
	 *
	 * @param types
	 * @return
	 */
	public Type union(Type... types) {
		if (types.length == 0) {
			return new Type.Void();
		} else if (types.length == 1) {
			return types[0];
		} else {
			// Now going to remove duplicates; for now, that's all we can do.
			Type[] rs = Arrays.copyOf(types, types.length);
			for (int i = 0; i != rs.length; ++i) {
				for (int j = i + 1; j != rs.length; ++j) {
					// TODO: soooo broken
					if (rs[i] == rs[j]) {
						rs[j] = null;
					}
				}
			}
			return new Type.Union(types);
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
		return isVoid(false, parent, true, child);
	}

	private boolean isVoid(boolean t1sign, Type t1, boolean t2sign, Type t2) {
		ArrayList<Atom> truths = new ArrayList<>();
		Worklist worklist = new Worklist();
		worklist.push(t1sign, t1);
		worklist.push(t2sign, t2);
		return isVoid(truths, worklist);
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
	 * @return
	 */
	private boolean isVoid(ArrayList<Atom> truths, Worklist worklist) {

		// FIXME: there is a bug in the following case which needs to be
		// addressed:
		//
		// {int|null f} & !{int f} & !{null f}
		//
		// The problem is that we need the "pairwise consistency property" in
		// order for this algorithm to be complete. To get that, we must expand
		// records containing union types.  Thus, the above should be expanded to:
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
					if (isVoid(truths.get(i), truths.get(j))) {
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
						if (!isVoid((ArrayList<Atom>) truths.clone(), tmp)) {
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
			return isVoid(truths, worklist);
		}
	}

	/**
	 * Determine whether the intersection of two arbitrary atoms results in void
	 * or not. Each atom is either a "positive" or "negative" term. The latter
	 * corresponds to negated terms, such as !int or !{int f}.
	 *
	 * @param a
	 * @param b
	 * @return
	 */
	private boolean isVoid(Atom a, Atom b) {
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
				return isVoidArray(aSign, (Type.Array) a.type, bSign, (Type.Array) b.type);
			case TYPE_rec:
				return isVoidRecord(aSign, (Type.Record) a.type, bSign, (Type.Record) b.type);
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
	 * @return
	 */
	private boolean isVoidArray(boolean lhsSign, Type.Array lhs, boolean rhsSign, Type.Array rhs) {
		if (lhsSign != rhsSign) {
			// In this case, we are intersecting two array types, of which at
			// least one is positive. This is void only if there is no
			// intersection of the underlying element types. For example, int[]
			// and bool[] is void, whilst (int|null)[] and int[] is not.
			return isVoid(lhsSign, lhs.getElement(), rhsSign, rhs.getElement());
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
	 * @return
	 */
	private boolean isVoidRecord(boolean lhsSign, Type.Record lhs, boolean rhsSign, Type.Record rhs) {
		VariableDeclaration[] lhsFields = lhs.getFields();
		VariableDeclaration[] rhsFields = rhs.getFields();
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
					VariableDeclaration lhsField = lhsFields[i];
					VariableDeclaration rhsField = rhsFields[i];
					if(!lhsField.getVariableName().equals(rhsField.getVariableName())) {
						// The fields have different names. In the pos-pos
						// case, this indicates no intersection is possible. For
						// pos-neg case, intersection exists.
						return sign;
					} else if (isVoid(lhsSign, lhsField.getType(), rhsSign, rhsField.getType()) == sign) {
						// For pos-pos case, there is no intersection between
						// these fields and, hence, no intersection overall; for
						// pos-neg case, there is some intersection between
						// these fields which means that some intersections
						// exists overall.  For example, consider the case
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

	public Declaration.Named resolveAsDeclaration(Name name) {
		Identifier[] components = name.getComponents();
		// FIXME: need to handle case where more than one component
		Identifier last = components[components.length-1];
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
		Identifier last = components[components.length-1];
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
}
