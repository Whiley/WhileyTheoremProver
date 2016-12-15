package wyal.util;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.BitSet;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import wyal.lang.SyntacticItem;
import wyal.lang.WyalFile;
import wyal.lang.WyalFile.Declaration;
import wyal.lang.WyalFile.Identifier;
import wyal.lang.WyalFile.Name;
import wyal.lang.WyalFile.Opcode;
import wyal.lang.WyalFile.Type;
import wyal.lang.WyalFile.VariableDeclaration;
import wyal.lang.WyalFile.Declaration.Named;

public class TypeSystem {
	private final WyalFile parent;
	private final ArrayList<Type> rewrites;

	public TypeSystem(WyalFile parent) {
		this.parent = parent;
		this.rewrites = new ArrayList<Type>();
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
			Identifier id = new Identifier(parent, e.getKey());
			declarations[index++] = new VariableDeclaration(parent, e.getValue(), id);
		}
		return new Type.Record(parent, declarations);
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
			return new Type.Array(parent, union(elements));
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
			return new Type.Void(parent);
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
			return new Type.Union(parent, types);
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
		System.out.print("CHECKING: " + parent + " :> " + child + " ... ");
		// return isOldSubtype(parent,child);
		boolean r = isNewSubtype(parent, child);
		System.out.println(r);
		return r;
	}

	private boolean isOldSubtype(Type parent, Type child) {
		WyalFile.Opcode pOpcode = parent.getOpcode();
		WyalFile.Opcode cOpcode = child.getOpcode();
		// Handle non-atomic cases
		// Handle atomic cases

		if (pOpcode == Opcode.TYPE_nom) {
			Type.Nominal nom = (Type.Nominal) parent;
			Named.Type decl = resolveAsDeclaredType(nom.getName());
			// FIXME: this will cause infinite loops
			return isOldSubtype(decl.getVariableDeclaration().getType(), child);
		} else if (cOpcode == Opcode.TYPE_nom) {
			Type.Nominal nom = (Type.Nominal) child;
			Named.Type decl = resolveAsDeclaredType(nom.getName());
			// FIXME: this will cause infinite loops
			return isOldSubtype(parent, decl.getVariableDeclaration().getType());
		} else if (pOpcode == Opcode.TYPE_any || cOpcode == Opcode.TYPE_void) {
			return true;
		} else if (cOpcode == Opcode.TYPE_or) {
			Type.Union cUnion = (Type.Union) child;
			for (int i = 0; i != cUnion.size(); ++i) {
				Type cChild = cUnion.getOperand(i);
				if (!isOldSubtype(parent, cChild)) {
					return false;
				}
			}
			return true;
		} else if (pOpcode == Opcode.TYPE_or) {
			Type.Union pUnion = (Type.Union) parent;
			for (int i = 0; i != pUnion.size(); ++i) {
				Type pChild = pUnion.getOperand(i);
				if (isOldSubtype(pChild, child)) {
					return true;
				}
			}
			return false;
		} else if (pOpcode == Opcode.TYPE_not) {
			Type.Negation pNot = (Type.Negation) parent;
			// !x :> y
			return !isOldSubtype(pNot.getElement(), child);
		} else if (pOpcode != cOpcode) {
			return false;
		}

		switch (parent.getOpcode()) {
		case TYPE_any:
			return true;
		case TYPE_null:
		case TYPE_bool:
		case TYPE_int:
		case TYPE_void:
			return cOpcode == pOpcode || cOpcode == Opcode.TYPE_void;
		case TYPE_arr: {
			Type.Array pArray = (Type.Array) parent;
			Type.Array cArray = (Type.Array) child;
			return isOldSubtype(pArray.getElement(), cArray.getElement());
		}
		default:
			throw new RuntimeException("unknown type encountered: " + parent);
		}
	}

	private boolean isNewSubtype(Type parent, Type child) {
		// A :> B iff (!A & B) == void
		return isVoid(false, parent, true, child);
	}

	private boolean isVoid(boolean t1sign, Type t1, boolean t2sign, Type t2) {
		ArrayList<Atom> truths = new ArrayList<Atom>();
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
		if (worklist.size() == 0) {
			return isVoid(truths);
		} else {
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
	 * Check whether a sequence of one or more atoms are inconsistent. Two atoms
	 * are inconsistent if they have no intersection; likewise, a single atom is
	 * inconsistent if it is equivalent to void.
	 *
	 * @param truths
	 * @return
	 */
	private boolean isVoid(ArrayList<Atom> truths) {
		for (int i = 0; i != truths.size(); ++i) {
			for (int j = i + 1; j != truths.size(); ++j) {
				if (isVoid(truths.get(i), truths.get(j))) {
					return true;
				}
			}
		}
		return false;
	}

	private boolean isVoid(Atom a, Atom b) {
		System.out.print("CHECKING " + a + " & " + b + " == void");
		if (isVoid(a) || isVoid(b)) {
			System.out.println(" TRUE(1)");
			return true;
		} else if (isAny(a) || isAny(b)) {
			System.out.println(" FALSE(2)");
			return false;
		}
		// At this point, we have several cases left to consider.
		boolean aSign = a.sign;
		boolean bSign = b.sign;
		WyalFile.Opcode aOpcode = a.type.getOpcode();
		WyalFile.Opcode bOpcode = b.type.getOpcode();
		//
		if (aSign == bSign) {
			if (aSign) {
				if (aOpcode != bOpcode) {
					// In this case, we are intersecting two positive atoms of
					// different kind. For example, an int and a record. This
					// always reduces to void.
					System.out.println(" TRUE(3)");
					return true;
				} else {
					// In this case, we are intersecting two positive atoms of
					// the same kind. For primitive types, this never reduces to
					// void.
					switch (aOpcode) {
					case TYPE_arr:
						return isVoidPosPos((Type.Array) a.type, (Type.Array) b.type);
					case TYPE_rec:
						throw new RuntimeException("Implement me!");
					case TYPE_ref:
						throw new RuntimeException("Implement me!");
					case TYPE_fun:
						throw new RuntimeException("Implement me!");
					default:
						// Intersecting two positive atoms of the same kind
						// always yields an atom of that kind.
						System.out.println(" FALSE(4)");
						return false;
					}
				}
			} else {
				// In this case, there is actually nothing to do. Two negative
				// atoms being intersected never reduce to void, unless one of
				// them is any (which we already know is not true).
				System.out.println(" FALSE(5)");
				return false;
			}
		} else {
			// In this case, we have one negative and one positive type. In the
			// case that they have different kinds, then the type will never
			// reduce to void. Otherwise, it might (though not necessarily).
			if (aOpcode != bOpcode) {
				System.out.println(" FALSE(6)");
				return false;
			} else {
				// The two atoms have the same kind. Now extract the positive
				// one and the negative one.
				Type pos = aSign ? a.type : b.type;
				Type neg = aSign ? b.type : a.type;
				//
				switch (aOpcode) {
				case TYPE_arr:
					System.out.println(" ...");
					return isVoidPosNeg((Type.Array) pos, (Type.Array) neg);
				case TYPE_rec:
					throw new RuntimeException("Implement me!");
				case TYPE_ref:
					throw new RuntimeException("Implement me!");
				case TYPE_fun:
					throw new RuntimeException("Implement me!");
				default:
					// A primitive being intersected with its negation is always
					// void. For example, (int & !int) is void.
					System.out.println(" TRUE(7)");
					return true;
				}
			}
		}
	}

	private boolean isVoidPosPos(Type.Array t1, Type.Array t2) {
		return isVoid(true, t1.getElement(), true, t2.getElement());
	}

	private boolean isVoidPosNeg(Type.Array pos, Type.Array neg) {
		System.out.println("GOT HERE: " + pos.getElement() + " & neg " + neg.getElement());
		return isVoid(true, pos.getElement(), false, neg.getElement());
	}

	private boolean isVoid(Atom atom) {
		WyalFile.Opcode opcode = atom.type.getOpcode();
		boolean sign = atom.sign;
		switch (opcode) {
		case TYPE_void:
			return sign;
		case TYPE_any:
			return !sign;
		default:
			// At this point, it may seem that we should do more work. For
			// example, a record with a void field is equivalent to void.
			// However, I don't believe this is the case since we can assume
			// that such types must be inconsistent at the source level and,
			// hence, would be caught earlier.
			return false;
		}
	}

	private boolean isAny(Atom atom) {
		WyalFile.Opcode opcode = atom.type.getOpcode();
		boolean sign = atom.sign;
		switch (opcode) {
		case TYPE_void:
			return !sign;
		case TYPE_any:
			return sign;
		default:
			return false;
		}
	}

	/**
	 * Expand a given named declaration on the assumption that it is a type.
	 * This will initially look for the given name in the enclosing file, before
	 * considering those import statements included in the appropriate order.
	 *
	 * @param name
	 * @return
	 */
	private Declaration.Named.Type resolveAsDeclaredType(Name name) {
		Identifier[] components = name.getComponents();
		if (components.length > 1) {
			// FIXME: implement this
			throw new IllegalArgumentException("Need to handle proper namespaces!");
		}
		// Look through the enclosing file first!
		WyalFile parent = name.getParent();
		for (int i = 0; i != parent.size(); ++i) {
			SyntacticItem item = parent.getSyntacticItem(i);
			if (item instanceof Declaration.Named.Type) {
				Declaration.Named.Type nd = (Declaration.Named.Type) item;
				if (nd.getName().equals(components[0])) {
					return nd;
				}
			}
		}
		// FIXME: consider imported files as well
		throw new IllegalArgumentException("unable to resolve " + name + " as type");
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
			if(sign) {
				return type.toString();
			} else {
				return "!" + type;
			}
		}
	}
}
