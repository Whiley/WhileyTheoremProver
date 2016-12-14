package wyal.util;

import java.util.Arrays;
import java.util.HashMap;
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

	public TypeSystem(WyalFile parent) {
		this.parent = parent;
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
		WyalFile.Opcode pOpcode = parent.getOpcode();
		WyalFile.Opcode cOpcode = child.getOpcode();
		// Handle non-atomic cases
		// Handle atomic cases

		if (pOpcode == Opcode.TYPE_nom) {
			Type.Nominal nom = (Type.Nominal) parent;
			Named.Type decl = resolveAsDeclaredType(nom.getName());
			// FIXME: this will cause infinite loops
			return isSubtype(decl.getVariableDeclaration().getType(), child);
		} else if (cOpcode == Opcode.TYPE_nom) {
			Type.Nominal nom = (Type.Nominal) child;
			Named.Type decl = resolveAsDeclaredType(nom.getName());
			// FIXME: this will cause infinite loops
			return isSubtype(parent, decl.getVariableDeclaration().getType());
		} else if (pOpcode == Opcode.TYPE_any || cOpcode == Opcode.TYPE_void) {
			return true;
		} else if (cOpcode == Opcode.TYPE_or) {
			Type.Union cUnion = (Type.Union) child;
			for (int i = 0; i != cUnion.size(); ++i) {
				Type cChild = cUnion.getOperand(i);
				if (!isSubtype(parent, cChild)) {
					return false;
				}
			}
			return true;
		} else if (pOpcode == Opcode.TYPE_or) {
			Type.Union pUnion = (Type.Union) parent;
			for (int i = 0; i != pUnion.size(); ++i) {
				Type pChild = pUnion.getOperand(i);
				if (isSubtype(pChild, child)) {
					return true;
				}
			}
			return false;
		} else if (pOpcode == Opcode.TYPE_not) {
			Type.Negation pNot = (Type.Negation) parent;
			// !x :> y
			return !isSubtype(pNot.getElement(), child);
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
			return isSubtype(pArray.getElement(), cArray.getElement());
		}
		default:
			throw new RuntimeException("unknown type encountered: " + parent);
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
}
