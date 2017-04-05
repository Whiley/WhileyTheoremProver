package wytp.types.extractors;

import java.util.ArrayList;

import wyal.lang.NameResolver;
import wyal.lang.WyalFile.FieldDeclaration;
import wyal.lang.WyalFile.Identifier;
import wyal.lang.WyalFile.Type;
import wytp.types.TypeSystem;
import wytp.types.util.AbstractTypeExtractor;

/**
 * <p>
 * Responsible for extracting a "readable array" from a given type. A readable
 * array is a conservative approximation of the arrays described in a given
 * type. Furthermore, it is safe used when reading elements from that type. For
 * example, the type <code>(int[])|(bool[])</code> has a readable array type of
 * <code>(int|bool)[]</code>. This is the readable type as, if we were to read
 * an element from either bound, the return type would be in
 * <code>int|bool</code>. However, we cannot use type for writing as this could
 * be unsafe. For example, if we actually had an array of type
 * <code>int[]</code>, then writing a boolean value is not permitted.
 * </p>
 * <p>
 * Not all types have readable array type and, furthermore, care must be
 * exercised for those that do. For example, <code>(int[])|int</code> does not
 * have a readable array type. Finally, negations play an important role in
 * determining the readable array type. For example,
 * <code>(int|null)[] & !(int[])</code> generates the readable array type
 * <code>null[]</code>.
 * </p>
 *
 * @author David J. Pearce
 *
 */
public class ReadableArrayExtractor extends AbstractTypeExtractor<Type.Array> {

	public ReadableArrayExtractor(NameResolver resolver, TypeSystem typeSystem) {
		super(resolver, typeSystem);
	}

	@Override
	protected Type.Array construct(Type.Atom type) {
		if(type instanceof Type.Array) {
			return (Type.Array) type;
		} else {
			return null;
		}
	}

	@Override
	protected Type.Array union(Type.Array lhs, Type.Array rhs) {
		//
		return new Type.Array(unionHelper(lhs.getElement(),rhs.getElement()));
	}

	@Override
	protected Type.Array subtract(Type.Array lhs, Type.Array rhs) {
		return new Type.Array(intersectionHelper(lhs.getElement(), new Type.Negation(rhs.getElement())));
	}

	@Override
	protected Type.Array intersect(Type.Array lhs, Type.Array rhs) {
		return new Type.Array(intersectionHelper(lhs.getElement(),rhs.getElement()));
	}
}
