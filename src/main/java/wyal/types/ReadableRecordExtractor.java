package wyal.types;

import wyal.lang.NameResolver;
import wyal.lang.WyalFile.Type;

/**
 * <p>
 * Responsible for extracting a "readable record" from a given type. A readable
 * record is a conservative approximation of the records described in a given
 * type. Furthermore, it is safe used when reading field values from that type.
 * For example, the type <code>{int f}|{bool f}</code> has a readable record
 * type of <code>{int|bool f}</code>. This is the readable type as, if we were
 * to read field <code>f</code> from either bound, the return type would be in
 * <code>int|bool</code>. However, we cannot use type for writing as this could
 * be unsafe. For example, if we actually had a record of type
 * <code>{int f}</code>, then writing a boolean value is not permitted.
 * </p>
 * <p>
 * Not all types have readable record type and, furthermore, care must be
 * exercised for those that do. For example, <code>{int f}|int</code> does not
 * have a readable record type. Likewise, the readable record type for
 * <code>{int f, int g}|{bool f}</code> is <code>{int|bool f, ...}</code>.
 * Finally, negations play an important role in determining the readable record
 * type. For example, <code>{int|null f} & !{int f}</code> generates the
 * readable record type <code>{null f}</code>.
 * </p>
 *
 * @author David J. Pearce
 *
 */
public class ReadableRecordExtractor implements TypeExtractor<Type.Record> {
	private final NameResolver resolver;

	public ReadableRecordExtractor(NameResolver resolver) {
		this.resolver = resolver;
	}

	@Override
	public Type.Record extract(Type type) {
		if (type instanceof Type.Primitive || type instanceof Type.Array || type instanceof Type.Reference
				|| type instanceof Type.Negation) {
			return null;
		} else if (type instanceof Type.Record) {
			return (Type.Record) type;
		} else if (type instanceof Type.Nominal) {
			return extract((Type.Nominal) type);
		} else if (type instanceof Type.Union) {
			return extract((Type.Union) type);
		} else {
			return extract((Type.Intersection) type);
		}
	}

	private Type.Record extract(Type.Union type) {
		return null;
	}

	private Type.Record extract(Type.Intersection type) {
		return null;
	}

	public Type.Record extract(Type.Nominal nominal) {
		return null;
	}
}
