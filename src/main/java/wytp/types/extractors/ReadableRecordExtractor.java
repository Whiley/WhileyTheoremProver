package wytp.types.extractors;

import java.util.ArrayList;

import wyal.lang.NameResolver;
import wyal.lang.WyalFile.FieldDeclaration;
import wyal.lang.WyalFile.Identifier;
import wyal.lang.WyalFile.Type;
import wyal.lang.WyalFile.Type.Atom;
import wyal.lang.WyalFile.Type.Record;
import wytp.types.TypeSystem;
import wytp.types.util.AbstractTypeExtractor;

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
public class ReadableRecordExtractor extends AbstractTypeExtractor<Type.Record> {

	public ReadableRecordExtractor(NameResolver resolver, TypeSystem typeSystem) {
		super(resolver, typeSystem);
	}

	@Override
	protected Record construct(Atom type) {
		if(type instanceof Record) {
			return (Record) type;
		} else {
			return null;
		}
	}

	@Override
	protected Type.Record union(Type.Record lhs, Type.Record rhs) {
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
					Type type = unionHelper(lhsField.getType(), rhsField.getType());
					fields.add(new FieldDeclaration(type, lhsFieldName));
				}
			}
		}
		//
		boolean isOpenRecord = lhs.isOpen() || rhs.isOpen();
		isOpenRecord |= (lhsFields.length > fields.size() || rhsFields.length > fields.size());
		//
		return new Type.Record(isOpenRecord, fields.toArray(new FieldDeclaration[fields.size()]));
	}

	@Override
	protected Type.Record subtract(Type.Record lhs, Type.Record rhs) {
		// FIXME: implement this
		return null;
	}

	@Override
	protected Type.Record intersect(Type.Record lhs, Type.Record rhs) {
		//
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
			return null;
		} else if (matches < rhsFields.length && !lhs.isOpen()) {
			// Not enough matches made to meet the requirements of the rhs
			// type.
			return null;
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

	/**
	 * Count the number of matching fields. That is, fields with the same name.
	 *
	 * @param lhsFields
	 * @param rhsFields
	 * @return
	 */
	protected int countMatchingFields(FieldDeclaration[] lhsFields, FieldDeclaration[] rhsFields) {
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
	protected int extractMatchingFields(FieldDeclaration[] lhsFields, FieldDeclaration[] rhsFields,
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
					FieldDeclaration combined = new FieldDeclaration(
							intersectionHelper(lhsField.getType(), rhsField.getType()), lhsFieldName);
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
	protected int extractNonMatchingFields(FieldDeclaration[] lhsFields, FieldDeclaration[] rhsFields,
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
}
