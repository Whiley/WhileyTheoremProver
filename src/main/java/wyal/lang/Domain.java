package wyal.lang;

import wyal.lang.WyalFile.Type;

/**
 * <p>
 * A domain represents a universe of values over which an assertion can be
 * tested for validity. The most obvious example of this would be the
 * <i>concrete domain</i>, which represents real concrete values and, hence, we
 * can simply execute an assertion to set whether it evaluates to
 * <code>true</code>, <code>false</code> or is <i>undefined</i>. The intention,
 * however, is that more complex abstract domains are possible allows us, for
 * example, to <i>symbolically execute</i> an assertion.
 * </p>
 *
 * @author David J. Pearce
 *
 */
public interface Domain {
	/**
	 * Construct an iterator that will walk over all known values for a
	 * given type.
	 *
	 * @param type
	 * @return
	 */
	Domain.Generator generator(Type type);

	public interface Generator {
		/**
		 * Determine whether there is another element in this domain.
		 *
		 * @return
		 */
		public boolean hasNext();

		/**
		 * Get the current value of this generator
		 *
		 * @return
		 */
		public Object get();

		/**
		 * Move this generator to its next value
		 */
		public void next();

		/**
		 * Reset this generator back to the beginning
		 */
		public void reset();
	}

	/**
	 * Represents an abstract value within the given domain.
	 *
	 * @author David J. Pearce
	 *
	 */
	public interface Value {
		/**
		 * Determine whether or not two abstract values are equal.
		 *
		 * @param value
		 * @return
		 */
		public Value.Boolean equal(Value value);

		/**
		 * Check whether a given abstract value is an instance of a give type or
		 * not.
		 *
		 * @param type
		 * @return
		 */
		public Value.Boolean isInstance(Type type);

		/**
		 * Represents an abstract <code>null</code> value.
		 *
		 * @author David J. Pearce
		 *
		 */
		public interface Null {

		}

		/**
		 * Represents an abstract <code>bool</code> value which has only two
		 * concrete instantiations (<code>true</code> and <code>false</code>).
		 *
		 * @author David J. Pearce
		 *
		 */
		public interface Boolean {
			public Value.Boolean and(Value.Boolean b);

			public Value.Boolean or(Value.Boolean b);
		}

		/**
		 * Represents an abstract <code>int</code> value which has a potentially
		 * infinite number of integer values.
		 *
		 * @author David J. Pearce
		 *
		 */
		public interface Integer {
			public Value.Boolean lessThanOrEqual(Value.Integer other);

			public Value.Integer add(Value.Integer other);

			public Value.Integer subtract(Value.Integer other);

			public Value.Integer multiply(Value.Integer other);

			public Value.Integer divide(Value.Integer other);
		}

		/**
		 * Represents an abstract <code>array</code> value which has a
		 * potentially infinite number of array values.
		 *
		 * @author David J. Pearce
		 *
		 */
		public interface Array {
			public Value.Integer length();

			public Value getIndex(Value.Integer index);

			public Value.Array setIndex(Value.Integer index, Value value);
		}

		/**
		 * Represents an abstract <code>record</code> value which has a
		 * potentially infinite number of record values.
		 *
		 * @author David J. Pearce
		 *
		 */
		public interface Record {
			public Value getField(WyalFile.Identifier fieldName);

			public Value.Record setField(WyalFile.Identifier fieldName, Value value);
		}
	}
}