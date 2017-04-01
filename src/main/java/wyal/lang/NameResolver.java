package wyal.lang;

import java.util.List;

import wyal.lang.WyalFile.Declaration;
import wyal.lang.WyalFile.Name;
import wybs.lang.SyntacticElement;

public interface NameResolver {

	/**
	 * Fully resolve a given name which occurs at some position in a compilation
	 * unit. This takes into account the context and, if necessary, will
	 * traverse important statements to resolve the query.
	 *
	 * @param name
	 * @return
	 */
	public Name resolveFully(Name name);

	/**
	 * <p>
	 * Resolve a given name which occurs at some position in a compilation unit
	 * into exactly one named declaration. Depending on the context, we may be
	 * looking for a specific kind of declaration. For example, for a variable
	 * declaration, we may be looking for the corresponding type declaration.
	 * </p>
	 * <p>
	 * Observe that this method is expecting to find <b>exactly</b> one
	 * corresponding declaration. If it find no such matches or if it finds more
	 * than one match, then a corresponding error will be reported.
	 * </p>
	 *
	 * @param name
	 *            The name to be resolved in the given context.
	 * @param kind
	 *            The kind of declaration we are looking for, which can simply
	 *            be <code>Declaration.Named</code> in the case we are looking
	 *            for any kind of declaration.
	 * @return
	 */
	public <T extends Declaration.Named> T resolveExactly(Name name, Class<T> kind)
			throws NameNotFoundError, AmbiguousNameError;

	/**
	 * <p>
	 * Resolve a given name which occurs at some position in a compilation unit
	 * into one or more named declarations. Depending on the context, we may be
	 * looking for a specific kind of declaration. For example, for a function
	 * invocation expression, we are looking for the corresponding function
	 * declaration.
	 * </p>
	 *
	 * @param name
	 *            The name to be resolved in the given context.
	 * @param kind
	 *            The kind of declaration we are looking for, which can simply
	 *            be <code>Declaration.Named</code> in the case we are looking
	 *            for any kind of declaration.
	 * @return
	 */
	public <T extends Declaration.Named> List<T> resolveAll(Name name, Class<T> kind)
			throws NameNotFoundError;

	/**
	 * A resolution error occurs when a given name cannot be successfully
	 * resolved. Such errors are typically propagated out of the current
	 * processing method to some kind of generic handler (e.g. for reporting
	 * errors).
	 *
	 * @author David J. Pearce
	 *
	 */
	public static class ResolutionError extends Exception {
		/**
		 *
		 */
		private static final long serialVersionUID = 1L;
		private final Name name;

		public ResolutionError(Name name, String message) {
			super(message);
			if(name == null) {
				throw new IllegalArgumentException("name is null");
			}
			this.name = name;
		}

		/**
		 * Get the name being resolved that lead to this error.
		 *
		 * @return
		 */
		public Name getName() {
			return name;
		}
	}

	/**
	 * This error is reported in the case that no matching name can be
	 * identified.
	 *
	 * @author David J. Pearce
	 *
	 */
	public static class NameNotFoundError extends ResolutionError {
		/**
		 *
		 */
		private static final long serialVersionUID = 1L;

		public NameNotFoundError(Name name) {
			super(name,"name \"" + name + "\" not found");
		}
	}

	/**
	 * This error is reported in the case that exactly one match was sought, but
	 * more than one match was found.
	 *
	 * @author David J. Pearce
	 *
	 */
	public static class AmbiguousNameError extends ResolutionError {
		/**
		 *
		 */
		private static final long serialVersionUID = 1L;

		public AmbiguousNameError(Name name) {
			super(name,"name \"" + name + "\" is ambiguous");
		}
	}
}
