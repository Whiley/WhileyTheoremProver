package wyal.lang;

import java.util.List;

import wyal.lang.WyalFile.Declaration;
import wyal.lang.WyalFile.Name;
import wybs.lang.SyntacticElement;

public interface NameResolver {


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
	 * @param context
	 *            The enclosing compilation unit from where we are attempting
	 *            resolve the name. This is important for several reasons.
	 *            Firstly, we may be able to resolve the name directly within
	 *            this compilation unit. Secondly, if we can't resolve within,
	 *            then we will examine those compilation units that are (in some
	 *            way) imported into this one.
	 * @return
	 */
	public <T extends Declaration.Named> T resolveExactly(Name name, Class<T> kind, SyntacticElement context)
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
	 * @param context
	 *            The enclosing compilation unit from where we are attempting
	 *            resolve the name. This is important for several reasons.
	 *            Firstly, we may be able to resolve the name directly within
	 *            this compilation unit. Secondly, if we can't resolve within,
	 *            then we will examine those compilation units that are (in some
	 *            way) imported into this one.
	 * @return
	 */
	public <T extends Declaration.Named> List<T> resolveAll(Name name, Class<T> kind, SyntacticElement context)
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
		private final SyntacticElement context;

		public ResolutionError(Name name, SyntacticElement context, String message) {
			super(message);
			this.name = name;
			this.context = context;
		}

		/**
		 * Get the name being resolved that lead to this error.
		 *
		 * @return
		 */
		public Name getNameBeingResolved() {
			return name;
		}

		/**
		 * Get the syntactic element which led to this name resolution query.
		 * This is important for properly attributing error messages to
		 * element(s) in the original source file which caused the problem.
		 *
		 * @return
		 */
		public SyntacticElement getContext() {
			return context;
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

		public NameNotFoundError(Name name, SyntacticElement context) {
			super(name,context,"name not found");
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

		public AmbiguousNameError(Name name, SyntacticElement context) {
			super(name,context,"ambiguous name");
		}
	}
}
