package wyal.lang;

import wyal.lang.NameResolver.ResolutionError;
import wyal.lang.WyalFile.Type;

public interface SubtypeOperator {
	/**
	 * Determine whether one type is a <i>subtype</i> of another. Specifically,
	 * whether the <code>rhs</code> is a subtype of the <code>lhs</code>
	 * (denoted <code>lhs :> rhs</code>). Depending on the exact language of
	 * types involved, this can be a surprisingly complex operation. For
	 * example, in the presence of <i>union</i>, <i>intersection</i> and
	 * <i>negation</i> types, the subtype algorithm is surprisingly intricate.
	 *
	 * @param lhs
	 *            The candidate "supertype". That is, the type for which the
	 *            <code>rhs</code> may be a subtype.
	 * @param rhs
	 *            The candidate "subtype". That is, the type for which the
	 *            <code>lhs</code> may be a supertype.
	 * @return
	 * @throws AmbiguousNameError
	 *             Occurs when a nominal type is encountered whose name is
	 *             resolved to more than one possible matching declaration.
	 * @throws NameNotFoundError
	 *             Occurs when a nominal type is encountered whose name cannot
	 *             be resolved to a corresponding type declaration.
	 */
	public boolean isSubtype(Type lhs, Type rhs) throws ResolutionError;
}
