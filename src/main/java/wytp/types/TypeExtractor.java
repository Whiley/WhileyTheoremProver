package wytp.types;

import wyal.lang.NameResolver.ResolutionError;
import wyal.lang.WyalFile.Type;

public interface TypeExtractor<T,S> {
	/**
	 * Attempt to extract a certain kind of type from an arbitrary type. This is
	 * necessary in the presence of powerful type connectives such as
	 * <i>union</i>, <i>intersection</i> and <i>negation</i>. For example, given
	 * the type <code>{int x}|{int x}</code> we can extract the type
	 * <code>{int x}</code>.
	 *
	 * @param type
	 *            The type for which information is to be extracted
	 * @param supplementary
	 *            Supplementary information which may be used by the extractor.
	 * @return
	 */
	public T extract(Type type, S supplementary) throws ResolutionError;
}
