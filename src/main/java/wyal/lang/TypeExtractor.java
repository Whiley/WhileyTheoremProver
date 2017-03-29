package wyal.lang;

import wyal.lang.WyalFile.Type;

public interface TypeExtractor {
	/**
	 * Attempt to extract a certain kind of type from an arbitrary type. This is
	 * necessary in the presence of powerful type connectives such as
	 * <i>union</i>, <i>intersection</i> and <i>negation</i>. For example, given
	 * the type <code>{int x}|{int x}</code> we can extract the type
	 * <code>{int x}</code>.
	 *
	 * @param type
	 * @param kind
	 * @return
	 */
	public <T extends Type> T extractFrom(Type type, Class<T> kind);
}
