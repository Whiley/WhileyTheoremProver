// Copyright 2011 The Whiley Project Developers
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//    http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.
package wyal.util;

import java.util.List;

import wybs.lang.CompilationUnit.Name;
import wybs.lang.CompilationUnit.Declaration;;

/**
 * Responsible for resolving a name which occurs at some position in a
 * compilation unit. This takes into account the context and, if necessary, will
 * traverse important statements to resolve the query. For example, consider a
 * compilation unit entitled "file":
 *
 * <pre>
 * import std::ascii::*
 *
 * function f(T1 x, T2 y) -> (int r):
 *    return g(x,y)
 * </pre>
 *
 * Here the name "<code>g</code>" is not fully qualified. Depending on which
 * file the matching declaration of <code>g</code> occurs will depend on what
 * its fully qualified name is. For example, if <code>g</code> is declared in
 * the current compilation unit then it's fully quaified name would be
 * <code>test.g</code>. However, it could well be declared in a compilation unit
 * matching the import <code>whiley.lang.*</code>.
 *
 * @author David J. Pearce
 *
 */
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
	 * <p>
	 * Resolution is determined by the context in which a given name is used.
	 * For example, what imports are active in the enclosing file, as in the
	 * following:
	 * </p>
	 *
	 * <pre>
	 * import std.*
	 *
	 * type nat is integer.uint
	 * </pre>
	 *
	 * <p>
	 * In resolving the name <code>integer.uint</code>, the resolver will
	 * examine the package <code>std</code> to see whether a compilation unit
	 * named "integer" exists. If so, it will then resolve the name
	 * <code>integer.uint</code> to <code>std.integer.uint</code>.
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
	public <T extends Declaration> T resolveExactly(Name name, Class<T> kind) throws ResolutionError;

	/**
	 * <p>
	 * Resolve a given name which occurs at some position in a compilation unit
	 * into one or more named declarations. Depending on the context, we may be
	 * looking for a specific kind of declaration. For example, for a function
	 * invocation expression, we are looking for the corresponding function
	 * declaration.
	 * </p>
	 * <p>
	 * Resolution is determined by the context in which a given name is used.
	 * For example, what imports are active in the enclosing file, as in the
	 * following:
	 * </p>
	 *
	 * <pre>
	 * import std.*
	 *
	 * type nat is integer.uint
	 * </pre>
	 *
	 * <p>
	 * In resolving the name <code>integer.uint</code>, the resolver will
	 * examine the package <code>std</code> to see whether a compilation unit
	 * named "integer" exists. If so, it will then resolve the name
	 * <code>integer.uint</code> to <code>std.integer.uint</code>.
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
	public <T extends Declaration> List<T> resolveAll(Name name, Class<T> kind) throws ResolutionError;

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
			if (name == null) {
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
			super(name, "name \"" + name + "\" not found");
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
			super(name, "name \"" + name + "\" is ambiguous");
		}
	}
}