// Copyright 2017 David J. Pearce
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
package wytp.types;

import java.util.List;

import wyal.lang.NameResolver;
import wyal.lang.NameResolver.ResolutionError;
import wyal.lang.WyalFile;
import wyal.lang.WyalFile.Declaration;
import wyal.lang.WyalFile.Expr;
import wyal.lang.WyalFile.Name;
import wyal.lang.WyalFile.Type;
import wyal.util.WyalFileResolver;
import wytp.proof.Formula;
import wytp.types.extractors.ReadableArrayExtractor;
import wytp.types.extractors.ReadableRecordExtractor;
import wytp.types.extractors.TypeInvariantExtractor;
import wytp.types.subtyping.CoerciveSubtypeOperator;

public class TypeSystem {
	private final NameResolver resolver;
	private final SubtypeOperator coerciveSubtypeOperator;
	private final ReadableRecordExtractor readableRecordExtractor;
	private final ReadableArrayExtractor readableArrayExtractor;
	private final TypeInvariantExtractor typeInvariantExtractor;

	public TypeSystem() {
		this.resolver = new WyalFileResolver();
		this.coerciveSubtypeOperator = new CoerciveSubtypeOperator(resolver);
		this.readableRecordExtractor = new ReadableRecordExtractor(resolver,this);
		this.readableArrayExtractor = new ReadableArrayExtractor(resolver,this);
		this.typeInvariantExtractor = new TypeInvariantExtractor(resolver);
	}

	/**
	 * <p>
	 * Determine whether one type is a <i>raw subtype</i> of another.
	 * Specifically, whether the raw type of <code>rhs</code> is a subtype of
	 * <code>lhs</code>'s raw type (i.e.
	 * "<code>&lfloor;lhs&rfloor; :> &lfloor;rhs&rfloor;</code>"). The raw type
	 * is that which ignores any type invariants involved. Thus, one must be
	 * careful when interpreting the meaning of this operation. Specifically,
	 * "<code>&lfloor;lhs&rfloor; :> &lfloor;rhs&rfloor;</code>" <b>does not
	 * imply</b> that "<code>lhs :> rhs</code>" holds. However, if
	 * "<code>&lfloor;lhs&rfloor; :> &lfloor;rhs&rfloor;</code>" does not hold,
	 * then it <b>does follow</b> that "<code>lhs :> rhs</code>" also does not
	 * hold.
	 * </p>
	 *
	 * <p>
	 * Depending on the exact language of types involved, this can be a
	 * surprisingly complex operation. For example, in the presence of
	 * <i>union</i>, <i>intersection</i> and <i>negation</i> types, the subtype
	 * algorithm is surprisingly intricate.
	 * </p>
	 *
	 * @param lhs
	 *            The candidate "supertype". That is, lhs's raw type may be a
	 *            supertype of <code>rhs</code>'s raw type.
	 * @param rhs
	 *            The candidate "subtype". That is, rhs's raw type may be a
	 *            subtype of <code>lhs</code>'s raw type.
	 * @return
	 * @throws ResolutionError
	 *             Occurs when a nominal type is encountered whose name cannot
	 *             be resolved properly. For example, it resolves to more than
	 *             one possible matching declaration, or it cannot be resolved
	 *             to a corresponding type declaration.
	 */
	public boolean isRawSubtype(Type lhs, Type rhs) throws ResolutionError {
		return coerciveSubtypeOperator.isSubtype(lhs,rhs) != SubtypeOperator.Result.False;
	}

	/**
	 * For a given type, extract its effective record type. For example, the
	 * type <code>({int x, int y}|{int x, int z})</code> has effective record
	 * type <code>{int x, ...}</code>. The following illustrates some more
	 * cases:
	 *
	 * <pre>
	 * {int x, int y} | null    ==> null
	 * {int x, int y} | {int x} ==> null
	 * {int x, int y} | {int x, bool y} ==> {int x, int|bool y}
	 * {int x, int y} & null    ==> null
	 * {int x, int y} & {int x} ==> null
	 * {int x, int y} & {int x, int|bool y} ==> {int x, int y}
	 * </pre>
	 *
	 * @param type
	 * @return
	 * @throws ResolutionError
	 */
	public Type.Record extractReadableRecord(Type type) throws ResolutionError {
		return readableRecordExtractor.extract(type,null);
	}

	/**
	 * Extract the readable array type from a given type. For example, the type
	 * <code>(int[])|(bool[])</code> has a readable array type of
	 * <code>(int|bool)[]</code>.
	 *
	 * @param type
	 * @return
	 * @throws ResolutionError
	 */
	public Type.Array extractReadableArray(Type type) throws ResolutionError {
		return readableArrayExtractor.extract(type,null);
	}

	/**
	 * Extracting the invariant (if any) from a given type. For example,
	 * consider the following type declaration:
	 *
	 * <pre>
	 * type nat is (int x) where x >= 0
	 * </pre>
	 *
	 * Then, extracting the invariant from type <code>nat</code> gives
	 * <code>x >= 0</code>. Likewise, extracting the invariant from the type
	 * <code>bool|int</code> gives the invariant
	 * <code>(x is int) ==> (x >= 0)</code>. Finally, extracting the invariant
	 * from the type <code>nat[]</code> gives the invariant
	 * <code>forall(int i).(0 <= i
	 * && i < |xs| ==> xs[i] >= 0)</code>.
	 *
	 *
	 */
	public Formula extractInvariant(Type type, Expr root)  throws ResolutionError {
		return typeInvariantExtractor.extract(type,root);
	}

	// ========================================================================
	// Resolution
	// ========================================================================

	public <T extends Declaration.Named> T resolveExactly(Name name, Class<T> kind)
			throws ResolutionError {
		return resolver.resolveExactly(name,kind);
	}

	public <T extends Declaration.Named> List<T> resolveAll(Name name, Class<T> kind)
			throws ResolutionError {
		return resolver.resolveAll(name,kind);
	}

}
