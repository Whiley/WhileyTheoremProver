package wyal.lang;

import wyal.lang.NameResolver.ResolutionError;
import wyal.lang.WyalFile.Type;

/**
 * <p>
 * Represents the operation of determining subtyping between <i>raw</i> types.
 * The raw type for a given type <code>T</code> is denoed by
 * <code>&lfloor;T&rfloor;</code>. Raw types ignore any type invariants defined
 * for their operand type. In some cases, a type and its raw type are the same
 * (<code>int</code> and <code>&lfloor;int&rfloor;</code> are the same). In
 * other cases, they are different (e.g. <code>&lfloor;nat&rfloor;</code> has
 * raw type <code>int</code> which is certainly distinct from <code>nat</code>).
 * </p>
 *
 * <p>
 * To understand the purpose of this operator, suppose <code>nat</code> and
 * <code>pos</code> are defined in the obvious way with respective type
 * invariants "<code>x >= 0</code>" and "<code>x > 0</code>". Then, it follows
 * that both "<code>&lfloor;nat&rfloor; :> &lfloor;pos&rfloor;</code>" and
 * "<code>&lfloor;pos&rfloor; :> &lfloor;nat&rfloor;</code>" hold since both
 * correspond to the subtype test "<code>int :> int</code>". That both of these
 * hold identifies the critical loss of information embodied in this operator
 * as, in truth, we know that <code>pos :> nat</code> is false.
 * </p>
 *
 *
 * @author David J. Pearce
 *
 */
public interface RawSubtypeOperator extends SubtypeOperator {
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
	public boolean isRawSubtype(Type lhs, Type rhs) throws ResolutionError;
}
