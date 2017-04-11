package wytp.proof.rules;

import java.util.ArrayList;
import java.util.List;

import wyal.lang.WyalFile;
import wyal.lang.NameResolver.ResolutionError;
import wyal.lang.WyalFile.Expr;
import wyal.lang.WyalFile.Type;
import wyal.lang.WyalFile.VariableDeclaration;
import wytp.proof.Formula;
import wytp.proof.Proof;
import wytp.proof.Proof.State;
import wytp.proof.util.AbstractProofRule;
import wytp.proof.util.Formulae;
import wytp.types.TypeSystem;

/**
 * <p>
 * Responsible for handling type tests. There are three essential cases that it
 * covers: first, the expansion of type invariants; second, the closure of
 * multiple tests over the same left-hand side; third, the retyping of a given
 * variable. We now consider each of these in turn.
 * </p>
 * <p>
 * <b>Expansion of type invariants.</b> Consider the following assertion:
 *
 * <pre>
 * type nat is (int x) where x >= 0
 *
 * assert:
 *    forall(int x):
 *        if:
 *           x is nat
 *        then:
 *           x >= 0
 * </pre>
 *
 * For proof-by-contradiction we have <code>x is nat && x < 0</code>. Type
 * expansion takes the test <code>x is nat</code> and infers
 * <code>nat(x)</code>, which represents the invariant for type <code>nat</code>
 * applied to <code>x</code>. This is then separately expanded to
 * <code>x >= 0</code> as expected, thus giving the contradiction.
 * </p>
 * <p>
 * <b>Closure over Type Tests.</b> Consider the following assertion
 *
 * <pre>
 * type nullint is (null|int x)
 * type boolint is (bool|int x)
 *
 * assert:
 *    forall({any f} x):
 *        if:
 *           x.f is nullint
 *           x.f is boolint
 *        then:
 *           x.f is int
 * </pre>
 *
 * In this case, to arrive at the contradiction we have to "close over"
 * <code>x.f is nullint</code> and <code>x.f is boolint</code> to conclude that
 * <code>x is int</code>. This is done by intersecting <code>nullint</code> with
 * <code>boolint</code>.
 * </p>
 * <p>
 * <b>Retyping of Variables.</b> In the case of a variable being tested (e.g.
 * <code>x is int</code>), we can perform a <i>complete retyping</i> of all
 * expressions involving <code>x</code> to exploit this additional information.
 * As an example, consider this assertion:
 *
 * <pre>
 * assert:
 *   forall(int[] xs, any i):
 *      if:
 *         i is int
 *      then:
 *         xs[i] is int
 * </pre>
 *
 * In this case, the expression <code>xs[i]</code> <i>can only be typed after
 * variable <code>i</code> is retyped to <code>int</code>.
 * </p>
 *
 * @author David J. Pearce
 *
 */
public class TypeTestClosure extends AbstractProofRule implements Proof.LinearRule {

	public TypeTestClosure(TypeSystem types) {
		super(types);
	}

	@Override
	public String getName() {
		return "Is-I";
	}

	@Override
	public State apply(State state, Formula newTruth) throws ResolutionError {
		if (newTruth instanceof Formula.Is) {
			Formula.Is test = (Formula.Is) newTruth;
			state = apply(test, state);
		}
		return state;
	}

	/**
	 * Effect the given type test by retyping the variable in question. The type
	 * test is made redundant at this point.
	 *
	 * @param typeTest
	 * @param state
	 * @param dependencies
	 * @return
	 */
	private State apply(Formula.Is typeTest, Proof.State state) throws ResolutionError {
		Expr lhs = typeTest.getExpr();
		Type lhsT = lhs.getReturnType(types);
		Type rhsT = typeTest.getTypeTest();
		if (lhsT != null) {
			// FIXME: at the moment, TypeSystem.intersect is not working
			// properly. It's possible that using new Type.Intersection could
			// potentially lead to unbounded growth of the overall type.
			Type intersection = new Type.Intersection(lhsT,rhsT);
			//
			if (types.isRawSubtype(new Type.Void(), intersection)) {
				// No possible intersection exists between the types in
				// question. Therefore, the test cannot be true.
				return state.subsume(this, typeTest, new Formula.Truth(false));
			} else {
				// At this point, it seems that the type test cannot be
				// eliminated. The next thing is to assert any type invariants
				// which now hold as a result of this test holding.
				Formula invariant = types.extractInvariant(intersection, lhs);
				// Assume extracted type invariant (if one exists)
				if (invariant != null) {
					state = state.infer(this, invariant, typeTest);
				}
				// In the case of a variable being retyped, we now need to go
				// through a properly effect that by retyping all truths which
				// use that variable. This may allow some of those truths to now
				// type themselves correctly.
				if (lhs instanceof Expr.VariableAccess) {
					state = retypeVariable(typeTest,intersection,state);
				} else {
					// FIXME: in the case of a field access, we can actually do
					// better here. For example, "x.f is int" can be reduced to
					// "x is {int f,...}".
					List<Formula.Is> matches = findMatches(typeTest,state);
					if(matches.size() > 1) {
						state = closeOver(matches,state);
					}
				}
			}
		}
		return state;
	}

	private Proof.State retypeVariable(Formula.Is typeTest, Type intersection, Proof.State state) {
		Expr.VariableAccess oldVar = (Expr.VariableAccess) typeTest.getOperand(0);
		VariableDeclaration oldDeclaration = oldVar.getVariableDeclaration();
		String tmp = oldDeclaration.getVariableName().get() + "'";
		VariableDeclaration newDeclaration = new VariableDeclaration(intersection,
				new WyalFile.Identifier(tmp));
		Expr.VariableAccess newVar = new Expr.VariableAccess(newDeclaration);
		//
		Proof.Delta history = state.getDelta(null);
		Proof.Delta.Set additions = history.getAdditions();
		//
		for (int i = 0; i != additions.size(); ++i) {
			Formula existing = additions.get(i);
			Formula updated = (Formula) substitute(oldVar, newVar, existing);
			if (existing != typeTest && updated != existing) {
				state = state.subsume(this, existing, updated, typeTest);
			}
		}
		//
		return state;
	}

	/**
	 * Find the complete set of matching type tests. A type test is matching if
	 * it refers to the same left-hand side. For example, if we are matching
	 * <code>(x is int)</code> against <code>(y is int) && (x is !int)</code>,
	 * then this will return <code>x is !int</code>.
	 *
	 * @param lhs
	 * @param state
	 * @return
	 */
	private List<Formula.Is> findMatches(Formula.Is lhs, Proof.State state) {
		Proof.Delta history = state.getDelta(null);
		Proof.Delta.Set additions = history.getAdditions();
		//
		List<Formula.Is> matches = new ArrayList<>();
		//
		for (int i = 0; i != additions.size(); ++i) {
			Formula existing = additions.get(i);
			if (existing instanceof Formula.Is) {
				Formula.Is rhs = (Formula.Is) existing;
				if (lhs.getExpr().equals(rhs.getExpr())) {
					matches.add(rhs);
				}
			}
		}
		//
		return matches;
	}

	private State closeOver(List<Formula.Is> matches, Proof.State state) throws ResolutionError {
		Formula.Is first = matches.get(0);
		Type[] bounds = new Type[matches.size()];
		//
		for (int i = 0; i != matches.size(); ++i) {
			Formula.Is match = matches.get(i);
			bounds[i] = match.getTypeTest();
		}
		//
		Type type = new Type.Intersection(bounds);
		Formula test = Formulae.simplifyFormula(new Formula.Is(first.getExpr(), type), types);
		//
		Formula[] froms = matches.toArray(new Formula[matches.size()]);
		state = state.subsume(this, froms, new Formula[] { test });
		//
		return state;
	}

}
