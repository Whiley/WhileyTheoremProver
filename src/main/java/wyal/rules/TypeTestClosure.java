package wyal.rules;

import java.util.ArrayList;
import java.util.List;

import wyal.lang.Formula;
import wyal.lang.Proof;
import wyal.lang.WyalFile;
import wyal.lang.NameResolver.ResolutionError;
import wyal.lang.Proof.State;
import wyal.lang.WyalFile.Expr;
import wyal.lang.WyalFile.Type;
import wyal.lang.WyalFile.VariableDeclaration;
import wyal.util.Formulae;
import wyal.util.TypeSystem;

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
			// properly. It's possible that using Type.intersection could
			// potentially lead to unbounded growth of the overall type.
			//Type intersection = TypeSystem.intersect(lhsT, rhsT);
			Type intersection = new Type.Intersection(lhsT,rhsT);
			//
			if (types.isSubtype(new Type.Void(), intersection)) {
				// No possible intersection exists between the types in
				// question. Therefore, the test cannot be true.
				return state.subsume(this, typeTest, state.allocate(new Formula.Truth(false)));
			} else {
				// At this point, it seems that the type test cannot be
				// eliminated. The next thing is to assert any type invariants
				// which now hold as a result of this test holding.
				Formula invariant = Formulae.extractTypeInvariant(intersection, lhs, types);
				// Assume extracted type invariant (if one exists)
				if (invariant != null) {
					invariant = state.allocate(invariant);
					state = state.infer(this, invariant, typeTest);
				}
				// In the case of a variable being retyped, we now need to go
				// through a properly effect that by retyping all truths which
				// use that variable. This may allow some of those truths to now
				// type themselves correctly.
				if (lhs instanceof Expr.VariableAccess) {
					state = retypeVariable(typeTest,intersection,state);
				} else {
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
				updated = state.allocate(updated);
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
		Type type = first.getTypeTest();
		//
		for (int i = 1; i != matches.size(); ++i) {
			Formula.Is match = matches.get(i);
			type = TypeSystem.intersect(type, match.getTypeTest());
		}
		//
		Formula test = Formulae.simplifyFormula(new Formula.Is(first.getExpr(), type), types);
		test = state.allocate(test);
		//
		Formula[] froms = matches.toArray(new Formula[matches.size()]);
		state = state.subsume(this, froms, new Formula[] { test });
		//
		return state;
	}

}
