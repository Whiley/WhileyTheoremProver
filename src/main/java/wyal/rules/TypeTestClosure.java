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

public class TypeTestClosure implements Proof.LinearRule {
	private final TypeSystem types;

	public TypeTestClosure(TypeSystem types) {
		this.types = types;
	}

	@Override
	public String getName() {
		return "Is-Ia";
	}

	@Override
	public State apply(State state, Formula newTruth) throws ResolutionError {
		if (newTruth instanceof Formula.Is) {
			Formula.Is test = (Formula.Is) newTruth;
			if(test.getExpr() instanceof Expr.VariableAccess){
				// FIXME: I think we probably can do better here in some cases
				// by back propagating type information through the expression
				// in question.
				state = retypeVariable(test, state, test);
			} else {
				// At this point, we have a type test which potentially could be
				// closed with one or more other type tests. Therefore, we need to
				// look back through the history to determine any inequalities which
				// are currently "active".
				List<Formula.Is> matches = findMatches(test,state);
				if(matches.size() > 1) {
					state = closeOver(matches,state);
				}
			}
		}
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
		for(int i=0;i!=additions.size();++i) {
			Formula existing = additions.get(i);
			if(existing instanceof Formula.Is) {
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

	/**
	 * Effect the given type test by retyping the variable in question. The type
	 * test is made redundant at this point.
	 *
	 * @param typeTest
	 * @param state
	 * @param dependencies
	 * @return
	 */
	private State retypeVariable(Formula.Is typeTest, Proof.State state, Formula... dependencies) throws ResolutionError {
		Expr lhs = typeTest.getExpr();
		Type lhsT = lhs.getReturnType(types);
		Type rhsT = typeTest.getTypeTest();
		if (lhsT == null) {
			return state;
		} else if (types.isSubtype(rhsT, lhsT)) {
			// Don't need to do anything in this situation.
			return state;
		} else if (lhs instanceof Expr.VariableAccess) {
			Expr.VariableAccess oldVar = (Expr.VariableAccess) lhs;
			VariableDeclaration oldDeclaration = oldVar.getVariableDeclaration();
			Type intersection = TypeSystem.intersect(oldDeclaration.getType(), rhsT);
			if (types.isSubtype(new Type.Void(), intersection)) {
				// This indicates something of a problem has occurred. The type
				// of this variable is void ... so it definitely cannot be
				// instantiated.
				return state.subsume(this, typeTest, state.allocate(new Formula.Truth(false)));
			} else {
				VariableDeclaration newDeclaration = new VariableDeclaration(intersection,
						oldDeclaration.getVariableName());
				Expr.VariableAccess newVar = new Expr.VariableAccess(newDeclaration);
				//
				Proof.Delta history = state.getDelta(null);
				Proof.Delta.Set additions = history.getAdditions();
				//
				for (int i = 0; i != additions.size(); ++i) {
					Formula existing = additions.get(i);
					Formula updated = (Formula) state.substitute(oldVar, newVar, existing, types);
					if (updated != existing) {
						updated = state.allocate(updated);
						state = state.subsume(this, existing, updated, dependencies);
					}
				}
			}
		}
		return state;
	}
}
