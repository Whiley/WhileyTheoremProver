package wyal.rules;

import java.util.ArrayList;
import java.util.List;

import wyal.lang.Formula;
import wyal.lang.Proof;
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
		return "Type-I";
	}

	@Override
	public State apply(State state, Formula newTruth) {
		if(newTruth instanceof Formula.Is) {
			Formula.Is test = (Formula.Is) newTruth;
			// At this point, we have a type test which potentially could be
			// closed with one or more other type tests. Therefore, we need to
			// look back through the history to determine any inequalities which
			// are currently "active".
			List<Formula.Is> matches = findMatches(test,state);
			if(matches.size() > 1) {
				state = closeOver(matches,state);
			} else {
				//state = retypeVariable(test,state);
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

	private State closeOver(List<Formula.Is> matches, Proof.State state) {
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

	private State retypeVariable(Formula.Is typeTest, Proof.State state) {
		Expr lhs = typeTest.getExpr();
		Type rhs = typeTest.getTypeTest();
		if(lhs instanceof Expr.VariableAccess){
			Expr.VariableAccess oldVar = (Expr.VariableAccess) lhs;
			VariableDeclaration oldDeclaration = oldVar.getVariableDeclaration();
			VariableDeclaration newDeclaration = new VariableDeclaration(rhs,oldDeclaration.getVariableName());
			Expr.VariableAccess newVar = new Expr.VariableAccess(newDeclaration);
			//
			Proof.Delta history = state.getDelta(null);
			Proof.Delta.Set additions = history.getAdditions();
			//
			for(int i=0;i!=additions.size();++i) {
				Formula existing = additions.get(i);
				Formula updated = (Formula) state.substitute(oldVar, newVar, existing, types);
				if(updated != existing) {
					updated = state.allocate(updated);
					state = state.subsume(this, existing, updated, typeTest);
				}
			}
		}
		//
		return state;
	}
}
