package wyal.rules;

import wyal.lang.Formula;
import wyal.lang.Proof;
import wyal.lang.Formula.Conjunct;
import wyal.lang.NameResolver.ResolutionError;
import wyal.lang.Proof.State;
import wyal.lang.WyalFile.Expr;
import wyal.lang.WyalFile.Tuple;
import wyal.lang.WyalFile.VariableDeclaration;
import wyal.types.TypeSystem;
import wyal.util.Formulae;

/**
 * <p>
 * Responsible for eliminating an existential quantifier through
 * <i>skolemisation</i>. For example, if we encounter
 * <code>exists(int i).(i >= 0)</code> then we replace this with the ground term
 * <code>i >= 0</code>, where <code>i</code> is now a <i>skolem</i> (that is, an
 * unknown constant).
 * </p>
 * <p>
 * <b>NOTE:</b> This rule current exploits the underlying structure of a
 * syntactic heap for ensuring that a given variable remains a skolem. This is
 * problematic in the case of existentials nested within universal quantifiers
 * and could be improved somewhat.
 * </p>
 *
 * @author David J. Pearce
 *
 */
public class ExistentialElimination implements Proof.LinearRule {
	private final TypeSystem types;

	public ExistentialElimination(TypeSystem types) {
		this.types = types;
	}

	@Override
	public String getName() {
		return "Exists-E";
	}

	@Override
	public State apply(Proof.State state, Formula truth) throws ResolutionError {
		if(truth instanceof Formula.Quantifier) {
			Formula.Quantifier qf = (Formula.Quantifier) truth;
			if(!qf.getSign()) {
				Formula body = qf.getBody();
				// Expand any type invariants
				Formula invariant = expandTypeInvariants(qf.getParameters(),types);
				// Add type invariants (if appropriate)
				if (invariant != null) {
					body = Formulae.simplifyFormula(new Conjunct(invariant, body),types);
					body = state.allocate(body);
				}
				state = state.subsume(this, qf, body);
			}
		}
		// No change in the normal case
		return state;
	}

	/**
	 * For a given sequence of variable declarations expand their type
	 * invariants as appropriate. This expansion is done lazily, in that it
	 * produces invocations to the type invariants themselves. Such invocations
	 * must then be separately expanded (like macros) later on. As an example,
	 * consider this:
	 *
	 * <pre>
	 * type nat is (int x) where x >= 0
	 *
	 * assert:
	 *     forall(nat x):
	 *         x >= 0
	 * </pre>
	 *
	 * The type invariant given for <code>x</code> in the quantifier will be
	 * expanded, to give then body <code>nat(x) ==> x >= 0</code>. The call
	 * <code>nat(x)</code> will later be expanded during theorem proving to
	 * <code>x >= 0</code>. The reason this is done lazily is to properly
	 * support recursive types and their invariants.
	 *
	 * @param declarations
	 * @param types
	 * @return
	 * @throws ResolutionError
	 */
	protected Formula expandTypeInvariants(Tuple<VariableDeclaration> declarations, TypeSystem types)
			throws ResolutionError {
		Formula result = null;
		for (int i = 0; i != declarations.size(); ++i) {
			VariableDeclaration variable = declarations.getOperand(i);
			Formula invariant = types.extractInvariant(variable.getType(), new Expr.VariableAccess(variable));
			// FIXME: need to perform appropriate variable substitution here?
			if (invariant != null && result == null) {
				result = invariant;
			} else if (invariant != null) {
				result = new Conjunct(result, invariant);
			}
		}
		return result;
	}
}
