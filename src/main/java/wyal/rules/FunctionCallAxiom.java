package wyal.rules;

import java.util.List;

import wyal.lang.Formula;
import wyal.lang.Proof;
import wyal.lang.NameResolver.*;
import wyal.lang.Proof.State;
import wyal.lang.WyalFile.Declaration;
import wyal.lang.WyalFile.Expr;
import wyal.lang.WyalFile.Opcode;
import wyal.lang.WyalFile.Tuple;
import wyal.lang.WyalFile.Type;
import wyal.lang.WyalFile.VariableDeclaration;
import wyal.util.Formulae;
import wyal.util.TypeSystem;

public class FunctionCallAxiom extends AbstractProofRule implements Proof.LinearRule {

	public FunctionCallAxiom(TypeSystem types) {
		super(types);
	}

	@Override
	public String getName() {
		return "FunCall-I";
	}

	@Override
	public State apply(State state, Formula truth) throws ResolutionError {
		List<Expr.Invoke> matches = extractDefinedTerms(truth,Opcode.EXPR_invoke);
		if (matches.size() > 0) {
			for (int i = 0; i != matches.size(); ++i) {
				state = applySpecificationInstantiation(state, truth, matches.get(i));
			}
		}
		return state;
	}

	/**
	 * Instantiate the specification of a given (defined) function invocation.
	 *
	 * @param state
	 * @param truth
	 * @param ivk
	 * @return
	 */
	private State applySpecificationInstantiation(Proof.State state, Formula truth, Expr.Invoke ivk) throws ResolutionError {
		// Determine the type declaration in question
		Type.FunctionOrMacroOrInvariant af = ivk.getSignatureType();
		// FIXME: this resolution should have already been performed
		// elsewhere
		Declaration.Named.Function decl = resolve(ivk);
		if (decl != null) {
			// FIXME: there are bugs in the procedure before when new
			// terms are introduced, but not taken to the representative of
			// their equivalence class.
			//
			// Calculate the precondition
			Formula precondition = expandFunctionPrecondition(decl, ivk.getArguments());
			//
			if (precondition != null) {
				precondition = Formulae.simplifyFormula(precondition, types);
				state = state.infer(this, state.allocate(precondition), truth);
			}
			// Calculate the postcondition
			Formula postcondition = expandFunctionPostcondition(decl, ivk);
			//
			if (postcondition != null) {
				postcondition = Formulae.simplifyFormula(postcondition, types);
				state = state.infer(this, state.allocate(postcondition), truth);
			}
		}
		return state;
	}

	private Formula expandFunctionPrecondition(Declaration.Named.Function decl, Tuple<Expr> arguments) throws ResolutionError {
		Formula precondition = null;
		Tuple<VariableDeclaration> parameters = decl.getParameters();
		for (int i = 0; i != parameters.size(); ++i) {
			VariableDeclaration parameter = parameters.getOperand(i);
			Expr argument = arguments.getOperand(i);
			Formula clause = Formulae.extractTypeInvariant(parameter.getType(), argument, types);
			precondition = or(precondition, clause);
		}
		return precondition;
	}

	private Formula expandFunctionPostcondition(Declaration.Named.Function decl, Expr.Invoke ivk) throws ResolutionError {
		Formula precondition = null;
		Tuple<VariableDeclaration> returns = decl.getReturns();
		for (int i = 0; i != returns.size(); ++i) {
			VariableDeclaration parameter = returns.getOperand(i);
			Formula clause = Formulae.extractTypeInvariant(parameter.getType(), ivk, types);
			precondition = or(precondition, clause);
		}
		return precondition;
	}

	private Formula or(Formula lhs, Formula rhs) {
		if(lhs == null) {
			return rhs;
		} else if(rhs == null) {
			return lhs;
		} else {
			return new Formula.Disjunct(lhs,rhs);
		}
	}

	private Declaration.Named.Function resolve(Expr.Invoke ivk) throws ResolutionError {
		Type.FunctionOrMacroOrInvariant signature = ivk.getSignatureType();
		List<Declaration.Named.Function> candidates = types.resolveAll(ivk.getName(),Declaration.Named.Function.class);
		for(int i=0;i!=candidates.size();++i) {
			Declaration.Named.Function fun = candidates.get(i);
			if(fun.getSignatureType().equals(signature)) {
				return fun;
			}
		}
		//
		// Should really be impossible to get here
		throw new NameNotFoundError(ivk.getName());
	}

}
