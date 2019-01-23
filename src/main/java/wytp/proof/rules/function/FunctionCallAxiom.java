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
package wytp.proof.rules.function;

import java.util.List;

import wyal.lang.WyalFile;
import wyal.util.NameResolver;
import wyal.util.NameResolver.ResolutionError;
import wyal.util.NameResolver.NameNotFoundError;

import static wyal.lang.WyalFile.*;
import wytp.proof.Formula;
import wytp.proof.Proof;
import wytp.proof.Proof.State;
import wytp.proof.rules.Simplification;
import wytp.proof.util.AbstractProofRule;
import wytp.proof.util.Formulae;
import wytp.types.TypeSystem;

public class FunctionCallAxiom extends AbstractProofRule implements Proof.LinearRule {

	public FunctionCallAxiom(Simplification simplify,TypeSystem types) {
		super(simplify,types);
	}

	@Override
	public String getName() {
		return "FunCall-I";
	}

	@Override
	public State apply(State state, Formula truth) throws ResolutionError {
		List<Expr.Invoke> matches = extractDefinedTerms(truth,WyalFile.EXPR_invoke);
		if (matches.size() > 0) {
			for (int i = 0; i != matches.size(); ++i) {
				Expr.Invoke ivk = matches.get(i);
				// Determine the type declaration in question
				Type.FunctionOrMacroOrInvariant af = ivk.getSignatureType();
				if(af instanceof Type.Function) {
					state = applySpecificationInstantiation(state, truth, matches.get(i));
				}
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
				state = state.infer(this, simp.simplify(precondition), truth);
			}
			// Calculate the postcondition
			Formula postcondition = expandFunctionPostcondition(decl, ivk);
			//
			if (postcondition != null) {
				state = state.infer(this, postcondition, truth);
			}
		}
		return state;
	}

	private Formula expandFunctionPrecondition(Declaration.Named.Function decl, Tuple<Expr> arguments) throws ResolutionError {
		Formula precondition = null;
		Tuple<VariableDeclaration> parameters = decl.getParameters();
		for (int i = 0; i != parameters.size(); ++i) {
			VariableDeclaration parameter = parameters.get(i);
			Expr argument = arguments.get(i);
			Formula clause = types.extractInvariant(parameter.getType(), argument);
			precondition = or(precondition, clause);
		}
		return precondition;
	}

	private Formula expandFunctionPostcondition(Declaration.Named.Function decl, Expr.Invoke ivk) throws ResolutionError {
		Tuple<VariableDeclaration> returns = decl.getReturns();
		Value.Int selector = ivk.getSelector();
		int index = selector == null ? 0 : selector.get().intValue();
		VariableDeclaration parameter = returns.get(index);
		return types.extractInvariant(parameter.getType(), ivk);
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
