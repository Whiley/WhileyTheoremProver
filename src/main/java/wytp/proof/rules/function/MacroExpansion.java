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
package wytp.proof.rules.function;

import java.util.Arrays;
import java.util.IdentityHashMap;
import java.util.List;
import java.util.Map;

import wyal.heap.SyntacticHeaps;
import wyal.lang.WyalFile;

import static wyal.lang.WyalFile.*;
import wyal.lang.WyalFile.Stmt.Block;
import wybs.lang.SyntacticItem;
import wybs.lang.NameResolver.NameNotFoundError;
import wybs.lang.NameResolver.ResolutionError;
import wytp.proof.Formula;
import wytp.proof.Proof;
import wytp.proof.Proof.State;
import wytp.proof.rules.Simplification;
import wytp.proof.util.AbstractProofRule;
import wytp.proof.util.Formulae;
import wytp.types.TypeSystem;

/**
 * <p>
 * Responsible for inlining macro invocations from their definitions. For
 * example, consider this assertion:
 * </p>
 *
 * <pre>
 * define nat(int n) is:
 *   n >= 0
 *
 * assert:
 *   forall(int x):
 *       if:
 *           x > 0
 *       then:
 *           nat(x)
 * </pre>
 * <p>
 * In proving this assertion, we will at some point come to the macro invocation
 * <code>nat(x)</code> or its <i>inversion</i> <code>!nat(x)</code>. To deal
 * with this, we simply replace <code>nat(x)</code> by its body where the
 * parameters are substituted for their arguments. That is, we replace
 * <code>nat(x)</code> by <code>n >= 0</code> and substitute <code>n</code> for
 * the argument <code>x</code>.
 * </p>
 * <p>
 * <b>NOTE:</b> A pretty obvious concern with this rule is how to deal with
 * recursive macro definitions. This has not been tried and tested at this
 * stage!
 * </p>
 *
 * @author David J. Pearce
 *
 */
public class MacroExpansion extends AbstractProofRule implements Proof.LinearRule {

	public MacroExpansion(Simplification simplify,TypeSystem types) {
		super(simplify,types);
	}

	@Override
	public String getName() {
		return "Macro-I";
	}

	@Override
	public State apply(Proof.State state, Formula truth) throws ResolutionError {
		Formula expanded = expandFormula(state, truth);
		if(expanded != truth) {
			state = state.subsume(this, truth, expanded);
		}
		return state;
	}

	private Formula expandFormula(Proof.State state, Formula formula) throws ResolutionError {
		if (formula instanceof Formula.Invoke) {
			Formula.Invoke ivk = (Formula.Invoke) formula;
			// Determine the type declaration in question
			Type.FunctionOrMacroOrInvariant af = ivk.getSignatureType();
			if(af instanceof Type.Function) {
				// We ignore function macros here
				return null;
			}
			// Resolve the declaration corresponding to this invocation
			Declaration.Named decl = resolve(ivk);
			//
			Formula invariant = extractDeclarationInvariant(state, decl, ivk.getArguments());
			if (invariant != null) {
				if (!ivk.getSign()) {
					invariant = Formulae.invert(invariant);
				}
				// Update the state
				return invariant;
			}
		} else if(formula instanceof Formula.Quantifier) {
			Formula.Quantifier quantifier = (Formula.Quantifier) formula;
			if(quantifier.getSign()) {
				// There's no point going into existentials since they will be
				// expanded anyway,
				Formula body = expandFormula(state, quantifier.getBody());
				if(body != quantifier.getBody()) {
					return new Formula.Quantifier(true, quantifier.getParameters(), body);
				}
			}
		} else if(formula instanceof Formula.Disjunct) {
			Formula.Disjunct disjunct = (Formula.Disjunct) formula;
			Formula[] children = disjunct.getOperands();
			Formula[] nChildren = expandFormula(state, children);
			if(nChildren != children) {
				return new Formula.Disjunct(nChildren);
			}
		} else if(formula instanceof Formula.Conjunct) {
			Formula.Conjunct disjunct = (Formula.Conjunct) formula;
			Formula[] children = disjunct.getOperands();
			Formula[] nChildren = expandFormula(state, children);
			if(nChildren != children) {
				return new Formula.Conjunct(nChildren);
			}
		}
		return formula;
	}

	private Formula[] expandFormula(Proof.State state, Formula... children) throws ResolutionError {
		Formula[] nChildren = children;
		for(int i=0;i!=children.length;++i) {
			Formula child = nChildren[i];
			Formula nChild = expandFormula(state, child);
			if(child != nChild && nChildren == children) {
				nChildren = Arrays.copyOf(children, children.length);
			}
			nChildren[i] = nChild;
		}
		return nChildren;
	}

	private Formula extractDeclarationInvariant(Proof.State state, Declaration.Named decl, Tuple<Expr> arguments) throws ResolutionError {
		if (decl instanceof Declaration.Named.Type) {
			// This is a type invariant macro call. In such case, we
			// need to first determine what the invariant actually is.
			Declaration.Named.Type td = (Declaration.Named.Type) decl;
			// Expand the corresponding type invariant
			return expandTypeInvariant(state, td, arguments.getOperand(0));
		} else if (decl instanceof Declaration.Named.Macro) {
			Declaration.Named.Macro md = (Declaration.Named.Macro) decl;
			// Expand the macro body with appropriate substitutions
			return expandMacroBody(state, md, arguments.getOperands());
		} else {
			// Functions are ignored
			return null;
		}
	}

	private Formula expandMacroBody(Proof.State state, Declaration.Named.Macro md, Expr[] arguments) throws ResolutionError {
		Tuple<VariableDeclaration> parameters = md.getParameters();
		// Initialise the map with the identity for parameters to ensure they
		// are preserved as is, and can then be substituted.
		Map<SyntacticItem, SyntacticItem> map = new IdentityHashMap<>();
		for (int i = 0; i != parameters.size(); ++i) {
			map.put(parameters.getOperand(i), parameters.getOperand(i));
		}
		// Clone is required at this point to ensure that any variable
		// declarations are distinguished appropriately.
		WyalFile.Stmt.Block block = SyntacticHeaps.cloneOnly(md.getBody(), map, WyalFile.VariableDeclaration.class);
		Formula body = Formulae.toFormula(block, types);
		for (int i = 0; i != arguments.length; ++i) {
			// At this point, we must substitute the parameter name used in
			// the type declaration for the name used as the invocation
			// argument.
			Expr.VariableAccess parameter = new Expr.VariableAccess(parameters.getOperand(i));
			body = (Formula) substitute(parameter, arguments[i], body);
		}
		return body;
	}

	private Formula expandTypeInvariant(Proof.State state, Declaration.Named.Type td, Expr argument) throws ResolutionError {
		// Extract only the explicit invariants given using where clauses.
		Tuple<Block> invariant = td.getInvariant();
		Formula result = types.extractInvariant(td.getVariableDeclaration().getType(), argument);
		for (int i = 0; i != invariant.size(); ++i) {
			// Convert the invariant clause into a formula
			Formula ith = Formulae.toFormula(invariant.getOperand(i), types);
			//
			result = result == null ? ith : new Formula.Conjunct(result, ith);
		}
		if (result == null) {
			return null;
		} else {
			// At this point, we must substitute the variable name used in
			// the type declaration for the name used as the invocation
			// argument.

			// FIXME: this is only necessary for the invariant itself, not the
			// extracted type invariant.

			Expr.VariableAccess parameter = new Expr.VariableAccess(td.getVariableDeclaration());
			result = (Formula) substitute(parameter, argument, result);
			return result;
		}
	}

	private Declaration.Named resolve(Expr.Invoke ivk) throws ResolutionError {
		if (ivk.getSignatureType() instanceof Type.Property) {
			List<Declaration.Named.Macro> candidates = types.resolveAll(ivk.getName(), Declaration.Named.Macro.class);
			Type.FunctionOrMacroOrInvariant signature = ivk.getSignatureType();
			for (int i = 0; i != candidates.size(); ++i) {
				Declaration.Named.Macro macro = candidates.get(i);
				if (macro.getSignatureType().equals(signature)) {
					return macro;
				}
			}
			//
			// Should really be impossible to get here
			throw new NameNotFoundError(ivk.getName());
		} else {
			return types.resolveExactly(ivk.getName(), Declaration.Named.Type.class);
		}
	}
}
