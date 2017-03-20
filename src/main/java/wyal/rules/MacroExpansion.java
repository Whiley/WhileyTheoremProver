package wyal.rules;

import java.util.IdentityHashMap;
import java.util.Map;

import wyal.heap.SyntacticHeaps;
import wyal.lang.Formula;
import wyal.lang.Proof;
import wyal.lang.SyntacticItem;
import wyal.lang.WyalFile;
import wyal.lang.Proof.State;
import wyal.lang.WyalFile.Declaration;
import wyal.lang.WyalFile.Expr;
import wyal.lang.WyalFile.Tuple;
import wyal.lang.WyalFile.Type;
import wyal.lang.WyalFile.VariableDeclaration;
import wyal.lang.WyalFile.Stmt.Block;
import wyal.util.Formulae;
import wyal.util.TypeSystem;

public class MacroExpansion implements Proof.LinearRule {
	private final TypeSystem types;

	public MacroExpansion(TypeSystem types) {
		this.types = types;
	}

	@Override
	public String getName() {
		return "Macro-I";
	}

	@Override
	public State apply(Proof.State state, Formula truth) {
		if(truth instanceof Formula.Invoke) {
			Formula.Invoke ivk = (Formula.Invoke) truth;
			// Determine the type declaration in question
			Type.FunctionOrMacro af = ivk.getSignatureType();
			// Resolve the declaration corresponding to this invocation
			Declaration.Named decl = types.resolveAsDeclaration(ivk.getName());
			// Calculate the invariant (if any)
			Formula invariant = extractDeclarationInvariant(decl, ivk.getArguments());
			if (invariant != null) {
				if (!ivk.getSign()) {
					invariant = Formulae.simplifyFormula(Formulae.invert(invariant), types);
				}
				// Update the state
				state = state.subsume(this, ivk, state.allocate(invariant));
			}
		}
		return state;
	}

	private Formula extractDeclarationInvariant(Declaration.Named decl, Tuple<Expr> arguments) {
		if (decl instanceof Declaration.Named.Type) {
			// This is a type invariant macro call. In such case, we
			// need to first determine what the invariant actually is.
			Declaration.Named.Type td = (Declaration.Named.Type) decl;
			// Expand the corresponding type invariant
			return expandTypeInvariant(td, arguments.getOperand(0));
		} else if (decl instanceof Declaration.Named.Macro) {
			Declaration.Named.Macro md = (Declaration.Named.Macro) decl;
			// Expand the macro body with appropriate substitutions
			return expandMacroBody(md, arguments.getOperands());
		} else {
			return null;
		}
	}

	private Formula expandMacroBody(Declaration.Named.Macro md, Expr[] arguments) {
		VariableDeclaration[] parameters = md.getParameters().getOperands();
		// Initialise the map with the identity for parameters to ensure they
		// are preserved as is, and can then be substituted.
		Map<SyntacticItem, SyntacticItem> map = new IdentityHashMap<>();
		for (int i = 0; i != parameters.length; ++i) {
			map.put(parameters[i], parameters[i]);
		}
		// Clone is required at this point to ensure that any variable
		// declarations are distinguished appropriately.
		WyalFile.Stmt.Block block = SyntacticHeaps.cloneOnly(md.getBody(), map, WyalFile.VariableDeclaration.class);
		Formula body = Formulae.toFormula(block, types);
		for (int i = 0; i != arguments.length; ++i) {
			// At this point, we must substitute the parameter name used in
			// the type declaration for the name used as the invocation
			// argument.
			Expr.VariableAccess parameter = new Expr.VariableAccess(parameters[i]);
			body = (Formula) Formulae.substitute(parameter, arguments[i], body);
		}
		return Formulae.simplifyFormula(body, types);
	}

	private Formula expandTypeInvariant(Declaration.Named.Type td, Expr argument) {
		// Extract only the explicit invariants given using where clauses.
		Tuple<Block> invariant = td.getInvariant();
		Formula result = Formulae.extractTypeInvariant(td.getVariableDeclaration().getType(), argument, types);
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
			Expr.VariableAccess parameter = new Expr.VariableAccess(td.getVariableDeclaration());
			result = (Formula) Formulae.substitute(parameter, argument, result);
			return Formulae.simplifyFormula(result, types);
		}
	}
}
