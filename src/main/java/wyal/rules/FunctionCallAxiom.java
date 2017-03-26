package wyal.rules;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.List;

import wyal.lang.Formula;
import wyal.lang.Proof;
import wyal.lang.SyntacticItem;
import wyal.lang.WyalFile;
import wyal.lang.Proof.State;
import wyal.lang.WyalFile.Declaration;
import wyal.lang.WyalFile.Expr;
import wyal.lang.WyalFile.Opcode;
import wyal.lang.WyalFile.Tuple;
import wyal.lang.WyalFile.Type;
import wyal.lang.WyalFile.VariableDeclaration;
import wyal.util.Formulae;
import wyal.util.TypeSystem;

public class FunctionCallAxiom implements Proof.LinearRule {
	private final TypeSystem types;

	public FunctionCallAxiom(TypeSystem types) {
		this.types = types;
	}

	@Override
	public String getName() {
		return "FunCall-I";
	}

	@Override
	public State apply(State state, Formula truth) {
		List<Expr.Invoke> matches = findFunctionInvocations(truth);
		if (matches.size() > 0) {
			for (int i = 0; i != matches.size(); ++i) {
				state = applyPreconditionInstantiation(state, truth, matches.get(i));
			}
		}
		return state;
	}

	/**
	 * Search through a given syntactic item looking for function invocation.
	 *
	 * @param e
	 * @return
	 */
	private List<Expr.Invoke> findFunctionInvocations(SyntacticItem e, Formula.Quantifier... stack) {
		List<Expr.Invoke> result = Collections.EMPTY_LIST;
		switch (e.getOpcode()) {
		case EXPR_invoke: {
			result = checkFunctionInvocation((Expr.Invoke) e, stack);
			break;
		}
		case EXPR_exists:
		case EXPR_forall: {
			stack = Arrays.copyOf(stack, stack.length+1);
			stack[stack.length-1] = (Formula.Quantifier)e;
			break;
		}
		case EXPR_or: {
			Formula.Disjunct disjunct = (Formula.Disjunct) e;
			// Disjunctions need to be handled with care. We cannot extract
			// truths which only hold in one clause of the disjunct. Rather, we
			// can only extract truths which hold on all clauses.
			result = null;
			for(int i=0;i!=disjunct.size();++i) {
				SyntacticItem child = disjunct.getOperand(i);
				List<Expr.Invoke> tmp = findFunctionInvocations(child,stack);
				if(result == null) {
					result = tmp;
				} else {
					result = intersect(result,tmp);
				}
			}
			return result;
		}
		}
		// Generic traversal, returning first split point encountered.
		for (int i = 0; i != e.size(); ++i) {
			SyntacticItem child = e.getOperand(i);
			result = union(result,findFunctionInvocations(child,stack));
		}
		//
		return result;
	}

	/**
	 * Check whether or not a function invocation can be matched. In essence, we
	 * cannot match anything which contains a universally quantified variable.
	 * This is because we cannot pull such information outside of the quantifier
	 * in question.
	 *
	 * @param ivk
	 * @param stack
	 * @return
	 */
	private List<Expr.Invoke> checkFunctionInvocation(Expr.Invoke ivk, Formula.Quantifier... stack) {
		for (int i = 0; i != stack.length; ++i) {
			Formula.Quantifier quantifier = stack[i];
			if (quantifier.getSign()) {
				// Only need to worry about universal quantification.
				Tuple<VariableDeclaration> parameters = quantifier.getParameters();
				if (containsQuantifiedVariable(ivk, parameters.getOperands())) {
					return Collections.EMPTY_LIST;
				}
			}
		}
		ArrayList<Expr.Invoke> result = new ArrayList<>();
		result.add(ivk);
		return result;
	}

	private boolean containsQuantifiedVariable(SyntacticItem item, VariableDeclaration[] quantifiedVariables) {
		List<VariableDeclaration> usedVariables = findAll(item, VariableDeclaration.class);
		for (int i = 0; i != quantifiedVariables.length; ++i) {
			for (int j = 0; j != usedVariables.size(); ++j) {
				if (quantifiedVariables[i] == usedVariables.get(j)) {
					return true;
				}
			}
		}
		//
		return false;
	}

	private State applyPreconditionInstantiation(Proof.State state, Formula truth, Expr.Invoke ivk) {
		// Determine the type declaration in question
		Type.FunctionOrMacroOrInvariant af = ivk.getSignatureType();
		// FIXME: this resolution should have already been performed
		// elsewhere
		Declaration.Named.Function decl = types.resolveAsDeclaration(ivk.getName(),Declaration.Named.Function.class);
		if (decl != null) {
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

	private Formula expandFunctionPrecondition(Declaration.Named.Function decl, Tuple<Expr> arguments) {
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

	private Formula expandFunctionPostcondition(Declaration.Named.Function decl, Expr.Invoke ivk) {
		Formula precondition = null;
		Tuple<VariableDeclaration> returns = decl.getReturns();
		for (int i = 0; i != returns.size(); ++i) {
			VariableDeclaration parameter = returns.getOperand(i);
			Formula clause = Formulae.extractTypeInvariant(parameter.getType(), ivk, types);
			precondition = or(precondition, clause);
		}
		return precondition;
	}

	private <T extends SyntacticItem> List<T> findAll(SyntacticItem e, Class<T> kind) {
		List<T> result = Collections.EMPTY_LIST;
		if(kind.isInstance(e)) {
			result = new ArrayList<>();
			result.add((T)e);
		}
		// Generic traversal, returning first split point encountered.
		for (int i = 0; i != e.size(); ++i) {
			SyntacticItem child = e.getOperand(i);
			result = union(result,findAll(child,kind));
		}
		//
		return result;
	}

	/**
	 * Add all items from two lists together. Either or both of these may be
	 * empty and equal to Collections.EMPTY_LIST.
	 *
	 * @param lhs
	 * @param rhs
	 * @return
	 */
	private <T> List<T> union(List<T> lhs, List<T> rhs) {
		if(lhs.size() > 0) {
			lhs.addAll(rhs);
			return lhs;
		} else {
			return rhs;
		}
	}

	private <T> List<T> intersect(List<T> lhs, List<T> rhs) {
		if(lhs.size() == 0) {
			return lhs;
		} else if(rhs.size() == 0) {
			return rhs;
		} else {
			ArrayList<T> result = new ArrayList<>();
			for(int i=0;i!=lhs.size();++i) {
				T l = lhs.get(i);
				for(int j=0;j!=rhs.size();++j) {
					T r = rhs.get(j);
					if(l.equals(r)) {
						result.add(l);
						break;
					}
				}
			}
			return result;
		}
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
}
