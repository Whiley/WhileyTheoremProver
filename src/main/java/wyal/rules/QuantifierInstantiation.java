package wyal.rules;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import wyal.lang.Formula;
import wyal.lang.Proof;
import wyal.lang.WyalFile;
import wyal.lang.Proof.State;
import wyal.lang.WyalFile.Expr;
import wyal.lang.WyalFile.Expr.Polynomial;
import wyal.lang.WyalFile.Pair;
import wyal.lang.WyalFile.Type;
import wyal.lang.WyalFile.VariableDeclaration;
import wyal.util.Formulae;
import wyal.util.TypeSystem;

public class QuantifierInstantiation implements Proof.LinearRule {
	private final TypeSystem types;

	public QuantifierInstantiation(TypeSystem types) {
		this.types = types;
	}

	@Override
	public String getName() {
		return "Forall-I";
	}

	@Override
	public State apply(Proof.State state, Formula newTruth) {

		if(newTruth instanceof Formula.Inequality) {
			Formula.Inequality ground = (Formula.Inequality) newTruth;
			return instantiateQuantifiers(ground,state);
		}
		// No change in the normal case
		return state;
	}

	private Set<Expr> extractTerms(Polynomial polynomial) {
		HashSet<Expr> terms = new HashSet<>();
		for (int i = 0; i != polynomial.size(); ++i) {
			Polynomial.Term term = polynomial.getOperand(i);
			Expr[] atoms = term.getAtoms();
			for (int j = 0; j != atoms.length; ++j) {
				terms.add(atoms[j]);
			}
		}
		return terms;
	}

	private State instantiateQuantifiers(Formula.Inequality groundTerm, State state) {
		// At this point, we have an equality or inequality which potentially
		// could be used to instantiate one or more existing (universal)
		// quantifiers. Therefore, we need to look back through the history to
		// determine any cases where this can be applied.
		Proof.Delta history = state.getDelta(null);
		Proof.Delta.Set additions = history.getAdditions();
		for(int i=0;i!=additions.size();++i) {
			Formula truth = additions.get(i);
			if(truth instanceof Formula.Quantifier) {
				Formula.Quantifier qf = (Formula.Quantifier) truth;
				if(qf.getSign()) {
					// Yes, this is a universal quantifier
					state = applyQuantifierInstantiation(qf,groundTerm,EMPTY_BINDING,state);
				}
			}
		}
		//
		return state;
	}

	private static Expr[] EMPTY_BINDING = new Expr[0];

	private State applyQuantifierInstantiation(Formula.Quantifier quantifier, Formula.Inequality groundTerm,
			Expr[] binding, State state) {

		VariableDeclaration[] parameters = quantifier.getParameters().getOperands();
		if (binding.length == parameters.length) {
			// Binding now complete, so proceed to instantiate quantifier.
			// First, substitute body through for the binding obtained for each
			// parameter.
			Formula body = quantifier.getBody();
			// FIXME: there is a bug of sorts here related to skolems
			for (int i = 0; i != parameters.length; ++i) {
				VariableDeclaration parameter = parameters[i];
				Expr.VariableAccess access = new Expr.VariableAccess(parameter);
				body = (Formula) Formulae.substitute(access, binding[i], body);
			}
			// Second, instantiate the ground body
			body = state.allocate(Formulae.simplifyFormula(body, types));
			return state.infer(QuantifierInstantiation.this, body, quantifier);
		} else {
			// Exhaustively instantiate this variable with all possible ground
			// terms.
			VariableDeclaration quantifiedVariable = parameters[binding.length];
			Type pt = quantifiedVariable.getType();
			List<Expr> grounds = match(quantifiedVariable, quantifier, groundTerm);
			//
			System.out.println("MATCHED: " + grounds);
			//
			for (int i = 0; i != grounds.size(); ++i) {
				Expr ground = grounds.get(i);
				Type gt = ground.getReturnType(types);
				// Make sure ground term is compatible with parameter in
				// question. If not, then it's not a valid substitution and
				// should be skipped.
				if (types.isSubtype(pt, gt)) {
					Expr[] nBinding = Arrays.copyOf(binding, binding.length + 1);
					nBinding[binding.length] = ground;
					state = applyQuantifierInstantiation(quantifier, groundTerm, nBinding, state);
				}
			}
			return state;
		}
	}

	/**
	 * Match a given term quantified over a given variable against a ground
	 * term. For example, if "i" is a quantified variable then we might try
	 * matching "A[i] < 0" against "0 < A[1]". In this case, our list of matches
	 * would contain just "1". Observe that the key here is that the matches are
	 * occurring on opposite "sides" of the equation. This is important for
	 * being "goal driven" in that we are looking for potential contradictions.
	 *
	 * @param variable
	 * @return
	 */
	private List<Expr> match(VariableDeclaration variable, Formula.Quantifier quantifier, Formula.Inequality ground) {
		ArrayList<Expr> matches = new ArrayList<>();
		matchHelper(variable,quantifier.getBody(),ground,matches);
		return matches;
	}

	private void matchHelper(VariableDeclaration variable, Formula quantified, Formula.Inequality ground,
			List<Expr> matches) {
		if (quantified instanceof Formula.Inequality) {
			matchInequality(variable, (Formula.Inequality) quantified, ground, matches);
		} else {
			// FIXME: should do more here!!
		}
	}

	private void matchInequality(VariableDeclaration variable, Formula.Inequality quantified, Formula.Inequality ground, List<Expr> matches) {

		// FIXME: do we need to have one side "locked". That is, matching?

		// Positive (Quantified) versus Negative (Ground)
		matchPolynomial(variable,quantified.getOperand(0),ground.getOperand(1),matches);
		//  Negative (Quantified) versus Positive (Ground)
		matchPolynomial(variable,quantified.getOperand(1),ground.getOperand(0),matches);
	}

	private void matchPolynomial(VariableDeclaration variable, Polynomial quantified, Polynomial ground, List<Expr> matches) {
		for(int i=0;i!=quantified.size();++i) {
			Polynomial.Term quantifiedTerm = quantified.getOperand(i);
			for(int j=0;j!=ground.size();++j) {
				Polynomial.Term groundTerm = ground.getOperand(j);
				matchPolynomialTerm(variable,quantifiedTerm,groundTerm,matches);
			}
		}
	}

	private void matchPolynomialTerm(VariableDeclaration variable, Polynomial.Term quantified, Polynomial.Term ground, List<Expr> matches) {
		Expr[] quantifiedAtoms = quantified.getAtoms();
		Expr[] groundAtoms = ground.getAtoms();
		for(int i=0;i!=quantifiedAtoms.length;++i) {
			Expr quantifiedAtom = quantifiedAtoms[i];
			for(int j=0;j!=groundAtoms.length;++j) {
				Expr groundAtom = groundAtoms[j];
				matchExpression(variable,quantifiedAtom,groundAtom,matches);
			}
		}
	}

	private boolean matchExpression(VariableDeclaration variable, Expr quantified, Expr ground, List<Expr> matches) {
		if(attemptMatch(variable,quantified,ground,matches)) {
			return true;
		} else {
			WyalFile.Opcode quantifiedOpcode = quantified.getOpcode();
			WyalFile.Opcode groundOpcode = ground.getOpcode();
			if(quantified.equals(ground)) {
				System.out.print("MATCHED IDENTICAL: ");
				WyalFile.print(quantified);
				System.out.print(" ");
				WyalFile.println(ground);
				return true;
			} else if (quantifiedOpcode == groundOpcode) {
				switch(quantifiedOpcode) {
				case EXPR_arridx:
					return matchArrayAccess(variable, (Expr.Operator) quantified, (Expr.Operator) ground, matches);
				case EXPR_add:
					return equateArithmeticExpression(variable, (Expr.Polynomial) quantified, (Expr.Polynomial) ground, matches);
				default:
					throw new IllegalArgumentException("attempting to match unknown expression: " + quantifiedOpcode);
				}
			}

			return false;
		}
	}

	private boolean attemptMatch(VariableDeclaration variable, Expr quantified, Expr ground, List<Expr> matches) {
		System.out.print("ATTEMPTING MATCH: ");
		WyalFile.print(quantified);
		System.out.print(" (" + quantified.getClass().getName() + ")");
		WyalFile.print(ground);
		System.out.println(" (" + ground.getClass().getName() + ")");
		if(quantified instanceof Expr.VariableAccess) {
			System.out.println("GOT IN");
			Expr.VariableAccess var = (Expr.VariableAccess) quantified;
			if(var.getVariableDeclaration().equals(variable)) {
				// Yes, this is the quantified variable we're looking for.
				// Therefore, we can now (finally) extract an actual match.
				matches.add(ground);
				return true;
			}
		}
		return false;
	}

	private boolean equateArithmeticExpression(VariableDeclaration variable, Expr.Polynomial quantified, Expr.Polynomial ground, List<Expr> matches) {
		boolean result = false;
		for(int i=0;i!=quantified.size();++i) {
			Polynomial.Term quantifiedTerm = quantified.getOperand(i);
			for(int j=0;j!=ground.size();++j) {
				Polynomial.Term groundTerm = ground.getOperand(j);
				result |= equatePolynomialTerm(variable,quantifiedTerm,groundTerm,matches);
			}
		}
		return result;
	}

	private boolean equatePolynomialTerm(VariableDeclaration variable, Polynomial.Term quantified, Polynomial.Term ground, List<Expr> matches) {
		boolean result = false;
		Expr[] quantifiedAtoms = quantified.getAtoms();
		Expr[] groundAtoms = ground.getAtoms();
		for(int i=0;i!=quantifiedAtoms.length;++i) {
			Expr quantifiedAtom = quantifiedAtoms[i];
			if (groundAtoms.length == 0) {
				result |= matchExpression(variable, quantifiedAtom, ground.getOperand(0), matches);
			} else {
				for (int j = 0; j != groundAtoms.length; ++j) {
					Expr groundAtom = groundAtoms[j];
					result |= matchExpression(variable, quantifiedAtom, groundAtom, matches);
				}
			}

		}
		return result;
	}

	private boolean matchArrayAccess(VariableDeclaration variable, Expr.Operator quantified, Expr.Operator ground, List<Expr> matches) {
		System.out.println("MATCHING ARRAY ACCESS: ");
		Expr quantifiedSource = quantified.getOperand(0);
		Expr quantifiedIndex = quantified.getOperand(1);
		Expr groundSource = ground.getOperand(0);
		Expr groundIndex = ground.getOperand(1);
		boolean r = matchExpression(variable,quantifiedSource, groundSource, matches);
		r &= matchExpression(variable,quantifiedIndex, groundIndex, matches);
		return r;
	}
}
