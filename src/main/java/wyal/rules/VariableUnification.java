package wyal.rules;

import java.math.BigInteger;
import java.util.Arrays;
import java.util.HashMap;

import wyal.lang.Formula;
import wyal.lang.Formula.Conjunct;
import wyal.lang.SyntacticItem;
import wyal.lang.WyalFile.Expr;
import wyal.lang.WyalFile.Expr.Polynomial;
import wyal.lang.WyalFile.Tuple;
import wyal.util.AutomatedTheoremProver;
import wyal.util.AutomatedTheoremProver.RewriteRule;

/**
 *
 * @author David J. Pearce
 *
 */
public class VariableUnification implements RewriteRule {

	@Override
	public Formula rewrite(Formula item) {
		if(item instanceof Conjunct) {
			return rewrite((Conjunct) item);
		} else {
			return item;
		}
	}

	private Formula rewrite(Conjunct item) {
		HashMap<String,Expr> map = null;
		//
		for(int i=0;i!=item.size();++i) {
			Formula f = item.getOperand(i);
			if(f instanceof Formula.Equality) {
				Formula.Equality eq = (Formula.Equality) f;
				if(eq.getSign()) {
					map = rearrangeForSubstitution(eq,map);
				}
			}
		}
		//
		Formula result = item;
		//
		if(map != null) {
			System.out.println("ATTEMPTING SUBSTITUTION:");
			System.out.print("   ");AutomatedTheoremProver.println(item);
			result = substitute(map,item);
			System.out.print("-->");AutomatedTheoremProver.println(result);
		}
		return item;
	}

	private HashMap<String,Expr> rearrangeForSubstitution(Formula.Equality f, HashMap<String,Expr> map) {
		String var;
		Expr bound;
		if(f instanceof Formula.ArithmeticEquality) {
			// Arithmetic equalities are a special case because we can actually
			// rearrange them.
			Formula.ArithmeticEquality e = (Formula.ArithmeticEquality) f;
			Polynomial lhs = e.getOperand(0);
			Polynomial rhs = e.getOperand(1);
			Polynomial.Term lhsCandidate = selectCandidateForSubstitution(lhs);
			Polynomial.Term rhsCandidate = selectCandidateForSubstitution(rhs);
			if(lhsCandidate != null && rhsCandidate != null) {
				String var1 = extractCandidateName(lhsCandidate);
				String var2 = extractCandidateName(rhsCandidate);
				if(var1.compareTo(var2) <= 0) {
					var = var1;
					bound = rhs.subtract(lhs.subtract(lhsCandidate));
				} else {
					var = var2;
					bound = lhs.subtract(rhs.subtract(lhsCandidate));
				}
			} else if(lhsCandidate != null) {
				var = extractCandidateName(lhsCandidate);
				bound = rhs.subtract(lhs.subtract(lhsCandidate));
			} else if(rhsCandidate != null) {
				var = extractCandidateName(rhsCandidate);
				bound = lhs.subtract(rhs.subtract(rhsCandidate));
			} else {
				return map;
			}
		} else {
			// For non-arithmetic equalities, we can't rearrange them.
			// Therefore, there are relatively few options.
			Expr lhs = f.getOperand(0);
			Expr rhs = f.getOperand(1);
			//
			if (lhs instanceof Expr.VariableAccess && rhs instanceof Expr.VariableAccess) {
				String v1 = ((Expr.VariableAccess) lhs).getVariableDeclaration().getVariableName().get();
				String v2 = ((Expr.VariableAccess) rhs).getVariableDeclaration().getVariableName().get();
				if (v1.compareTo(v2) <= 0) {
					var = v1;
					bound = rhs;
				} else {
					var = v2;
					bound = lhs;
				}
			} else if (lhs instanceof Expr.VariableAccess) {
				Expr.VariableAccess v = (Expr.VariableAccess) lhs;
				var = v.getVariableDeclaration().getVariableName().get();
				bound = rhs;
			} else if (rhs instanceof Expr.VariableAccess) {
				Expr.VariableAccess v = (Expr.VariableAccess) rhs;
				var = v.getVariableDeclaration().getVariableName().get();
				bound = lhs;
			} else {
				// no option here
				return map;
			}
		}

		if(map == null) {
			// We found a candidate, but the map is not yet initialised!
			map = new HashMap<>();
		} else {
			// FIXME: need to actually substitute the bound against prior
			// substitutions at this point. Otherwise, some will be lost.
		}
		System.out.print("ADDING SUBSTITUTION MAP: " + var + " ==> ");
		AutomatedTheoremProver.println(bound);
		map.put(var, bound);
		return map;
	}

	/**
	 * Examine all terms in a polynomial to see whether any is a candidate for
	 * substitution or not. If one or more are found, then the least candidate is
	 * returned.
	 *
	 * @param p
	 * @return
	 */
	private Polynomial.Term selectCandidateForSubstitution(Polynomial p) {
		Polynomial.Term candidate = null;
		String candidateVar = null;
		for(int i=0;i!=p.size();++i) {
			Polynomial.Term term = p.getOperand(0);
			if(isCandidate(term)) {
				String var = extractCandidateName(term);
				if(candidateVar == null || var.compareTo(candidateVar) < 0) {
					candidateVar = var;
					candidate = term;
				}
			}
		}
		return candidate;
	}

	/**
	 * Determine whether a given polynomial term is a candidate for
	 * substitution. A candidate must be a single atom with a trivial
	 * coefficient (i.e. 1). At this time, a candidate must also be a variable
	 * access (though this may be later relaxed).
	 *
	 * @param term
	 * @return
	 */
	public boolean isCandidate(Polynomial.Term term) {
		Tuple<Expr> atoms = term.getAtoms();
		BigInteger coefficient = term.getCoefficient().get();
		if (atoms.size() == 1 && coefficient.equals(BigInteger.ONE)) {
			// FIXME: can we substitute for things other than a variable access?
			// I think perhapds we should be able to.
			return atoms.getOperand(0) instanceof Expr.VariableAccess;
		} else {
			return false;
		}
	}

	/**
	 * Extract the name of a candidate. That is, the variable which is being
	 * rearranged for. This is necessary to determine whether a given candidate
	 * is the <i>least</i> candidate or not.
	 *
	 * @param term
	 * @return
	 */
	private String extractCandidateName(Polynomial.Term term) {
		Expr.VariableAccess va = (Expr.VariableAccess) term.getAtoms().getOperand(0);
		return va.getVariableDeclaration().getVariableName().get();
	}

	private Formula substitute(HashMap<String,Expr> map, Formula item) {
		switch (item.getOpcode()) {
		case EXPR_or: {
			Formula.Disjunct disjunct = (Formula.Disjunct) item;
			Formula[] children = disjunct.getOperands();
			Formula[] nChildren = substitute(map, children);
			if (children != nChildren) {
				return item.clone(nChildren);
			} else {
				return item;
			}
		}
		case EXPR_and: {
			Formula.Conjunct conjunct = (Formula.Conjunct) item;
			Formula[] children = conjunct.getOperands();
			Formula[] nChildren = substitute(map, children);
			if (children != nChildren) {
				return item.clone(nChildren);
			} else {
				return item;
			}
		}
		case EXPR_forall:
		case EXPR_exists: {
			Formula.Quantifier quantifier = (Formula.Quantifier) item;
			Formula body = quantifier.getBody();
			Formula nBody = substitute(map, body);
			if (body == nBody) {
				return item;
			} else if (quantifier.getSign()) {
				return Formula.forall(quantifier.getParameters(), nBody);
			} else {
				return Formula.exists(quantifier.getParameters(), nBody);
			}
		}
		case EXPR_eq:
		case EXPR_neq: {
			Formula.Equality equality = (Formula.Equality) item;
			Expr[] children = equality.getOperands();
			Expr[] nChildren = substitute(map, children);
			if (children != nChildren) {
				return item.clone(nChildren);
			} else {
				return item;
			}
		}
		case EXPR_lt:
		case EXPR_gteq: {
			Formula.Inequality inequality = (Formula.Inequality) item;
			Expr[] children = inequality.getOperands();
			Expr[] nChildren = substitute(map, children);
			if (children != nChildren) {
				return item.clone(nChildren);
			} else {
				return item;
			}
		}

		default:
			throw new IllegalArgumentException("invalid formula opcode: " + item.getOpcode());
		}
	}

	private Expr[] substitute(HashMap<String,Expr> map, Expr[] children) {
		Expr[] nChildren = children;
		for(int i=0;i!=children.length;++i) {
			Expr before = children[i];
			Expr after = substitute(map,before);
			if(before != after && nChildren == children) {
				nChildren = Arrays.copyOf(children,children.length);
			}
			nChildren[i] = after;
		}
		return nChildren;
	}

	private Formula[] substitute(HashMap<String,Expr> map, Formula[] children) {
		Formula[] nChildren = children;
		for(int i=0;i!=children.length;++i) {
			Formula before = children[i];
			Formula after = substitute(map,before);
			if(before != after && nChildren == children) {
				nChildren = Arrays.copyOf(children,children.length);
			}
			nChildren[i] = after;
		}
		return nChildren;
	}

	private Expr substitute(HashMap<String,Expr> map, Expr atom) {
		if(atom instanceof Expr.VariableAccess) {
			// In this case, we might be able to make a substitution.
			Expr.VariableAccess v = (Expr.VariableAccess) atom;
			String name = v.getVariableDeclaration().getVariableName().get();
			System.out.println("MATCHED VARIABLE: " + name);
			Expr result = map.get(name);
			if(result != null) {
				// Yes, we made a substitution!
				return result;
			}
		} else {
			SyntacticItem[] children = atom.getOperands();
			SyntacticItem[] nChildren = children;
			for(int i=0;i!=children.length;++i) {
				SyntacticItem child = children[i];
				if(child instanceof Expr) {
					// FIXME: this is broken because it won't substitute through
					// Polynomial terms (since they are not currently
					// expressions).
					Expr before = (Expr) child;
					Expr after = substitute(map,before);
					if(before != after && nChildren == children) {
						nChildren = Arrays.copyOf(children,children.length);
					}
					nChildren[i] = after;
				}
			}
			//
			if(nChildren != children) {
				// something changed!
				return (Expr) atom.clone(nChildren);
			}
		}

		// If we get here, then no substitution was made.
		return atom;
	}
}
