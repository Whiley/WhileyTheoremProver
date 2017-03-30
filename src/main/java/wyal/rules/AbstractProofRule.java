package wyal.rules;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.List;

import wyal.lang.Formula;
import wyal.lang.NameResolver;
import wyal.lang.Proof;
import wyal.lang.SyntacticItem;
import wyal.lang.WyalFile;
import wyal.lang.WyalFile.Expr;
import wyal.lang.WyalFile.Tuple;
import wyal.lang.WyalFile.VariableDeclaration;
import wyal.util.Formulae;
import wyal.util.TypeSystem;

public abstract class AbstractProofRule implements Proof.Rule {
	protected TypeSystem types;

	public AbstractProofRule(TypeSystem types) {
		this.types = types;
	}

	protected static <T extends SyntacticItem> List<T> findAllInstances(SyntacticItem e, Class<T> kind) {
		List<T> result = Collections.EMPTY_LIST;
		if(kind.isInstance(e)) {
			result = new ArrayList<>();
			result.add((T)e);
		}
		// Generic traversal, returning first split point encountered.
		for (int i = 0; i != e.size(); ++i) {
			SyntacticItem child = e.getOperand(i);
			result = union(result,findAllInstances(child,kind));
		}
		//
		return result;
	}

	/**
	 * <p>
	 * Search through a given syntactic item looking for matching ground terms
	 * which are guaranteed to be defined in the given state. This is useful for
	 * a number of different rules which attempt to extract information from
	 * formulae, even when they are universally quantified or contained in
	 * disjunctions. As an example, consider the following:
	 * </p>
	 *
	 * <pre>
	 * type nat is (int n) where n >= 0
	 * function f(int x) -> (nat r)
	 *
	 * define invariant(int[] xs, int x) is:
	 *   forall(int k):
	 *      (f(x) > xs[k]) || (f(x) < xs[k])
	 *
	 * assert:
	 *   forall (int[] ys, int i):
	 *     if:
	 *       i < 0
	 *       invariant(ys,i)
	 *     then:
	 *       false
	 * </pre>
	 * <p>
	 * The key is that, since <code>invarint(ys,i)</code> is asserted, it
	 * follows that <code>f(i)</code> is defined in the antecedent. As a result,
	 * the postcondition of <code>f()</code> dictates that <code>i >= 0</code>
	 * must follow. This gives a contradiction in the antecedent, meaning the
	 * overall assertion holds.
	 * </p>
	 *
	 * @param item
	 *            SyntacticItem to search through
	 * @param kind
	 *            Instances of this class will be extracted
	 * @return
	 */
	public static <T extends Expr> List<T> extractDefinedTerms(SyntacticItem item, WyalFile.Opcode kind, Formula.Quantifier... stack) {
		List<T> result = Collections.EMPTY_LIST;
		// Attempt to match the given item
		if (item.getOpcode() == kind && !containsQuantifiedVariable(item, stack)) {
			result = new ArrayList<>();
			result.add((T) item);
		}
		// Now, try to handle quantifiers and disjuncts appropriately.
		switch (item.getOpcode()) {
		case EXPR_exists:
		case EXPR_forall: {
			stack = Arrays.copyOf(stack, stack.length+1);
			stack[stack.length-1] = (Formula.Quantifier)item;
			break;
		}
		case EXPR_or: {
			Formula.Disjunct disjunct = (Formula.Disjunct) item;
			// Disjunctions need to be handled with care. We cannot extract
			// truths which only hold in one clause of the disjunct. Rather, we
			// can only extract truths which hold on all clauses.
			result = null;
			for(int i=0;i!=disjunct.size();++i) {
				SyntacticItem child = disjunct.getOperand(i);
				List<T> tmp = extractDefinedTerms(child,kind,stack);
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
		for (int i = 0; i != item.size(); ++i) {
			SyntacticItem child = item.getOperand(i);
			result = union(result,extractDefinedTerms(child,kind,stack));
		}
		//
		return result;
	}

	/**
	 * Check whether a given syntactic item contains a reference to one of the
	 * given quantifier variables.
	 *
	 * @param item
	 * @param quantifiedVariables
	 * @return
	 */
	private static boolean containsQuantifiedVariable(SyntacticItem item, Formula.Quantifier[] quantifiers) {
		List<VariableDeclaration> usedVariables = findAllInstances(item, VariableDeclaration.class);
		for (int i = 0; i != quantifiers.length; ++i) {
			Formula.Quantifier quantifier = quantifiers[i];
			if (quantifier.getSign()) {
				VariableDeclaration[] quantifiedVariables = quantifier.getParameters().getOperands();
				for (int j = 0; j != quantifiedVariables.length; ++j) {
					for (int k = 0; k != usedVariables.size(); ++k) {
						if (quantifiedVariables[j] == usedVariables.get(k)) {
							return true;
						}
					}
				}
			}
		}
		//
		return false;
	}

	/**
	 * When generating an entirely new term within a given rule (i.e. one
	 * that has not been previously seen in the proof), we need to check
	 * whether it is the subject of some existing assignment or not.
	 *
	 * @param newTerm
	 * @return
	 */
	public SyntacticItem construct(Proof.State state, SyntacticItem term) {
		SyntacticItem[] children = term.getOperands();
		SyntacticItem[] nChildren = children;
		if(children != null) {
			for (int i = 0; i != children.length; ++i) {
				SyntacticItem child = children[i];
				SyntacticItem nChild;
				if(child instanceof Expr) {
					 nChild = construct(state, (Expr) child);
				} else if(child instanceof Tuple) {
					nChild = construct(state,(Tuple)child);
				} else {
					nChild = child;
				}
				if (child != nChild && nChildren == children) {
					// Clone the new children array to avoid interfering
					// with original item.
					nChildren = Arrays.copyOf(children, children.length);
				}
				nChildren[i] = nChild;
			}
		}
		if (nChildren != children) {
			// At least one child was changed, therefore clone the original
			// item with the new children.
			term = (SyntacticItem) term.clone(nChildren);
		}
		if(term instanceof Expr) {
			return localConstruct(state,(Expr) term);
		} else {
			return term;
		}
	}

	public Expr localConstruct(Proof.State state, Expr term) {
		try {
			Expr tmp = Formulae.simplify(term, types);
			CongruenceClosure.Assignment assignment = lookupAssignment(state,tmp);
			if (assignment != null) {
				return assignment.getRightHandSide();
			} else {
				return term;
			}
		} catch (NameResolver.ResolutionError e) {
			// FIXME: now this is clearly scaffolding (i.e. a hack).
			throw new RuntimeException("name resolution error", e);
		}
	}


	private CongruenceClosure.Assignment lookupAssignment(Proof.State state, Expr term) {
		Proof.State parent = state.getParent();
		Proof.Delta.Set additions = state.getDelta().getAdditions();
		//
		for (int i = additions.size()-1; i >= 0; --i) {
			Formula f = additions.get(i);
			if (f instanceof Formula.Equality) {
				Formula.Equality eq = (Formula.Equality) f;
				if(eq.getSign()) {
					CongruenceClosure.Assignment assign = CongruenceClosure.rearrangeToAssignment(eq);
					// FIXME: this is essentially pretty broken. Need to find a
					// much better way to handle congruence closure.
					if (assign != null && assign.getLeftHandSide().equals(term)) {
						return assign;
					}
				}
			}
		}
		if (parent == null) {
			return null;
		} else {
			return lookupAssignment(parent,term);
		}
	}

	/**
	 * <p>
	 * Substitute for a given variable within a given syntactic item.
	 * Specifically, this replaces all instances of VariableAccess which match
	 * the given declaration. Observe that the substitution is performed
	 * verbatim and (for example) without simplifying the underlying item.
	 * </p>
	 * <p>
	 * This function preserves the aliasing structure of the original item up to
	 * the substitution itself. Furthermore, if no substitution was performed
	 * then the original item is returned as is.
	 * </p>
	 * @param from
	 * @param to
	 * @param item
	 * @return
	 */
	public SyntacticItem substitute(SyntacticItem from, SyntacticItem to, SyntacticItem item) {
		if (item.equals(from)) {
			// Yes, we made a substitution!
			return to;
		} else {
			// No immediate substitution possible. Instead, recursively traverse
			// term looking for substitution.
			SyntacticItem[] children = item.getOperands();
			SyntacticItem[] nChildren = children;
			if(children != null) {
				for (int i = 0; i != children.length; ++i) {
					SyntacticItem child = children[i];
					if(child != null) {
						SyntacticItem nChild = substitute(from, to, child);
						if (child != nChild && nChildren == children) {
							// Clone the new children array to avoid interfering with
							// original item.
							nChildren = Arrays.copyOf(children, children.length);
						}
						nChildren[i] = nChild;
					}
				}
			}
			if (nChildren == children) {
				// No children were updated, hence simply return the original
				// item.
				return item;
			} else {
				// At least one child was changed, therefore clone the original
				// item with the new children.
				return item.clone(nChildren);
			}
		}
	}

	// =====================================================================
	// HELPERS
	// =====================================================================
	/**
	 * Add all items from two lists together. Either or both of these may be
	 * empty and equal to Collections.EMPTY_LIST.
	 *
	 * @param lhs
	 * @param rhs
	 * @return
	 */
	private static <T> List<T> union(List<T> lhs, List<T> rhs) {
		if(lhs.size() > 0) {
			lhs.addAll(rhs);
			return lhs;
		} else {
			return rhs;
		}
	}

	private static <T> List<T> intersect(List<T> lhs, List<T> rhs) {
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

}
