package wyal.rules;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.List;

import wyal.lang.Formula;
import wyal.lang.Proof;
import wyal.lang.SyntacticItem;
import wyal.lang.WyalFile;
import wyal.lang.WyalFile.Expr;
import wyal.lang.WyalFile.VariableDeclaration;
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
