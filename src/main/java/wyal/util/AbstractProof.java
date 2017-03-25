package wyal.util;

import java.util.*;

import wyal.lang.Formula;
import wyal.lang.Proof;
import wyal.lang.SyntacticHeap;
import wyal.lang.SyntacticItem;
import wyal.lang.WyalFile;
import wyal.lang.WyalFile.Declaration.Assert;
import wyal.lang.WyalFile.Expr;
import wyal.lang.WyalFile.Tuple;

public class AbstractProof<T extends Proof.State> implements Proof {
	protected final WyalFile.Declaration.Assert assertion;
	protected final SyntacticHeap heap;

	protected final ArrayList<T> states;

	public AbstractProof(WyalFile.Declaration.Assert assertion, SyntacticHeap heap) {
		this.states = new ArrayList<>();
		this.assertion = assertion;
		this.heap = heap;
	}

	@Override
	public SyntacticHeap getHeap() {
		return heap;
	}

	@Override
	public Assert getAssertion() {
		return assertion;
	}

	@Override
	public boolean isComplete() {
		// TODO Auto-generated method stub
		return false;
	}

	@Override
	public int size() {
		return states.size();
	}

	@Override
	public T getState(int ith) {
		return states.get(ith);
	}

	public T register(T state) {
		states.add(state);
		return state;
	}

	public abstract static class AbstractState<T extends Proof.State> implements Proof.State {
		protected final AbstractProof<T> proof;
		protected final List<Formula> dependencies;
		protected final Proof.Rule rule;
		protected final ArrayList<T> children;
		protected T parent;

		public AbstractState(AbstractProof<T> proof, T parent, Proof.Rule rule, Formula... dependencies) {
			this.proof = proof;
			this.parent = parent;
			this.dependencies = Arrays.asList(dependencies);
			this.rule = rule;
			this.children = new ArrayList<>();
		}

		@Override
		public Proof getProof() {
			return proof;
		}

		@Override
		public T getParent() {
			return parent;
		}

		@Override
		public Proof.Rule getRule() {
			return rule;
		}

		@Override
		public List<Formula> getDependencies() {
			return dependencies;
		}

		@Override
		public int numberOfChildren() {
			return children.size();
		}

		@Override
		public T getChild(int ith) {
			return children.get(ith);
		}

		@Override
		public void applyBypass(Proof.State child) {
			children.clear();
			if (child != null) {
				// FIXME: this line is clearly a hack for now
				AbstractState c = (AbstractState) child;
				children.addAll(c.children);
				c.parent = null;
				for (int i = 0; i != children.size(); ++i) {
					c = (AbstractState) children.get(i);
					c.parent = this;
				}
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
		 *
		 * @param to
		 * @param item
		 * @return
		 */
		@Override
		public SyntacticItem substitute(SyntacticItem from, SyntacticItem to, SyntacticItem item, TypeSystem types) {
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
							SyntacticItem nChild = substitute(from, to, child, types);
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
					SyntacticItem result = item.clone(nChildren);
					if(result instanceof Expr) {
						return construct((Expr) result, types);
					} else {
						// FIXME: this case is only possible because arguments
						// on functions are represented as tuples.
						return result;
					}
				}
			}
		}
	}
}
