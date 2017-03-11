package wyal.util;

import java.util.ArrayList;
import java.util.BitSet;
import java.util.List;

import wyal.lang.Formula;
import wyal.lang.Proof;
import wyal.lang.SyntacticHeap;
import wyal.lang.WyalFile;
import wyal.util.AbstractProof;
import wyal.util.AbstractProof.AbstractStep;
import wycc.util.ArrayUtils;
import wyal.lang.WyalFile.Declaration.Assert;

public class BitSetProof extends AbstractProof<BitSetProof.State> {

	public BitSetProof(Assert assertion, SyntacticHeap heap, Formula formula) {
		super(assertion);
		// Initialise the proof with the root state
		State root = new State(this,heap);
		states.add(root.set("init",formula));
	}

	public static class State extends AbstractStep<State> {
		private final SyntacticHeap heap;
		/**
		 * The set of all known truths, including those which are subsumed.
		 * Always a superset of activeTruths.
		 */
		private final BitSet allTruths;
		/**
		 * The set of all known truths, excluding those which are subsumed.
		 * Always a subset of allTruths.
		 */
		private final BitSet activeTruths;

		public State(Proof proof, SyntacticHeap heap) {
			super(proof,null,null);
			this.heap = heap;
			this.allTruths = new BitSet();
			this.activeTruths = new BitSet();
		}

		private State(State state, String rule, WyalFile.Expr... dependencies) {
			super(state.getProof(),state,rule,dependencies);
			this.heap = state.heap;
			this.allTruths = (BitSet) state.allTruths.clone();
			this.activeTruths = (BitSet) state.activeTruths.clone();
			state.children.add(this);
		}

		public int size() {
			return activeTruths.length();
		}

		public SyntacticHeap getHeap() {
			return heap;
		}

		@Override
		public BitSet getDependencyCone() {
			BitSet cone = new BitSet();

			// Compute dependency cone for children
			for (int i = 0; i != children.size(); ++i) {
				State child = children.get(i);
				cone.or(child.getDependencyCone());
			}
			// Add all dependencies for this rule, if the rule
			boolean include = false;

			for(Formula f : getIntroductions()) {
				if(cone.get(f.getIndex()) ) {
					include = true;
					break;
				} else if(f instanceof Formula.Truth) {
					Formula.Truth t = (Formula.Truth) f;
					if(!t.holds()) {
						include = true;
						break;
					}
				}
			}
			if(include) {
				// yes, should include dependencies for this step
				for (WyalFile.Expr e : dependencies) {
					if (e instanceof Formula) {
						cone.set(e.getIndex());
					}
				}
			}
			return cone;
		}

		/**
		 * Return the list of formulae introduced by this step.
		 *
		 * @return
		 */
		@Override
		public List<Formula> getIntroductions() {
			State parent = getParent();
			ArrayList<Formula> diff = new ArrayList<>();
			for(int i=0;i!=activeTruths.size();++i) {
				Formula f = getActive(i);
				if(f != null && (parent == null || !parent.contains(f))) {
					diff.add(f);
				}
			}
			return diff;
		}

		/**
		 * Determine whether a given truth is known or not.
		 *
		 * @param truth
		 * @return
		 */
		public boolean contains(Formula truth) {
			return allTruths.get(truth.getIndex());
		}

		public Formula getActive(int index) {
			if (activeTruths.get(index)) {
				return (Formula) heap.getSyntacticItem(index);
			} else {
				return null;
			}
		}

		public State subsume(String rule, Formula from, Formula to, Formula... deps) {
			return subsume(rule,from,new Formula[]{to},deps);
		}
		/**
		 * Subume one formula with one or more formulae. This implication is
		 * that latter "cover" the former. The former is no longer active,
		 * though it remains a known truth. The new formula are active.
		 *
		 * @param from
		 * @param to
		 */
		public State subsume(String rule, Formula from, Formula[] tos, Formula... deps) {
			final int fromIndex = from.getIndex();
			if(activeTruths.get(fromIndex)) {
				State next = new State(this,rule,ArrayUtils.append(from,deps));
				next.activeTruths.clear(fromIndex);
				for (int i = 0; i != tos.length; ++i) {
					final int toIndex = tos[i].getIndex();
					if(!allTruths.get(toIndex)) {
						next.allTruths.set(toIndex);
						next.activeTruths.set(toIndex);
					}
				}
				return next;
			} else {
				return this;
			}
		}

		public State set(String rule, Formula truth, WyalFile.Expr... dependencies) {
			final int index = truth.getIndex();
			if(!allTruths.get(index)) {
				State next = new State(this,rule,dependencies);
				next.allTruths.set(index);
				next.activeTruths.set(index);
				return next;
			} else {
				return this;
			}
		}

		public State[] split(Formula.Disjunct disjunct) {
			Formula[] cases = disjunct.getOperands();
			State[] result = new State[cases.length];
			for (int i = 0; i != cases.length; ++i) {
				result[i] = this.subsume("split",disjunct,cases[i]);
			}
			return result;
		}

		public Formula allocate(Formula f) {
			return heap.allocate(f);
		}
	}

}
