package wyal.util;

import java.util.ArrayList;
import java.util.Arrays;
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
		super(assertion,heap);
		// Initialise the proof with the root state
		states.add(new State(this,formula));
	}

	public static class Delta implements Proof.Delta {
		private final Set additions;
		private final Set removals;

		public Delta() {
			this.additions = EMPTY_SET;
			this.removals = EMPTY_SET;
		}

		public Delta(Set additions, Set removals) {
			if(additions == removals) {
				throw new IllegalArgumentException("aliasing of additions and removals not allowed!");
			}
			this.additions = additions;
			this.removals = removals;
		}

		@Override
		public boolean isAddition(Formula truth) {
			return additions.contains(truth);
		}

		@Override
		public boolean isRemoval(Formula truth) {
			return removals.contains(truth);
		}

		@Override
		public Set getAdditions() {
			return additions;
		}

		@Override
		public Set getRemovals() {
			return removals;
		}

		@Override
		public Delta add(Formula truth) {
			return new Delta(additions.add(truth),removals.remove(truth));
		}

		@Override
		public Delta remove(Formula truth) {
			return new Delta(additions.remove(truth),removals.add(truth));
		}

		@Override
		public Delta apply(Proof.Delta delta) {
			Set nAdditions = additions.remove(delta.getRemovals()).union(delta.getAdditions());
			Set nRemovals = removals.remove(delta.getAdditions()).union(delta.getRemovals());
			return new Delta(nAdditions,nRemovals);
		}

		@Override
		public String toString() {
			return additions.toString() + "-" + removals.toString();
		}

		private static Set EMPTY_SET = new Set();

		public static class Set implements Proof.Delta.Set {
			private final BitSet bits;
			private final Formula[] items;

			public Set() {
				this.bits = new BitSet();
				this.items = new Formula[]{};
			}

			public Set(Formula f) {
				this.bits = new BitSet();
				this.items = new Formula[]{f};
				this.bits.set(f.getIndex());
			}

			private Set(BitSet bits, Formula[] items) {
				if(items.length != bits.cardinality()) {
					throw new IllegalArgumentException("invariant broken (i)");
				}
				for(int i=0;i!=items.length;++i) {
					if(!bits.get(items[i].getIndex())) {
						throw new IllegalArgumentException("invariant broken (ii)");
					}
				}
				this.bits = bits;
				this.items = items;
			}

			@Override
			public int size() {
				return items.length;
			}

			@Override
			public boolean contains(Formula truth) {
				return bits.get(truth.getIndex());
			}

			@Override
			public Formula get(int ith) {
				return items[ith];
			}

			@Override
			public Set add(Formula truth) {
				int index = truth.getIndex();
				if (bits.get(index)) {
					// Item is already contained in this set, hence this is a
					// no-operation.
					return this;
				} else {
					Formula[] nItems = Arrays.copyOf(items, items.length + 1);
					BitSet nBits = (BitSet) bits.clone();
					nBits.set(index);
					nItems[items.length] = truth;
					return new Set(nBits, nItems);
				}
			}

			@Override
			public Set remove(Formula truth) {
				int index = truth.getIndex();
				if (!bits.get(index)) {
					// Item is not contained in this set, hence this is a
					// no-operation.
					return this;
				} else {
					Formula[] nItems = new Formula[items.length-1];
					BitSet nBits = (BitSet) bits.clone();
					nBits.clear(index);
					int j = 0;
					for(int i=0;i!=items.length;++i) {
						Formula ith = items[i];
						if(ith.getIndex() != index) {
							nItems[j++] = ith;
						}
					}
					return new Set(nBits, nItems);
				}
			}

			@Override
			public Set union(Proof.Delta.Set other) {
				Set result = this;
				for(int i=0;i!=other.size();++i) {
					result = result.add(other.get(i));
				}
				return result;
			}

			@Override
			public Set remove(Proof.Delta.Set other) {
				Set result = this;
				for(int i=0;i!=other.size();++i) {
					result = result.remove(other.get(i));
				}
				return result;
			}

			@Override
			public String toString() {
				String r = "{";
				for(int i=0;i!=items.length;++i) {
					if(i != 0) {
						r += ", ";
					}
					r += items[i];
				}
				return r + "}";
			}
		}

	}

	public static class State extends AbstractStep<State> {
		/**
		 * The set of all known truths, including those which are subsumed.
		 * Always a superset of activeTruths.
		 */
		private final BitSet truths;

		private final Delta delta;

		public State(Proof proof, Formula axiom) {
			super(proof,null,null);
			this.truths = new BitSet();
			this.delta = new Delta(new Delta.Set(axiom),Delta.EMPTY_SET);
		}

		private State(State state, Proof.Rule rule, Delta delta, WyalFile.Expr... dependencies) {
			super(state.getProof(),state,rule,dependencies);
			this.truths = (BitSet) state.truths.clone();
			this.delta = delta;
			state.children.add(this);
			// Update our state of the world
			Delta.Set additions = delta.additions;
			Delta.Set removals = delta.removals;
			for(int i=0;i!=additions.size();++i) {
				truths.set(additions.get(i).getIndex());
			}
			for(int i=0;i!=removals.size();++i) {
				truths.clear(removals.get(i).getIndex());
			}
		}

		/**
		 * Return the list of formulae introduced by this step.
		 *
		 * @return
		 */
		@Override
		public Delta getDelta() {
			return delta;
		}

		/**
		 * Return the list of formulae introduced by this step.
		 *
		 * @return
		 */
		@Override
		public Proof.Delta getDelta(Proof.State ancestor) {
			if(this == ancestor) {
				return new Delta();
			} else if(parent == null) {
				// At this point, we must be the root node. In which case, we
				// just return what we have.
				return delta;
			} else {
				return parent.getDelta(ancestor).apply(delta);
			}
		}

		/**
		 * Determine whether a given truth is known or not.
		 *
		 * @param truth
		 * @return
		 */
		@Override
		public boolean isKnown(Formula truth) {
			return truths.get(truth.getIndex());
		}

		@Override
		public State subsume(Proof.Rule rule, Formula from, Formula to, Formula... deps) {
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
		@Override
		public State subsume(Proof.Rule rule, Formula from, Formula[] tos, Formula... deps) {
			Delta.Set removals = new Delta.Set(from);
			Delta.Set additions = Delta.EMPTY_SET;
			for (int i = 0; i != tos.length; ++i) {
				Formula ith = tos[i];
				final int toIndex = ith.getIndex();
				if (!truths.get(toIndex)) {
					additions = additions.add(ith);
				}
			}
			Delta nDelta = new Delta(additions, removals);
			return new State(this, rule, nDelta, ArrayUtils.append(from, deps));
		}

		@Override
		public State infer(Proof.Rule rule, Formula truth, Formula... dependencies) {
			final int index = truth.getIndex();
			if(!truths.get(index)) {
				Delta delta = new Delta(new Delta.Set(truth), Delta.EMPTY_SET);
				State next = new State(this,rule,delta,dependencies);
				return next;
			} else {
				return this;
			}
		}

		@Override
		public State[] split(Formula.Disjunct disjunct) {
			Formula[] cases = disjunct.getOperands();
			State[] result = new State[cases.length];
			for (int i = 0; i != cases.length; ++i) {
				result[i] = this.subsume(null,disjunct,cases[i]);
			}
			return result;
		}

		@Override
		public Formula allocate(Formula truth) {
			return proof.getHeap().allocate(truth);
		}
	}

}
