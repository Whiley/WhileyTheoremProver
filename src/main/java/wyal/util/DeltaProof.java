package wyal.util;

import java.util.BitSet;

import wyal.lang.Formula;
import wyal.lang.Proof;
import wyal.lang.SyntacticHeap;
import wyal.lang.WyalFile;
import wyal.util.AbstractProof;
import wyal.util.AbstractProof.AbstractState;
import wycc.util.ArrayUtils;
import wyal.lang.WyalFile.Declaration.Assert;
import wyal.lang.WyalFile.Expr;

public class DeltaProof extends AbstractProof<DeltaProof.State> {

	public DeltaProof(Assert assertion, SyntacticHeap heap, Formula formula) {
		super(assertion,heap);
		// Initialise the proof with the root state
		states.add(new State(this,formula));
	}

	public static class State extends AbstractState<State> {
		/**
		 * The set of all known truths, including those which are subsumed.
		 * Always a superset of activeTruths.
		 */
		private final BitSet truths;

		private final Delta delta;

		public State(DeltaProof proof, Formula axiom) {
			super(proof, null, null);
			this.truths = new BitSet();
			this.delta = new FastDelta(new FastDelta.Set(axiom), FastDelta.EMPTY_SET);
			this.truths.set(axiom.getIndex());
		}

		private State(State state, Proof.Rule rule, FastDelta delta, Formula... dependencies) {
			super((DeltaProof) state.getProof(), state, rule, dependencies);
			this.truths = (BitSet) state.truths.clone();
			this.delta = delta;
			state.children.add(this);
			// Update our state of the world
			FastDelta.Set additions = delta.getAdditions();
			//
			for (int i = 0; i != additions.size(); ++i) {
				truths.set(additions.get(i).getIndex());
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
				return FastDelta.EMPTY_DELTA;
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
			FastDelta.Set removals = new FastDelta.Set(from);
			FastDelta.Set additions = FastDelta.EMPTY_SET;
			for (int i = 0; i != tos.length; ++i) {
				Formula ith = tos[i];
				final int toIndex = ith.getIndex();
				if (!truths.get(toIndex)) {
					additions = additions.add(ith);
				}
			}
			FastDelta nDelta = new FastDelta(additions, removals);
			// Register this state
			return proof.register(new State(this, rule, nDelta, ArrayUtils.append(from, deps)));
		}

		@Override
		public State infer(Proof.Rule rule, Formula truth, Formula... dependencies) {
			//
			final int index = truth.getIndex();
			if(!truths.get(index)) {
				FastDelta delta = new FastDelta(new FastDelta.Set(truth), FastDelta.EMPTY_SET);
				return proof.register(new State(this,rule,delta,dependencies));
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

		@Override
		public Expr construct(Expr term) {
			Proof.Delta.Set additions = delta.getAdditions();
			for (int i = 0; i != additions.size(); ++i) {
				Formula f = additions.get(i);
				if (f instanceof Formula.Assignment) {
					Formula.Assignment assign = (Formula.Assignment) f;
					// Found an assignment, so check whether term is being
					// assigned or not.
					if (assign.getLeftHandSide().equals(term)) {
						// Term is being assigned.
						return assign.getRightHandSide();
					}
				}
			}
			if (parent == null) {
				return term;
			} else {
				return parent.construct(term);
			}
		}
	}
}
