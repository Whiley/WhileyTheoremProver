package wycs.util;

import java.util.ArrayList;
import java.util.BitSet;
import java.util.List;

import wycs.lang.Bytecode;
import wycs.lang.Proof;

public abstract class AbstractProof implements Proof {
	/**
	 * The abstract syntax tree corresponding to all known information.
	 */
	protected ArrayList<Bytecode> tree;

	/**
	 * The set of current proof states. Each state represents a set of known
	 * truths within the current tree.
	 */
	protected ArrayList<State> states = new ArrayList<State>();

	public AbstractProof(List<Bytecode> tree) {
		this.tree = new ArrayList<Bytecode>(tree);
	}

	@Override
	public int numberOfStates() {
		return states.size();
	}

	@Override
	public State getState(int ith) {
		return states.get(ith);
	}

	public class State implements Proof.State {
		/**
		 * The set of items known to be true in this state.
		 */
		private final BitSet truths;

		private List<Step> steps = new ArrayList<Step>();

		public State(BitSet truths) {
			this.truths = truths;
		}

		@Override
		public boolean isKnown(int location) {
			return truths.get(location);
		}

		@Override
		public int numberOfSteps() {
			return steps.size();
		}

		@Override
		public Step getStep(int ith) {
			return steps.get(ith);
		}

		@Override
		public int getIndex() {
			for(int i=0;i!=states.size();++i) {
				if(states.get(i) == this) {
					return i;
				}
			}
			throw new IllegalArgumentException("state should not exist?");
		}
	}

	public class Step implements Proof.Step {
		private final int parent;
		private final int child;
		private final Rule rule;

		private Step(int parent, int child, Rule rule) {
			this.parent = parent;
			this.child = child;
			this.rule = rule;
		}

		@Override
		public wycs.lang.Proof.State getParentState() {
			return states.get(parent);
		}

		@Override
		public wycs.lang.Proof.State getChildState() {
			return states.get(child);
		}

		@Override
		public Rule getRule() {
			return rule;
		}
	}
}
