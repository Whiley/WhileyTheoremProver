package wycs.util;

import java.util.ArrayList;
import java.util.List;

import wycs.lang.Proof;

public class AbstractProof implements Proof {
	private List<State> states = new ArrayList<State>();

	@Override
	public int numberOfStates() {
		return states.size();
	}

	@Override
	public State getState(int ith) {
		return states.get(ith);
	}

	public class State implements Proof.State {
		private List<Step> steps = new ArrayList<Step>();

		@Override
		public boolean isKnown(int location) {
			// TODO Auto-generated method stub
			return false;
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
