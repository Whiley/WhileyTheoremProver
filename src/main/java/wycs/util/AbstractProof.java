package wycs.util;

import java.util.ArrayList;
import java.util.BitSet;
import java.util.List;

import wycs.lang.Bytecode;
import wycs.lang.Proof;
import wycs.lang.SemanticType;
import wycs.lang.SyntaxTree;
import wycs.lang.SyntaxTree.Location;
import wycs.lang.WycsFile;

public abstract class AbstractProof implements Proof {
	/**
	 * The assertion being resolved
	 */
	protected WycsFile.Assert assertion;

	/**
	 * The abstract syntax tree corresponding to all known information.
	 */
	protected SyntaxTree tree;

	/**
	 * The set of current proof states. Each state represents a set of known
	 * truths within the current tree.
	 */
	protected ArrayList<State> states = new ArrayList<State>();

	/**
	 * Represents the current position of the interactive proof.
	 */
	private int HEAD;

	public AbstractProof(WycsFile.Assert assertion) {
		this.assertion = assertion;
		this.tree = new SyntaxTree(assertion.getTree());
	}

	@Override
	public WycsFile.Assert getAssertion() {
		return assertion;
	}

	public int numberOfLocations() {
		return tree.size();
	}

	@Override
	public int numberOfStates() {
		return states.size();
	}

	@Override
	public State getState(int ith) {
		return states.get(ith);
	}


	public int getHEAD() {
		return HEAD;
	}

	/**
	 * Assume the negation of a given statement holds
	 *
	 * @param l
	 */
	public void assumeNot(Location<?> stmt) {
		Bytecode b = new Bytecode.Operator(Bytecode.Opcode.NOT, stmt.getIndex());
		int idx = addStatement(b);
		BitSet truths;
		if (HEAD < states.size()) {
			State parent = states.get(HEAD);
			truths = (BitSet) parent.truths.clone();
		} else {
			truths = new BitSet();
		}
		truths.set(idx);
		states.add(new State(truths));
		// Update the HEAD position
		HEAD = states.size()-1;
	}

	private int addStatement(Bytecode b) {
		tree.getLocations().add(new SyntaxTree.Location<Bytecode>(tree, SemanticType.Bool, b));
		return tree.getLocations().size() - 1;
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

		/**
		 * Get the truths associated with this state
		 *
		 * @return
		 */
		public BitSet getTruths() {
			return truths;
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
