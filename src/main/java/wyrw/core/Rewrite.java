package wyrw.core;

import java.util.List;

import wyautl.core.Automaton;
import wyrw.util.AbstractActivation;

public interface Rewrite {
	
	/**
	 * Initialise the rewrite with a given automaton.
	 * 
	 * @param automaton
	 */
	public int initialise(Automaton automaton);

	/**
	 * Add a new step to the rewrite.
	 * 
	 * @param state
	 * @param activation
	 * @return
	 */
	public int step(int from, int activation);
	
	/**
	 * Get the list of steps which make up this rewrite. This list is not
	 * modifiable.
	 * 
	 * @return
	 */
	public List<Step> steps();
	
	/**
	 * Get the list of states which have been encountered during the rewrite.
	 * This list is not modifiable.
	 * 
	 * @return
	 */
	public List<State> states();
	
	/**
	 * Represents a single rewriting step. This may or may not correspond
	 * directly to a single application of an underlying rewrite rule. For
	 * example, it might correspond to a single "inference step".
	 *
	 * @author David J. Pearce
	 *
	 */
	public interface Step {

		/**
		 * Return the index of the state before this rewrite step was applied.
		 * 
		 * @return
		 */
		public int before();

		/**
		 * Return the index of the state after this rewrite step was applied. If
		 * the rewrite didn't apply, or had no actual effect, then this can be
		 * the same as the before state.
		 * 
		 * @return
		 */
		public int after();

		/**
		 * Return the activation that was applied to the before state to produce
		 * the after state.
		 * 
		 * @return
		 */
		public int activation();
	}

	/**
	 * Represents a single state in the rewriter proof. From each state, there
	 * are a finite number of possible rule activations. The state records which
	 * of these have been applied, and which have not.
	 * 
	 * @author David J. Pearce
	 *
	 */
	public interface State {
		/**
		 * Return the underlying automaton for this state.
		 * 
		 * @return
		 */
		public Automaton automaton();

		/**
		 * Return the number of possible activations from this state. This
		 * method forces the state to enumerate all possible activations.
		 * 
		 * @return
		 */
		public int size();

		/**
		 * Return the number of unexplored activations from this state. This
		 * method forces the state to enumerate all possible activations.
		 * 
		 * @return
		 */
		public int rank();

		/**
		 * Return the activation at the given index
		 * 
		 * @param index
		 * @return
		 */
		public AbstractActivation activation(int index);
		
		/**
		 * Return the rewrite step associated with this activation
		 * 
		 * @param index
		 * @return
		 */
		public Rewrite.Step step(int index);
		
		/**
		 * Select the first unvisited state, or return -1 if none exists. This
		 * method can be used without forcing the state to enumerate all
		 * possible activations.
		 * 
		 * @return
		 */
		public int select();
	}
	
	/**
	 * Represents a concrete activation of this rule to a given automaton
	 * 
	 * @author David J. Pearce
	 *
	 */
	public interface Activation {
		
		public RewriteRule rule();
		
		public int target();
		
		public int[] binding();
		
		public int apply(Automaton automaton);
	}
}
