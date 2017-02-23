package wyal.lang;

import wyal.lang.WyalFile.Declaration;

public interface Proof {

	/**
	 * Get the assertion to which this proof applies.
	 *
	 * @return
	 */
	public Declaration.Assert getAssertion();

	/**
	 * Determine whether or not the proof is complete. That is, whether or not
	 * the proof demonstrates that the given assertion is correct.
	 *
	 * @return
	 */
	public boolean isComplete();

	/**
	 * Determine the number of states in this proof.
	 *
	 * @return
	 */
	public int numberOfStates();

	/**
	 * Get the ith state in this proof.
	 *
	 * @param ith
	 * @return
	 */
	public State getState(int ith);

	/**
	 * Represents a specific state within a proof. A state identifies known
	 * truths on a given branch within the proof. Using these truths, further
	 * states can be identified or a contradiction maybe found.
	 *
	 * @author David J. Pearce
	 *
	 */
	public interface State {
		/**
		 * Determine whether a given SyntaxTree location is known to hold or not
		 * in this state.
		 *
		 * @param location
		 * @return
		 */
		boolean isKnown(int location);

		/**
		 * Determine the number of branches currently being explored from this
		 * state.
		 *
		 * @return
		 */
		int numberOfSteps();

		/**
		 * Get the ith step currently being explored from this state. If this
		 * uncovers a contradiction, then we have a contradiction overall.
		 */
		Step getStep(int ith);

		/**
		 * Get the index in the enclosing proof of this state.
		 *
		 * @return
		 */
		int getIndex();
	}

	/**
	 * A proof branch considered of one or more states which were derived from
	 * an existing state using a given rule.
	 *
	 * @author David J. Peare
	 *
	 */
	public interface Step {
		/**
		 * Get the parent (i.e. before) state for this step.
		 *
		 * @return
		 */
		State getParentState();

		/**
		 * Get the child (i.e. after) state resulting from this step
		 *
		 * @return
		 */
		State getChildState();

		/**
		 * Get the rule used to generate this step.
		 */
		Rule getRule();
	}

	/**
	 * A rule takes a given state and produces zero or more subsequent states.
	 * Every rule has a unique name and a description. Rules also have a concept
	 * of "applicability". That is, the distinct situations (if any) to which a
	 * rule can be applied in any given situation.
	 *
	 * @author David J. Pearce
	 *
	 */
	public interface Rule {
		/**
		 * Get the unique name for this rule.
		 *
		 * @return
		 */
		public String getName();

		/**
		 * Get the description of this rule, which roughly describes what the
		 * rule does.
		 *
		 * @return
		 */
		public String getDescription();

		/**
		 * Determine whether or not this rule is applicable in the given state.
		 *
		 * @param state
		 * @return
		 */
		public boolean isApplicable(State state);

		/**
		 * Apply a rule to a given state, producing zero or more subsequent
		 * states.
		 *
		 * @param state
		 * @return
		 */
		public State[] applyRule(State state);
	}
}
