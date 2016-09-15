package wycs.lang;

public interface Proof {

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
		int numberOfBranches();

		/**
		 * Get the ith step currently being explored from this state. If this
		 * uncovers a contradiction, then we have a contradiction overall.
		 */
		Branch getBranch(int ith);
	}

	/**
	 * A proof branch considered of one or more states which were derived from
	 * an existing state using a given rule.
	 *
	 * @author David J. Peare
	 *
	 */
	public interface Branch {
		/**
		 * Determine the number of cases arising from this proof step. Every
		 * case has to be shown in order for this branch to be considered shown
		 *
		 * @return
		 */
		int numberOfCases();

		/**
		 * Get the ith case needing to be considered from this proof step. This
		 * identifies a state in the enclosing proof.
		 */
		int getCase(int i);

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
