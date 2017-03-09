package wyal.lang;

import java.util.List;

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
	 * Determine the number of steps in this proof.
	 *
	 * @return
	 */
	public int numberOfSteps();

	/**
	 * Get the ith step in this proof.
	 *
	 * @param ith
	 * @return
	 */
	public Step getStep(int ith);

	/**
	 * A proof branch considered of one or more states which were derived from
	 * an existing state using a given rule.
	 *
	 * @author David J. Peare
	 *
	 */
	public interface Step {
		/**
		 * Get the enclosing proof for this step. Every step must be associated
		 * with a proof, and all connected steps must be in the same proof.
		 *
		 * @return
		 */
		Proof getProof();
		/**
		 * Get the parent (i.e. before) state for this step.
		 *
		 * @return
		 */
		Step getParent();

		/**
		 * Get the list of formulae introduced by this step
		 * @return
		 */
		List<Formula> getIntroductions();

		/**
		 * Get the formulae on which this step depends
		 *
		 * @return
		 */
		List<WyalFile.Expr> getDependencies();

		/**
		 * Get the number of child steps originating from this step
		 *
		 * @return
		 */
		int numberOfChildren();

		/**
		 * Get the child (i.e. after) state resulting from this step
		 *
		 * @return
		 */
		Step getChild(int ith);
	}
}
