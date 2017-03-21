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
	public int size();

	/**
	 * Get the ith step in this proof.
	 *
	 * @param ith
	 * @return
	 */
	public State getState(int ith);

	/**
	 * Get the heap in which this proof is operating within.
	 *
	 * @return
	 */
	public SyntacticHeap getHeap();

	/**
	 * A proof branch considered of one or more states which were derived from
	 * an existing state using a given rule.
	 *
	 * @author David J. Peare
	 *
	 */
	public interface State {
		/**
		 * Get the enclosing proof for this step. Every step must be associated
		 * with a proof, and all connected steps must be in the same proof.
		 *
		 * @return
		 */
		Proof getProof();

		/**
		 * Get the parent (i.e. before) state for this step. This is
		 * <code>null</code> if this state represents the root of the proof.
		 *
		 * @return
		 */
		State getParent();

		/**
		 * Determine whether a truth is already known or not. Truths which are
		 * already known do not need to be reintroduced.
		 *
		 * @param truth
		 * @return
		 */
		boolean isKnown(Formula truth);

		/**
		 * Get the delta between this state and its parent.
		 *
		 * @return
		 */
		Delta getDelta();

		/**
		 * Get the delta between this state and an ancestor.
		 *
		 * @return
		 */
		Delta getDelta(State ancestor);

		/**
		 * Get the name of the rule used for this step.
		 *
		 * @return
		 */
		Rule getRule();

		/**
		 * Get the formulae on which this step depends
		 *
		 * @return
		 */
		List<Formula> getDependencies();

		/**
		 * Get the number of child steps originating from this step
		 *
		 * @return
		 */
		int numberOfChildren();

		/**
		 * Get the child state resulting from this step
		 *
		 * @return
		 */
		State getChild(int ith);

		void applyBypass(State bypass);

		/**
		 * Apply a simple proof step which splits a given disjunct into several
		 * sub-states.
		 *
		 * @param disjunct
		 * @return
		 */
		State[] split(Formula.Disjunct disjunct);

		/**
		 * Subsume a given truth by a replacement.
		 *
		 * @param rule
		 * @param truth
		 * @param replacement
		 * @param dependencies
		 * @return
		 */
		State subsume(Proof.Rule rule, Formula truth, Formula replacement, Formula... dependencies);

		/**
		 * Subsume a given truth by one (or more) replacements.
		 *
		 * @param rule
		 * @param truth
		 * @param replacement
		 * @param dependencies
		 * @return
		 */
		State subsume(Proof.Rule rule, Formula truth, Formula[] replacements, Formula... dependencies);

		/**
		 * Infer a new fact from one or more existing facts.
		 *
		 * @param rule
		 * @param truth
		 * @param dependencies
		 * @return
		 */
		State infer(Proof.Rule rule, Formula truth, Formula... dependencies);

		/**
		 * Allocate a new truth into the underlying SyntacticHeap.
		 *
		 * @param truth
		 * @return
		 */
		Formula allocate(Formula truth);
	}

	/**
	 * A proof delta represents a set of truths which have been introduced
	 * during one or more proof steps.
	 *
	 * @author David J. Pearce
	 *
	 */
	interface Delta {

		/**
		 * Check whether or not a given formula is in the additions set
		 *
		 * @param truth
		 * @return
		 */
		public boolean isAddition(Formula truth);

		/**
		 * Check whether or not a given formula is in the removals set
		 *
		 * @param truth
		 * @return
		 */
		public boolean isRemoval(Formula truth);

		/**
		 * Get the set of truths added to this delta
		 *
		 * @return
		 */
		public Set getAdditions();

		/**
		 * Get the set of truths removed from this delta
		 *
		 * @return
		 */
		public Set getRemovals();

		/**
		 * Add a new formula to this delta
		 *
		 * @param truth
		 * @return
		 */
		public Delta add(Formula truth);

		/**
		 * Remove a truth from this delta (e.g. because it has been processed).
		 *
		 * @param truth
		 * @return
		 */
		public Delta remove(Formula truth);

		/**
		 * Apply a given delta on top of this one.
		 *
		 * @param delta
		 * @return
		 */
		public Delta apply(Delta delta);

		/**
		 * A set of truths in a delta, either representing those added or those
		 * removed.
		 *
		 * @author David J. Pearce
		 *
		 */
		public interface Set {
			/**
			 * Determine the number of truths in this set
			 *
			 * @return
			 */
			public int size();

			/**
			 * Check whether the given formula is contained within this set or
			 * not.
			 *
			 * @param truth
			 * @return
			 */
			public boolean contains(Formula truth);

			/**
			 * Get the ith truth in this set
			 *
			 * @param ith
			 * @return
			 */
			public Formula get(int ith);

			/**
			 * Add a truth to this set.
			 *
			 * @param truth
			 * @return
			 */
			public Set add(Formula truth);

			/**
			 * Remove a formula from this set
			 *
			 * @param truth
			 * @return
			 */
			public Set remove(Formula truth);

			/**
			 * Union two sets together
			 *
			 * @param other
			 * @return
			 */
			public Set union(Proof.Delta.Set other);

			/**
			 * Remove the elements of one set from this
			 *
			 * @param other
			 * @return
			 */
			public Set remove(Proof.Delta.Set other);
		}
	}

	/**
	 * A proof rule represents the transformation of a given proof according to
	 * some logical inference.
	 *
	 * @author David J. Pearce
	 *
	 */
	interface Rule {
		/**
		 * Get the name of this rule
		 * @return
		 */
		public String getName();
	}

	interface LinearRule extends Rule {
		/**
		 * Apply a given rule to a given state, producing one potentially
		 * updated state. If the rule does not apply or produces no additional
		 * information, then the original state is returned untouched.
		 *
		 * @param state
		 *            The current state of truth. That is, everything which is
		 *            known to be true at this point.
		 * @param truth
		 *            The given truth to which this rule should be applied.
		 * @return One or more states representing the remaining states to be
		 *         discharged
		 */
		State apply(State state, Formula truth);
	}

	interface NonLinearRule extends Rule {
		/**
		 * Apply a given rule to a given state, producing one (or more)
		 * potentially updated states. If the rule does not apply or produces no
		 * additional information, then the original state is returned untouched.
		 *
		 * @param state
		 *            The current state of truth. That is, everything which is
		 *            known to be true at this point.
		 * @param truth
		 *            The given truth to which this rule should be applied.
		 * @return One or more states representing the remaining states to be
		 *         discharged
		 */
		State[] apply(State state, Formula truth);
	}
}
