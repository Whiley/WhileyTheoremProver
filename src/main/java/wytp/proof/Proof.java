// Copyright 2017 David J. Pearce
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//    http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.
package wytp.proof;

import java.util.List;

import wyal.lang.WyalFile;
import wyal.lang.WyalFile.Declaration;
import wyal.lang.WyalFile.Expr;
import wyal.lang.WyalFile.Declaration.Assert;
import wybs.lang.NameResolver;
import wybs.lang.SyntacticHeap;
import wybs.lang.NameResolver.ResolutionError;
import wytp.proof.Formula.Disjunct;
import wytp.types.TypeInferer;
import wytp.types.TypeSystem;

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
		 * Get the typing environment at this state in a given proof. The type
		 * environment gives the current type for all declared variables. The
		 * environment is not static as the type of a given variable can be
		 * refined at any given state as more facts become known.
		 *
		 * @return
		 */
		TypeInferer.Environment getTypeEnvironment();

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
		 * Infer a new fact from one or more existing facts.
		 *
		 * @param rule
		 * @param truth
		 * @param dependencies
		 * @return
		 */
		State infer(Proof.Rule rule, Formula truth, Formula... dependencies);

		/**
		 * Refine the type of a given variable in this state. That is, make the
		 * type more precise at this point.
		 *
		 * @param rule
		 *            The rule which is causing this particular refinement.
		 * @param variable
		 *            The variable whose type is being refined.
		 * @param type
		 *            The type which this variable is refined with.
		 * @param dependencies
		 *            The immediate dependencies needed to establish this
		 *            refinement.
		 *
		 * @return
		 */
		State refine(Proof.Rule rule, WyalFile.VariableDeclaration variable, WyalFile.Type type, Formula... dependencies);

		/**
		 * Ensure a given formula is properly allocated into this state.
		 *
		 * @param f
		 * @return
		 */
		Formula allocate(Formula f);
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
		 * @param current
		 *            The current state of truth. That is, everything which is
		 *            known to be true at this point.
		 * @param head
		 *            The current tip of the proof branch. This maybe some
		 *            distance in the future from the current state, and
		 *            identifies truths which have yet to be processed.
		 * @return One or more states representing the remaining states to be
		 *         discharged
		 */
		State apply(State current, State head) throws ResolutionError;
	}

	interface NonLinearRule extends Rule {
		/**
		 * Apply a given rule to a given state, producing one (or more)
		 * potentially updated states. If the rule does not apply or produces no
		 * additional information, then the original state is returned
		 * untouched.
		 *
		 * @param current
		 *            The current state of truth. That is, everything which is
		 *            known to be true at this point.
		 * @param head
		 *            The current tip of the proof branch. This maybe some
		 *            distance in the future from the current state, and
		 *            identifies truths which have yet to be processed.
		 * @return One or more states representing the remaining states to be
		 *         discharged
		 */
		State[] apply(State current, State head) throws ResolutionError;
	}
}
