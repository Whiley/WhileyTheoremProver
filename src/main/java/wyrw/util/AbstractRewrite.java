// Copyright (c) 2011, David J. Pearce (djp@ecs.vuw.ac.nz)
// All rights reserved.
//
// Redistribution and use in source and binary forms, with or without
// modification, are permitted provided that the following conditions are met:
//    * Redistributions of source code must retain the above copyright
//      notice, this list of conditions and the following disclaimer.
//    * Redistributions in binary form must reproduce the above copyright
//      notice, this list of conditions and the following disclaimer in the
//      documentation and/or other materials provided with the distribution.
//    * Neither the name of the <organization> nor the
//      names of its contributors may be used to endorse or promote products
//      derived from this software without specific prior written permission.
//
// THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS" AND
// ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED
// WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
// DISCLAIMED. IN NO EVENT SHALL DAVID J. PEARCE BE LIABLE FOR ANY
// DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES
// (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES;
// LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND
// ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
// (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS
// SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

package wyrw.util;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.Comparator;
import java.util.List;

import wyautl.core.Automaton;
import wyautl.core.Schema;
import wyrw.core.Rewrite;
import wyrw.core.RewriteRule;

public abstract class AbstractRewrite implements Rewrite {
	/**
	 * The schema used by automata being reduced. This is primarily useful for
	 * debugging purposes.
	 */
	protected final Schema schema;
	
	/**
	 * The list of states in the rewrite.
	 */
	protected final ArrayList<State> states = new ArrayList<State>();
	
	/**
	 * The list of rewrite steps which have been taken so far. Each step refers
	 * to a state in the list above.
	 */
	protected final ArrayList<Rewrite.Step> steps = new ArrayList<Rewrite.Step>();
	
	/**
	 * Used to sort activations generated for a given state. This allows for
	 * some heuristics which reduce the amount of rewriting required.
	 */
	protected final Comparator<Rewrite.Activation> comparator;

	public AbstractRewrite(Schema schema, Comparator<Rewrite.Activation> comparator,
			RewriteRule... rules) {
		this.schema = schema;
		this.comparator = comparator;
	}
	
	@Override
	public List<Rewrite.Step> steps() {
		return Collections.unmodifiableList(steps);
	}

	@Override
	public List<Rewrite.State> states() {
		// Following is safe because list is unmodifiable
		return (List) Collections.unmodifiableList(states);
	}

	@Override
	public abstract int step(int from, int activation);
	
	public class State implements Rewrite.State {
		/**
		 * The automaton which this state represents.
		 */
		protected final Automaton automaton;

		/**
		 * The array of all possible activations on the given automaton.
		 */
		protected final AbstractActivation[] activations;

		/**
		 * The array of possible steps from this automaton. Each entry matches
		 * the corresponding entry in the activations array. Entries maybe null
		 * to signal steps which have not yet been explored.
		 */
		public final Rewrite.Step[] steps;

		public State(Automaton automaton, AbstractActivation... activations) {
			this.automaton = automaton;
			this.activations = activations;
			this.steps = new Rewrite.Step[activations.length];
		}

		public int size() {
			return activations.length;
		}

		public int rank() {
			int c = 0;
			for (int i = 0; i != activations.length; ++i) {
				if (steps[i] == null) {
					c++;
				}
			}
			return c;
		}

		public Automaton automaton() {
			return automaton;
		}

		public AbstractActivation activation(int index) {
			return activations[index];
		}

		public Rewrite.Step step(int index) {
			return steps[index];
		}

		private void update(int index, Rewrite.Step step) {
			this.steps[index] = step;
		}

		/**
		 * Select the first unvisited state, or return -1 if none exists.
		 * 
		 * @return
		 */
		public int select() {
			for (int i = 0; i != steps.length; ++i) {
				if (steps[i] == null) {
					return i;
				}
			}
			return -1;
		}
	}
	
	public static class Step implements Rewrite.Step {
		/**
		 * State which held before this step
		 */
		protected final int before;
		
		/**
		 * State which held after this step
		 */
		protected final int after;
		
		/**
		 * Activation which took us from before state to after state.
		 */
		protected final int activation;
		
		public Step(int before, int after, int activation) {
			this.before = before;
			this.after = after;
			this.activation = activation;
		}
		
		@Override
		public int before() {
			return before;
		}

		@Override
		public int after() {
			return after;
		}

		@Override
		public int activation() {
			return activation;
		}
		
	}
}
