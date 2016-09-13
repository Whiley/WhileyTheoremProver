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

import java.util.BitSet;
import java.util.Comparator;

import wyautl.core.Automaton;
import wyrw.core.InferenceRule;
import wyrw.core.ReductionRule;
import wyrw.core.Rewrite;
import wyrw.core.RewriteRule;

/**
 * Represents the potential activation of a given rewrite rule. An activation
 * maps states in the automaton to the inputs of a rewrite rule. An activation
 * has a dependence set which includes exactly those states upon which this
 * activation depends. Thus, any changes to those states will potentially
 * invalidate this activation.
 *
 * @author David J. Pearce
 *
 */
public abstract class AbstractActivation implements Rewrite.Activation {

	/**
	 * The complete set of states upon which this activation depends. This must
	 * include all those identified in the mapping.
	 */
	protected final BitSet dependencies;
	
	/**
	 * Temporary state used by the rule to control the rewrite. For example,
	 * this might match rewrite variables with states. In essence, the state is
	 * a continuation which gives enough information for the rewrite to pick up
	 * immediately from where it got to during probing.
	 */
	protected final int[] state;

	public AbstractActivation(BitSet dependencies, int[] state) {		
		this.dependencies = dependencies;
		this.state = state;
	}

	/**
	 * Return the target of this activation. That is the automaton state
	 * potentially being rewritten by this activation.
	 * 
	 * @return
	 */
	@Override
	public int target() {
		return state[0];
	}

	public abstract RewriteRule rule();

	public int[] binding() {
		return state;
	}
	
	/**
	 * Returns the complete set of states upon which this activation depends.
	 * Any changes to those states necessarily invalidates this activation, and
	 * requires the dirty states be rechecked for potential activations.
	 *
	 * @return
	 */
	public BitSet dependencies() {
		return dependencies;
	}

	/**
	 * <p>
	 * Apply this activation to a given automaton. This application may or may
	 * not actually modify the automaton and this is indicates by the return
	 * value.
	 * </p>
	 *
	 * @param automaton
	 *            --- the automaton to be rewritten.
	 * @param binding
	 *            --- Returns a mapping from states before the rewrite to states
	 *            after the rewrite. This must at least as big as the automaton.
	 *            Note, if the activation was unsuccessful, then this is
	 *            guaranteed to be the identity map.
	 *
	 * @return The state that was rewriten to, or K_VOID is no such state.
	 */
	public abstract int apply(Automaton automaton);
	
	/**
	 * A simple comparator for comparing activations based primarily on rule
	 * rank.
	 *
	 * @param <AbstractActivation>
	 */

	/**
	 * A standard comparator for comparing rewrite rules based on a given
	 * annotation. The annotation itself must be of integer type, and rules are
	 * simply compared using this directory.
	 *
	 * @author David J. Pearce
	 *
	 */
	public static final class RankComparator
			implements Comparator<Rewrite.Activation> {

		private final String annotation;
		
		public RankComparator(String annotation) {
			this.annotation = annotation;
		}
		
		@Override
		public int compare(Rewrite.Activation o1, Rewrite.Activation o2) {
			Object r1_ann = o1.rule().annotation(annotation);
			Object r2_ann = o2.rule().annotation(annotation);
			
			if(r1_ann == null) {
				return r2_ann == null ? 0 : 1;
			} else if(r2_ann == null) {
				return -1;
			}
			
			int r1_rank = (int) r1_ann;
			int r2_rank = (int) r2_ann;
			if (r1_rank < r2_rank) {
				return -1;
			} else if (r1_rank > r2_rank) {
				return 1;
			}

			return 0;
		}
	}
}
