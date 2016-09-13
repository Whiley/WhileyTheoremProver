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

package wyrw.core;

import java.util.List;

import wyautl.core.Automaton;
import wyrw.util.AbstractActivation;

/**
 * A rewrite rule guaranteed to reduce the Automaton (in some sense). Typically,
 * this means it is guaranteed to reduce the number of states in the automaton
 * by at least one (although it can often be many more). The following
 * illustrates such a rule:
 *
 * <pre>
 * reduce Not(Not(* x)):
 *    => x
 * </pre>
 *
 * This rewrite rule is guaranteed to reduce the automaton by exactly two
 * states. As another example, consider the following:
 *
 * <pre>
 * reduce And{Bool b, BExpr... xs}:
 *    => False, if b == False
 *    => True, if |xs| == 0
 *    => And (xs)
 * </pre>
 *
 * This rewrite rule is guaranteed to reduce the automaton by at least one or
 * more states. However, some rewrite rules do not necessarily reduce the
 * automaton's size. For example, consider the following rule which distributes
 * logical <code>And</code> over logical <code>Or</code>:
 *
 * <pre>
 * reduce And{Or{BExpr... xs}, BExpr... ys}:
 *    => let ys = { And(x ++ ys) | x in xs }
 *       in Or(ys)
 * </pre>
 *
 * Observe that this rule may <i>increase</i> the overall number of states in
 * the automaton. For example, the logical expresion <code>X && (Y || Z)</code>
 * becomes <code>(X && Y) || (X && Z)</code>, which contains one additional
 * state. However, observe also that this rule cannot be applied indefinitely
 * and, for this reason, is considered to "reduce" the automaton (provided there
 * is no other rule which can "undo" what this rule does, leading to an infinite
 * rewrite cycle).
 *
 * @author David J. Pearce
 *
 */
public interface ReductionRule extends RewriteRule {

	/**
	 * Probe a given root to see whether or not this rule could be applied to
	 * it. If it can, the corresponding activation record(s) are added to the
	 * list. Note that, under no circumstances is this function permitted to
	 * modify the automaton.
	 *
	 * @param automaton
	 *            Automaton to probe.
	 * @param target
	 *            State to use as the target for the probe.
	 * @param activations
	 *            List of activations onto which to add any which are discovered
	 *            during the probe.
	 *
	 * @return
	 */
	public void probe(Automaton automaton, int target, List<Reduction.Activation> activations);

	/**
	 * <p>
	 * Apply this rule to a given automaton using the given continuation state.
	 * The application may or may not actually modify the automaton and this is
	 * indicated by the return value.
	 * </p>
	 * <p>
	 * After a <i>successful</i> rule application, the automaton may in a
	 * different state as before. However, some constraints apply. Whilst new
	 * states may be added to the automaton, states which existed prior to
	 * <code>apply()</code> being called cannot be removed (even if they become
	 * unreachable). Thus, a separate call is required to place the automaton
	 * into a compacted state.
	 * </p>
	 * <p>
	 * After an <i>unsuccessful</i> rule application, the automaton should be
	 * left in an identical state as before <code>apply()</code> was called.
	 * This means any temporary states added during <code>apply()</code> must be
	 * removed from the automaton.
	 * </p>
	 *
	 * @param automaton
	 *            --- The automaton to be rewritten.
	 * @param state
	 *            --- Data required by the rewrite to perform the rewrite. This
	 *            may be null if no such data is required.
	 *
	 * @return The state that was rewritten to. Using this, and state[0], you
	 *         can determine which state was rewritten from, and which was
	 *         rewritten to. In the case of an unsuccessful rewrite, then K_Void
	 *         is returned (-1).
	 */
	public int apply(Automaton automaton, int[] state);
	
}
