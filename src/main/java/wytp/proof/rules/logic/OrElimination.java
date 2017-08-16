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
package wytp.proof.rules.logic;

import wybs.lang.NameResolver.ResolutionError;
import wytp.proof.Formula;
import wytp.proof.Proof;

/**
 * <p>
 * Responsible for eliminating disjuncts by forking the proof into multiple
 * branches, one for each clause in the disjunct. This is the canonical example
 * of a non-linear proof rule. For example, consider an assertion such as the
 * following:
 * </p>
 *
 * <pre>
 * assert:
 *   forall(int x):
 *       if:
 *           (x > 0) || (x == 0)
 *       then:
 *           x >= 0
 * </pre>
 * <p>
 * At some point during a proof-by-contradiction for this assertion, our proof
 * will begin roughly as follows:
 * </p>
 *
 * <pre>
 * 1. exists(int x).(((x == 0) || (x >= 1)) && (x < 0))
 * 2. ((x == 0) || (x >= 1)) && (x < 0)                  (Exists-E;1)
 * 3. (x == 0) || (x >= 1)                                  (And-E;2)
 * 4. x < 0                                                 (And-E;2)
 * </pre>
 * <p>
 * At this point, we must apply or-elimination on (3) to complete the proof.
 * Specifically, we split into two branches where one clause is assumed on each.
 * This looks roughly as follows:
 * </p>
 *
 * <pre>
 * 1. exists(int x).(((x == 0) || (x >= 1)) && (x < 0))
 * 2. ((x == 0) || (x >= 1)) && (x < 0)                  (Exists-E;1)
 * 3. (x == 0) || (x >= 1)                                  (And-E;2)
 * 4. x < 0                                                 (And-E;2)
 * ==================================================================
 * | 5. x == 0                                               (Or-I;3)
 * | 6. false                                              (Eq-S;4,5)
 * ------------------------------------------------------------------
 * | 7. x >= 1                                               (Or-I;3)
 * | 8. false                                             (Ieq-I;4,7)
 * ==================================================================
 * </pre>
 * <p>
 * Here we see the proof is completed by showing a contradiction in both
 * branches.
 * </p>
 *
 * @author David J. Pearce
 *
 */
public class OrElimination implements Proof.NonLinearRule {

	@Override
	public String getName() {
		return "Or-E";
	}

	@Override
	public Proof.State[] apply(Proof.State current, Proof.State head) throws ResolutionError {
		Proof.Delta.Set additions = current.getDelta().getAdditions();
		if(additions.size() > 1) {
			throw new IllegalArgumentException("should be impossible to get here");
		} else if(additions.size() != 0) {
			Proof.Delta delta = head.getDelta(current);
			Formula truth = additions.get(0);
			if(!delta.isRemoval(truth)) {
				// Truth not yet subsumed by existing rule
				return apply(head, truth);
			}
		}
		return new Proof.State[]{head};
	}

	public Proof.State[] apply(Proof.State state, Formula truth) {
		if(truth instanceof Formula.Disjunct) {
			Formula.Disjunct disjunct = (Formula.Disjunct) truth;
			Formula[] cases = disjunct.getOperands();
			Proof.State[] result = new Proof.State[cases.length];
			for (int i = 0; i != cases.length; ++i) {
				result[i] = state.subsume(this,disjunct,cases[i]);
			}
			return result;
		} else {
			// No change in the normal case
			return new Proof.State[]{state};
		}
	}
}
