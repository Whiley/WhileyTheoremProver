// Copyright 2011 The Whiley Project Developers
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

import wytp.proof.Formula;
import wytp.proof.Proof;
import wytp.proof.Proof.State;
import wytp.proof.rules.Simplification;
import wytp.proof.util.AbstractProofRule;
import wytp.types.TypeSystem;

/**
 * <p>
 * Responsible for breaking conjuncts down into their individual terms. This is
 * perhaps the most simple implementation of a <code>Proof.Rule</code> which is
 * also useful. For example, consider this simple assertion:
 * </p>
 * <pre>
 * assert:
 *   forall(int x):
 *       if:
 *           x > 0
 *       then:
 *           x >= 0
 * </pre>
 * <p>
 * To prove this by contradiction, we invert the term and look for a
 * contradiction. Eventually, we will encounter the conjunct
 * <code>(x > 0) && (x < 0)</code> and, in order to proceed, this is broken down
 * (by this rule) into the atomic truths <code>x > 0</code> and
 * <code>x < 0</code>. From there a separate rule shows the final contradiction.
 * </p>
 *
 * @author David J. Pearce
 *
 */
public class AndElimination extends AbstractProofRule implements Proof.LinearRule {

	public AndElimination(Simplification simplify,TypeSystem types) {
		super(simplify,types);
	}

	@Override
	public String getName() {
		return "And-E";
	}

	@Override
	public State apply(Proof.State head, Formula truth) {
		if (truth instanceof Formula.Conjunct) {
			Formula.Conjunct conjunct = (Formula.Conjunct) truth;
			for(int i=0;i!=conjunct.size();++i) {
				head = head.subsume(this, conjunct, conjunct.get(i));
			}
			return head;
		} else {
			// No change in the normal case
			return head;
		}
	}

}
