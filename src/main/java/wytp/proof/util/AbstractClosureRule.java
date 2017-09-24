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
package wytp.proof.util;

import wybs.lang.NameResolver.ResolutionError;
import wytp.proof.Formula;
import wytp.proof.Proof;
import wytp.proof.rules.Simplification;
import wytp.types.TypeSystem;

public abstract class AbstractClosureRule extends AbstractProofRule {
	public AbstractClosureRule(Simplification simp, TypeSystem types) {
		super(simp,types);
	}

	@Override
	public Proof.State apply(Proof.State current, Proof.State head) throws ResolutionError {
		Proof.Delta.Set additions = current.getDelta().getAdditions();
		if (additions.size() > 1) {
			throw new IllegalArgumentException("should be impossible to get here");
		} else if (additions.size() != 0) {
			Proof.Delta delta = head.getDelta(current);
			Formula truth = additions.get(0);
			if(!delta.isRemoval(truth)) {
				// Truth not yet subsumed by existing rule
				Proof.Delta.Set existingTruths = getExistingTruths(current);
				return apply(existingTruths, head, truth);
			}
		}
		// Default case: nothing to do
		return head;
	}

	@Override
	public final Proof.State apply(Proof.State head, Formula truth) {
		throw new UnsupportedOperationException();
	}

	public abstract Proof.State apply(Proof.Delta.Set existingTruths, Proof.State head, Formula truth)
			throws ResolutionError;

	protected Proof.Delta.Set getExistingTruths(Proof.State current) {
		Proof.Delta history = current.getDelta(null);
		Proof.Delta.Set existingTruths = history.getAdditions().remove(history.getRemovals());
		// We remove any additions from this state here to ensure that the new
		// truth being processed is not included in the list of existing truths.
		// However, we do want to keep any removals since these may corresponds
		// to existing truths which are subsumed by the new truth and we don't
		// to apply the new truth against a subsumed version of itself.
		return existingTruths.remove(current.getDelta().getAdditions());
	}
}
