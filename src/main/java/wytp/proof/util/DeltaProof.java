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

import java.util.BitSet;

import wyal.lang.WyalFile;
import wycc.util.ArrayUtils;
import wytp.proof.Formula;
import wytp.proof.Proof;
import wytp.proof.rules.CongruenceClosure;
import wytp.proof.util.AbstractProof.AbstractState;
import wytp.proof.util.FastDelta.Set;
import wytp.types.TypeInferer;
import wytp.types.TypeInferer.Environment;
import wytp.types.util.StdTypeEnvironment;
import wyal.lang.WyalFile.Declaration.Assert;
import wyal.util.NameResolver;
import wyal.util.NameResolver.ResolutionError;
import wybs.lang.SyntacticHeap;
import wyal.lang.WyalFile.Expr;
import wyal.lang.WyalFile.Type;
import wyal.lang.WyalFile.VariableDeclaration;

public class DeltaProof extends AbstractProof<DeltaProof.State> {

	public DeltaProof(Assert assertion, SyntacticHeap heap, Formula axiom) {
		super(assertion,heap);
		// Initialise the proof with the root state
		states.add(new State(this, axiom));
	}

	public static class State extends AbstractState<State> {
		/**
		 * The set of all known truths, including those which are subsumed.
		 * Always a superset of activeTruths.
		 */
		private final BitSet truths;

		private final Delta delta;

		private final TypeInferer.Environment environment;

		public State(DeltaProof proof, Formula axiom) {
			super(proof, null, null);
			this.truths = new BitSet();
			this.delta = new FastDelta(new FastDelta.Set(axiom), FastDelta.EMPTY_SET);
			this.environment = new StdTypeEnvironment();
			truths.set(axiom.getIndex());
		}

		private State(State state, Proof.Rule rule, FastDelta delta, Formula... dependencies) {
			super((DeltaProof) state.getProof(), state, rule, dependencies);
			this.truths = (BitSet) state.truths.clone();
			this.environment = state.getTypeEnvironment();
			this.delta = delta;
			state.children.add(this);
			// Update our state of the world
			FastDelta.Set additions = delta.getAdditions();
			//
			for (int i = 0; i != additions.size(); ++i) {
				truths.set(additions.get(i).getIndex());
			}
		}

		private State(State state, TypeInferer.Environment environment,  Proof.Rule rule, Formula... dependencies) {
			super((DeltaProof) state.getProof(), state, rule, dependencies);
			this.truths = (BitSet) state.truths.clone();
			this.environment = environment;
			this.delta = FastDelta.EMPTY_DELTA;
			state.children.add(this);
		}

		/**
		 * Return the list of formulae introduced by this step.
		 *
		 * @return
		 */
		@Override
		public Delta getDelta() {
			return delta;
		}

		/**
		 * Return the list of formulae introduced by this step.
		 *
		 * @return
		 */
		@Override
		public Proof.Delta getDelta(Proof.State ancestor) {
			if(this == ancestor) {
				return FastDelta.EMPTY_DELTA;
			} else if(parent == null) {
				// At this point, we must be the root node. In which case, we
				// just return what we have.
				return delta;
			} else {
				return parent.getDelta(ancestor).apply(delta);
			}
		}

		/**
		 * Determine whether a given truth is known or not.
		 *
		 * @param truth
		 * @return
		 */
		@Override
		public boolean isKnown(Formula truth) {
			return truths.get(truth.getIndex());
		}

		@Override
		public Environment getTypeEnvironment() {
			return environment;
		}

		/**
		 * Subume one formula with one or more formulae. This implication is
		 * that latter "cover" the former. The former is no longer active,
		 * though it remains a known truth. The new formula are active.
		 *
		 * @param from
		 * @param to
		 */
		@Override
		public State subsume(Proof.Rule rule, Formula from, Formula to, Formula... deps) {
			FastDelta.Set removals = FastDelta.EMPTY_SET.add(from);
			FastDelta.Set additions = FastDelta.EMPTY_SET;
			// Check whether target already known
			to = allocate(to);
			final int toIndex = to.getIndex();
			if (!truths.get(toIndex)) {
				additions = additions.add(to);
			}
			FastDelta nDelta = new FastDelta(additions, removals);
			// Register this state
			return proof.register(new State(this, rule, nDelta, ArrayUtils.append(from, deps)));
		}

		@Override
		public State infer(Proof.Rule rule, Formula truth, Formula... dependencies) {
			//
			truth = allocate(truth);
			final int index = truth.getIndex();
			if(!truths.get(index)) {
				FastDelta delta = new FastDelta(new FastDelta.Set(truth), FastDelta.EMPTY_SET);
				return proof.register(new State(this,rule,delta,dependencies));
			} else {
				return this;
			}
		}

		@Override
		public State[] split(Formula.Disjunct disjunct) {
			Formula[] cases = disjunct.getAll();
			State[] result = new State[cases.length];
			for (int i = 0; i != cases.length; ++i) {
				result[i] = this.subsume(null,disjunct,cases[i]);
			}
			return result;
		}

		@Override
		public wytp.proof.Proof.State refine(Rule rule, VariableDeclaration variable, Type type,
				Formula... dependencies) {
			Type old = environment.getType(variable);
			if(old.equals(type)) {
				// nothing has changed.
				return this;
			} else {
				TypeInferer.Environment env = environment.refineType(variable, type);
				return proof.register(new State(this,env,rule,dependencies));
			}
		}

		@Override
		public Formula allocate(Formula truth) {
			return proof.getHeap().allocate(truth);
		}
	}
}
