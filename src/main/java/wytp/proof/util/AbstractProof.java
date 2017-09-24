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

import java.util.*;

import wyal.lang.WyalFile;
import wyal.lang.WyalFile.Declaration.Assert;
import wybs.lang.SyntacticHeap;
import wytp.proof.Formula;
import wytp.proof.Proof;

public class AbstractProof<T extends Proof.State> implements Proof {
	protected final WyalFile.Declaration.Assert assertion;
	protected final SyntacticHeap heap;

	protected final ArrayList<T> states;

	public AbstractProof(WyalFile.Declaration.Assert assertion, SyntacticHeap heap) {
		this.states = new ArrayList<>();
		this.assertion = assertion;
		this.heap = heap;
	}

	@Override
	public SyntacticHeap getHeap() {
		return heap;
	}

	@Override
	public Assert getAssertion() {
		return assertion;
	}

	@Override
	public boolean isComplete() {
		// TODO Auto-generated method stub
		return false;
	}

	@Override
	public int size() {
		return states.size();
	}

	@Override
	public T getState(int ith) {
		return states.get(ith);
	}

	public T register(T state) {
		states.add(state);
		return state;
	}

	public abstract static class AbstractState<T extends Proof.State> implements Proof.State {
		protected final AbstractProof<T> proof;
		protected final List<Formula> dependencies;
		protected final Proof.Rule rule;
		protected final ArrayList<T> children;
		protected T parent;

		public AbstractState(AbstractProof<T> proof, T parent, Proof.Rule rule, Formula... dependencies) {
			this.proof = proof;
			this.parent = parent;
			this.dependencies = Arrays.asList(dependencies);
			this.rule = rule;
			this.children = new ArrayList<>();
		}

		@Override
		public Proof getProof() {
			return proof;
		}

		@Override
		public T getParent() {
			return parent;
		}

		@Override
		public Proof.Rule getRule() {
			return rule;
		}

		@Override
		public List<Formula> getDependencies() {
			return dependencies;
		}

		@Override
		public int numberOfChildren() {
			return children.size();
		}

		@Override
		public T getChild(int ith) {
			return children.get(ith);
		}

		@Override
		public void applyBypass(Proof.State child) {
			children.clear();
			if (child != null) {
				// FIXME: this line is clearly a hack for now
				AbstractState c = (AbstractState) child;
				children.addAll(c.children);
				c.parent = null;
				for (int i = 0; i != children.size(); ++i) {
					c = (AbstractState) children.get(i);
					c.parent = this;
				}
			}
		}

	}
}
