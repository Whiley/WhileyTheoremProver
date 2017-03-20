package wyal.util;

import java.util.*;

import wyal.lang.Formula;
import wyal.lang.Proof;
import wyal.lang.SyntacticHeap;
import wyal.lang.WyalFile;
import wyal.lang.WyalFile.Declaration.Assert;

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

	public abstract static class AbstractStep<T extends Proof.State> implements Proof.State {
		protected final Proof proof;
		protected final List<WyalFile.Expr> dependencies;
		protected final Proof.Rule rule;
		protected final ArrayList<T> children;
		protected T parent;

		public AbstractStep(Proof proof, T parent, Proof.Rule rule, WyalFile.Expr... dependencies) {
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

		public void setParent(T parent) {
			this.parent = parent;
		}

		@Override
		public Proof.Rule getRule() {
			return rule;
		}

		@Override
		public List<WyalFile.Expr> getDependencies() {
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

		public void setChild(int ith, T child) {
			children.set(ith, child);
		}
	}
}
