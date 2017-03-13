package wyal.util;

import java.util.*;

import wyal.lang.Formula;
import wyal.lang.Proof;
import wyal.lang.WyalFile;
import wyal.lang.WyalFile.Declaration.Assert;

public class AbstractProof<T extends Proof.Step> implements Proof {
	protected final WyalFile.Declaration.Assert assertion;

	protected final ArrayList<T> states;

	public AbstractProof(WyalFile.Declaration.Assert assertion) {
		this.states = new ArrayList<>();
		this.assertion = assertion;
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
	public int numberOfSteps() {
		return states.size();
	}

	@Override
	public T getStep(int ith) {
		return states.get(ith);
	}

	public abstract static class AbstractStep<T extends Proof.Step> implements Proof.Step {
		protected final Proof proof;
		protected  final T parent;
		protected final List<WyalFile.Expr> dependencies;
		protected final String rule;
		protected final ArrayList<T> children;

		public AbstractStep(Proof proof, T parent, String rule, WyalFile.Expr... dependencies) {
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
		public String getRule() {
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
	}
}
