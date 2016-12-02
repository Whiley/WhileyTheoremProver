package wyal.util;

import java.util.BitSet;
import java.util.List;

import wyail.lang.SyntaxTree;
import wyal.lang.Bytecode;
import wyal.lang.WyalFile;
import wyal.lang.WyalFile.Assert;

public abstract class InteractiveProof extends AbstractProof {
	/**
	 * The set of all possible rules which can be used during this interactive
	 * proof.
	 */
	private final Rule[] rules;

	public InteractiveProof(WyalFile.Assert assertion, Rule...rules) {
		super(assertion);
		this.rules = rules;
	}

	public SyntaxTree.Term getLocation(int index) {
		return tree.getLocation(index);
	}

	/**
	 * Begin the proof. This initialises data and simplifies information as
	 * necessary.
	 */
	public abstract void begin();

	/**
	 * Represents a proof by contradiction. This is the most common way to
	 * determine that a given assertion is correct. Specifically, we assume the
	 * assertion is *not* correct and then attempt to prove a contradiction.
	 *
	 * @author David J. Pearce
	 *
	 */
	public static class ByContradiction extends InteractiveProof {
		public ByContradiction(Assert assertion, Rule[] rules) {
			super(assertion, rules);
		}

		@Override
		public boolean isComplete() {
			throw new RuntimeException("Implemnent me!");
		}

		@Override
		public void begin() {
			assumeNot(assertion.getBody());
		}
	}
}
