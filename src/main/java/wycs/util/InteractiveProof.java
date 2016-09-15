package wycs.util;

import java.util.BitSet;
import java.util.List;

import wycs.lang.Bytecode;

public class InteractiveProof extends AbstractProof {
	/**
	 * The set of all possible rules which can be used during this interactive
	 * proof.
	 */
	private final Rule[] rules;

	/**
	 * Represents the current position of the interactive proof.
	 */
	private int HEAD;

	public InteractiveProof(BitSet truths, List<Bytecode> tree, Rule...rules) {
		super(tree);
		this.rules = rules;
		this.states.add(new State(truths));
		this.HEAD = 0;
	}

	@Override
	public Status getStatus() {
		return Status.INPROGRESS;
	}
}
