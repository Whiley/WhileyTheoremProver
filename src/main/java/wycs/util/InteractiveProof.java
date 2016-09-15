package wycs.util;

import wycs.lang.Bytecode;

public class InteractiveProof extends AbstractProof {
	/**
	 * Represents the current position of the interactive proof.
	 */
	private int HEAD;

	/**
	 * The set of all possible rules which can be used during this interactive
	 * proof.
	 */
	private Rule[] rules;

	public InteractiveProof(Bytecode[] facts) {

	}
}
