package wyail.util;

import java.util.ArrayList;
import java.util.BitSet;
import java.util.List;

import wyail.lang.SyntaxTree;
import wyal.lang.Bytecode;
import wyal.lang.WyalFile;
import wyal.lang.Proof.Rule;

/**
 * Provides a general interface for undertaking interactive proofs. Such proofs
 * may occur through, for example, a command-line interface. However, they may
 * also occur through other, more complex means (e.g. GUI, or Web Application).
 *
 * @author David J. Pearce
 *
 */
public class InteractiveProver {

	/**
	 * The WycsFile for which we are proving theorems.
	 */
	private final WyalFile wycsFile;

	/**
	 * The set of all possible rules which can be used during any interactive
	 * proof undertaken by this prover.
	 */
	private final Rule[] rules;

	/**
	 * The array of interactive proofs. Each proof corresponds to an assertion
	 * in the given wycsFile. At any given moment, multiple proofs may be in
	 * progress. Furthermore, some assertions maybe have been proved already
	 * using an automated tool. In which case, we can examine the proofs
	 * generated.
	 */
	private final InteractiveProof[] proofs;

	/**
	 * Construct a new proof console for performing interactive proofs to
	 * discharge all assertions in a given WyCS file.
	 *
	 * @param file
	 *            The WyCS file for which we are discharging assertions (i.e.
	 *            proof obligations).
	 */
	public InteractiveProver(WyalFile file, Rule...rules) {
		this.wycsFile = file;
		this.rules = rules;
		int count = 0;
		for(WyalFile.Declaration d : wycsFile.getDeclarations()) {
			if(d instanceof WyalFile.Assert) {
				count = count + 1;
			}
		}
		this.proofs = new InteractiveProof[count];
	}

	public InteractiveProof getProof(int proof) {
		return proofs[proof];
	}

	/**
	 * Get the list of interactive proofs being managed by this prover.
	 *
	 * @return
	 */
	public InteractiveProof[] getProofs() {
		return proofs;
	}

	/**
	 * Begin a new proof by contradiction.
	 */
	public void beginByContradiction(int proof) {
		WyalFile.Assert assertion = getAssertion(proof);
		InteractiveProof p = new InteractiveProof.ByContradiction(assertion,rules);
		proofs[proof] = p;
		p.begin();
	}

	private WyalFile.Assert getAssertion(int index) {
		int count = 0;
		for(WyalFile.Declaration d : wycsFile.getDeclarations()) {
			if(d instanceof WyalFile.Assert) {
				if(count == index) {
					return ((WyalFile.Assert) d);
				}
				count = count + 1;
			}
		}
		throw new IllegalArgumentException("invalid assertion: " + index);
	}

	private BitSet getInitialTruths(WyalFile.Assert assertion) {
		// Create an empty set of truths
		BitSet truths = new BitSet();
		// Set the body of the assertion as the only initial truth.
		truths.set(assertion.getBody().getIndex());
		// Done
		return truths;
	}
}
