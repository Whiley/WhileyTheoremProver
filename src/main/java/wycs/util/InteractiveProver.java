package wycs.util;

import java.util.ArrayList;
import java.util.BitSet;
import java.util.List;

import wycs.lang.Bytecode;
import wycs.lang.SyntaxTree;
import wycs.lang.WycsFile;
import wycs.lang.Proof.Rule;

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
	private final WycsFile wycsFile;

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
	public InteractiveProver(WycsFile file, Rule...rules) {
		this.wycsFile = file;
		this.rules = rules;
		int count = 0;
		for(WycsFile.Declaration d : wycsFile.getDeclarations()) {
			if(d instanceof WycsFile.Assert) {
				count = count + 1;
			}
		}
		this.proofs = new InteractiveProof[count];
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
		WycsFile.Assert assertion = getAssertion(proof);
		List<Bytecode> tree = generateInitialTree(assertion);
		BitSet truths = getInitialTruths(assertion);
		proofs[proof] = new InteractiveProof(truths,tree,rules);
	}

	private WycsFile.Assert getAssertion(int index) {
		int count = 0;
		for(WycsFile.Declaration d : wycsFile.getDeclarations()) {
			if(d instanceof WycsFile.Assert) {
				if(count == index) {
					return ((WycsFile.Assert) d);
				}
				count = count + 1;
			}
		}
		throw new IllegalArgumentException("invalid assertion: " + index);
	}

	private List<Bytecode> generateInitialTree(WycsFile.Declaration declaration) {
		ArrayList<Bytecode> locations = new ArrayList<>();
		SyntaxTree tree = declaration.getTree();
		for (int i = 0; i != tree.size(); ++i) {
			locations.add(tree.getLocation(i).getCode());
		}
		return locations;
	}

	private BitSet getInitialTruths(WycsFile.Assert assertion) {
		// Create an empty set of truths
		BitSet truths = new BitSet();
		// Set the body of the assertion as the only initial truth.
		truths.set(assertion.getBody().getIndex());
		// Done
		return truths;
	}
}
