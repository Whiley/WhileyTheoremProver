package wyal.util;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.BitSet;
import java.util.Collections;

import wyal.lang.SyntacticItem;
import wyal.lang.WyalFile;
import wyal.lang.WyalFile.*;

public class AutomatedTheoremProver {
	/**
	 * The enclosing WyAL file being checked.
	 */
	private final WyalFile parent;

	public AutomatedTheoremProver(final WyalFile parent) {
		this.parent = parent;
	}

	public void check() {
		for (int i = 0; i != parent.size(); ++i) {
			SyntacticItem item = parent.getSyntacticItem(i);
			if (item instanceof WyalFile.Declaration.Assert) {
				check((WyalFile.Declaration.Assert) item);
			}
		}
	}

	private void check(WyalFile.Declaration.Assert decl) {

	}

}
