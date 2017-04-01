package wyal.util;

import java.util.ArrayList;
import java.util.BitSet;

import wyal.lang.NameResolver;
import wyal.lang.NameResolver.AmbiguousNameError;
import wyal.lang.NameResolver.NameNotFoundError;
import wyal.lang.NameResolver.ResolutionError;
import wyal.lang.RawSubtypeOperator;
import wyal.lang.WyalFile;
import wyal.lang.WyalFile.FieldDeclaration;
import wyal.lang.WyalFile.Opcode;
import wyal.lang.WyalFile.Tuple;
import wyal.lang.WyalFile.Type;
import wyal.lang.WyalFile.Declaration.Named;
import wyal.util.CoerciveSubtypeOperator.Worklist;

public class CoerciveRawSubtypeOperator extends CoerciveSubtypeOperator implements RawSubtypeOperator {

	public CoerciveRawSubtypeOperator(NameResolver resolver) {
		super(resolver);
	}

	@Override
	public boolean isRawSubtype(Type parent, Type child) throws ResolutionError {
		// A :> B iff (!A & B) == void
		Result r = super.isSubtype(parent,child);
		//
		if(r == Result.Unknown) {
			// This should be dead-code as the raw subtype operator is
			// decidable.
			throw new RuntimeException("raw subtype operator returned unknown result");
		} else {
			return r == Result.True;
		}
	}
}
