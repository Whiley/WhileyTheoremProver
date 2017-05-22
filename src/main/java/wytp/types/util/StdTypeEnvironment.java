package wytp.types.util;

import java.util.HashMap;
import java.util.Map;
import java.util.Set;

import wyal.lang.WyalFile;
import wyal.lang.WyalFile.Type;
import wyal.lang.WyalFile.VariableDeclaration;
import wytp.types.TypeInferer;
import wytp.types.TypeInferer.Environment;

/**
 * Provides a very simple typing environment which defaults to using the
 * declared type for a variable (this is the "null" case). However, the
 * environment can also be updated to override the declared type with a new type
 * as appropriate.
 *
 * @author David J. Pearce
 *
 */
public class StdTypeEnvironment implements TypeInferer.Environment {
	private final Map<WyalFile.VariableDeclaration,Type> refinements;

	public StdTypeEnvironment() {
		this.refinements = new HashMap<>();
	}

	public StdTypeEnvironment(Map<WyalFile.VariableDeclaration,Type> refinements) {
		this.refinements = new HashMap<>(refinements);
	}

	@Override
	public Type getType(VariableDeclaration var) {
		Type refined = refinements.get(var);
		if(refined != null) {
			return refined;
		} else {
			return var.getType();
		}
	}

	@Override
	public Environment refineType(VariableDeclaration var, Type refinement) {
		Type type = intersect(getType(var),refinement);
		StdTypeEnvironment r = new StdTypeEnvironment(this.refinements);
		r.refinements.put(var,type);
		return r;
	}


	@Override
	public Set<VariableDeclaration> getRefinedVariables() {
		return refinements.keySet();
	}

	@Override
	public String toString() {
		String r = "{";
		boolean firstTime = true;
		for(WyalFile.VariableDeclaration var : refinements.keySet()) {
			if(!firstTime) {
				r += ", ";
			}
			firstTime=false;
			r += var.getVariableName() + "->" + getType(var);
		}
		return r + "}";
	}


	private Type intersect(Type left, Type right) {
		// FIXME: a more comprehensive simplification strategy would make sense
		// here.
		if(left == right || left.equals(right)) {
			return left;
		} else {
			return new Type.Intersection(left,right);
		}
	}
}
