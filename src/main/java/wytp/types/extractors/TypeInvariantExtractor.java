// Copyright 2017 David J. Pearce
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//    http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.
package wytp.types.extractors;

import static wytp.proof.util.Formulae.*;

import java.util.BitSet;
import java.util.HashSet;

import wyal.lang.WyalFile;
import wyal.lang.NameResolver;
import wyal.lang.NameResolver.ResolutionError;
import wyal.lang.WyalFile.Declaration;
import wyal.lang.WyalFile.Expr;
import wyal.lang.WyalFile.FieldDeclaration;
import wyal.lang.WyalFile.Identifier;
import wyal.lang.WyalFile.Opcode;
import wyal.lang.WyalFile.Tuple;
import wyal.lang.WyalFile.Type;
import wyal.lang.WyalFile.Declaration.Named;
import wytp.proof.Formula;
import wytp.proof.Formula.Conjunct;
import wytp.proof.Formula.Disjunct;
import wytp.proof.Formula.Quantifier;
import wytp.types.TypeExtractor;

/**
 * Responsible for extracting the invariant (if any) from a given type. For
 * example, consider the following type declaration:
 *
 * <pre>
 * type nat is (int x) where x >= 0
 * </pre>
 *
 * Then, extracting the invariant from type <code>nat</code> gives
 * <code>x >= 0</code>. Likewise, extracting the invariant from the type
 * <code>bool|int</code> gives the invariant
 * <code>(x is int) ==> (x >= 0)</code>. Finally, extracting the invariant from
 * the type <code>nat[]</code> gives the invariant <code>forall(int i).(0 <= i
 * && i < |xs| ==> xs[i] >= 0)</code>.
 *
 * @author David J. Pearce
 *
 */
public class TypeInvariantExtractor implements TypeExtractor<Formula,Expr> {
	private final NameResolver resolver;
	private int skolem = 0;

	public TypeInvariantExtractor(NameResolver resolver) {
		this.resolver = resolver;
	}

	@Override
	public Formula extract(Type type, Expr root) throws ResolutionError {
		return extractTypeInvariant(type, root, new HashSet());
	}

	/**
	 *
	 * @param type
	 * @param root
	 * @param typeSystem
	 * @param visited
	 *            Used to identify types previously encountered during this
	 *            search. Such types are necessarily recursive, and should only
	 *            be visited once to prevent infinite loops.
	 * @return
	 * @throws ResolutionError
	 */
	private Formula extractTypeInvariant(Type type, Expr root, HashSet<Type> visited) throws ResolutionError {
		Formula invariant = null;
		if(type.getParent() == null) {
			invariant = extractTypeInvariantInner(type,root,visited);
		} else if(!visited.contains(type)) {
			visited.add(type);
			invariant = extractTypeInvariantInner(type,root,visited);
			visited.remove(type);
		}
		return invariant;
	}
	public Formula extractTypeInvariantInner(Type type, Expr root, HashSet<Type> visited) throws ResolutionError {
		switch(type.getOpcode()) {
		case TYPE_void:
		case TYPE_any:
		case TYPE_null:
		case TYPE_bool:
		case TYPE_int:
			return null; // no invariant
		case TYPE_nom: {
			Type.Nominal nom = (Type.Nominal) type;
			Declaration.Named.Type td = resolver.resolveExactly(nom.getName(),Named.Type.class);
			Formula invariant = extractTypeInvariant(td.getVariableDeclaration().getType(), root, visited);
			if (td.getInvariant().size() == 0 && invariant == null) {
				return null;
			} else {
				Type parameter = td.getVariableDeclaration().getType();
				Type.Invariant ft = new Type.Invariant(new Tuple<>(parameter));
				return new Formula.Invoke(true, ft, nom.getName(), null, root);
			}
		}
		case TYPE_rec: {
			Type.Record r = (Type.Record) type;
			FieldDeclaration[] fields = r.getFields();
			Formula inv = null;
			for(int i=0;i!=fields.length;++i) {
				FieldDeclaration fieldDecl = (FieldDeclaration) fields[i];
				Expr.RecordAccess access = new Expr.RecordAccess(root, fieldDecl.getVariableName());
				Formula fieldInv = extractTypeInvariant(fieldDecl.getType(), access, visited);
				if(fieldInv != null) {
					if(inv == null) {
						inv = fieldInv;
					} else {
						inv = and(inv,fieldInv);
					}
				}
			}
			return inv;
		}
		case TYPE_arr: {
			Type.Array t = (Type.Array) type;
			// FIXME: trying to get rid of this would somehow be useful
			WyalFile.VariableDeclaration var = new WyalFile.VariableDeclaration(new Type.Int(),
					new Identifier("i:" + skolem++));
			Expr va = new Expr.VariableAccess(var);
			Expr el = new Expr.ArrayAccess(root, va);
			Formula inv = extractTypeInvariant(t.getElement(), el, visited);
			Expr zero = new Expr.Constant(new WyalFile.Value.Int(0));
			Expr len = new Expr.ArrayLength(root);
			if (inv != null) {
				// forall i.(0 <= i && i <|root|) ==> inv
				Formula gt = greaterOrEqual(va, zero);
				Formula lt = lessThan(va, len);
				inv = new Quantifier(true, var, implies(and(gt, lt), inv));
			}
			return inv;
		}
		case TYPE_or: {
			Type.Union t = (Type.Union) type;
			Formula result = null;
			boolean hasInvariant = false;
			for(int i=0;i!=t.size();++i) {
				Formula inv = extractTypeInvariant(t.getOperand(i),root, visited);
				Formula.Is tt = new Formula.Is(root, t.getOperand(i));
				if(result == null) {
					result = tt;
				} else {
					result = new Disjunct(result,tt);
				}
				hasInvariant |= inv != null;
			}
			if(hasInvariant) {
				return result;
			} else {
				return null;
			}
		}
		case TYPE_and: {
			Type.Intersection t = (Type.Intersection) type;
			Formula result = null;
			for(int i=0;i!=t.size();++i) {
				Formula inv = extractTypeInvariant(t.getOperand(i),root, visited);
				if(inv != null && result == null) {
					result = inv;
				} else if(inv != null) {
					result = new Conjunct(result,inv);
				}
			}
			return result;
		}
		case TYPE_not: {
			Type.Negation t = (Type.Negation) type;
			Formula inv = extractTypeInvariant(t.getElement(),root, visited);
			if(inv == null) {
				return null;
			} else {
				return invert(inv);
			}
		}
		case TYPE_fun:
		case TYPE_macro: {
			// NOTE: not very clear whether we can useful extract a type
			// invariant from here or not.
			return null;
		}
		case TYPE_ref: {
			Type.Reference t = (Type.Reference) type;
			return extractTypeInvariant(t.getElement(), new Expr.Dereference(root), visited);
		}
		default:
			throw new IllegalArgumentException("invalid type opcode: " + type.getOpcode());
		}
	}


}
