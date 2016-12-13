// Copyright (c) 2011, David J. Pearce (djp@ecs.vuw.ac.nz)
// All rights reserved.
//
// This software may be modified and distributed under the terms
// of the BSD license.  See the LICENSE file for details.
package wyal.util;

import java.lang.reflect.InvocationTargetException;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import wyal.lang.SyntacticItem;
import wyal.lang.WyalFile;
import wyal.lang.SemanticType.Bool;
import wyal.lang.WyalFile.Declaration;
import wyal.lang.WyalFile.Declaration.Named;
import wyal.lang.WyalFile.Expr;
import wyal.lang.WyalFile.Identifier;
import wyal.lang.WyalFile.Item;
import wyal.lang.WyalFile.Name;
import wyal.lang.WyalFile.Opcode;
import wyal.lang.WyalFile.Pair;
import wyal.lang.WyalFile.Type;
import wyal.lang.WyalFile.VariableDeclaration;

/**
 * Implements the type checker for WyAL source files. This is a standard and
 * relatively straightforward type checker which simply propagates declared type
 * information through all expressions within a WyAL file. In addition, this
 * resolves names and invocations as necessary.
 *
 * @author David J. Pearce
 *
 */
public class TypeChecker {

	public void check(final WyalFile parent) {
		for (int i = 0; i != parent.size(); ++i) {
			check(parent.getSyntacticItem(i));
		}
	}

	private void check(SyntacticItem item) {
		if (item instanceof Expr) {
			check((Expr) item);
		}
	}

	private Type check(Expr expr) {
		switch (expr.getOpcode()) {
		// Ignored
		case EXPR_const:
			return checkConstant((Expr.Constant) expr);
		case EXPR_var:
			return checkVariable((Expr.VariableAccess) expr);
		// Invocation
		case EXPR_invoke:
			return checkInvocation((Expr.Invoke) expr);
		// Logical operators
		case EXPR_not:
		case EXPR_and:
		case EXPR_or:
		case EXPR_implies:
		case EXPR_iff:
			return checkLogicalOperator((Expr.Operator) expr);
		// Arithmetic operators
		case EXPR_eq:
		case EXPR_neq:
		case EXPR_lt:
		case EXPR_lteq:
		case EXPR_gt:
		case EXPR_gteq:
			return checkComparisonOperator((Expr.Operator) expr);
		case EXPR_neg:
		case EXPR_add:
		case EXPR_sub:
		case EXPR_mul:
		case EXPR_div:
		case EXPR_rem:
			return checkArithmeticOperator((Expr.Operator) expr);
		// Other operators
		case EXPR_is:
			return checkIsOperator((Expr.Is) expr);
			// Record expressions
		case EXPR_recinit:
			return checkRecordInitialiser((Expr.RecordInitialiser) expr);
		case EXPR_recfield:
			return checkRecordAccess((Expr.RecordAccess) expr);
			// Array expressions
		case EXPR_arrlen:
			return checkArrayLength((Expr.Operator) expr);
		case EXPR_arrinit:
			return checkArrayInitialiser((Expr.Operator) expr);
		case EXPR_arrgen:
			return checkArrayGenerator((Expr.Operator) expr);
		case EXPR_arridx:
			return checkArrayAccess((Expr.Operator) expr);
			// Reference expressions
		default:
			throw new RuntimeException("unknown bytecode encountered: " + expr);
		}
	}

	/**
	 * Check the type of a given constant expression. This is straightforward
	 * since the determine is fully determined by the kind of constant we have.
	 *
	 * @param expr
	 * @return
	 */
	private Type checkConstant(Expr.Constant expr) {
		Item item = expr.getValue();
		switch (item.getOpcode()) {
		case CONST_null:
			return findPrimitiveType(expr.getParent(), Type.Null.class);
		case CONST_bool:
			return findPrimitiveType(expr.getParent(), Type.Bool.class);
		case CONST_int:
			return findPrimitiveType(expr.getParent(), Type.Int.class);
		default:
			throw new RuntimeException("unknown constant encountered: " + expr);
		}
	}

	/**
	 * Check the type of a given variable access. This is straightforward since
	 * the determine is fully determined by the declared type for the variable
	 * in question.
	 *
	 * @param expr
	 * @return
	 */
	private Type checkVariable(Expr.VariableAccess expr) {
		VariableDeclaration decl = expr.getVariableDeclaration();
		return decl.getType();
	}

	private Type checkInvocation(Expr.Invoke expr) {
		// Determine the argument types
		Expr[] arguments = expr.getArguments();
		Type[] types = new Type[arguments.length];
		for (int i = 0; i != arguments.length; ++i) {
			types[i] = check(arguments[i]);
		}
		// Attempt to resolve the appropriate function type
		Named.FunctionOrMacro sig = resolveAsDeclaredFunctionOrMacro(expr.getName(), types);
		// Finally, return the declared returns
		if (sig instanceof Named.Function) {
			Named.Function fn = (Named.Function) sig;
			// Functions have specific return values
			VariableDeclaration[] d = fn.getReturns();
			if (d.length != 1) {
				throw new RuntimeException("invalid number of returns");
			} else {
				return d[0].getType();
			}
		} else {
			return findPrimitiveType(expr.getParent(), Type.Bool.class);
		}
	}

	private Type checkIsOperator(Expr.Is expr) {
		Type lhs = check(expr.getExpr());
		Type rhs = expr.getType();
		// TODO: implement a proper intersection test here to ensure the lhs and
		// rhs types make sense (i.e. have some intersection).
		return findPrimitiveType(expr.getParent(), Type.Bool.class);
	}

	private Type checkRecordAccess(Expr.RecordAccess expr) {
		Type src = check(expr.getSource());
		Type.Record record = expandAsEffectiveRecord(src);
		VariableDeclaration[] fields = record.getFields();
		String actualFieldName = expr.getField().get();
		for(int i=0;i!=fields.length;++i) {
			VariableDeclaration vd = fields[i];
			String declaredFieldName = vd.getVariableName().get();
			if(declaredFieldName.equals(actualFieldName)) {
				return vd.getType();
			}
		}
		//
		throw new RuntimeException("invalid field access: " + actualFieldName);
	}

	private Type checkRecordInitialiser(Expr.RecordInitialiser expr) {
		WyalFile parent = expr.getParent();
		Pair[] fields = expr.getFields();
		VariableDeclaration[] decls = new VariableDeclaration[fields.length];
		for(int i=0;i!=fields.length;++i) {
			Identifier fieldName = (Identifier) fields[i].getOperand(0);
			Type fieldType = check((Expr) fields[i].getOperand(1));
			decls[i] = new VariableDeclaration(parent,fieldType,fieldName);
		}
		//
		return new Type.Record(parent, decls);
	}

	/**
	 * Check the type for a given logical operator. Such an operator has the
	 * type bool, and all children should also produce values of type bool.
	 *
	 * @param expr
	 * @return
	 */
	private Type checkLogicalOperator(Expr.Operator expr) {
		checkOperands(expr, Type.Bool.class);
		return findPrimitiveType(expr.getParent(), Type.Bool.class);
	}

	/**
	 * Check the type for a given arithmetic operator. Such an operator has the
	 * type int, and all children should also produce values of type int.
	 *
	 * @param expr
	 * @return
	 */
	private Type checkArithmeticOperator(Expr.Operator expr) {
		checkOperands(expr, Type.Int.class);
		return findPrimitiveType(expr.getParent(), Type.Int.class);
	}

	/**
	 * Check the type for a given arithmetic operator. Such an operator has the
	 * type bool, and all children should also produce values of type int.
	 *
	 * @param expr
	 * @return
	 */
	private Type checkComparisonOperator(Expr.Operator expr) {
		switch(expr.getOpcode()) {
		case EXPR_eq:
		case EXPR_neq:
			//
			// TODO: could be more restrictive here
			break;
		case EXPR_lt:
		case EXPR_lteq:
		case EXPR_gt:
		case EXPR_gteq:
			checkOperands(expr, Type.Int.class);
			break;
		default:
			throw new RuntimeException("Unknown bytecode encountered: " + expr);
		}

		return findPrimitiveType(expr.getParent(), Type.Bool.class);
	}

	private void checkOperands(Expr.Operator expr, Class<? extends Type> kind) {
		for (int i = 1; i != expr.numberOfOperands(); ++i) {
			checkIsType(check(expr.getOperand(i)), kind);
		}
	}

	private Type checkArrayLength(Expr.Operator expr) {
		checkIsType(check(expr.getOperand(1)), Type.Array.class);
		return findPrimitiveType(expr.getParent(), Type.Int.class);
	}

	private Type checkArrayInitialiser(Expr.Operator expr) {
		Type[] types = new Type[expr.numberOfOperands()-1];
		for (int i = 0; i != types.length; ++i) {
			types[i] = check(expr.getOperand(i+1));
		}
		Type element = union(expr.getParent(),types);
		return new Type.Array(expr.getParent(),element);
	}

	private Type checkArrayGenerator(Expr.Operator expr) {
		Type element = check(expr.getOperand(1));
		checkIsType(check(expr.getOperand(2)), Type.Int.class);
		return new Type.Array(expr.getParent(), element);
	}

	private Type checkArrayAccess(Expr.Operator expr) {
		Type.Array at = checkIsType(check(expr.getOperand(1)), Type.Array.class);
		Type indexType = check(expr.getOperand(2));
		checkIsSubtype(findPrimitiveType(expr.getParent(),Type.Int.class),indexType);
		checkIsType(check(expr.getOperand(2)), Type.Int.class);
		return at.getElement();
	}

	/**
	 * Check whether a given instance of type is, in fact, an instance of a
	 * given kind. For example, we might want to check whether a given type is a
	 * bool or not (i.e. an instance of Type.Bool)
	 *
	 * @param type
	 * @param kind
	 */
	private <T extends Type> T checkIsType(Type type, Class<T> kind) {
		if (kind.isInstance(type)) {
			return (T) type;
		} else if (type instanceof Type.Nominal) {
			Type.Nominal nt = (Type.Nominal) type;
			// Look up the type declaration to which the name refers
			Declaration.Named.Type td = resolveAsDeclaredType(nt.getName());
			// Extract the actual type corresponding to this declaration
			Type declared = td.getVariableDeclaration().getType();
			// Check it makes sense
			return checkIsType(declared, kind);
		} else {
			throw new RuntimeException("expected " + kind.getName() + ", got " + type);
		}
	}

	/**
	 * Attempt to find an instance of a given primitive type in the enclosing
	 * WyalFile. If no such instances is found, then a new "virtual" instance is
	 * created. Virtual instances are those which have no source information
	 * associated with them.
	 *
	 * @param parent
	 * @param kind
	 * @return
	 */
	private <T extends Type> T findPrimitiveType(WyalFile parent, Class<T> kind) {
		// Look through the set of existing objects to see whether any items can
		// be reused.
		for (int i = 0; i != parent.size(); ++i) {
			SyntacticItem item = parent.getSyntacticItem(i);
			if (kind.isInstance(item)) {
				return (T) item;
			}
		}
		// Cannot find any existing occurrence of this type to use.
		// Therefore, construct one within the context of the enclosing
		// WyalFile.
		try {
			return kind.getConstructor(WyalFile.class).newInstance(parent);
		} catch (InstantiationException | IllegalAccessException | IllegalArgumentException | InvocationTargetException
				| NoSuchMethodException | SecurityException e) {
			throw new RuntimeException("Internal failure", e);
		}
	}

	/**
	 * Expand a given named declaration on the assumption that it is a type.
	 * This will initially look for the given name in the enclosing file, before
	 * considering those import statements included in the appropriate order.
	 *
	 * @param name
	 * @return
	 */
	private Declaration.Named.Type resolveAsDeclaredType(Name name) {
		Identifier[] components = name.getComponents();
		if (components.length > 1) {
			// FIXME: implement this
			throw new IllegalArgumentException("Need to handle proper namespaces!");
		}
		// Look through the enclosing file first!
		WyalFile parent = name.getParent();
		for (int i = 0; i != parent.size(); ++i) {
			SyntacticItem item = parent.getSyntacticItem(i);
			if (item instanceof Declaration.Named.Type) {
				Declaration.Named.Type nd = (Declaration.Named.Type) item;
				if (nd.getName().equals(components[0])) {
					return nd;
				}
			}
		}
		// FIXME: consider imported files as well
		throw new IllegalArgumentException("unable to resolve " + name + " as type");
	}

	/**
	 * Attempt to determine the declared function or macro to which a given
	 * invocation refers. To resolve this requires considering the name, along
	 * with the argument types as well.
	 *
	 * @param name
	 * @param args
	 * @return
	 */
	private Named.FunctionOrMacro resolveAsDeclaredFunctionOrMacro(Name name, Type... args) {
		// Identify all function or macro declarations which should be considered
		List<Named.FunctionOrMacro> candidates = findCandidateFunctionOrMacroDeclarations(name);
		// Based on given argument types, select the most precise signature from the candidates.
		Named.FunctionOrMacro selected = selectCandidateFunctionOrMacroDeclaration(candidates,args);
		return selected;
	}

	/**
	 * Extract all candidate function or macro declarations. This is basically
	 * just the complete list of function or macro declarations in the given
	 * file which have the matching name. Many of these will be immediately
	 * non-applicable because, for example, they have different numbers of
	 * parameters, etc. We don't worry about this here, we just find and return
	 * them all.
	 *
	 * @param name
	 * @return
	 */
	private List<Named.FunctionOrMacro> findCandidateFunctionOrMacroDeclarations(Name name) {
		Identifier[] components = name.getComponents();
		if (components.length > 1) {
			// FIXME: implement this
			throw new IllegalArgumentException("Need to handle proper namespaces!");
		}
		WyalFile parent = name.getParent();
		ArrayList<Named.FunctionOrMacro> candidates = new ArrayList<>();
		for (int i = 0; i != parent.size(); ++i) {
			SyntacticItem item = parent.getSyntacticItem(i);
			if (item instanceof Named.FunctionOrMacro) {
				Named.FunctionOrMacro nd = (Named.FunctionOrMacro) item;
				if (nd.getName().equals(components[0])) {
					candidates.add(nd);
				}
			}
		}
		return candidates;
	}

	/**
	 * Given a list of candidate function or macro declarations, determine the
	 * most precise match for the supplied argument types. The given argument
	 * types must be applicable to this function or macro declaration, and it
	 * must be a subtype of all other applicable candidates.
	 *
	 * @param candidates
	 * @param args
	 * @return
	 */
	private Named.FunctionOrMacro selectCandidateFunctionOrMacroDeclaration(List<Named.FunctionOrMacro> candidates, Type... args) {
		Named.FunctionOrMacro best = null;
		for(int i=0;i!=candidates.size();++i) {
			Named.FunctionOrMacro candidate = candidates.get(i);
			// Check whether the given candidate is a real candidate or not.  A
			if(isApplicable(candidate,args)) {
				// Yes, this candidate is applicable.
				if(best == null) {
					// No other candidates are applicable so far. Hence, this
					// one is automatically promoted to the best seen so far.
					best = candidate;
				} else if(isSubtype(candidate,best)) {
					// This candidate is a subtype of the best seen so far.
					// Hence, it is now the best seen so far.
					best = candidate;
				} else if(isSubtype(best,candidate)) {
					// This best so far is a subtype of this candidate.
					// Therefore, we can simply discard this candidate from
					// consideration.
				} else {
					// This is the awkward case. Neither the best so far, nor
					// the candidate, are subtypes of each other. In this case,
					// we report an error.
					throw new IllegalArgumentException("unable to resolve function");
				}
			}
		}
		// Having considered each candidate in turn, do we now have a winner?
		if(best != null) {
			// Yes, we have a winner.
			return best;
		} else {
			// No, there was no winner. In fact, there must have been no
			// applicable candidates to get here.
			throw new IllegalArgumentException("unable to resolve function");
		}
	}

	/**
	 * Determine whether a given function or macro declaration is applicable to
	 * a given set of argument types. If there number of arguments differs, it's
	 * definitely not applicable. Otherwise, we need every argument type to be a
	 * subtype of its corresponding parameter type.
	 *
	 * @param decl
	 * @param args
	 * @return
	 */
	private boolean isApplicable(Named.FunctionOrMacro decl, Type... args) {
		VariableDeclaration[] parameters = decl.getParameters();
		if(parameters.length != args.length) {
			// Differing number of parameters / arguments. Since we don't
			// support variable-length argument lists (yet), there is nothing
			// more to consider.
			return false;
		}
		// Number of parameters matches number of arguments. Now, check that
		// each argument is a subtype of its corresponding parameter.
		for(int i=0;i!=args.length;++i) {
			Type param = parameters[i].getType();
			if(!isSubtype(param,args[i])) {
				return false;
			}
		}
		//
		return true;
	}

	private Type.Record expandAsEffectiveRecord(Type type) {
		if(type instanceof Type.Record) {
			return (Type.Record) type;
		} else if(type instanceof Type.Union) {
			Type.Union union = (Type.Union) type;
			HashMap<String,Type> fields = null;
			for(int i=0;i!=union.numberOfOperands();++i) {
				Type.Record r = expandAsEffectiveRecord(union.getOperand(i));
				merge(fields,r);
			}
			//
			return constructEffectiveRecord(type.getParent(),fields);
		} else if(type instanceof Type.Nominal) {
			Type.Nominal nom = (Type.Nominal) type;
			Named.Type decl = resolveAsDeclaredType(nom.getName());
			return expandAsEffectiveRecord(decl.getVariableDeclaration().getType());
		} else {
			throw new RuntimeException("expected record type, found: " + type);
		}
	}

	private void merge(HashMap<String, Type> fields, Type.Record r) {
		VariableDeclaration[] vds = r.getFields();
		for (Map.Entry<String, Type> e : fields.entrySet()) {
			String fieldName = e.getKey();
			Type fieldType = null;
			for (int i = 0; i != vds.length; ++i) {
				VariableDeclaration fd = vds[i];
				String name = fd.getVariableName().get();
				if (fieldName.equals(name)) {
					fieldType = union(r.getParent(), e.getValue(), fd.getType());
				}
			}
			fields.put(fieldName, fieldType);
		}
	}

	private Type.Record constructEffectiveRecord(WyalFile parent, Map<String,Type> fields) {
		VariableDeclaration[] declarations = new VariableDeclaration[fields.size()];
		int index = 0;
		for(Map.Entry<String, Type> e : fields.entrySet()) {
			Identifier id = new Identifier(parent,e.getKey());
			declarations[index++] = new VariableDeclaration(parent,e.getValue(),id);
		}
		return new Type.Record(parent,declarations);
	}

	private void checkIsSubtype(Type lhs, Type rhs) {
		if(!isSubtype(lhs,rhs)) {
			throw new RuntimeException("type " + rhs + " not subtype of " + lhs);
		}
	}

	private Type union(WyalFile parent, Type...types) {
		if(types.length == 0) {
			return new Type.Void(parent);
		} else if(types.length == 1) {
			return types[0];
		} else {
			// Now going to remove duplicates; for now, that's all we can do.
			Type[] rs = Arrays.copyOf(types, types.length);
			for(int i=0;i!=rs.length;++i) {
				for(int j=i+1;j!=rs.length;++j) {
					// TODO: soooo broken
					if(rs[i] == rs[j]) {
						rs[j] = null;
					}
				}
			}
			return new Type.Union(parent, types);
		}
	}

	/**
	 * Check whether the type signature for a given function declaration is a
	 * super type of a given child declaration.
	 *
	 * @param parent
	 * @param child
	 * @return
	 */
	private boolean isSubtype(Named.FunctionOrMacro parent, Named.FunctionOrMacro child) {
		VariableDeclaration[] parentParams = parent.getParameters();
		VariableDeclaration[] childParams = child.getParameters();
		if (parentParams.length != childParams.length) {
			// Differing number of parameters / arguments. Since we don't
			// support variable-length argument lists (yet), there is nothing
			// more to consider.
			return false;
		}
		// Number of parameters matches number of arguments. Now, check that
		// each argument is a subtype of its corresponding parameter.
		for (int i = 0; i != parentParams.length; ++i) {
			Type parentParam = parentParams[i].getType();
			Type childParam = childParams[i].getType();
			if (!isSubtype(parentParam, childParam)) {
				return false;
			}
		}
		//
		return true;
	}

	/**
	 * Check whether a given "parent" type is indeed a supertype of a given
	 * "child". In the presence of arbitrary recursive types with unions,
	 * intersections and negations, this is a challenging operation.
	 *
	 * @param parent
	 * @param child
	 * @return
	 */
	private boolean isSubtype(Type parent, Type child) {
		System.out.println("IS SUBTYPE " + parent + " :> " + child);
		WyalFile.Opcode pOpcode = parent.getOpcode();
		WyalFile.Opcode cOpcode = child.getOpcode();
		// Handle non-atomic cases
		// Handle atomic cases

		if(pOpcode == Opcode.TYPE_nom) {
			Type.Nominal nom = (Type.Nominal) parent;
			Named.Type decl = resolveAsDeclaredType(nom.getName());
			// FIXME: this will cause infinite loops
			return isSubtype(decl.getVariableDeclaration().getType(),child);
		} else if(cOpcode == Opcode.TYPE_nom) {
			Type.Nominal nom = (Type.Nominal) child;
			Named.Type decl = resolveAsDeclaredType(nom.getName());
			// FIXME: this will cause infinite loops
			return isSubtype(parent,decl.getVariableDeclaration().getType());
		} else if(pOpcode == Opcode.TYPE_any || cOpcode == Opcode.TYPE_void) {
			return true;
		} else if(cOpcode == Opcode.TYPE_or) {
			Type.Union cUnion = (Type.Union) child;
			for(int i=0;i!=cUnion.numberOfOperands();++i) {
				Type cChild = cUnion.getOperand(i);
				if(!isSubtype(parent,cChild)) {
					return false;
				}
			}
			return true;
		} else if(pOpcode == Opcode.TYPE_or) {
			Type.Union pUnion = (Type.Union) parent;
			for(int i=0;i!=pUnion.numberOfOperands();++i) {
				Type pChild = pUnion.getOperand(i);
				if(isSubtype(pChild,child)) {
					return true;
				}
			}
			return false;
		} else if(pOpcode == Opcode.TYPE_not) {
			Type.Negation pNot = (Type.Negation) parent;
			// !x :> y
			return !isSubtype(pNot.getElement(),child);
		} else if(pOpcode != cOpcode) {
			return false;
		}

		switch(parent.getOpcode()) {
		case TYPE_any:
			return true;
		case TYPE_null:
		case TYPE_bool:
		case TYPE_int:
		case TYPE_void:
			return cOpcode == pOpcode || cOpcode == Opcode.TYPE_void;
		case TYPE_arr: {
			Type.Array pArray = (Type.Array) parent;
			Type.Array cArray = (Type.Array) child;
			return isSubtype(pArray.getElement(),cArray.getElement());
		}
		default:
			throw new RuntimeException("unknown type encountered: " + parent);
		}
	}

}
