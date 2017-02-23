// Copyright (c) 2011, David J. Pearce (djp@ecs.vuw.ac.nz)
// All rights reserved.
//
// This software may be modified and distributed under the terms
// of the BSD license.  See the LICENSE file for details.
package wyal.util;

import java.util.ArrayList;
import java.util.List;

import wyal.lang.SyntacticItem;
import wyal.lang.WyalFile;
import wyal.lang.WyalFile.Declaration;
import wyal.lang.WyalFile.Declaration.Named;
import wyal.lang.WyalFile.Expr;
import wyal.lang.WyalFile.Identifier;
import wyal.lang.WyalFile.Name;
import wyal.lang.WyalFile.Pair;
import wyal.lang.WyalFile.Stmt;
import wyal.lang.WyalFile.Type;
import wyal.lang.WyalFile.Value;
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
	/**
	 * The enclosing WyAL file being checked.
	 */
	private final WyalFile parent;

	/**
	 * The type system encapsulates the core algorithms for type simplification
	 * and subtyping testing.
	 */
	private TypeSystem types;

	public TypeChecker(final WyalFile parent) {
		this.parent = parent;
		this.types = new TypeSystem(parent);
	}

	public void check() {
		// FIXME: this is horifically inefficient!!
		for (int i = 0; i != parent.size(); ++i) {
			check(parent.getSyntacticItem(i));
		}
	}

	private void check(SyntacticItem item) {
		if(item instanceof Stmt) {
			check((Stmt) item);
		}
	}

	private Type check(Stmt expr) {
		switch (expr.getOpcode()) {
		case STMT_block:
			return checkBlock((Stmt.Block) expr);
		case STMT_ifthen:
			return checkIfThen((Stmt.IfThen) expr);
		case STMT_caseof:
			return checkCaseOf((Stmt.CaseOf) expr);
		case STMT_forall:
		case STMT_exists:
			return checkQuantifier((Stmt.Quantifier) expr);
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

	private Type checkBlock(Stmt.Block stmt) {
		for(Stmt child : stmt.getOperands()) {
			Type t = check(child);
			checkIsSubtype(new Type.Bool(), t);
		}
		return new Type.Bool();
	}

	private Type checkCaseOf(Stmt.CaseOf stmt) {
		for(Stmt child : stmt.getOperands()) {
			Type t = check(child);
			checkIsSubtype(new Type.Bool(), t);
		}
		return new Type.Bool();
	}

	private Type checkIfThen(Stmt.IfThen stmt) {
		Type lhs = check(stmt.getIfBody());
		Type rhs = check(stmt.getThenBody());
		checkIsSubtype(new Type.Bool(), lhs);
		checkIsSubtype(new Type.Bool(), rhs);
		return new Type.Bool();
	}

	private Type checkQuantifier(Stmt.Quantifier stmt) {
		Type body = check(stmt.getBody());
		checkIsSubtype(new Type.Bool(), body);
		return new Type.Bool();
	}

	/**
	 * Check the type of a given constant expression. This is straightforward
	 * since the determine is fully determined by the kind of constant we have.
	 *
	 * @param expr
	 * @return
	 */
	private Type checkConstant(Expr.Constant expr) {
		Value item = expr.getValue();
		switch (item.getOpcode()) {
		case CONST_null:
			return new Type.Null();
		case CONST_bool:
			return new Type.Bool();
		case CONST_int:
			return new Type.Int();
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
		WyalFile.Tuple<Expr> arguments = expr.getArguments();
		Type[] types = new Type[arguments.size()];
		for (int i = 0; i != arguments.size(); ++i) {
			types[i] = check(arguments.getOperand(i));
		}
		// Attempt to resolve the appropriate function type
		Named.FunctionOrMacro sig = resolveAsDeclaredFunctionOrMacro(expr.getName(), types);
		// Finally, return the declared returns
		if (sig instanceof Named.Function) {
			Named.Function fn = (Named.Function) sig;
			// Functions have specific return values
			WyalFile.Tuple<VariableDeclaration> d = fn.getReturns();
			if (d.size() != 1) {
				throw new RuntimeException("invalid number of returns");
			} else {
				return d.getOperand(0).getType();
			}
		} else {
			return new Type.Bool();
		}
	}

	private Type checkIsOperator(Expr.Is expr) {
		Type lhs = check(expr.getExpr());
		Type rhs = expr.getTypeTest();
		// TODO: implement a proper intersection test here to ensure the lhs and
		// rhs types make sense (i.e. have some intersection).
		return new Type.Bool();
	}

	private Type checkRecordAccess(Expr.RecordAccess expr) {
		Type src = check(expr.getSource());
		Type.Record effectiveRecord = types.extractReadableRecordType(src);
		VariableDeclaration[] fields = effectiveRecord.getFields();
		String actualFieldName = expr.getField().get();
		for (int i = 0; i != fields.length; ++i) {
			VariableDeclaration vd = fields[i];
			String declaredFieldName = vd.getVariableName().get();
			if (declaredFieldName.equals(actualFieldName)) {
				return vd.getType();
			}
		}
		//
		throw new RuntimeException("invalid field access: " + actualFieldName);
	}

	private Type checkRecordInitialiser(Expr.RecordInitialiser expr) {
		Pair<Identifier,Expr>[] fields = expr.getFields();
		VariableDeclaration[] decls = new VariableDeclaration[fields.length];
		for (int i = 0; i != fields.length; ++i) {
			Identifier fieldName = fields[i].getFirst();
			Type fieldType = check(fields[i].getSecond());
			decls[i] = new VariableDeclaration(fieldType, fieldName);
		}
		//
		return new Type.Record(decls);
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
		return new Type.Bool();
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
		return new Type.Int();
	}

	/**
	 * Check the type for a given arithmetic operator. Such an operator has the
	 * type bool, and all children should also produce values of type int.
	 *
	 * @param expr
	 * @return
	 */
	private Type checkComparisonOperator(Expr.Operator expr) {
		switch (expr.getOpcode()) {
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

		return new Type.Bool();
	}

	private void checkOperands(Expr.Operator expr, Class<? extends Type> kind) {
		for (int i = 0; i != expr.size(); ++i) {
			checkIsType(check(expr.getOperand(i)), kind);
		}
	}

	private Type checkArrayLength(Expr.Operator expr) {
		Type src = check(expr.getOperand(0));
		Type.Array effectiveArray = types.extractReadableArrayType(src);
		return new Type.Int();
	}

	private Type checkArrayInitialiser(Expr.Operator expr) {
		Type[] ts = new Type[expr.size()];
		for (int i = 0; i != ts.length; ++i) {
			ts[i] = check(expr.getOperand(i));
		}
		Type element = types.union(ts);
		return new Type.Array(element);
	}

	private Type checkArrayGenerator(Expr.Operator expr) {
		Type element = check(expr.getOperand(0));
		checkIsType(check(expr.getOperand(1)), Type.Int.class);
		return new Type.Array(element);
	}

	private Type checkArrayAccess(Expr.Operator expr) {
		Type src = check(expr.getOperand(0));
		Type.Array effectiveArray = types.extractReadableArrayType(src);
		Type indexType = check(expr.getOperand(1));
		checkIsSubtype(new Type.Int(), indexType);
		return effectiveArray.getElement();
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
			Declaration.Named.Type td = types.resolveAsDeclaredType(nt.getName());
			// Extract the actual type corresponding to this declaration
			Type declared = td.getVariableDeclaration().getType();
			// Check it makes sense
			return checkIsType(declared, kind);
		} else {
			throw new RuntimeException("expected " + kind.getName() + ", got " + type);
		}
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
		// Identify all function or macro declarations which should be
		// considered
		List<Named.FunctionOrMacro> candidates = findCandidateFunctionOrMacroDeclarations(name);
		// Based on given argument types, select the most precise signature from
		// the candidates.
		Named.FunctionOrMacro selected = selectCandidateFunctionOrMacroDeclaration(candidates, args);
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
	private Named.FunctionOrMacro selectCandidateFunctionOrMacroDeclaration(List<Named.FunctionOrMacro> candidates,
			Type... args) {
		Named.FunctionOrMacro best = null;
		for (int i = 0; i != candidates.size(); ++i) {
			Named.FunctionOrMacro candidate = candidates.get(i);
			// Check whether the given candidate is a real candidate or not. A
			if (isApplicable(candidate, args)) {
				// Yes, this candidate is applicable.
				if (best == null) {
					// No other candidates are applicable so far. Hence, this
					// one is automatically promoted to the best seen so far.
					best = candidate;
				} else if (isSubtype(candidate, best)) {
					// This candidate is a subtype of the best seen so far.
					// Hence, it is now the best seen so far.
					best = candidate;
				} else if (isSubtype(best, candidate)) {
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
		if (best != null) {
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
		WyalFile.Tuple<VariableDeclaration> parameters = decl.getParameters();
		if (parameters.size() != args.length) {
			// Differing number of parameters / arguments. Since we don't
			// support variable-length argument lists (yet), there is nothing
			// more to consider.
			return false;
		}
		// Number of parameters matches number of arguments. Now, check that
		// each argument is a subtype of its corresponding parameter.
		for (int i = 0; i != args.length; ++i) {
			Type param = parameters.getOperand(i).getType();
			if (!types.isSubtype(param, args[i])) {
				return false;
			}
		}
		//
		return true;
	}

	private void checkIsSubtype(Type lhs, Type rhs) {
		if (!types.isSubtype(lhs, rhs)) {
			throw new RuntimeException("type " + rhs + " not subtype of " + lhs);
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
		WyalFile.Tuple<VariableDeclaration> parentParams = parent.getParameters();
		WyalFile.Tuple<VariableDeclaration> childParams = child.getParameters();
		if (parentParams.size() != childParams.size()) {
			// Differing number of parameters / arguments. Since we don't
			// support variable-length argument lists (yet), there is nothing
			// more to consider.
			return false;
		}
		// Number of parameters matches number of arguments. Now, check that
		// each argument is a subtype of its corresponding parameter.
		for (int i = 0; i != parentParams.size(); ++i) {
			Type parentParam = parentParams.getOperand(i).getType();
			Type childParam = childParams.getOperand(i).getType();
			if (!types.isSubtype(parentParam, childParam)) {
				return false;
			}
		}
		//
		return true;
	}
}