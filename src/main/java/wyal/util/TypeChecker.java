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
package wyal.util;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

import wyal.lang.NameResolver;
import wyal.lang.SyntacticHeap;
import wyal.lang.SyntacticItem;
import wyal.lang.WyalFile;
import wyal.lang.NameResolver.NameNotFoundError;
import wyal.lang.NameResolver.ResolutionError;
import wyal.lang.WyalFile.Declaration;
import wyal.lang.WyalFile.Declaration.Named;
import wybs.lang.SyntacticElement;
import wybs.lang.SyntaxError;
import wycc.util.ArrayUtils;
import wytp.types.TypeSystem;
import wyal.lang.WyalFile.Expr;
import wyal.lang.WyalFile.FieldDeclaration;
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

	public TypeChecker(TypeSystem typeSystem, final WyalFile parent) {
		this.parent = parent;
		this.types = typeSystem;
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
		case EXPR_forall:
		case EXPR_exists:
			return checkQuantifier((Expr.Quantifier) expr);
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
		case EXPR_recupdt:
			return checkRecordUpdate((Expr.RecordUpdate) expr);
		// Array expressions
		case EXPR_arrlen:
			return checkArrayLength((Expr.Operator) expr);
		case EXPR_arrinit:
			return checkArrayInitialiser((Expr.Operator) expr);
		case EXPR_arrgen:
			return checkArrayGenerator((Expr.Operator) expr);
		case EXPR_arridx:
			return checkArrayAccess((Expr.Operator) expr);
		case EXPR_arrupdt:
			return checkArrayUpdate((Expr.Operator) expr);
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

	private Type checkQuantifier(Expr.Quantifier stmt) {
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
		Named.FunctionOrMacro sig = resolveAsDeclaredFunctionOrMacro(expr.getName(), expr, types);
		Type.FunctionOrMacro type = sig.getSignatureType();
		// Replace old object with fully resolved object
		expr.setSignatureType(parent.allocate(type));
		// Finally, return the declared returns
		if(type.getReturns().size() != 1) {
			throw new RuntimeException("invalid number of returns");
		} else {
			return type.getReturns().getOperand(0);
		}
	}

	/**
	 * Convert a declaration into a type signature.
	 *
	 * @param declaration
	 * @return
	 */
	private Type.FunctionOrMacroOrInvariant constructFunctionOrMacroType(Named.FunctionOrMacro declaration) {
		Type[] parameters = toTypeArray(declaration.getParameters().getOperands());
		if (declaration instanceof Named.Function) {
			Named.Function nf = (Named.Function) declaration;
			Type[] returns = toTypeArray(nf.getReturns().getOperands());
			return new Type.Function(new WyalFile.Tuple<>(parameters), new WyalFile.Tuple<>(returns));
		} else {
			return new Type.Macro(new WyalFile.Tuple<>(parameters));
		}
	}

	private Type[] toTypeArray(VariableDeclaration... declarations) {
		Type[] types = new Type[declarations.length];
		for (int i = 0; i != types.length; ++i) {
			types[i] = declarations[i].getType();
		}
		return types;
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
		Type.Record effectiveRecord = checkIsRecordType(src);
		//
		FieldDeclaration[] fields = effectiveRecord.getFields();
		String actualFieldName = expr.getField().get();
		for (int i = 0; i != fields.length; ++i) {
			FieldDeclaration vd = fields[i];
			String declaredFieldName = vd.getVariableName().get();
			if (declaredFieldName.equals(actualFieldName)) {
				return vd.getType();
			}
		}
		//
		throw new RuntimeException("invalid field access: " + actualFieldName);
	}

	private Type checkRecordUpdate(Expr.RecordUpdate expr) {
		Type src = check(expr.getSource());
		Type val = check(expr.getValue());
		Type.Record effectiveRecord = checkIsRecordType(src);
		//
		FieldDeclaration[] fields = effectiveRecord.getFields();
		String actualFieldName = expr.getField().get();
		for (int i = 0; i != fields.length; ++i) {
			FieldDeclaration vd = fields[i];
			String declaredFieldName = vd.getVariableName().get();
			if (declaredFieldName.equals(actualFieldName)) {
				// Matched the field type
				checkIsSubtype(vd.getType(),val);
				return src;
			}
		}
		//
		throw new RuntimeException("invalid field update: " + actualFieldName);
	}

	private Type checkRecordInitialiser(Expr.RecordInitialiser expr) {
		Pair<Identifier, Expr>[] fields = expr.getFields();
		FieldDeclaration[] decls = new FieldDeclaration[fields.length];
		for (int i = 0; i != fields.length; ++i) {
			Identifier fieldName = fields[i].getFirst();
			Type fieldType = check(fields[i].getSecond());
			decls[i] = new FieldDeclaration(fieldType, fieldName);
		}
		//
		return new Type.Record(false,decls);
	}

	/**
	 * Check the type for a given logical operator. Such an operator has the
	 * type bool, and all children should also produce values of type bool.
	 *
	 * @param expr
	 * @return
	 */
	private Type checkLogicalOperator(Expr.Operator expr) {
		checkOperands(expr, new Type.Bool());
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
		checkOperands(expr, new Type.Int());
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
			checkOperands(expr, new Type.Int());
			break;
		default:
			throw new RuntimeException("Unknown bytecode encountered: " + expr);
		}

		return new Type.Bool();
	}

	private void checkOperands(Expr.Operator expr, Type type) {
		for (int i = 0; i != expr.size(); ++i) {
			checkIsSubtype(type, check(expr.getOperand(i)));
		}
	}

	private Type checkArrayLength(Expr.Operator expr) {
		Type src = check(expr.getOperand(0));
		Type.Array effectiveArray = checkIsArrayType(src);
		return new Type.Int();
	}

	private Type checkArrayInitialiser(Expr.Operator expr) {
		Type[] ts = new Type[expr.size()];
		for (int i = 0; i != ts.length; ++i) {
			ts[i] = check(expr.getOperand(i));
		}
		ts = ArrayUtils.removeDuplicates(ts);
		Type element = ts.length == 1 ? ts[0] : new Type.Union(ts);
		return new Type.Array(element);
	}

	private Type checkArrayGenerator(Expr.Operator expr) {
		Type element = check(expr.getOperand(0));
		checkIsSubtype(new Type.Int(), check(expr.getOperand(1)));
		return new Type.Array(element);
	}

	private Type checkArrayAccess(Expr.Operator expr) {
		Type src = check(expr.getOperand(0));
		Type.Array effectiveArray = checkIsArrayType(src);
		Type indexType = check(expr.getOperand(1));
		checkIsSubtype(new Type.Int(), indexType);
		return effectiveArray.getElement();
	}

	private Type checkArrayUpdate(Expr.Operator expr) {
		Type src = check(expr.getOperand(0));
		Type.Array effectiveArray = checkIsArrayType(src);
		Type indexType = check(expr.getOperand(1));
		checkIsSubtype(new Type.Int(), indexType);
		Type valueType = check(expr.getOperand(2));
		checkIsSubtype(effectiveArray.getElement(), valueType);
		return effectiveArray;
	}

	/**
	 * Check whether a given type is an array type of some sort.
	 *
	 * @param type
	 * @return
	 * @throws ResolutionError
	 */
	private Type.Array checkIsArrayType(Type type) {
		try {
			Type.Array arrT = types.extractReadableArray(type);
			if(arrT == null) {
				throw new RuntimeException("expected array type, got " + type);
			}
			return arrT;
		} catch (NameResolver.ResolutionError e) {
			throw new SyntaxError(e.getMessage(), parent.getEntry(), e.getName(), e);
		}
	}

	/**
	 * Check whether a given type is a record type of some sort.
	 *
	 * @param type
	 * @return
	 */
	private Type.Record checkIsRecordType(Type type) {
		try {
			Type.Record recT = types.extractReadableRecord(type);
			if(recT == null) {
				throw new RuntimeException("expected record type, got " + type);
			}
			return recT;
		} catch (NameResolver.ResolutionError e) {
			throw new SyntaxError(e.getMessage(), parent.getEntry(), e.getName(), e);
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
	private Named.FunctionOrMacro resolveAsDeclaredFunctionOrMacro(Name name, SyntacticElement context, Type... args) {
		try {
			// Identify all function or macro declarations which should be
			// considered
			List<Named.FunctionOrMacro> candidates = types.resolveAll(name, Named.FunctionOrMacro.class);
			// Based on given argument types, select the most precise signature
			// from
			// the candidates.
			Named.FunctionOrMacro selected = selectCandidateFunctionOrMacroDeclaration(candidates, args);
			return selected;
		} catch (ResolutionError e) {
			throw new SyntaxError(e.getMessage(), parent.getEntry(), context);
		}
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
	 * @param candidate
	 * @param args
	 * @return
	 */
	private boolean isApplicable(Named.FunctionOrMacro candidate, Type... args) {
		WyalFile.Tuple<VariableDeclaration> parameters = candidate.getParameters();
		if (parameters.size() != args.length) {
			// Differing number of parameters / arguments. Since we don't
			// support variable-length argument lists (yet), there is nothing
			// more to consider.
			return false;
		}
		try {
			// Number of parameters matches number of arguments. Now, check that
			// each argument is a subtype of its corresponding parameter.
			for (int i = 0; i != args.length; ++i) {
				Type param = parameters.getOperand(i).getType();
				if (!types.isRawSubtype(param, args[i])) {
					return false;
				}
			}
			//
			return true;
		} catch (NameResolver.ResolutionError e) {
			throw new SyntaxError(e.getMessage(), parent.getEntry(), e.getName(), e);
		}
	}

	private void checkIsSubtype(Type lhs, Type rhs) {
		try {
			if (!types.isRawSubtype(lhs, rhs)) {
				throw new RuntimeException("type " + rhs + " not subtype of " + lhs);
			}
		} catch (NameResolver.ResolutionError e) {
			throw new SyntaxError(e.getMessage(), parent.getEntry(), e.getName(), e);
		}
	}

	/**
	 * Check whether the type signature for a given function declaration is a
	 * super type of a given child declaration.
	 *
	 * @param lhs
	 * @param rhs
	 * @return
	 */
	private boolean isSubtype(Named.FunctionOrMacro lhs, Named.FunctionOrMacro rhs) {
		WyalFile.Tuple<VariableDeclaration> parentParams = lhs.getParameters();
		WyalFile.Tuple<VariableDeclaration> childParams = rhs.getParameters();
		if (parentParams.size() != childParams.size()) {
			// Differing number of parameters / arguments. Since we don't
			// support variable-length argument lists (yet), there is nothing
			// more to consider.
			return false;
		}
		try {
			// Number of parameters matches number of arguments. Now, check that
			// each argument is a subtype of its corresponding parameter.
			for (int i = 0; i != parentParams.size(); ++i) {
				Type parentParam = parentParams.getOperand(i).getType();
				Type childParam = childParams.getOperand(i).getType();
				if (!types.isRawSubtype(parentParam, childParam)) {
					return false;
				}
			}
			//
			return true;
		} catch (NameResolver.ResolutionError e) {
			throw new SyntaxError(e.getMessage(), parent.getEntry(), e.getName(), e);
		}
	}
}
