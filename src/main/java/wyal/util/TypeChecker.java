// Copyright (c) 2011, David J. Pearce (djp@ecs.vuw.ac.nz)
// All rights reserved.
//
// This software may be modified and distributed under the terms
// of the BSD license.  See the LICENSE file for details.
package wyal.util;

import java.lang.reflect.InvocationTargetException;

import wyal.lang.SyntacticItem;
import wyal.lang.WyalFile;
import wyal.lang.WyalFile.Expr;
import wyal.lang.WyalFile.Item;
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
		for(int i=0;i!=parent.size();++i) {
			check(parent.getSyntacticItem(i));
		}
	}

	private void check(SyntacticItem item) {
		if(item instanceof Expr) {
			check((Expr) item);
		}
	}

	private Type check(Expr expr) {
		switch(expr.getOpcode()) {
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
		case EXPR_neg:
		case EXPR_eq:
		case EXPR_neq:
		case EXPR_lt:
		case EXPR_lteq:
		case EXPR_gt:
		case EXPR_gteq:
			return checkComparisonOperator((Expr.Operator) expr);
		case EXPR_add:
		case EXPR_sub:
		case EXPR_mul:
		case EXPR_div:
		case EXPR_rem:
			return checkArithmeticOperator((Expr.Operator) expr);
		// Other operators
		case EXPR_is:
		// Record expressions
		case EXPR_recinit:
		case EXPR_recfield:
		// Array expressions
		case EXPR_arrlen:
		case EXPR_arrinit:
		case EXPR_arrgen:
		case EXPR_arridx:
		// Reference expressions
		default:
			throw new RuntimeException("unknown bytecode encountered");
		}
	}

	private Type checkConstant(Expr.Constant expr) {
		Item item = expr.getValue();
		switch(item.getOpcode()) {
		case CONST_null:
			return findPrimitiveType(expr.getParent(),Type.Null.class);
		case CONST_bool:
			return findPrimitiveType(expr.getParent(),Type.Bool.class);
		case CONST_int:
			return findPrimitiveType(expr.getParent(),Type.Int.class);
		default:
			throw new RuntimeException("unknown constant encountered: " + expr);
		}
	}

	private Type checkVariable(Expr.VariableAccess expr) {
		VariableDeclaration decl = expr.getVariableDeclaration();
		return decl.getType();
	}

	private Type checkInvocation(Expr.Invoke expr) {
		throw new RuntimeException("Need to check invoke bytecodes");
	}

	private Type checkLogicalOperator(Expr.Operator expr) {
		checkOperands(expr,Type.Bool.class);
		return findPrimitiveType(expr.getParent(),Type.Bool.class);
	}

	private Type checkArithmeticOperator(Expr.Operator expr) {
		checkOperands(expr,Type.Int.class);
		return findPrimitiveType(expr.getParent(),Type.Int.class);
	}

	private Type checkComparisonOperator(Expr.Operator expr) {
		checkOperands(expr,Type.Int.class);
		return findPrimitiveType(expr.getParent(),Type.Bool.class);
	}

	private void checkOperands(Expr.Operator expr, Class<? extends Type> kind) {
		for(int i=1;i!=expr.numberOfOperands();++i) {
			checkIsType(check(expr.getOperand(i)),kind);
		}
	}

	private void checkIsType(Type type, Class<? extends Type> kind) {
		if(!kind.isInstance(type)) {
			throw new RuntimeException("expected " + kind.getName() + ", got " + type);
		}
	}

	private <T extends Type> T findPrimitiveType(WyalFile parent, Class<T> kind) {
		for(int i=0;i!=parent.size();++i) {
			SyntacticItem item = parent.getSyntacticItem(i);
			if(kind.isInstance(item)) {
				return (T) item;
			}
		}
		try {
			// Cannot find any existing occurence of this type to use.
			// Therefore, we need to construct another within the context of the
			// same WyalFile.
			return kind.getConstructor(WyalFile.class).newInstance(parent);
		} catch (InstantiationException
				| IllegalAccessException
				| IllegalArgumentException
				| InvocationTargetException
				| NoSuchMethodException
				| SecurityException e) {
			throw new RuntimeException("Internal failure", e);
		}
	}
}
