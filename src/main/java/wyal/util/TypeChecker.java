// Copyright (c) 2011, David J. Pearce (djp@ecs.vuw.ac.nz)
// All rights reserved.
//
// This software may be modified and distributed under the terms
// of the BSD license.  See the LICENSE file for details.
package wyal.util;

import java.lang.reflect.InvocationTargetException;

import wyal.lang.SyntacticItem;
import wyal.lang.WyalFile;
import wyal.lang.WyalFile.Declaration;
import wyal.lang.WyalFile.Expr;
import wyal.lang.WyalFile.Identifier;
import wyal.lang.WyalFile.Item;
import wyal.lang.WyalFile.Name;
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
			// Record expressions
		case EXPR_recinit:
		case EXPR_recfield:
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
		throw new RuntimeException("Need to check invoke bytecodes");
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
		checkOperands(expr, Type.Int.class);
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
		Type[] types = new Type[expr.numberOfOperands()];
		for (int i = 1; i != types.length; ++i) {
			types[i] = check(expr.getOperand(i));
		}
		return new Type.Union(expr.getParent(), types);
	}

	private Type checkArrayGenerator(Expr.Operator expr) {
		Type element = check(expr.getOperand(1));
		checkIsType(check(expr.getOperand(2)), Type.Int.class);
		return new Type.Array(expr.getParent(), element);
	}

	private Type checkArrayAccess(Expr.Operator expr) {
		Type.Array at = checkIsType(check(expr.getOperand(1)), Type.Array.class);
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
			return checkIsType(expandAsType(nt.getName()), kind);
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
	private Type expandAsType(Name name) {
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
					return nd.getVariableDeclaration().getType();
				}
			}
		}
		// FIXME: consider imported files as well
		throw new IllegalArgumentException("unable to resolve " + name + " as type");
	}
}
