// Copyright (c) 2011, David J. Pearce (djp@ecs.vuw.ac.nz)
// All rights reserved.
//
// This software may be modified and distributed under the terms
// of the BSD license.  See the LICENSE file for details.
package wyal.util;

import wyal.lang.SyntacticItem;
import wyal.lang.WyalFile;
import wyal.lang.WyalFile.Expr;

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

	private void check(Expr item) {
		switch(item.getOpcode()) {
		// Ignored
		case EXPR_const:
		case EXPR_var:
			break;
		// Invocation
		case EXPR_invoke:
			break;
		// Logical operators
		case EXPR_not:
		case EXPR_and:
		case EXPR_or:
		case EXPR_implies:
		case EXPR_iff:
			break;
		// Arithmetic operators
		case EXPR_neg:
		case EXPR_eq:
		case EXPR_neq:
		case EXPR_lt:
		case EXPR_lteq:
		case EXPR_gt:
		case EXPR_gteq:
		case EXPR_add:
		case EXPR_sub:
		case EXPR_mul:
		case EXPR_div:
		case EXPR_rem:
			break;
		// Other operators
		case EXPR_is:
			break;
		// Record expressions
		case EXPR_recinit:
		case EXPR_recfield:
			break;
		// Array expressions
		case EXPR_arrlen:
		case EXPR_arrinit:
		case EXPR_arrgen:
		case EXPR_arridx:
		// Reference expressions
			break;
		}
	}
}
