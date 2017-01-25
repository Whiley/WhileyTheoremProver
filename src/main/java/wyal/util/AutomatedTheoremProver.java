package wyal.util;

import java.io.PrintWriter;
import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.BitSet;
import java.util.Collections;
import java.util.IdentityHashMap;

import wyal.lang.SyntacticHeap;
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
		AbstractSyntacticHeap heap = new AbstractSyntacticHeap();
		WyalFile.Block block = decl.getBody().clone(new IdentityHashMap<>());
		heap.allocate(block);
		// Prepare for proof-by-contradiction
		negateAndSimplify(block);
		heap.print(new PrintWriter(System.out));
	}

	/**
	 * Propagate negations throughout the formula, thereby eliminating them
	 * entirely from the resulting formula.
	 *
	 * @param item
	 * @param sign
	 */
	private SyntacticItem simplify(SyntacticItem item) {
		switch(item.getOpcode()) {
		case STMT_ifthen: {
			Stmt.IfThen s = (Stmt.IfThen) item;
			SyntacticItem lhs = negateAndSimplify(s.getIfBody());
			SyntacticItem rhs = simplify(s.getThenBody());
			//?
		}

		case STMT_caseof:
		case STMT_forall:
		case STMT_exists:

		case EXPR_not:
			return negateAndSimplify(item.getOperand(0));
		case EXPR_and:
		case EXPR_or:
		case EXPR_eq:
		case EXPR_neq:
		case EXPR_lt:
		case EXPR_lteq:
		case EXPR_gt:
		case EXPR_gteq:
			for(int i=0;i!=item.size();++i) {
				SyntacticItem child = simplify(item);
				item.setOperand(i,child);
			}
			return item;
		default:
			throw new IllegalArgumentException("cannot simplify item: " + item);
		}
	}

	private SyntacticItem negateAndSimplify(SyntacticItem item) {
		switch(item.getOpcode()) {
		case STMT_ifthen:
		case STMT_caseof:
		case STMT_forall:
		case STMT_exists:
			//
		case EXPR_not:
			return simplify(item.getOperand(0));
		case EXPR_and:
		case EXPR_or:
		case EXPR_eq:
		case EXPR_neq:
		case EXPR_lt:
		case EXPR_lteq:
		case EXPR_gt:
		case EXPR_gteq:
			for(int i=0;i!=item.size();++i) {
				SyntacticItem child = negateAndSimplify(item);
				item.setOperand(i,child);
			}
			item.setOpcode(invert(item.getOpcode()));
			return item;
		default:
			throw new IllegalArgumentException("cannot simplify item: " + item);
		}
	}

	private Opcode invert(Opcode opcode) {
		switch(opcode) {
		case EXPR_and:
			return Opcode.EXPR_or;
		case EXPR_or:
			return Opcode.EXPR_and;
		// COMPARATORS
		case EXPR_eq:
			return Opcode.EXPR_neq;
		case EXPR_neq:
			return Opcode.EXPR_eq;
		case EXPR_lt:
			return Opcode.EXPR_gteq;
		case EXPR_lteq:
			return Opcode.EXPR_gt;
		case EXPR_gt:
			return Opcode.EXPR_lteq;
		case EXPR_gteq:
			return Opcode.EXPR_lt;
		default:
			throw new IllegalArgumentException("Cannot invert opcode: " + opcode);
		}
	}
}
