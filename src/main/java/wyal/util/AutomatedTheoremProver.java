package wyal.util;

import java.io.PrintWriter;
import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.BitSet;
import java.util.Collections;
import java.util.IdentityHashMap;
import java.util.Objects;

import wyal.io.WyalFilePrinter;
import wyal.lang.SyntacticHeap;
import wyal.lang.SyntacticItem;
import wyal.lang.WyalFile;
import wyal.lang.WyalFile.*;
import wyal.rules.AndElimination;
import wyal.rules.NotElimination;

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
		Expr body = toExpressionForm(SyntacticHeaps.clone(decl.getBody()));
		// This is a bit naughty I suppose.
		WyalFile.Expr root = new WyalFile.Expr.Operator(Opcode.EXPR_not, body);
		heap.allocate(root);
		root = (WyalFile.Expr) pushDownRewrite(new AndElimination(),root,root);
		PrintWriter out = new PrintWriter(System.out);
		new WyalFilePrinter(out).writeExpression(root);
		out.flush();
		System.out.println();
		// Prepare for proof-by-contradiction
		heap.print(new PrintWriter(System.out));
	}

	/**
	 * Take a tree of statements and expressions, and return a tree of just
	 * expressions (modulo variable declarations). This is necessary to then
	 * invert the tree using not elimination. It's also straightforward, since
	 * every statement corresponds directly to an expression. For example, a
	 * "block" is a conjunction, a "case of" is a disjunction, etc.
	 *
	 * @param s
	 * @return
	 */
	public static WyalFile.Expr toExpressionForm(WyalFile.Stmt s) {
		switch(s.getOpcode()) {
		case STMT_block: {
			WyalFile.Stmt.Block b = (WyalFile.Stmt.Block) s;
			Expr[] operands = toExpressionForm(b.getOperands());
			return new Expr.Operator(Opcode.EXPR_and, operands);
		}
		case STMT_caseof: {
			WyalFile.Stmt.CaseOf b = (WyalFile.Stmt.CaseOf) s;
			Expr[] operands = toExpressionForm(b.getOperands());
			return new Expr.Operator(Opcode.EXPR_or, operands);
		}
		case STMT_ifthen: {
			WyalFile.Stmt.IfThen it = (WyalFile.Stmt.IfThen) s;
			Expr lhs = toExpressionForm(it.getIfBody());
			Expr rhs = toExpressionForm(it.getThenBody());
			// Invert lhs
			lhs = new Expr.Operator(Opcode.EXPR_not, lhs);
			// Done
			return new Expr.Operator(Opcode.EXPR_or, lhs, rhs);
		}
		case STMT_forall: {
			WyalFile.Stmt.Quantifier q = (WyalFile.Stmt.Quantifier) s;
			WyalFile.Expr body = toExpressionForm(q.getBody());
			return new WyalFile.Expr.Quantifier(Opcode.EXPR_forall, q.getParameters(), body);
		}
		case STMT_exists: {
			WyalFile.Stmt.Quantifier q = (WyalFile.Stmt.Quantifier) s;
			WyalFile.Expr body = toExpressionForm(q.getBody());
			return new WyalFile.Expr.Quantifier(Opcode.EXPR_exists, q.getParameters(), body);
		}
		default:
			if(s instanceof WyalFile.Expr) {
				return (WyalFile.Expr) s;
			} else {
				throw new IllegalArgumentException("unknown statement encountered: " + s.getOpcode());
			}
		}
	}

	public static WyalFile.Expr[] toExpressionForm(WyalFile.Stmt[] stmts) {
		WyalFile.Expr[] exprs = new WyalFile.Expr[stmts.length];
		for(int i=0;i!=exprs.length;++i) {
			exprs[i] = toExpressionForm(stmts[i]);
		}
		return exprs;
	}

	public static interface RewriteRule {
		/**
		 * Attempt to rewrite a given syntactic item, producing a potentially
		 * updated item. In the case that the rewrite did not apply, then the
		 * original item is returned. Otherwise, a new item may be returned
		 * (which may be completed new, or maybe an existing item in the heap).
		 *
		 * @param item
		 * @return
		 */
		SyntacticItem rewrite(SyntacticItem item);
	}

	public static SyntacticItem pushDownRewrite(RewriteRule rule, SyntacticItem item, SyntacticItem root) {
		// FIXME: this strategy can be vastly improved by integrating properly
		// with substitute(). Basically, to avoid much needless copying of
		// items.
		SyntacticItem nItem = rule.rewrite(item);
		if(nItem != item) {
			root = SyntacticHeaps.substitute(root, item, nItem);
		}
		SyntacticItem[] children = nItem.getOperands();
		if(children != null) {
			for(int i=0;i!=children.length;++i) {
				SyntacticItem child = children[i];
				if(child != null) {
					root = pushDownRewrite(rule,child,root);
				}
			}
		}
		return root;
	}
}
