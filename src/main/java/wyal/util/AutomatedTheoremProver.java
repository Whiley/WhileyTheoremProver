package wyal.util;

import java.io.PrintWriter;
import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.BitSet;
import java.util.Collections;
import java.util.IdentityHashMap;
import java.util.Objects;

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
		WyalFile.Block block = SyntacticHeaps.clone(decl.getBody());
		heap.allocate(block);
		pushDownRewrite(new NotElimination(),block,block);
		// Prepare for proof-by-contradiction
		heap.print(new PrintWriter(System.out));
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
		SyntacticItem[] children = item.getOperands();
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

	/**
	 * <p>
	 * Identifies syntactic items which are structurally equivalent. Typically
	 * they may differ, for example, in the attributes provided. From the
	 * perspective of the rewrite system, such details are not important.
	 * Furthermore, it is critical to ensure that equivalent items are
	 * represented using the same item.
	 * </p>
	 * <p>
	 * This operation takes time quadatric in the number of children for the
	 * item in question. Furthermore, in the worst case, it will traverse the
	 * entire tree below this item.
	 * </p>
	 *
	 * @author David J. Pearce
	 *
	 */
	private static class NotElimination implements RewriteRule {

		@Override
		public SyntacticItem rewrite(SyntacticItem item) {
			if(item.getOpcode() == Opcode.EXPR_not) {
				// Matched not(...)
				Expr child = (Expr) item.getOperand(0);
				switch(child.getOpcode()) {
				case EXPR_not:
					// not(not(x)) => x
					return child.getOperand(0);
				default:
				}
			}
			// Default case, no rewrite applied
			return item;
		}
	}
}
