package wyal.io;

import java.io.ByteArrayOutputStream;
import java.io.OutputStream;
import java.io.OutputStreamWriter;
import java.io.PrintWriter;
import java.io.Writer;
import java.util.ArrayList;
import java.util.List;

import wyal.lang.Formula;
import wyal.lang.Proof;
import wyal.lang.WyalFile;

public class ProofPrinter {
	private final PrintWriter out;
	private final int width = 120;
	private final boolean fullDelta = false;

	public ProofPrinter(OutputStream writer) {
		this(new OutputStreamWriter(writer));
	}

	public ProofPrinter(Writer writer) {
		this.out = new PrintWriter(writer);
	}

	public ProofPrinter(PrintWriter writer) {
		this.out = writer;
	}

	public void flush() {
		out.flush();
	}

	public void print(Proof p) {
		print(0, p.getState(0));
	}

	public void print(int depth, Proof.State step) {
		tab(depth);
		String[] lines = toLines(step);
		String title = title(step);
		int indent = depth*3;
		for(int i=0;i!=lines.length;++i) {
			String t;
			if(i == 0) {
				t = title;
			} else {
				out.println();
				tab(depth);
				t = "";
			}
			out.print(pad(lines[i],t,width - indent));
		}
		out.println();
		// now print any children
		if(step.numberOfChildren() == 0) {
			tab(depth);
			out.println("_|_");
			tab(depth);
		} else if(step.numberOfChildren() == 1) {
			//tab(depth);
			print(depth,step.getChild(0));
		} else {
			indent += 3;
			tab(depth+1);
			printLine(width-indent,'>');
			for(int i=0;i!=step.numberOfChildren();++i) {
				print(depth+1,step.getChild(i));
				if((i+1) != step.numberOfChildren()) {
					printLine(width-indent,'=');
				}
			}
			printLine(width-indent,'<');
		}
	}

	public void tab(int indent) {
		if(indent > 0) {
			for (int i = 0; i < (indent-1); ++i) {
				out.print(" | ");
			}
			out.print(" | ");
		}
	}
	private Proof.State[] expandFrontier(Proof.State[] steps) {
		ArrayList<Proof.State> nSteps = new ArrayList<>();
		boolean allLeaf = true;
		for(int i=0;i!=steps.length;++i) {
			Proof.State step = steps[i];
			if(step.numberOfChildren() == 0) {
				nSteps.add(step);
			} else {
				for(int j=0;j!=step.numberOfChildren();++j) {
					nSteps.add(step.getChild(j));
				}
				allLeaf = false;
			}
		}
		if(allLeaf) {
			return new Proof.State[0];
		} else {
			return nSteps.toArray(new Proof.State[nSteps.size()]);
		}
	}

	private int calculateColumnWidth(Proof.State step, int maxWidth) {
		Proof.State parent = step.getParent();
		if(parent == null) {
			return maxWidth;
		} else {
			int parentWidth = calculateColumnWidth(parent,maxWidth);
			return parentWidth / parent.numberOfChildren();
		}
	}

	private int maxDepth(String[][] lines) {
		int max = 0;
		for(int i=0;i!=lines.length;++i) {
			max = Math.max(lines[i].length, max);
		}
		return max;
	}

	private String pad(String left, String right, int width) {
		if(width <= 0) {
			return "";
		} else {
			if(right.length() > width) {
				right = right.substring(0, width);
			}
			width -= right.length();
			if(left.length() > width) {
				left = left.substring(0, width);
			} else {
				while(left.length() < width) {
					left = left + " ";
				}
			}
			return left + right;
		}
	}

	private String[] toLines(Proof.State s) {
		Proof.Delta delta = s.getDelta();
		Proof.Delta.Set additions = delta.getAdditions();
		Proof.Delta.Set removals = delta.getRemovals();
		if(fullDelta) {
			// Full delta (usually for debugging)
			String[] lines = new String[additions.size()+removals.size()];
			for(int i=0;i!=removals.size();++i) {
				lines[i] = "-" + toLine(removals.get(i));
			}
			for(int i=0;i!=additions.size();++i) {
				lines[i+removals.size()] = "+" + toLine(additions.get(i));
			}
			return lines;
		} else {
			// Half delta
			String[] lines = new String[additions.size()];
			for(int i=0;i!=lines.length;++i) {
				lines[i] = toLine(additions.get(i));
			}
			return lines;
		}
	}

	private String title(Proof.State step) {
		String title = " (";
		if(step.getRule() != null) {
			title += step.getRule().getName();
			title += " ";
		}
		List<WyalFile.Expr> deps = step.getDependencies();
		for(int j=0;j!=deps.size();++j) {
			if(j != 0) {
				title += ",";
			}
			title = title + deps.get(j).getIndex();
		}
		return title + ") ";
	}

	private String toLine(WyalFile.Expr e) {
		ByteArrayOutputStream out = new ByteArrayOutputStream();
		PrintWriter pw = new PrintWriter(out);
		WyalFilePrinter printer = new WyalFilePrinter(pw);
		pw.print(e.getIndex() + ". ");
		printer.writeExpression(e);
		printer.flush();
		return new String(out.toByteArray());
	}

	private void printLine(int width, char c) {
		for(int i=0;i!=width;i++) {
			out.print(c);
		}
		out.println();
	}
}
