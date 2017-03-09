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
	private final int width = 80;

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
		print(0, p.getStep(0));
	}

	public void print(int depth, Proof.Step step) {
		tab(depth);
		String[] lines = toLines(step);
		String title = title(step);
		int indent = depth*3;
		for(int i=0;i!=lines.length;++i) {
			String t = i == 0 ? title : "";
			out.println(pad(lines[i],t,width - indent));
		}
		// now print any children
		if(step.numberOfChildren() == 1) {
			print(depth,step.getChild(0));
		} else {
			printLine(width);
			for(int i=0;i!=step.numberOfChildren();++i) {
				print(depth+1,step.getChild(i));
			}
		}
	}

	public void tab(int indent) {
		if(indent > 0) {
			for (int i = 0; i < (indent-1); ++i) {
				out.print("---");
			}
			out.print("-> ");
		}
	}
	private Proof.Step[] expandFrontier(Proof.Step[] steps) {
		ArrayList<Proof.Step> nSteps = new ArrayList<>();
		boolean allLeaf = true;
		for(int i=0;i!=steps.length;++i) {
			Proof.Step step = steps[i];
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
			return new Proof.Step[0];
		} else {
			return nSteps.toArray(new Proof.Step[nSteps.size()]);
		}
	}

	private int calculateColumnWidth(Proof.Step step, int maxWidth) {
		Proof.Step parent = step.getParent();
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

	private String[] toLines(Proof.Step s) {
		List<Formula> is = s.getIntroductions();
		String[] lines = new String[is.size()];
		for(int i=0;i!=lines.length;++i) {
			lines[i] = toLine(is.get(i));
		}
		return lines;
	}

	private String title(Proof.Step step) {
		String title = " (";
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

	private void printLine(int width) {
		for(int i=0;i!=width;++i) {
			out.print("=");
		}
		out.println();
	}
}
