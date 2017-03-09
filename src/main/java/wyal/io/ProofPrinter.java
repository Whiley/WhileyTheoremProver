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
		print(p.getStep(0));
	}

	public void print(Proof.Step...steps) {
		printLine(width);
		int colwidth = width / steps.length;
		String[][] lines = new String[steps.length][];
		for(int i=0;i!=steps.length;++i) {
			Proof.Step step = steps[i];
			lines[i] = toLines(step);
		}
		int depth = maxDepth(lines);
		for(int i=0;i!=depth;++i) {
			for(int j=0;j!=steps.length;++j) {
				String title = (i == 0) ? title(steps[j]) : "";
				String line;
				if(i < lines[j].length) {
					line = lines[j][i];
				} else {
					line = "";
				}
				line = pad(line,title,colwidth-1);
				out.print(line);
				out.print("|");
			}
			out.println();
		}
		// now print any children
		steps = expandFrontier(steps);
		if(steps.length > 0) {
			print(steps);
		}
	}

	private Proof.Step[] expandFrontier(Proof.Step[] steps) {
		ArrayList<Proof.Step> nSteps = new ArrayList<>();
		for(int i=0;i!=steps.length;++i) {
			Proof.Step step = steps[i];
			for(int j=0;j!=step.numberOfChildren();++j) {
				nSteps.add(step.getChild(j));
			}
		}
		return nSteps.toArray(new Proof.Step[nSteps.size()]);
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
