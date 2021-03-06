// Copyright 2011 The Whiley Project Developers
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
package wytp.proof.io;

import java.io.ByteArrayOutputStream;
import java.io.OutputStream;
import java.io.OutputStreamWriter;
import java.io.PrintWriter;
import java.io.Writer;
import java.util.ArrayList;
import java.util.List;

import wyal.io.WyalFilePrinter;
import wyal.lang.WyalFile;
import wytp.proof.Formula;
import wytp.proof.Proof;

public class ProofPrinter {
	private final PrintWriter out;
	private int width = 120;
	private boolean fullDelta = false;

	public ProofPrinter(OutputStream writer) {
		this(new OutputStreamWriter(writer));
	}

	public ProofPrinter(Writer writer) {
		this.out = new PrintWriter(writer);
	}

	public ProofPrinter(PrintWriter writer) {
		this.out = writer;
	}

	public ProofPrinter setWidth(int width) {
		this.width = width;
		return this;
	}

	public ProofPrinter setShowAll(boolean flag) {
		this.fullDelta = flag;
		return this;
	}

	public void flush() {
		out.flush();
	}

	public void print(Proof p) {
		print(0, p.getState(0));
	}

	private static final char BOX_TOP='\u2500';
	private static final char BOX_BOTTOM='\u2500';
	private static final char BOX_SPLIT='\u2500';
	private static final char BOX_LEFTSIDE='\u2502';
	private static final char BOX_TOPLEFTCORNER='\u250c';
	private static final char BOX_TOPRIGHTCORNER='\u2510';
	private static final char BOX_BOTTOMLEFTCORNER='\u2514';
	private static final char BOX_BOTTOMRIGHTCORNER='\u2518';
	private static final char BOX_SPLITLEFT='\u251c';
	private static final char BOX_SPLITRIGHT='\u2524';

	public void print(int depth, Proof.State step) {
		printBoxContents(depth,step);
		// now print any children
		if(step.numberOfChildren() == 0) {
			// do nothing
		} else if(step.numberOfChildren() == 1) {
			print(depth,step.getChild(0));
		} else {
			printOpenBox(depth);
			for(int i=0;i!=step.numberOfChildren();++i) {
				print(depth+1,step.getChild(i));
				if((i+1) != step.numberOfChildren()) {
					printSplitBox(depth);
				}
			}
			printCloseBox(depth);
		}
	}

	public void printBoxContents(int depth, Proof.State step) {
		String[] lines = toLines(step);
		String title = title(step);
		int lineWidth = width - depth;
		lineWidth = depth == 0 ? lineWidth : lineWidth-1;
		for(int i=0;i!=lines.length;++i) {
			String t;
			if(i == 0) {
				t = title;
			} else {
				t = "";
			}
			tab(depth);
			out.print(pad(lines[i],t,lineWidth));
			if(depth > 0) {
				out.print(BOX_LEFTSIDE);
			}
			out.println();
		}
	}
	public void tab(int indent) {
		if(indent > 0) {
			for (int i = 0; i < (indent-1); ++i) {
				out.print(BOX_LEFTSIDE);
			}
			out.print(BOX_LEFTSIDE);
		}
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
			for(int i=0;i<removals.size();++i) {
				lines[i] = "-" + toLine(removals.get(i));
			}
			for(int i=0;i<additions.size();++i) {
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
		List<Formula> deps = step.getDependencies();
		for(int j=0;j<deps.size();++j) {
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
		pw.print(" " + e.getIndex() + ". ");
		printer.writeExpression(e);
		printer.flush();
		return new String(out.toByteArray());
	}


	private void printOpenBox(int depth) {
		printBoxLine(depth,BOX_TOPLEFTCORNER,BOX_TOP,BOX_TOPRIGHTCORNER);
	}

	private void printCloseBox(int depth) {
		printBoxLine(depth,BOX_BOTTOMLEFTCORNER,BOX_BOTTOM,BOX_BOTTOMRIGHTCORNER);
	}

	private void printSplitBox(int depth) {
		printBoxLine(depth,BOX_SPLITLEFT,BOX_SPLIT,BOX_SPLITRIGHT);
	}

	private void printBoxLine(int depth, char lc, char mc, char rc) {
		tab(depth);
		int boxWidth = this.width - depth;
		out.print(lc);
		for(int i=1;i<(boxWidth-1);i++) {
			out.print(mc);
		}
		if(depth != 0) {
			out.print(BOX_SPLITRIGHT);
		} else {
			out.print(rc);
		}
		out.println();
	}
}
