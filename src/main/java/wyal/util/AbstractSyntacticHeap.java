package wyal.util;

import java.io.PrintWriter;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.IdentityHashMap;
import java.util.List;
import java.util.Map;

import wyal.lang.SyntacticHeap;
import wyal.lang.SyntacticItem;
import wybs.lang.Attribute;

public abstract class AbstractSyntacticHeap implements SyntacticHeap {
	protected final ArrayList<SyntacticItem> syntacticItems = new ArrayList<>();

	@Override
	public int size() {
		return syntacticItems.size();
	}

	@Override
	public SyntacticItem getSyntacticItem(int index) {
		return syntacticItems.get(index);
	}

	@Override
	public int getIndexOf(SyntacticItem item) {
		for (int i = 0; i != syntacticItems.size(); ++i) {
			if (syntacticItems.get(i) == item) {
				return i;
			}
		}
		throw new IllegalArgumentException("invalid syntactic item");
	}

	public <T extends SyntacticItem> List<T> getSyntacticItems(Class<T> kind) {
		ArrayList<T> matches = new ArrayList<>();
		for (int i = 0; i != syntacticItems.size(); ++i) {
			SyntacticItem item = syntacticItems.get(i);
			if (kind.isInstance(item)) {
				matches.add((T) item);
			}
		}
		return matches;
	}

	@Override
	public <T extends SyntacticItem> T allocate(T item) {
		SyntacticHeap parent = item.getParent();
		if (parent == this) {
			// Item already allocated to this heap, hence nothing to do.
		} else if (parent != null) {
			throw new IllegalArgumentException(
					"Cannot allocate item since a descendent is already allocated to another heap");
		} else {
			// Item not allocated to this heap. Therefore, recursively allocate
			// all children ...
			for (int i = 0; i != item.size(); ++i) {
				SyntacticItem child = item.getOperand(i);
				if (child != null) {
					allocate(child);
				}
			}
			// ... and allocate item itself
			int index = syntacticItems.size();
			syntacticItems.add(item);
			item.allocate(this, index);
		}
		// We just return the original item here since, in the abstract case,
		// we're not doing anything fancy. Subclasses may choose to do more,
		// which is why we have this hook here.
		return item;
	}

	public void print(PrintWriter out) {
		String lenStr = Integer.toString(syntacticItems.size());
		for (int i = 0; i != syntacticItems.size(); ++i) {
			SyntacticItem item = syntacticItems.get(i);
			out.print("// ");
			// Right align the string to ensure that all bytecodes are
			// displayed on the same column. This just helps reading them.
			String iStr = Integer.toString(i);
			for (int j = iStr.length(); j < lenStr.length(); ++j) {
				out.print(" ");
			}
			out.print("#" + i + " " + item);
			//
			List<Attribute> attributes = item.attributes();
			if (attributes.size() > 0) {
				out.print(" [");
				for (int j = 0; j != attributes.size(); ++j) {
					if (j != 0) {
						out.print(", ");
					}
					out.print(attributes.get(j));
				}
				out.print("]");
			}

			out.println();
		}
		out.flush();
	}
}
