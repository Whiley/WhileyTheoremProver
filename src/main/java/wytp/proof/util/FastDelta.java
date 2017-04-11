package wytp.proof.util;

import java.util.Arrays;
import java.util.BitSet;

import wytp.proof.Formula;
import wytp.proof.Proof;

public class FastDelta implements Proof.Delta {
	public final static Set EMPTY_SET = new Set();
	public final static FastDelta EMPTY_DELTA = new FastDelta();

	private final Set additions;
	private final Set removals;

	public FastDelta() {
		this.additions = EMPTY_SET;
		this.removals = EMPTY_SET;
	}

	public FastDelta(Set additions, Set removals) {
		if(additions == removals) {
			throw new IllegalArgumentException("aliasing of additions and removals not allowed!");
		}
		this.additions = additions;
		this.removals = removals;
	}

	@Override
	public boolean isAddition(Formula truth) {
		return additions.contains(truth);
	}

	@Override
	public boolean isRemoval(Formula truth) {
		return removals.contains(truth);
	}

	@Override
	public Set getAdditions() {
		return additions;
	}

	@Override
	public Set getRemovals() {
		return removals;
	}

	@Override
	public FastDelta add(Formula truth) {
		return new FastDelta(additions.add(truth),removals.remove(truth));
	}

	@Override
	public FastDelta remove(Formula truth) {
		return new FastDelta(additions.remove(truth),removals.add(truth));
	}

	@Override
	public FastDelta apply(Proof.Delta delta) {
		Set nAdditions = additions.remove(delta.getRemovals()).union(delta.getAdditions());
		Set nRemovals = removals.remove(delta.getAdditions()).union(delta.getRemovals());
		return new FastDelta(nAdditions,nRemovals);
	}

	@Override
	public String toString() {
		return additions.toString() + "-" + removals.toString();
	}

	public static class Set implements Proof.Delta.Set {
		private final BitSet bits;
		private final Formula[] items;

		public Set() {
			this.bits = new BitSet();
			this.items = new Formula[]{};
		}

		public Set(Formula f) {
			this.bits = new BitSet();
			this.items = new Formula[]{f};
			this.bits.set(f.getIndex());
		}

		private Set(BitSet bits, Formula[] items) {
			if(items.length != bits.cardinality()) {
				throw new IllegalArgumentException("invariant broken (i)");
			}
			for(int i=0;i!=items.length;++i) {
				if(!bits.get(items[i].getIndex())) {
					throw new IllegalArgumentException("invariant broken (ii)");
				}
			}
			this.bits = bits;
			this.items = items;
		}

		@Override
		public int size() {
			return items.length;
		}

		@Override
		public boolean contains(Formula truth) {
			return bits.get(truth.getIndex());
		}

		@Override
		public Formula get(int ith) {
			return items[ith];
		}

		@Override
		public Set add(Formula truth) {
			int index = truth.getIndex();
			if (bits.get(index)) {
				// Item is already contained in this set, hence this is a
				// no-operation.
				return this;
			} else {
				Formula[] nItems = Arrays.copyOf(items, items.length + 1);
				BitSet nBits = (BitSet) bits.clone();
				nBits.set(index);
				nItems[items.length] = truth;
				return new Set(nBits, nItems);
			}
		}

		@Override
		public Set remove(Formula truth) {
			int index = truth.getIndex();
			if (!bits.get(index)) {
				// Item is not contained in this set, hence this is a
				// no-operation.
				return this;
			} else {
				Formula[] nItems = new Formula[items.length-1];
				BitSet nBits = (BitSet) bits.clone();
				nBits.clear(index);
				int j = 0;
				for(int i=0;i!=items.length;++i) {
					Formula ith = items[i];
					if(ith.getIndex() != index) {
						nItems[j++] = ith;
					}
				}
				return new Set(nBits, nItems);
			}
		}

		@Override
		public Set union(Proof.Delta.Set other) {
			Set result = this;
			for(int i=0;i!=other.size();++i) {
				result = result.add(other.get(i));
			}
			return result;
		}

		@Override
		public Set remove(Proof.Delta.Set other) {
			Set result = this;
			for(int i=0;i!=other.size();++i) {
				result = result.remove(other.get(i));
			}
			return result;
		}

		@Override
		public String toString() {
			String r = "{";
			for(int i=0;i!=items.length;++i) {
				if(i != 0) {
					r += ", ";
				}
				r += items[i];
			}
			return r + "}";
		}
	}

}
