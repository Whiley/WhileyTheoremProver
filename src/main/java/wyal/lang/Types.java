package wyal.lang;

import java.io.*;
import java.util.*;
import java.math.BigInteger;
import wyautl.util.BigRational;
import wyautl.io.*;
import wyautl.core.*;
import wyrw.core.*;
import wyrw.util.AbstractRewriteRule;
import wyrl.core.*;
import wyrl.util.Runtime;
import wyrl.util.Pair;

public final class Types {
	// term $4<NotT($2<^Type<$4|Atom<NotT($16<^Proton<TupleT(^[$16...])|ArrayT($16)|Quark<AnyT|NullT|VoidT|BoolT|IntT|RealT|StringT|VarT(^string)|NominalT(^string)>>>)|Proton<TupleT(^[$16...])|ArrayT($16)|Quark<AnyT|NullT|VoidT|BoolT|IntT|RealT|StringT|VarT(^string)|NominalT(^string)>>>|OrT(^{$2...})|AndT(^{$2...})|ArrayT($2)|TupleT(^[$2...])|FunctionT(^[$2,$2,$2...])>>)>
	public final static int K_NotT = 0;
	public final static int NotT(Automaton automaton, int r0) {
		return automaton.add(new Automaton.Term(K_NotT, r0));
	}

	private final static class Reduction_0 extends AbstractRewriteRule implements ReductionRule {

		public Reduction_0(Pattern.Term pattern) {
			super(pattern);
			put("name","NotT(AnyT)");
			put("rank",0);
		}

		public final void probe(Automaton automaton, int target, List<Reduction.Activation> activations) {
			int r0 = target;
			Automaton.State s0 = automaton.get(r0);
			if(s0.kind == K_NotT) {
				Automaton.Term t0 = (Automaton.Term) s0;
				int r1 = t0.contents;
				if(Runtime.accepts(type0,automaton,automaton.get(r1), SCHEMA)) {
					int[] state = {r0, r1};
					activations.add(new Reduction.Activation(this,null,state));
				}
			}
		}

		public final int apply(Automaton automaton, int[] state) {
			int nStates = automaton.nStates();
			int r0 = state[0];
			Automaton.Term r2 = VoidT;
			int r3 = automaton.add(r2);
			if(r0 != r3) {
				return automaton.rewrite(r0, r3);
			}
			automaton.resize(nStates);
			return Automaton.K_VOID;
		}

	}
	private final static class Reduction_1 extends AbstractRewriteRule implements ReductionRule {

		public Reduction_1(Pattern.Term pattern) {
			super(pattern);
			put("name","NotT(VoidT)");
			put("rank",0);
		}

		public final void probe(Automaton automaton, int target, List<Reduction.Activation> activations) {
			int r0 = target;
			Automaton.State s0 = automaton.get(r0);
			if(s0.kind == K_NotT) {
				Automaton.Term t0 = (Automaton.Term) s0;
				int r1 = t0.contents;
				if(Runtime.accepts(type1,automaton,automaton.get(r1), SCHEMA)) {
					int[] state = {r0, r1};
					activations.add(new Reduction.Activation(this,null,state));
				}
			}
		}

		public final int apply(Automaton automaton, int[] state) {
			int nStates = automaton.nStates();
			int r0 = state[0];
			Automaton.Term r2 = AnyT;
			int r3 = automaton.add(r2);
			if(r0 != r3) {
				return automaton.rewrite(r0, r3);
			}
			automaton.resize(nStates);
			return Automaton.K_VOID;
		}

	}
	private final static class Reduction_2 extends AbstractRewriteRule implements ReductionRule {

		public Reduction_2(Pattern.Term pattern) {
			super(pattern);
			put("name","NotT(NotT)");
			put("rank",0);
		}

		public final void probe(Automaton automaton, int target, List<Reduction.Activation> activations) {
			int r0 = target;
			Automaton.State s0 = automaton.get(r0);
			if(s0.kind == K_NotT) {
				Automaton.Term t0 = (Automaton.Term) s0;
				int r1 = t0.contents;
				Automaton.State s1 = automaton.get(r1);
				if(s1.kind == K_NotT) {
					Automaton.Term t1 = (Automaton.Term) s1;
					int r2 = t1.contents;
					int[] state = {r0, r1, r2};
					activations.add(new Reduction.Activation(this,null,state));
				}
			}
		}

		public final int apply(Automaton automaton, int[] state) {
			int nStates = automaton.nStates();
			int r0 = state[0];
			int r2 = state[2]; // t
			if(r0 != r2) {
				return automaton.rewrite(r0, r2);
			}
			automaton.resize(nStates);
			return Automaton.K_VOID;
		}

	}
	private final static class Reduction_3 extends AbstractRewriteRule implements ReductionRule {

		public Reduction_3(Pattern.Term pattern) {
			super(pattern);
			put("name","NotT(OrT)");
			put("rank",1);
		}

		public final void probe(Automaton automaton, int target, List<Reduction.Activation> activations) {
			int r0 = target;
			Automaton.State s0 = automaton.get(r0);
			if(s0.kind == K_NotT) {
				Automaton.Term t0 = (Automaton.Term) s0;
				int r1 = t0.contents;
				Automaton.State s1 = automaton.get(r1);
				if(s1.kind == K_OrT) {
					Automaton.Term t1 = (Automaton.Term) s1;
					int r2 = t1.contents;
					Automaton.State s2 = automaton.get(r2);
					Automaton.Collection c2 = (Automaton.Collection) s2;
					int[] state = {r0, r1, r2, 0};
					activations.add(new Reduction.Activation(this,null,state));
				}
			}
		}

		public final int apply(Automaton automaton, int[] state) {
			int nStates = automaton.nStates();
			int r0 = state[0];
			Automaton.Collection c2 = (Automaton.Collection) automaton.get(state[2]);
			int[] c2children = new int[c2.size() - 0];
			for(int s2i=0, s2j=0; s2i != c2.size();++s2i) {
				c2children[s2j++] = c2.get(s2i);
			}
			Automaton.Set r3 = new Automaton.Set(c2children);
			Automaton.List t4 = new Automaton.List();
			for(int i5=0;i5<r3.size();i5++) {
				int r5 = (int) r3.get(i5);
				Automaton.Term r6 = new Automaton.Term(K_NotT, r5);
				int r7 = automaton.add(r6);
				t4.add(r7);
			}
			Automaton.Set r4 = new Automaton.Set(t4.toArray());
			int r8 = automaton.add(r4);
			Automaton.Term r9 = new Automaton.Term(K_AndT, r8);
			int r10 = automaton.add(r9);
			if(r0 != r10) {
				return automaton.rewrite(r0, r10);
			}
			automaton.resize(nStates);
			return Automaton.K_VOID;
		}

	}
	private final static class Reduction_4 extends AbstractRewriteRule implements ReductionRule {

		public Reduction_4(Pattern.Term pattern) {
			super(pattern);
			put("name","NotT(AndT)");
			put("rank",2);
		}

		public final void probe(Automaton automaton, int target, List<Reduction.Activation> activations) {
			int r0 = target;
			Automaton.State s0 = automaton.get(r0);
			if(s0.kind == K_NotT) {
				Automaton.Term t0 = (Automaton.Term) s0;
				int r1 = t0.contents;
				Automaton.State s1 = automaton.get(r1);
				if(s1.kind == K_AndT) {
					Automaton.Term t1 = (Automaton.Term) s1;
					int r2 = t1.contents;
					Automaton.State s2 = automaton.get(r2);
					Automaton.Collection c2 = (Automaton.Collection) s2;
					int[] state = {r0, r1, r2, 0};
					activations.add(new Reduction.Activation(this,null,state));
				}
			}
		}

		public final int apply(Automaton automaton, int[] state) {
			int nStates = automaton.nStates();
			int r0 = state[0];
			Automaton.Collection c2 = (Automaton.Collection) automaton.get(state[2]);
			int[] c2children = new int[c2.size() - 0];
			for(int s2i=0, s2j=0; s2i != c2.size();++s2i) {
				c2children[s2j++] = c2.get(s2i);
			}
			Automaton.Set r3 = new Automaton.Set(c2children);
			Automaton.List t4 = new Automaton.List();
			for(int i5=0;i5<r3.size();i5++) {
				int r5 = (int) r3.get(i5);
				Automaton.Term r6 = new Automaton.Term(K_NotT, r5);
				int r7 = automaton.add(r6);
				t4.add(r7);
			}
			Automaton.Set r4 = new Automaton.Set(t4.toArray());
			int r8 = automaton.add(r4);
			Automaton.Term r9 = new Automaton.Term(K_OrT, r8);
			int r10 = automaton.add(r9);
			if(r0 != r10) {
				return automaton.rewrite(r0, r10);
			}
			automaton.resize(nStates);
			return Automaton.K_VOID;
		}

	}
	// term $7<AndT($5<^{$2<^Type<$7|Atom<NotT($19<^Proton<TupleT(^[$19...])|ArrayT($19)|Quark<AnyT|NullT|VoidT|BoolT|IntT|RealT|StringT|VarT(^string)|NominalT(^string)>>>)|Proton<TupleT(^[$19...])|ArrayT($19)|Quark<AnyT|NullT|VoidT|BoolT|IntT|RealT|StringT|VarT(^string)|NominalT(^string)>>>|NotT($2)|OrT($5)|ArrayT($2)|TupleT(^[$2...])|FunctionT(^[$2,$2,$2...])>>...}>)>
	public final static int K_AndT = 1;
	public final static int AndT(Automaton automaton, int... r0) {
		int r1 = automaton.add(new Automaton.Set(r0));
		return automaton.add(new Automaton.Term(K_AndT, r1));
	}
	public final static int AndT(Automaton automaton, List<Integer> r0) {
		int r1 = automaton.add(new Automaton.Set(r0));
		return automaton.add(new Automaton.Term(K_AndT, r1));
	}

	private final static class Reduction_5 extends AbstractRewriteRule implements ReductionRule {

		public Reduction_5(Pattern.Term pattern) {
			super(pattern);
			put("name","AndT{}");
			put("rank",0);
		}

		public final void probe(Automaton automaton, int target, List<Reduction.Activation> activations) {
			int r0 = target;
			Automaton.State s0 = automaton.get(r0);
			if(s0.kind == K_AndT) {
				Automaton.Term t0 = (Automaton.Term) s0;
				int r1 = t0.contents;
				Automaton.State s1 = automaton.get(r1);
				Automaton.Collection c1 = (Automaton.Collection) s1;
				if(c1.size() == 0) {
					int[] state = {r0, r1};
					activations.add(new Reduction.Activation(this,null,state));
				}
			}
		}

		public final int apply(Automaton automaton, int[] state) {
			int nStates = automaton.nStates();
			int r0 = state[0];
			Automaton.Term r2 = VoidT;
			int r3 = automaton.add(r2);
			if(r0 != r3) {
				return automaton.rewrite(r0, r3);
			}
			automaton.resize(nStates);
			return Automaton.K_VOID;
		}

	}
	private final static class Reduction_6 extends AbstractRewriteRule implements ReductionRule {

		public Reduction_6(Pattern.Term pattern) {
			super(pattern);
			put("name","AndT{Type}");
			put("rank",0);
		}

		public final void probe(Automaton automaton, int target, List<Reduction.Activation> activations) {
			int r0 = target;
			Automaton.State s0 = automaton.get(r0);
			if(s0.kind == K_AndT) {
				Automaton.Term t0 = (Automaton.Term) s0;
				int r1 = t0.contents;
				Automaton.State s1 = automaton.get(r1);
				Automaton.Collection c1 = (Automaton.Collection) s1;
				if(c1.size() == 1) {
					for(int r3=0;r3!=c1.size();++r3) {
						int r2 = c1.get(r3);
						int[] state = {r0, r1, r2, r3};
						activations.add(new Reduction.Activation(this,null,state));
					}
				}
			}
		}

		public final int apply(Automaton automaton, int[] state) {
			int nStates = automaton.nStates();
			int r0 = state[0];
			int r2 = state[2]; // t
			int r3 = state[3];
			if(r0 != r2) {
				return automaton.rewrite(r0, r2);
			}
			automaton.resize(nStates);
			return Automaton.K_VOID;
		}

	}
	private final static class Reduction_7 extends AbstractRewriteRule implements ReductionRule {

		public Reduction_7(Pattern.Term pattern) {
			super(pattern);
			put("name","AndT{AndT,Type...}");
			put("rank",1);
		}

		public final void probe(Automaton automaton, int target, List<Reduction.Activation> activations) {
			int r0 = target;
			Automaton.State s0 = automaton.get(r0);
			if(s0.kind == K_AndT) {
				Automaton.Term t0 = (Automaton.Term) s0;
				int r1 = t0.contents;
				Automaton.State s1 = automaton.get(r1);
				Automaton.Collection c1 = (Automaton.Collection) s1;
				if(c1.size() >= 1) {
					for(int r3=0;r3!=c1.size();++r3) {
						int r2 = c1.get(r3);
						Automaton.State s2 = automaton.get(r2);
						if(s2.kind == K_AndT) {
							Automaton.Term t2 = (Automaton.Term) s2;
							int r4 = t2.contents;
							Automaton.State s4 = automaton.get(r4);
							Automaton.Collection c4 = (Automaton.Collection) s4;
							int[] state = {r0, r1, r2, r3, r4, 0, 0};
							activations.add(new Reduction.Activation(this,null,state));
						}
					}
				}
			}
		}

		public final int apply(Automaton automaton, int[] state) {
			int nStates = automaton.nStates();
			int r0 = state[0];
			int r3 = state[3];
			Automaton.Collection c4 = (Automaton.Collection) automaton.get(state[4]);
			int[] c4children = new int[c4.size() - 0];
			for(int s4i=0, s4j=0; s4i != c4.size();++s4i) {
				c4children[s4j++] = c4.get(s4i);
			}
			Automaton.Set r5 = new Automaton.Set(c4children);
			Automaton.Collection c1 = (Automaton.Collection) automaton.get(state[1]);
			int[] c1children = new int[c1.size() - 1];
			for(int s1i=0, s1j=0; s1i != c1.size();++s1i) {
				if(s1i == r3) { continue; }
				c1children[s1j++] = c1.get(s1i);
			}
			Automaton.Set r6 = new Automaton.Set(c1children);
			Automaton.Set r7 = r5.append(r6); // xs append ys
			int r8 = automaton.add(r7);
			Automaton.Term r9 = new Automaton.Term(K_AndT, r8);
			int r10 = automaton.add(r9);
			if(r0 != r10) {
				return automaton.rewrite(r0, r10);
			}
			automaton.resize(nStates);
			return Automaton.K_VOID;
		}

	}
	private final static class Reduction_8 extends AbstractRewriteRule implements ReductionRule {

		public Reduction_8(Pattern.Term pattern) {
			super(pattern);
			put("name","AndT{OrT,Type...}");
			put("rank",3);
		}

		public final void probe(Automaton automaton, int target, List<Reduction.Activation> activations) {
			int r0 = target;
			Automaton.State s0 = automaton.get(r0);
			if(s0.kind == K_AndT) {
				Automaton.Term t0 = (Automaton.Term) s0;
				int r1 = t0.contents;
				Automaton.State s1 = automaton.get(r1);
				Automaton.Collection c1 = (Automaton.Collection) s1;
				if(c1.size() >= 1) {
					for(int r3=0;r3!=c1.size();++r3) {
						int r2 = c1.get(r3);
						Automaton.State s2 = automaton.get(r2);
						if(s2.kind == K_OrT) {
							Automaton.Term t2 = (Automaton.Term) s2;
							int r4 = t2.contents;
							Automaton.State s4 = automaton.get(r4);
							Automaton.Collection c4 = (Automaton.Collection) s4;
							int[] state = {r0, r1, r2, r3, r4, 0, 0};
							activations.add(new Reduction.Activation(this,null,state));
						}
					}
				}
			}
		}

		public final int apply(Automaton automaton, int[] state) {
			int nStates = automaton.nStates();
			int r0 = state[0];
			int r3 = state[3];
			Automaton.Collection c4 = (Automaton.Collection) automaton.get(state[4]);
			int[] c4children = new int[c4.size() - 0];
			for(int s4i=0, s4j=0; s4i != c4.size();++s4i) {
				c4children[s4j++] = c4.get(s4i);
			}
			Automaton.Set r5 = new Automaton.Set(c4children);
			Automaton.Collection c1 = (Automaton.Collection) automaton.get(state[1]);
			int[] c1children = new int[c1.size() - 1];
			for(int s1i=0, s1j=0; s1i != c1.size();++s1i) {
				if(s1i == r3) { continue; }
				c1children[s1j++] = c1.get(s1i);
			}
			Automaton.Set r6 = new Automaton.Set(c1children);
			Automaton.List t7 = new Automaton.List();
			for(int i8=0;i8<r5.size();i8++) {
				int r8 = (int) r5.get(i8);
				Automaton.Set r9 = r6.appendFront(r8); // x append ys
				int r10 = automaton.add(r9);
				Automaton.Term r11 = new Automaton.Term(K_AndT, r10);
				int r12 = automaton.add(r11);
				t7.add(r12);
			}
			Automaton.Set r7 = new Automaton.Set(t7.toArray());
			int r13 = automaton.add(r7);
			Automaton.Term r14 = new Automaton.Term(K_OrT, r13);
			int r15 = automaton.add(r14);
			if(r0 != r15) {
				return automaton.rewrite(r0, r15);
			}
			automaton.resize(nStates);
			return Automaton.K_VOID;
		}

	}
	// term $7<OrT($5<^{$2<^Type<$7|Atom<NotT($19<^Proton<TupleT(^[$19...])|ArrayT($19)|Quark<AnyT|NullT|VoidT|BoolT|IntT|RealT|StringT|VarT(^string)|NominalT(^string)>>>)|Proton<TupleT(^[$19...])|ArrayT($19)|Quark<AnyT|NullT|VoidT|BoolT|IntT|RealT|StringT|VarT(^string)|NominalT(^string)>>>|NotT($2)|AndT($5)|ArrayT($2)|TupleT(^[$2...])|FunctionT(^[$2,$2,$2...])>>...}>)>
	public final static int K_OrT = 2;
	public final static int OrT(Automaton automaton, int... r0) {
		int r1 = automaton.add(new Automaton.Set(r0));
		return automaton.add(new Automaton.Term(K_OrT, r1));
	}
	public final static int OrT(Automaton automaton, List<Integer> r0) {
		int r1 = automaton.add(new Automaton.Set(r0));
		return automaton.add(new Automaton.Term(K_OrT, r1));
	}

	private final static class Reduction_9 extends AbstractRewriteRule implements ReductionRule {

		public Reduction_9(Pattern.Term pattern) {
			super(pattern);
			put("name","OrT{}");
			put("rank",0);
		}

		public final void probe(Automaton automaton, int target, List<Reduction.Activation> activations) {
			int r0 = target;
			Automaton.State s0 = automaton.get(r0);
			if(s0.kind == K_OrT) {
				Automaton.Term t0 = (Automaton.Term) s0;
				int r1 = t0.contents;
				Automaton.State s1 = automaton.get(r1);
				Automaton.Collection c1 = (Automaton.Collection) s1;
				if(c1.size() == 0) {
					int[] state = {r0, r1};
					activations.add(new Reduction.Activation(this,null,state));
				}
			}
		}

		public final int apply(Automaton automaton, int[] state) {
			int nStates = automaton.nStates();
			int r0 = state[0];
			Automaton.Term r2 = VoidT;
			int r3 = automaton.add(r2);
			if(r0 != r3) {
				return automaton.rewrite(r0, r3);
			}
			automaton.resize(nStates);
			return Automaton.K_VOID;
		}

	}
	private final static class Reduction_10 extends AbstractRewriteRule implements ReductionRule {

		public Reduction_10(Pattern.Term pattern) {
			super(pattern);
			put("name","OrT{Type}");
			put("rank",0);
		}

		public final void probe(Automaton automaton, int target, List<Reduction.Activation> activations) {
			int r0 = target;
			Automaton.State s0 = automaton.get(r0);
			if(s0.kind == K_OrT) {
				Automaton.Term t0 = (Automaton.Term) s0;
				int r1 = t0.contents;
				Automaton.State s1 = automaton.get(r1);
				Automaton.Collection c1 = (Automaton.Collection) s1;
				if(c1.size() == 1) {
					for(int r3=0;r3!=c1.size();++r3) {
						int r2 = c1.get(r3);
						int[] state = {r0, r1, r2, r3};
						activations.add(new Reduction.Activation(this,null,state));
					}
				}
			}
		}

		public final int apply(Automaton automaton, int[] state) {
			int nStates = automaton.nStates();
			int r0 = state[0];
			int r2 = state[2]; // t
			int r3 = state[3];
			if(r0 != r2) {
				return automaton.rewrite(r0, r2);
			}
			automaton.resize(nStates);
			return Automaton.K_VOID;
		}

	}
	private final static class Reduction_11 extends AbstractRewriteRule implements ReductionRule {

		public Reduction_11(Pattern.Term pattern) {
			super(pattern);
			put("name","OrT{OrT,Type...}");
			put("rank",1);
		}

		public final void probe(Automaton automaton, int target, List<Reduction.Activation> activations) {
			int r0 = target;
			Automaton.State s0 = automaton.get(r0);
			if(s0.kind == K_OrT) {
				Automaton.Term t0 = (Automaton.Term) s0;
				int r1 = t0.contents;
				Automaton.State s1 = automaton.get(r1);
				Automaton.Collection c1 = (Automaton.Collection) s1;
				if(c1.size() >= 1) {
					for(int r3=0;r3!=c1.size();++r3) {
						int r2 = c1.get(r3);
						Automaton.State s2 = automaton.get(r2);
						if(s2.kind == K_OrT) {
							Automaton.Term t2 = (Automaton.Term) s2;
							int r4 = t2.contents;
							Automaton.State s4 = automaton.get(r4);
							Automaton.Collection c4 = (Automaton.Collection) s4;
							int[] state = {r0, r1, r2, r3, r4, 0, 0};
							activations.add(new Reduction.Activation(this,null,state));
						}
					}
				}
			}
		}

		public final int apply(Automaton automaton, int[] state) {
			int nStates = automaton.nStates();
			int r0 = state[0];
			int r3 = state[3];
			Automaton.Collection c4 = (Automaton.Collection) automaton.get(state[4]);
			int[] c4children = new int[c4.size() - 0];
			for(int s4i=0, s4j=0; s4i != c4.size();++s4i) {
				c4children[s4j++] = c4.get(s4i);
			}
			Automaton.Set r5 = new Automaton.Set(c4children);
			Automaton.Collection c1 = (Automaton.Collection) automaton.get(state[1]);
			int[] c1children = new int[c1.size() - 1];
			for(int s1i=0, s1j=0; s1i != c1.size();++s1i) {
				if(s1i == r3) { continue; }
				c1children[s1j++] = c1.get(s1i);
			}
			Automaton.Set r6 = new Automaton.Set(c1children);
			Automaton.Set r7 = r5.append(r6); // xs append ys
			int r8 = automaton.add(r7);
			Automaton.Term r9 = new Automaton.Term(K_OrT, r8);
			int r10 = automaton.add(r9);
			if(r0 != r10) {
				return automaton.rewrite(r0, r10);
			}
			automaton.resize(nStates);
			return Automaton.K_VOID;
		}

	}
	// term $7<TupleT(^[$2<^Type<$7|Atom<NotT($19<^Proton<TupleT(^[$19...])|ArrayT($19)|Quark<AnyT|NullT|VoidT|BoolT|IntT|RealT|StringT|VarT(^string)|NominalT(^string)>>>)|Proton<TupleT(^[$19...])|ArrayT($19)|Quark<AnyT|NullT|VoidT|BoolT|IntT|RealT|StringT|VarT(^string)|NominalT(^string)>>>|NotT($2)|OrT(^{$2...})|AndT(^{$2...})|ArrayT($2)|FunctionT(^[$2,$2,$2...])>>...])>
	public final static int K_TupleT = 3;
	public final static int TupleT(Automaton automaton, int... r0) {
		int r1 = automaton.add(new Automaton.List(r0));
		return automaton.add(new Automaton.Term(K_TupleT, r1));
	}
	public final static int TupleT(Automaton automaton, List<Integer> r0) {
		int r1 = automaton.add(new Automaton.List(r0));
		return automaton.add(new Automaton.Term(K_TupleT, r1));
	}

	private final static class Reduction_12 extends AbstractRewriteRule implements ReductionRule {

		public Reduction_12(Pattern.Term pattern) {
			super(pattern);
			put("name","TupleT[Type...]");
			put("rank",0);
		}

		public final void probe(Automaton automaton, int target, List<Reduction.Activation> activations) {
			int r0 = target;
			Automaton.State s0 = automaton.get(r0);
			if(s0.kind == K_TupleT) {
				Automaton.Term t0 = (Automaton.Term) s0;
				int r1 = t0.contents;
				Automaton.State s1 = automaton.get(r1);
				Automaton.List l1 = (Automaton.List) s1;
				Automaton.List r2 = l1;
				Automaton.Term r3 = VoidT;
				int r4 = automaton.add(r3);
				boolean r5 = r2.contains(r4);  // VoidT in ts
				if(r5) { // REQUIRES
					int[] state = {r0, r1, 0};
					activations.add(new Reduction.Activation(this,null,state));
				}
			}
		}

		public final int apply(Automaton automaton, int[] state) {
			int nStates = automaton.nStates();
			int r0 = state[0];
			Automaton.List r2 = ((Automaton.List) automaton.get(state[1])).sublist(0);
			Automaton.Term r3 = VoidT;
			int r4 = automaton.add(r3);
			if(r0 != r4) {
				return automaton.rewrite(r0, r4);
			}
			automaton.resize(nStates);
			return Automaton.K_VOID;
		}

	}
	private final static class Reduction_13 extends AbstractRewriteRule implements ReductionRule {

		public Reduction_13(Pattern.Term pattern) {
			super(pattern);
			put("name","TupleT[]");
			put("rank",0);
		}

		public final void probe(Automaton automaton, int target, List<Reduction.Activation> activations) {
			int r0 = target;
			Automaton.State s0 = automaton.get(r0);
			if(s0.kind == K_TupleT) {
				Automaton.Term t0 = (Automaton.Term) s0;
				int r1 = t0.contents;
				Automaton.State s1 = automaton.get(r1);
				Automaton.List l1 = (Automaton.List) s1;
				Automaton.List r2 = l1;
				Automaton.Int r3 = r2.lengthOf(); // |ts|
				Automaton.Int r4 = new Automaton.Int(0); // 0
				boolean r5 = r3.equals(r4);    // |ts| eq 0
				if(r5) { // REQUIRES
					int[] state = {r0, r1, 0};
					activations.add(new Reduction.Activation(this,null,state));
				}
			}
		}

		public final int apply(Automaton automaton, int[] state) {
			int nStates = automaton.nStates();
			int r0 = state[0];
			Automaton.List r2 = ((Automaton.List) automaton.get(state[1])).sublist(0);
			Automaton.Term r3 = VoidT;
			int r4 = automaton.add(r3);
			if(r0 != r4) {
				return automaton.rewrite(r0, r4);
			}
			automaton.resize(nStates);
			return Automaton.K_VOID;
		}

	}
	private final static class Reduction_14 extends AbstractRewriteRule implements ReductionRule {

		public Reduction_14(Pattern.Term pattern) {
			super(pattern);
			put("name","TupleT[Type]");
			put("rank",0);
		}

		public final void probe(Automaton automaton, int target, List<Reduction.Activation> activations) {
			int r0 = target;
			Automaton.State s0 = automaton.get(r0);
			if(s0.kind == K_TupleT) {
				Automaton.Term t0 = (Automaton.Term) s0;
				int r1 = t0.contents;
				Automaton.State s1 = automaton.get(r1);
				Automaton.List l1 = (Automaton.List) s1;
				if(l1.size() == 1) {
					int r2 = l1.get(0);
					int[] state = {r0, r1, r2};
					activations.add(new Reduction.Activation(this,null,state));
				}
			}
		}

		public final int apply(Automaton automaton, int[] state) {
			int nStates = automaton.nStates();
			int r0 = state[0];
			int r2 = state[2]; // t
			if(r0 != r2) {
				return automaton.rewrite(r0, r2);
			}
			automaton.resize(nStates);
			return Automaton.K_VOID;
		}

	}
	private final static class Reduction_15 extends AbstractRewriteRule implements ReductionRule {

		public Reduction_15(Pattern.Term pattern) {
			super(pattern);
			put("name","AndT{TupleT,TupleT,Type...}");
			put("rank",2);
		}

		public final void probe(Automaton automaton, int target, List<Reduction.Activation> activations) {
			int r0 = target;
			Automaton.State s0 = automaton.get(r0);
			if(s0.kind == K_AndT) {
				Automaton.Term t0 = (Automaton.Term) s0;
				int r1 = t0.contents;
				Automaton.State s1 = automaton.get(r1);
				Automaton.Collection c1 = (Automaton.Collection) s1;
				if(c1.size() >= 2) {
					for(int r3=0;r3!=c1.size();++r3) {
						int r2 = c1.get(r3);
						Automaton.State s2 = automaton.get(r2);
						if(s2.kind == K_TupleT) {
							Automaton.Term t2 = (Automaton.Term) s2;
							int r4 = t2.contents;
							Automaton.State s4 = automaton.get(r4);
							Automaton.List l4 = (Automaton.List) s4;
							for(int r7=0;r7!=c1.size();++r7) {
								if(r7 == r3) { continue; }
								int r6 = c1.get(r7);
								Automaton.State s6 = automaton.get(r6);
								if(s6.kind == K_TupleT) {
									Automaton.Term t6 = (Automaton.Term) s6;
									int r8 = t6.contents;
									Automaton.State s8 = automaton.get(r8);
									Automaton.List l8 = (Automaton.List) s8;
									int[] state = {r0, r1, r2, r3, r4, 0, r6, r7, r8, 0, 0};
									activations.add(new Reduction.Activation(this,null,state));
								}
							}
						}
					}
				}
			}
		}

		public final int apply(Automaton automaton, int[] state) {
			int nStates = automaton.nStates();
			int r0 = state[0];
			int r3 = state[3];
			Automaton.List r5 = ((Automaton.List) automaton.get(state[4])).sublist(0);
			int r7 = state[7];
			Automaton.List r9 = ((Automaton.List) automaton.get(state[8])).sublist(0);
			Automaton.Collection c1 = (Automaton.Collection) automaton.get(state[1]);
			int[] c1children = new int[c1.size() - 2];
			for(int s1i=0, s1j=0; s1i != c1.size();++s1i) {
				if(s1i == r3 || s1i == r7) { continue; }
				c1children[s1j++] = c1.get(s1i);
			}
			Automaton.Set r10 = new Automaton.Set(c1children);
			Automaton.Int r11 = r5.lengthOf(); // |t1s|
			Automaton.Int r12 = r9.lengthOf(); // |t2s|
			boolean r13 = !r11.equals(r12); // |t1s| neq |t2s|
			if(r13) {
				Automaton.Term r14 = VoidT;
				int r15 = automaton.add(r14);
				if(r0 != r15) {
					return automaton.rewrite(r0, r15);
				}
			}
			Automaton.Int r17 = new Automaton.Int(0); // 0
			Automaton.Int r18 = r5.lengthOf(); // |t1s|
			Automaton.List r19 = Runtime.rangeOf(automaton,r17,r18); // 0 range |t1s|
			Automaton.List t16 = new Automaton.List();
			for(int i20=0;i20<r19.size();i20++) {
				Automaton.Int r20 = (Automaton.Int) automaton.get(r19.get(i20));;
				int r21 = r5.indexOf(r20);     // t1s[i]
				int r22 = r9.indexOf(r20);     // t2s[i]
				Automaton.Set r23 = new Automaton.Set(r21, r22); // {t1s[i]t2s[i]}
				int r24 = automaton.add(r23);
				Automaton.Term r25 = new Automaton.Term(K_AndT, r24);
				int r26 = automaton.add(r25);
				t16.add(r26);
			}
			Automaton.List r16 = t16;
			int r27 = automaton.add(r16);
			Automaton.Term r28 = new Automaton.Term(K_TupleT, r27);
			int r29 = automaton.add(r28);
			Automaton.Set r30 = r10.appendFront(r29); // TupleT(r) append ts
			int r31 = automaton.add(r30);
			Automaton.Term r32 = new Automaton.Term(K_AndT, r31);
			int r33 = automaton.add(r32);
			if(r0 != r33) {
				return automaton.rewrite(r0, r33);
			}
			automaton.resize(nStates);
			return Automaton.K_VOID;
		}

	}
	private final static class Reduction_16 extends AbstractRewriteRule implements ReductionRule {

		public Reduction_16(Pattern.Term pattern) {
			super(pattern);
			put("name","AndT{TupleT,NotT(TupleT,Type...}");
			put("rank",2);
		}

		public final void probe(Automaton automaton, int target, List<Reduction.Activation> activations) {
			int r0 = target;
			Automaton.State s0 = automaton.get(r0);
			if(s0.kind == K_AndT) {
				Automaton.Term t0 = (Automaton.Term) s0;
				int r1 = t0.contents;
				Automaton.State s1 = automaton.get(r1);
				Automaton.Collection c1 = (Automaton.Collection) s1;
				if(c1.size() >= 2) {
					for(int r3=0;r3!=c1.size();++r3) {
						int r2 = c1.get(r3);
						Automaton.State s2 = automaton.get(r2);
						if(s2.kind == K_TupleT) {
							Automaton.Term t2 = (Automaton.Term) s2;
							int r4 = t2.contents;
							Automaton.State s4 = automaton.get(r4);
							Automaton.List l4 = (Automaton.List) s4;
							for(int r7=0;r7!=c1.size();++r7) {
								if(r7 == r3) { continue; }
								int r6 = c1.get(r7);
								Automaton.State s6 = automaton.get(r6);
								if(s6.kind == K_NotT) {
									Automaton.Term t6 = (Automaton.Term) s6;
									int r8 = t6.contents;
									Automaton.State s8 = automaton.get(r8);
									if(s8.kind == K_TupleT) {
										Automaton.Term t8 = (Automaton.Term) s8;
										int r9 = t8.contents;
										Automaton.State s9 = automaton.get(r9);
										Automaton.List l9 = (Automaton.List) s9;
										int[] state = {r0, r1, r2, r3, r4, 0, r6, r7, r8, r9, 0, 0};
										activations.add(new Reduction.Activation(this,null,state));
									}
								}
							}
						}
					}
				}
			}
		}

		public final int apply(Automaton automaton, int[] state) {
			int nStates = automaton.nStates();
			int r0 = state[0];
			int r2 = state[2]; // t1
			int r3 = state[3];
			Automaton.List r5 = ((Automaton.List) automaton.get(state[4])).sublist(0);
			int r7 = state[7];
			Automaton.List r10 = ((Automaton.List) automaton.get(state[9])).sublist(0);
			Automaton.Collection c1 = (Automaton.Collection) automaton.get(state[1]);
			int[] c1children = new int[c1.size() - 2];
			for(int s1i=0, s1j=0; s1i != c1.size();++s1i) {
				if(s1i == r3 || s1i == r7) { continue; }
				c1children[s1j++] = c1.get(s1i);
			}
			Automaton.Set r11 = new Automaton.Set(c1children);
			Automaton.Int r12 = r5.lengthOf(); // |t1s|
			Automaton.Int r13 = r10.lengthOf(); // |t2s|
			boolean r14 = !r12.equals(r13); // |t1s| neq |t2s|
			if(r14) {
				Automaton.Set r15 = r11.appendFront(r2); // t1 append ts
				int r16 = automaton.add(r15);
				Automaton.Term r17 = new Automaton.Term(K_AndT, r16);
				int r18 = automaton.add(r17);
				if(r0 != r18) {
					return automaton.rewrite(r0, r18);
				}
			}
			Automaton.Int r19 = r5.lengthOf(); // |t1s|
			Automaton.Int r20 = new Automaton.Int(0); // 0
			boolean r21 = r19.equals(r20); // |t1s| eq 0
			if(r21) {
				Automaton.Term r22 = VoidT;
				int r23 = automaton.add(r22);
				if(r0 != r23) {
					return automaton.rewrite(r0, r23);
				}
			}
			Automaton.Int r25 = new Automaton.Int(0); // 0
			Automaton.Int r26 = r5.lengthOf(); // |t1s|
			Automaton.List r27 = Runtime.rangeOf(automaton,r25,r26); // 0 range |t1s|
			Automaton.List t24 = new Automaton.List();
			for(int i28=0;i28<r27.size();i28++) {
				Automaton.Int r28 = (Automaton.Int) automaton.get(r27.get(i28));;
				int r29 = r5.indexOf(r28);     // t1s[i]
				int r30 = r10.indexOf(r28);    // t2s[i]
				Automaton.Term r31 = new Automaton.Term(K_NotT, r30);
				int r32 = automaton.add(r31);
				Automaton.Set r33 = new Automaton.Set(r29, r32); // {t1s[i]NotT(t2s[i])}
				int r34 = automaton.add(r33);
				Automaton.Term r35 = new Automaton.Term(K_AndT, r34);
				int r36 = automaton.add(r35);
				t24.add(r36);
			}
			Automaton.List r24 = t24;
			int r37 = automaton.add(r24);
			Automaton.Term r38 = new Automaton.Term(K_TupleT, r37);
			int r39 = automaton.add(r38);
			Automaton.Set r40 = r11.appendFront(r39); // TupleT(r) append ts
			int r41 = automaton.add(r40);
			Automaton.Term r42 = new Automaton.Term(K_AndT, r41);
			int r43 = automaton.add(r42);
			if(r0 != r43) {
				return automaton.rewrite(r0, r43);
			}
			automaton.resize(nStates);
			return Automaton.K_VOID;
		}

	}
	private final static class Reduction_17 extends AbstractRewriteRule implements ReductionRule {

		public Reduction_17(Pattern.Term pattern) {
			super(pattern);
			put("name","AndT{TupleT,NotT(ArrayT),Type...}");
			put("rank",2);
		}

		public final void probe(Automaton automaton, int target, List<Reduction.Activation> activations) {
			int r0 = target;
			Automaton.State s0 = automaton.get(r0);
			if(s0.kind == K_AndT) {
				Automaton.Term t0 = (Automaton.Term) s0;
				int r1 = t0.contents;
				Automaton.State s1 = automaton.get(r1);
				Automaton.Collection c1 = (Automaton.Collection) s1;
				if(c1.size() >= 2) {
					for(int r3=0;r3!=c1.size();++r3) {
						int r2 = c1.get(r3);
						Automaton.State s2 = automaton.get(r2);
						if(s2.kind == K_TupleT) {
							Automaton.Term t2 = (Automaton.Term) s2;
							int r4 = t2.contents;
							Automaton.State s4 = automaton.get(r4);
							Automaton.List l4 = (Automaton.List) s4;
							for(int r7=0;r7!=c1.size();++r7) {
								if(r7 == r3) { continue; }
								int r6 = c1.get(r7);
								Automaton.State s6 = automaton.get(r6);
								if(s6.kind == K_NotT) {
									Automaton.Term t6 = (Automaton.Term) s6;
									int r8 = t6.contents;
									Automaton.State s8 = automaton.get(r8);
									if(s8.kind == K_ArrayT) {
										Automaton.Term t8 = (Automaton.Term) s8;
										int r9 = t8.contents;
										int[] state = {r0, r1, r2, r3, r4, 0, r6, r7, r8, r9, 0};
										activations.add(new Reduction.Activation(this,null,state));
									}
								}
							}
						}
					}
				}
			}
		}

		public final int apply(Automaton automaton, int[] state) {
			int nStates = automaton.nStates();
			int r0 = state[0];
			int r2 = state[2]; // t1
			int r3 = state[3];
			int r7 = state[7];
			Automaton.Collection c1 = (Automaton.Collection) automaton.get(state[1]);
			int[] c1children = new int[c1.size() - 2];
			for(int s1i=0, s1j=0; s1i != c1.size();++s1i) {
				if(s1i == r3 || s1i == r7) { continue; }
				c1children[s1j++] = c1.get(s1i);
			}
			Automaton.Set r10 = new Automaton.Set(c1children);
			Automaton.Set r11 = new Automaton.Set(r2); // {t1}
			Automaton.Set r12 = r11.append(r10); // {t1} append ts
			int r13 = automaton.add(r12);
			Automaton.Term r14 = new Automaton.Term(K_AndT, r13);
			int r15 = automaton.add(r14);
			if(r0 != r15) {
				return automaton.rewrite(r0, r15);
			}
			automaton.resize(nStates);
			return Automaton.K_VOID;
		}

	}
	// term $4<ArrayT($2<^Type<$4|Atom<NotT($16<^Proton<TupleT(^[$16...])|ArrayT($16)|Quark<AnyT|NullT|VoidT|BoolT|IntT|RealT|StringT|VarT(^string)|NominalT(^string)>>>)|Proton<TupleT(^[$16...])|ArrayT($16)|Quark<AnyT|NullT|VoidT|BoolT|IntT|RealT|StringT|VarT(^string)|NominalT(^string)>>>|NotT($2)|OrT(^{$2...})|AndT(^{$2...})|TupleT(^[$2...])|FunctionT(^[$2,$2,$2...])>>)>
	public final static int K_ArrayT = 4;
	public final static int ArrayT(Automaton automaton, int r0) {
		return automaton.add(new Automaton.Term(K_ArrayT, r0));
	}

	private final static class Reduction_18 extends AbstractRewriteRule implements ReductionRule {

		public Reduction_18(Pattern.Term pattern) {
			super(pattern);
			put("name","ArrayT(VoidT)");
			put("rank",0);
		}

		public final void probe(Automaton automaton, int target, List<Reduction.Activation> activations) {
			int r0 = target;
			Automaton.State s0 = automaton.get(r0);
			if(s0.kind == K_ArrayT) {
				Automaton.Term t0 = (Automaton.Term) s0;
				int r1 = t0.contents;
				if(Runtime.accepts(type1,automaton,automaton.get(r1), SCHEMA)) {
					int[] state = {r0, r1};
					activations.add(new Reduction.Activation(this,null,state));
				}
			}
		}

		public final int apply(Automaton automaton, int[] state) {
			int nStates = automaton.nStates();
			int r0 = state[0];
			Automaton.Term r2 = VoidT;
			int r3 = automaton.add(r2);
			if(r0 != r3) {
				return automaton.rewrite(r0, r3);
			}
			automaton.resize(nStates);
			return Automaton.K_VOID;
		}

	}
	private final static class Reduction_19 extends AbstractRewriteRule implements ReductionRule {

		public Reduction_19(Pattern.Term pattern) {
			super(pattern);
			put("name","AndT{ArrayT,ArrayT,Type...}");
			put("rank",2);
		}

		public final void probe(Automaton automaton, int target, List<Reduction.Activation> activations) {
			int r0 = target;
			Automaton.State s0 = automaton.get(r0);
			if(s0.kind == K_AndT) {
				Automaton.Term t0 = (Automaton.Term) s0;
				int r1 = t0.contents;
				Automaton.State s1 = automaton.get(r1);
				Automaton.Collection c1 = (Automaton.Collection) s1;
				if(c1.size() >= 2) {
					for(int r3=0;r3!=c1.size();++r3) {
						int r2 = c1.get(r3);
						Automaton.State s2 = automaton.get(r2);
						if(s2.kind == K_ArrayT) {
							Automaton.Term t2 = (Automaton.Term) s2;
							int r4 = t2.contents;
							for(int r6=0;r6!=c1.size();++r6) {
								if(r6 == r3) { continue; }
								int r5 = c1.get(r6);
								Automaton.State s5 = automaton.get(r5);
								if(s5.kind == K_ArrayT) {
									Automaton.Term t5 = (Automaton.Term) s5;
									int r7 = t5.contents;
									int[] state = {r0, r1, r2, r3, r4, r5, r6, r7, 0};
									activations.add(new Reduction.Activation(this,null,state));
								}
							}
						}
					}
				}
			}
		}

		public final int apply(Automaton automaton, int[] state) {
			int nStates = automaton.nStates();
			int r0 = state[0];
			int r3 = state[3];
			int r4 = state[4]; // t1
			int r6 = state[6];
			int r7 = state[7]; // t2
			Automaton.Collection c1 = (Automaton.Collection) automaton.get(state[1]);
			int[] c1children = new int[c1.size() - 2];
			for(int s1i=0, s1j=0; s1i != c1.size();++s1i) {
				if(s1i == r3 || s1i == r6) { continue; }
				c1children[s1j++] = c1.get(s1i);
			}
			Automaton.Set r8 = new Automaton.Set(c1children);
			Automaton.Set r9 = new Automaton.Set(r4, r7); // {t1t2}
			int r10 = automaton.add(r9);
			Automaton.Term r11 = new Automaton.Term(K_AndT, r10);
			int r12 = automaton.add(r11);
			Automaton.Term r13 = new Automaton.Term(K_ArrayT, r12);
			int r14 = automaton.add(r13);
			Automaton.Set r15 = r8.appendFront(r14); // ArrayT(AndT({t1t2})) append ts
			int r16 = automaton.add(r15);
			Automaton.Term r17 = new Automaton.Term(K_AndT, r16);
			int r18 = automaton.add(r17);
			if(r0 != r18) {
				return automaton.rewrite(r0, r18);
			}
			automaton.resize(nStates);
			return Automaton.K_VOID;
		}

	}
	private final static class Reduction_20 extends AbstractRewriteRule implements ReductionRule {

		public Reduction_20(Pattern.Term pattern) {
			super(pattern);
			put("name","AndT{ArrayT,NotT(ArrayT),Type...}");
			put("rank",2);
		}

		public final void probe(Automaton automaton, int target, List<Reduction.Activation> activations) {
			int r0 = target;
			Automaton.State s0 = automaton.get(r0);
			if(s0.kind == K_AndT) {
				Automaton.Term t0 = (Automaton.Term) s0;
				int r1 = t0.contents;
				Automaton.State s1 = automaton.get(r1);
				Automaton.Collection c1 = (Automaton.Collection) s1;
				if(c1.size() >= 2) {
					for(int r3=0;r3!=c1.size();++r3) {
						int r2 = c1.get(r3);
						Automaton.State s2 = automaton.get(r2);
						if(s2.kind == K_ArrayT) {
							Automaton.Term t2 = (Automaton.Term) s2;
							int r4 = t2.contents;
							for(int r6=0;r6!=c1.size();++r6) {
								if(r6 == r3) { continue; }
								int r5 = c1.get(r6);
								Automaton.State s5 = automaton.get(r5);
								if(s5.kind == K_NotT) {
									Automaton.Term t5 = (Automaton.Term) s5;
									int r7 = t5.contents;
									Automaton.State s7 = automaton.get(r7);
									if(s7.kind == K_ArrayT) {
										Automaton.Term t7 = (Automaton.Term) s7;
										int r8 = t7.contents;
										int[] state = {r0, r1, r2, r3, r4, r5, r6, r7, r8, 0};
										activations.add(new Reduction.Activation(this,null,state));
									}
								}
							}
						}
					}
				}
			}
		}

		public final int apply(Automaton automaton, int[] state) {
			int nStates = automaton.nStates();
			int r0 = state[0];
			int r3 = state[3];
			int r4 = state[4]; // t1
			int r6 = state[6];
			int r8 = state[8]; // t2
			Automaton.Collection c1 = (Automaton.Collection) automaton.get(state[1]);
			int[] c1children = new int[c1.size() - 2];
			for(int s1i=0, s1j=0; s1i != c1.size();++s1i) {
				if(s1i == r3 || s1i == r6) { continue; }
				c1children[s1j++] = c1.get(s1i);
			}
			Automaton.Set r9 = new Automaton.Set(c1children);
			Automaton.Term r10 = new Automaton.Term(K_NotT, r8);
			int r11 = automaton.add(r10);
			Automaton.Set r12 = new Automaton.Set(r4, r11); // {t1NotT(t2)}
			int r13 = automaton.add(r12);
			Automaton.Term r14 = new Automaton.Term(K_AndT, r13);
			int r15 = automaton.add(r14);
			Automaton.Term r16 = new Automaton.Term(K_ArrayT, r15);
			int r17 = automaton.add(r16);
			Automaton.Set r18 = r9.appendFront(r17); // ArrayT(AndT({t1NotT(t2)})) append ts
			int r19 = automaton.add(r18);
			Automaton.Term r20 = new Automaton.Term(K_AndT, r19);
			int r21 = automaton.add(r20);
			if(r0 != r21) {
				return automaton.rewrite(r0, r21);
			}
			automaton.resize(nStates);
			return Automaton.K_VOID;
		}

	}
	private final static class Reduction_21 extends AbstractRewriteRule implements ReductionRule {

		public Reduction_21(Pattern.Term pattern) {
			super(pattern);
			put("name","AndT{ArrayT,NotT(Tuple),Type...}");
			put("rank",2);
		}

		public final void probe(Automaton automaton, int target, List<Reduction.Activation> activations) {
			int r0 = target;
			Automaton.State s0 = automaton.get(r0);
			if(s0.kind == K_AndT) {
				Automaton.Term t0 = (Automaton.Term) s0;
				int r1 = t0.contents;
				Automaton.State s1 = automaton.get(r1);
				Automaton.Collection c1 = (Automaton.Collection) s1;
				if(c1.size() >= 2) {
					for(int r3=0;r3!=c1.size();++r3) {
						int r2 = c1.get(r3);
						Automaton.State s2 = automaton.get(r2);
						if(s2.kind == K_ArrayT) {
							Automaton.Term t2 = (Automaton.Term) s2;
							int r4 = t2.contents;
							for(int r6=0;r6!=c1.size();++r6) {
								if(r6 == r3) { continue; }
								int r5 = c1.get(r6);
								Automaton.State s5 = automaton.get(r5);
								if(s5.kind == K_NotT) {
									Automaton.Term t5 = (Automaton.Term) s5;
									int r7 = t5.contents;
									Automaton.State s7 = automaton.get(r7);
									if(s7.kind == K_TupleT) {
										Automaton.Term t7 = (Automaton.Term) s7;
										int r8 = t7.contents;
										Automaton.State s8 = automaton.get(r8);
										Automaton.List l8 = (Automaton.List) s8;
										int[] state = {r0, r1, r2, r3, r4, r5, r6, r7, r8, 0, 0};
										activations.add(new Reduction.Activation(this,null,state));
									}
								}
							}
						}
					}
				}
			}
		}

		public final int apply(Automaton automaton, int[] state) {
			int nStates = automaton.nStates();
			int r0 = state[0];
			int r2 = state[2]; // t1
			int r3 = state[3];
			int r6 = state[6];
			Automaton.Collection c1 = (Automaton.Collection) automaton.get(state[1]);
			int[] c1children = new int[c1.size() - 2];
			for(int s1i=0, s1j=0; s1i != c1.size();++s1i) {
				if(s1i == r3 || s1i == r6) { continue; }
				c1children[s1j++] = c1.get(s1i);
			}
			Automaton.Set r10 = new Automaton.Set(c1children);
			Automaton.Set r11 = new Automaton.Set(r2); // {t1}
			Automaton.Set r12 = r11.append(r10); // {t1} append ts
			int r13 = automaton.add(r12);
			Automaton.Term r14 = new Automaton.Term(K_AndT, r13);
			int r15 = automaton.add(r14);
			if(r0 != r15) {
				return automaton.rewrite(r0, r15);
			}
			automaton.resize(nStates);
			return Automaton.K_VOID;
		}

	}
	private final static class Reduction_22 extends AbstractRewriteRule implements ReductionRule {

		public Reduction_22(Pattern.Term pattern) {
			super(pattern);
			put("name","AndT{ArrayT,Proton,Type...}");
			put("rank",1);
		}

		public final void probe(Automaton automaton, int target, List<Reduction.Activation> activations) {
			int r0 = target;
			Automaton.State s0 = automaton.get(r0);
			if(s0.kind == K_AndT) {
				Automaton.Term t0 = (Automaton.Term) s0;
				int r1 = t0.contents;
				Automaton.State s1 = automaton.get(r1);
				Automaton.Collection c1 = (Automaton.Collection) s1;
				if(c1.size() >= 2) {
					for(int r3=0;r3!=c1.size();++r3) {
						int r2 = c1.get(r3);
						Automaton.State s2 = automaton.get(r2);
						if(s2.kind == K_ArrayT) {
							Automaton.Term t2 = (Automaton.Term) s2;
							int r4 = t2.contents;
							for(int r6=0;r6!=c1.size();++r6) {
								if(r6 == r3) { continue; }
								int r5 = c1.get(r6);
								if(Runtime.accepts(type3,automaton,automaton.get(r5), SCHEMA)) {
									int[] c1children = new int[c1.size() - 2];
									for(int s1i=0, s1j=0; s1i != c1.size();++s1i) {
										if(s1i == r3 || s1i == r6) { continue; }
										c1children[s1j++] = c1.get(s1i);
									}
									Automaton.Set r7 = new Automaton.Set(c1children);
									boolean r8 = Runtime.accepts(type4, automaton, r5, SCHEMA); // p is ^AnyT
									boolean r9 = !r8;              // !p is ^AnyT
									if(r9) { // REQUIRES
										int[] state = {r0, r1, r2, r3, r4, r5, r6, 0};
										activations.add(new Reduction.Activation(this,null,state));
									}
								}
							}
						}
					}
				}
			}
		}

		public final int apply(Automaton automaton, int[] state) {
			int nStates = automaton.nStates();
			int r0 = state[0];
			int r2 = state[2]; // s
			int r3 = state[3];
			int r5 = state[5]; // p
			int r6 = state[6];
			Automaton.Collection c1 = (Automaton.Collection) automaton.get(state[1]);
			int[] c1children = new int[c1.size() - 2];
			for(int s1i=0, s1j=0; s1i != c1.size();++s1i) {
				if(s1i == r3 || s1i == r6) { continue; }
				c1children[s1j++] = c1.get(s1i);
			}
			Automaton.Set r7 = new Automaton.Set(c1children);
			Automaton.Term r8 = VoidT;
			int r9 = automaton.add(r8);
			if(r0 != r9) {
				return automaton.rewrite(r0, r9);
			}
			automaton.resize(nStates);
			return Automaton.K_VOID;
		}

	}
	private final static class Reduction_23 extends AbstractRewriteRule implements ReductionRule {

		public Reduction_23(Pattern.Term pattern) {
			super(pattern);
			put("name","OrT{ArrayT,ArrayT,Type...}");
			put("rank",2);
		}

		public final void probe(Automaton automaton, int target, List<Reduction.Activation> activations) {
			int r0 = target;
			Automaton.State s0 = automaton.get(r0);
			if(s0.kind == K_OrT) {
				Automaton.Term t0 = (Automaton.Term) s0;
				int r1 = t0.contents;
				Automaton.State s1 = automaton.get(r1);
				Automaton.Collection c1 = (Automaton.Collection) s1;
				if(c1.size() >= 2) {
					for(int r3=0;r3!=c1.size();++r3) {
						int r2 = c1.get(r3);
						Automaton.State s2 = automaton.get(r2);
						if(s2.kind == K_ArrayT) {
							Automaton.Term t2 = (Automaton.Term) s2;
							int r4 = t2.contents;
							for(int r6=0;r6!=c1.size();++r6) {
								if(r6 == r3) { continue; }
								int r5 = c1.get(r6);
								Automaton.State s5 = automaton.get(r5);
								if(s5.kind == K_ArrayT) {
									Automaton.Term t5 = (Automaton.Term) s5;
									int r7 = t5.contents;
									int[] c1children = new int[c1.size() - 2];
									for(int s1i=0, s1j=0; s1i != c1.size();++s1i) {
										if(s1i == r3 || s1i == r6) { continue; }
										c1children[s1j++] = c1.get(s1i);
									}
									Automaton.Set r8 = new Automaton.Set(c1children);
									boolean r9 = r4 == r7;         // t1 eq t2
									if(r9) { // REQUIRES
										int[] state = {r0, r1, r2, r3, r4, r5, r6, r7, 0};
										activations.add(new Reduction.Activation(this,null,state));
									}
								}
							}
						}
					}
				}
			}
		}

		public final int apply(Automaton automaton, int[] state) {
			int nStates = automaton.nStates();
			int r0 = state[0];
			int r2 = state[2]; // s1
			int r3 = state[3];
			int r4 = state[4]; // t1
			int r5 = state[5]; // s2
			int r6 = state[6];
			int r7 = state[7]; // t2
			Automaton.Collection c1 = (Automaton.Collection) automaton.get(state[1]);
			int[] c1children = new int[c1.size() - 2];
			for(int s1i=0, s1j=0; s1i != c1.size();++s1i) {
				if(s1i == r3 || s1i == r6) { continue; }
				c1children[s1j++] = c1.get(s1i);
			}
			Automaton.Set r8 = new Automaton.Set(c1children);
			Automaton.Set r9 = new Automaton.Set(r2); // {s1}
			Automaton.Set r10 = r9.append(r8); // {s1} append ts
			int r11 = automaton.add(r10);
			Automaton.Term r12 = new Automaton.Term(K_OrT, r11);
			int r13 = automaton.add(r12);
			if(r0 != r13) {
				return automaton.rewrite(r0, r13);
			}
			automaton.resize(nStates);
			return Automaton.K_VOID;
		}

	}
	// term AnyT
	public final static int K_AnyT = 5;
	public final static Automaton.Term AnyT = new Automaton.Term(K_AnyT);

	// term VoidT
	public final static int K_VoidT = 6;
	public final static Automaton.Term VoidT = new Automaton.Term(K_VoidT);

	// term NullT
	public final static int K_NullT = 7;
	public final static Automaton.Term NullT = new Automaton.Term(K_NullT);

	// term BoolT
	public final static int K_BoolT = 8;
	public final static Automaton.Term BoolT = new Automaton.Term(K_BoolT);

	// term IntT
	public final static int K_IntT = 9;
	public final static Automaton.Term IntT = new Automaton.Term(K_IntT);

	// term RealT
	public final static int K_RealT = 10;
	public final static Automaton.Term RealT = new Automaton.Term(K_RealT);

	// term StringT
	public final static int K_StringT = 11;
	public final static Automaton.Term StringT = new Automaton.Term(K_StringT);

	// term VarT(^string)
	public final static int K_VarT = 12;
	public final static int VarT(Automaton automaton, String r0) {
		int r1 = automaton.add(new Automaton.Strung(r0));
		return automaton.add(new Automaton.Term(K_VarT, r1));
	}

	// term NominalT(^string)
	public final static int K_NominalT = 13;
	public final static int NominalT(Automaton automaton, String r0) {
		int r1 = automaton.add(new Automaton.Strung(r0));
		return automaton.add(new Automaton.Term(K_NominalT, r1));
	}

	private final static class Reduction_24 extends AbstractRewriteRule implements ReductionRule {

		public Reduction_24(Pattern.Term pattern) {
			super(pattern);
			put("name","AndT{VoidT,Type...}");
			put("rank",0);
		}

		public final void probe(Automaton automaton, int target, List<Reduction.Activation> activations) {
			int r0 = target;
			Automaton.State s0 = automaton.get(r0);
			if(s0.kind == K_AndT) {
				Automaton.Term t0 = (Automaton.Term) s0;
				int r1 = t0.contents;
				Automaton.State s1 = automaton.get(r1);
				Automaton.Collection c1 = (Automaton.Collection) s1;
				if(c1.size() >= 1) {
					for(int r3=0;r3!=c1.size();++r3) {
						int r2 = c1.get(r3);
						if(Runtime.accepts(type1,automaton,automaton.get(r2), SCHEMA)) {
							int[] state = {r0, r1, r2, r3, 0};
							activations.add(new Reduction.Activation(this,null,state));
						}
					}
				}
			}
		}

		public final int apply(Automaton automaton, int[] state) {
			int nStates = automaton.nStates();
			int r0 = state[0];
			int r3 = state[3];
			Automaton.Collection c1 = (Automaton.Collection) automaton.get(state[1]);
			int[] c1children = new int[c1.size() - 1];
			for(int s1i=0, s1j=0; s1i != c1.size();++s1i) {
				if(s1i == r3) { continue; }
				c1children[s1j++] = c1.get(s1i);
			}
			Automaton.Set r4 = new Automaton.Set(c1children);
			Automaton.Term r5 = VoidT;
			int r6 = automaton.add(r5);
			if(r0 != r6) {
				return automaton.rewrite(r0, r6);
			}
			automaton.resize(nStates);
			return Automaton.K_VOID;
		}

	}
	private final static class Reduction_25 extends AbstractRewriteRule implements ReductionRule {

		public Reduction_25(Pattern.Term pattern) {
			super(pattern);
			put("name","AndT{AnyT, Type...}");
			put("rank",0);
		}

		public final void probe(Automaton automaton, int target, List<Reduction.Activation> activations) {
			int r0 = target;
			Automaton.State s0 = automaton.get(r0);
			if(s0.kind == K_AndT) {
				Automaton.Term t0 = (Automaton.Term) s0;
				int r1 = t0.contents;
				Automaton.State s1 = automaton.get(r1);
				Automaton.Collection c1 = (Automaton.Collection) s1;
				if(c1.size() >= 1) {
					for(int r3=0;r3!=c1.size();++r3) {
						int r2 = c1.get(r3);
						if(Runtime.accepts(type0,automaton,automaton.get(r2), SCHEMA)) {
							int[] state = {r0, r1, r2, r3, 0};
							activations.add(new Reduction.Activation(this,null,state));
						}
					}
				}
			}
		}

		public final int apply(Automaton automaton, int[] state) {
			int nStates = automaton.nStates();
			int r0 = state[0];
			int r3 = state[3];
			Automaton.Collection c1 = (Automaton.Collection) automaton.get(state[1]);
			int[] c1children = new int[c1.size() - 1];
			for(int s1i=0, s1j=0; s1i != c1.size();++s1i) {
				if(s1i == r3) { continue; }
				c1children[s1j++] = c1.get(s1i);
			}
			Automaton.Set r4 = new Automaton.Set(c1children);
			int r5 = automaton.add(r4);
			Automaton.Term r6 = new Automaton.Term(K_AndT, r5);
			int r7 = automaton.add(r6);
			if(r0 != r7) {
				return automaton.rewrite(r0, r7);
			}
			automaton.resize(nStates);
			return Automaton.K_VOID;
		}

	}
	private final static class Reduction_26 extends AbstractRewriteRule implements ReductionRule {

		public Reduction_26(Pattern.Term pattern) {
			super(pattern);
			put("name","AndT{Quark,Proton,Type...}");
			put("rank",1);
		}

		public final void probe(Automaton automaton, int target, List<Reduction.Activation> activations) {
			int r0 = target;
			Automaton.State s0 = automaton.get(r0);
			if(s0.kind == K_AndT) {
				Automaton.Term t0 = (Automaton.Term) s0;
				int r1 = t0.contents;
				Automaton.State s1 = automaton.get(r1);
				Automaton.Collection c1 = (Automaton.Collection) s1;
				if(c1.size() >= 2) {
					for(int r3=0;r3!=c1.size();++r3) {
						int r2 = c1.get(r3);
						if(Runtime.accepts(type5,automaton,automaton.get(r2), SCHEMA)) {
							for(int r5=0;r5!=c1.size();++r5) {
								if(r5 == r3) { continue; }
								int r4 = c1.get(r5);
								if(Runtime.accepts(type3,automaton,automaton.get(r4), SCHEMA)) {
									int[] c1children = new int[c1.size() - 2];
									for(int s1i=0, s1j=0; s1i != c1.size();++s1i) {
										if(s1i == r3 || s1i == r5) { continue; }
										c1children[s1j++] = c1.get(s1i);
									}
									Automaton.Set r6 = new Automaton.Set(c1children);
									boolean r7 = r2 != r4;         // a1 neq a2
									boolean r8 = false;            // a1 neq a2 && a1 neq AnyT && a2 neq AnyT
									if(r7) {
										Automaton.Term r9 = AnyT;
										Object r10 = (Object) automaton.get(r2);
										boolean r11 = !r10.equals(r9); // a1 neq AnyT
										boolean r12 = false;           // a1 neq AnyT && a2 neq AnyT
										if(r11) {
											Automaton.Term r13 = AnyT;
											Object r14 = (Object) automaton.get(r4);
											boolean r15 = !r14.equals(r13); // a2 neq AnyT
											r12 = r15;
										}
										r8 = r12;
									}
									if(r8) { // REQUIRES
										int[] state = {r0, r1, r2, r3, r4, r5, 0};
										activations.add(new Reduction.Activation(this,null,state));
									}
								}
							}
						}
					}
				}
			}
		}

		public final int apply(Automaton automaton, int[] state) {
			int nStates = automaton.nStates();
			int r0 = state[0];
			int r2 = state[2]; // a1
			int r3 = state[3];
			int r4 = state[4]; // a2
			int r5 = state[5];
			Automaton.Collection c1 = (Automaton.Collection) automaton.get(state[1]);
			int[] c1children = new int[c1.size() - 2];
			for(int s1i=0, s1j=0; s1i != c1.size();++s1i) {
				if(s1i == r3 || s1i == r5) { continue; }
				c1children[s1j++] = c1.get(s1i);
			}
			Automaton.Set r6 = new Automaton.Set(c1children);
			Automaton.Term r7 = VoidT;
			int r8 = automaton.add(r7);
			if(r0 != r8) {
				return automaton.rewrite(r0, r8);
			}
			automaton.resize(nStates);
			return Automaton.K_VOID;
		}

	}
	private final static class Reduction_27 extends AbstractRewriteRule implements ReductionRule {

		public Reduction_27(Pattern.Term pattern) {
			super(pattern);
			put("name","AndT{Quark,NotT(Proton),Type...}");
			put("rank",1);
		}

		public final void probe(Automaton automaton, int target, List<Reduction.Activation> activations) {
			int r0 = target;
			Automaton.State s0 = automaton.get(r0);
			if(s0.kind == K_AndT) {
				Automaton.Term t0 = (Automaton.Term) s0;
				int r1 = t0.contents;
				Automaton.State s1 = automaton.get(r1);
				Automaton.Collection c1 = (Automaton.Collection) s1;
				if(c1.size() >= 2) {
					for(int r3=0;r3!=c1.size();++r3) {
						int r2 = c1.get(r3);
						if(Runtime.accepts(type5,automaton,automaton.get(r2), SCHEMA)) {
							for(int r5=0;r5!=c1.size();++r5) {
								if(r5 == r3) { continue; }
								int r4 = c1.get(r5);
								Automaton.State s4 = automaton.get(r4);
								if(s4.kind == K_NotT) {
									Automaton.Term t4 = (Automaton.Term) s4;
									int r6 = t4.contents;
									if(Runtime.accepts(type3,automaton,automaton.get(r6), SCHEMA)) {
										int[] c1children = new int[c1.size() - 2];
										for(int s1i=0, s1j=0; s1i != c1.size();++s1i) {
											if(s1i == r3 || s1i == r5) { continue; }
											c1children[s1j++] = c1.get(s1i);
										}
										Automaton.Set r7 = new Automaton.Set(c1children);
										boolean r8 = r2 == r6;         // a1 eq a2
										if(r8) { // REQUIRES
											int[] state = {r0, r1, r2, r3, r4, r5, r6, 0};
											activations.add(new Reduction.Activation(this,null,state));
										}
									}
								}
							}
						}
					}
				}
			}
		}

		public final int apply(Automaton automaton, int[] state) {
			int nStates = automaton.nStates();
			int r0 = state[0];
			int r2 = state[2]; // a1
			int r3 = state[3];
			int r5 = state[5];
			int r6 = state[6]; // a2
			Automaton.Collection c1 = (Automaton.Collection) automaton.get(state[1]);
			int[] c1children = new int[c1.size() - 2];
			for(int s1i=0, s1j=0; s1i != c1.size();++s1i) {
				if(s1i == r3 || s1i == r5) { continue; }
				c1children[s1j++] = c1.get(s1i);
			}
			Automaton.Set r7 = new Automaton.Set(c1children);
			Automaton.Term r8 = VoidT;
			int r9 = automaton.add(r8);
			if(r0 != r9) {
				return automaton.rewrite(r0, r9);
			}
			automaton.resize(nStates);
			return Automaton.K_VOID;
		}

	}
	private final static class Reduction_28 extends AbstractRewriteRule implements ReductionRule {

		public Reduction_28(Pattern.Term pattern) {
			super(pattern);
			put("name","AndT{Quark,NotT(Proton),Type...}");
			put("rank",1);
		}

		public final void probe(Automaton automaton, int target, List<Reduction.Activation> activations) {
			int r0 = target;
			Automaton.State s0 = automaton.get(r0);
			if(s0.kind == K_AndT) {
				Automaton.Term t0 = (Automaton.Term) s0;
				int r1 = t0.contents;
				Automaton.State s1 = automaton.get(r1);
				Automaton.Collection c1 = (Automaton.Collection) s1;
				if(c1.size() >= 2) {
					for(int r3=0;r3!=c1.size();++r3) {
						int r2 = c1.get(r3);
						if(Runtime.accepts(type5,automaton,automaton.get(r2), SCHEMA)) {
							for(int r5=0;r5!=c1.size();++r5) {
								if(r5 == r3) { continue; }
								int r4 = c1.get(r5);
								Automaton.State s4 = automaton.get(r4);
								if(s4.kind == K_NotT) {
									Automaton.Term t4 = (Automaton.Term) s4;
									int r6 = t4.contents;
									if(Runtime.accepts(type3,automaton,automaton.get(r6), SCHEMA)) {
										int[] c1children = new int[c1.size() - 2];
										for(int s1i=0, s1j=0; s1i != c1.size();++s1i) {
											if(s1i == r3 || s1i == r5) { continue; }
											c1children[s1j++] = c1.get(s1i);
										}
										Automaton.Set r7 = new Automaton.Set(c1children);
										boolean r8 = r2 != r6;         // a1 neq a2
										boolean r9 = false;            // a1 neq a2 && a2 neq AnyT
										if(r8) {
											Automaton.Term r10 = AnyT;
											Object r11 = (Object) automaton.get(r6);
											boolean r12 = !r11.equals(r10); // a2 neq AnyT
											r9 = r12;
										}
										if(r9) { // REQUIRES
											int[] state = {r0, r1, r2, r3, r4, r5, r6, 0};
											activations.add(new Reduction.Activation(this,null,state));
										}
									}
								}
							}
						}
					}
				}
			}
		}

		public final int apply(Automaton automaton, int[] state) {
			int nStates = automaton.nStates();
			int r0 = state[0];
			int r2 = state[2]; // a1
			int r3 = state[3];
			int r5 = state[5];
			int r6 = state[6]; // a2
			Automaton.Collection c1 = (Automaton.Collection) automaton.get(state[1]);
			int[] c1children = new int[c1.size() - 2];
			for(int s1i=0, s1j=0; s1i != c1.size();++s1i) {
				if(s1i == r3 || s1i == r5) { continue; }
				c1children[s1j++] = c1.get(s1i);
			}
			Automaton.Set r7 = new Automaton.Set(c1children);
			Automaton.Set r8 = r7.appendFront(r2); // a1 append ts
			int r9 = automaton.add(r8);
			Automaton.Term r10 = new Automaton.Term(K_AndT, r9);
			int r11 = automaton.add(r10);
			if(r0 != r11) {
				return automaton.rewrite(r0, r11);
			}
			automaton.resize(nStates);
			return Automaton.K_VOID;
		}

	}
	private final static class Reduction_29 extends AbstractRewriteRule implements ReductionRule {

		public Reduction_29(Pattern.Term pattern) {
			super(pattern);
			put("name","OrT{AnyT,Type...}");
			put("rank",0);
		}

		public final void probe(Automaton automaton, int target, List<Reduction.Activation> activations) {
			int r0 = target;
			Automaton.State s0 = automaton.get(r0);
			if(s0.kind == K_OrT) {
				Automaton.Term t0 = (Automaton.Term) s0;
				int r1 = t0.contents;
				Automaton.State s1 = automaton.get(r1);
				Automaton.Collection c1 = (Automaton.Collection) s1;
				if(c1.size() >= 1) {
					for(int r3=0;r3!=c1.size();++r3) {
						int r2 = c1.get(r3);
						if(Runtime.accepts(type0,automaton,automaton.get(r2), SCHEMA)) {
							int[] state = {r0, r1, r2, r3, 0};
							activations.add(new Reduction.Activation(this,null,state));
						}
					}
				}
			}
		}

		public final int apply(Automaton automaton, int[] state) {
			int nStates = automaton.nStates();
			int r0 = state[0];
			int r3 = state[3];
			Automaton.Collection c1 = (Automaton.Collection) automaton.get(state[1]);
			int[] c1children = new int[c1.size() - 1];
			for(int s1i=0, s1j=0; s1i != c1.size();++s1i) {
				if(s1i == r3) { continue; }
				c1children[s1j++] = c1.get(s1i);
			}
			Automaton.Set r4 = new Automaton.Set(c1children);
			Automaton.Term r5 = AnyT;
			int r6 = automaton.add(r5);
			if(r0 != r6) {
				return automaton.rewrite(r0, r6);
			}
			automaton.resize(nStates);
			return Automaton.K_VOID;
		}

	}
	private final static class Reduction_30 extends AbstractRewriteRule implements ReductionRule {

		public Reduction_30(Pattern.Term pattern) {
			super(pattern);
			put("name","Or{VoidT,Type...}");
			put("rank",0);
		}

		public final void probe(Automaton automaton, int target, List<Reduction.Activation> activations) {
			int r0 = target;
			Automaton.State s0 = automaton.get(r0);
			if(s0.kind == K_OrT) {
				Automaton.Term t0 = (Automaton.Term) s0;
				int r1 = t0.contents;
				Automaton.State s1 = automaton.get(r1);
				Automaton.Collection c1 = (Automaton.Collection) s1;
				if(c1.size() >= 1) {
					for(int r3=0;r3!=c1.size();++r3) {
						int r2 = c1.get(r3);
						if(Runtime.accepts(type1,automaton,automaton.get(r2), SCHEMA)) {
							int[] state = {r0, r1, r2, r3, 0};
							activations.add(new Reduction.Activation(this,null,state));
						}
					}
				}
			}
		}

		public final int apply(Automaton automaton, int[] state) {
			int nStates = automaton.nStates();
			int r0 = state[0];
			int r3 = state[3];
			Automaton.Collection c1 = (Automaton.Collection) automaton.get(state[1]);
			int[] c1children = new int[c1.size() - 1];
			for(int s1i=0, s1j=0; s1i != c1.size();++s1i) {
				if(s1i == r3) { continue; }
				c1children[s1j++] = c1.get(s1i);
			}
			Automaton.Set r4 = new Automaton.Set(c1children);
			int r5 = automaton.add(r4);
			Automaton.Term r6 = new Automaton.Term(K_OrT, r5);
			int r7 = automaton.add(r6);
			if(r0 != r7) {
				return automaton.rewrite(r0, r7);
			}
			automaton.resize(nStates);
			return Automaton.K_VOID;
		}

	}
	// term $8<FunctionT(^[$2<^Type<$8|Atom<NotT($20<^Proton<TupleT(^[$20...])|ArrayT($20)|Quark<AnyT|NullT|VoidT|BoolT|IntT|RealT|StringT|VarT(^string)|NominalT(^string)>>>)|Proton<TupleT(^[$20...])|ArrayT($20)|Quark<AnyT|NullT|VoidT|BoolT|IntT|RealT|StringT|VarT(^string)|NominalT(^string)>>>|NotT($2)|OrT(^{$2...})|AndT(^{$2...})|ArrayT($2)|TupleT(^[$2...])>>,$2,$2...])>
	public final static int K_FunctionT = 14;
	public final static int FunctionT(Automaton automaton, int... r0) {
		int r1 = automaton.add(new Automaton.List(r0));
		return automaton.add(new Automaton.Term(K_FunctionT, r1));
	}
	public final static int FunctionT(Automaton automaton, List<Integer> r0) {
		int r1 = automaton.add(new Automaton.List(r0));
		return automaton.add(new Automaton.Term(K_FunctionT, r1));
	}

	// =========================================================================
	// Schema
	// =========================================================================

	public static final Schema SCHEMA = new Schema(new Schema.Term[]{
		// $4<NotT($2<^Type<$4|Atom<NotT($16<^Proton<TupleT(^[$16...])|ArrayT($16)|Quark<AnyT|NullT|VoidT|BoolT|IntT|RealT|StringT|VarT(^string)|NominalT(^string)>>>)|Proton<TupleT(^[$16...])|ArrayT($16)|Quark<AnyT|NullT|VoidT|BoolT|IntT|RealT|StringT|VarT(^string)|NominalT(^string)>>>|OrT(^{$2...})|AndT(^{$2...})|ArrayT($2)|TupleT(^[$2...])|FunctionT(^[$2,$2,$2...])>>)>
		Schema.Term("NotT",Schema.Or(Schema.Any, Schema.Or(Schema.Term("NotT",Schema.Or(Schema.Term("TupleT",Schema.List(true)), Schema.Term("ArrayT",Schema.Any), Schema.Or(Schema.Term("AnyT"), Schema.Term("NullT"), Schema.Term("VoidT"), Schema.Term("BoolT"), Schema.Term("IntT"), Schema.Term("RealT"), Schema.Term("StringT"), Schema.Term("VarT",Schema.String), Schema.Term("NominalT",Schema.Any)))), Schema.Any), Schema.Term("OrT",Schema.Set(true)), Schema.Term("AndT",Schema.Any), Schema.Term("ArrayT",Schema.Any), Schema.Term("TupleT",Schema.List(true)), Schema.Term("FunctionT",Schema.List(true,Schema.Any,Schema.Any)))),
		// $7<AndT($5<^{$2<^Type<$7|Atom<NotT($19<^Proton<TupleT(^[$19...])|ArrayT($19)|Quark<AnyT|NullT|VoidT|BoolT|IntT|RealT|StringT|VarT(^string)|NominalT(^string)>>>)|Proton<TupleT(^[$19...])|ArrayT($19)|Quark<AnyT|NullT|VoidT|BoolT|IntT|RealT|StringT|VarT(^string)|NominalT(^string)>>>|NotT($2)|OrT($5)|ArrayT($2)|TupleT(^[$2...])|FunctionT(^[$2,$2,$2...])>>...}>)>
		Schema.Term("AndT",Schema.Set(true)),
		// $7<OrT($5<^{$2<^Type<$7|Atom<NotT($19<^Proton<TupleT(^[$19...])|ArrayT($19)|Quark<AnyT|NullT|VoidT|BoolT|IntT|RealT|StringT|VarT(^string)|NominalT(^string)>>>)|Proton<TupleT(^[$19...])|ArrayT($19)|Quark<AnyT|NullT|VoidT|BoolT|IntT|RealT|StringT|VarT(^string)|NominalT(^string)>>>|NotT($2)|AndT($5)|ArrayT($2)|TupleT(^[$2...])|FunctionT(^[$2,$2,$2...])>>...}>)>
		Schema.Term("OrT",Schema.Set(true)),
		// $7<TupleT(^[$2<^Type<$7|Atom<NotT($19<^Proton<TupleT(^[$19...])|ArrayT($19)|Quark<AnyT|NullT|VoidT|BoolT|IntT|RealT|StringT|VarT(^string)|NominalT(^string)>>>)|Proton<TupleT(^[$19...])|ArrayT($19)|Quark<AnyT|NullT|VoidT|BoolT|IntT|RealT|StringT|VarT(^string)|NominalT(^string)>>>|NotT($2)|OrT(^{$2...})|AndT(^{$2...})|ArrayT($2)|FunctionT(^[$2,$2,$2...])>>...])>
		Schema.Term("TupleT",Schema.List(true)),
		// $4<ArrayT($2<^Type<$4|Atom<NotT($16<^Proton<TupleT(^[$16...])|ArrayT($16)|Quark<AnyT|NullT|VoidT|BoolT|IntT|RealT|StringT|VarT(^string)|NominalT(^string)>>>)|Proton<TupleT(^[$16...])|ArrayT($16)|Quark<AnyT|NullT|VoidT|BoolT|IntT|RealT|StringT|VarT(^string)|NominalT(^string)>>>|NotT($2)|OrT(^{$2...})|AndT(^{$2...})|TupleT(^[$2...])|FunctionT(^[$2,$2,$2...])>>)>
		Schema.Term("ArrayT",Schema.Or(Schema.Any, Schema.Or(Schema.Term("NotT",Schema.Or(Schema.Term("TupleT",Schema.List(true)), Schema.Term("ArrayT",Schema.Any), Schema.Or(Schema.Term("AnyT"), Schema.Term("NullT"), Schema.Term("VoidT"), Schema.Term("BoolT"), Schema.Term("IntT"), Schema.Term("RealT"), Schema.Term("StringT"), Schema.Term("VarT",Schema.String), Schema.Term("NominalT",Schema.Any)))), Schema.Any), Schema.Term("NotT",Schema.Any), Schema.Term("OrT",Schema.Set(true)), Schema.Term("AndT",Schema.Any), Schema.Term("TupleT",Schema.List(true)), Schema.Term("FunctionT",Schema.List(true,Schema.Any,Schema.Any)))),
		// AnyT
		Schema.Term("AnyT"),
		// VoidT
		Schema.Term("VoidT"),
		// NullT
		Schema.Term("NullT"),
		// BoolT
		Schema.Term("BoolT"),
		// IntT
		Schema.Term("IntT"),
		// RealT
		Schema.Term("RealT"),
		// StringT
		Schema.Term("StringT"),
		// VarT(^string)
		Schema.Term("VarT",Schema.String),
		// NominalT(^string)
		Schema.Term("NominalT",Schema.String),
		// $8<FunctionT(^[$2<^Type<$8|Atom<NotT($20<^Proton<TupleT(^[$20...])|ArrayT($20)|Quark<AnyT|NullT|VoidT|BoolT|IntT|RealT|StringT|VarT(^string)|NominalT(^string)>>>)|Proton<TupleT(^[$20...])|ArrayT($20)|Quark<AnyT|NullT|VoidT|BoolT|IntT|RealT|StringT|VarT(^string)|NominalT(^string)>>>|NotT($2)|OrT(^{$2...})|AndT(^{$2...})|ArrayT($2)|TupleT(^[$2...])>>,$2,$2...])>
		Schema.Term("FunctionT",Schema.List(true,Schema.Or(Schema.Any, Schema.Or(Schema.Term("NotT",Schema.Or(Schema.Term("TupleT",Schema.List(true)), Schema.Term("ArrayT",Schema.Any), Schema.Or(Schema.Term("AnyT"), Schema.Term("NullT"), Schema.Term("VoidT"), Schema.Term("BoolT"), Schema.Term("IntT"), Schema.Term("RealT"), Schema.Term("StringT"), Schema.Term("VarT",Schema.String), Schema.Term("NominalT",Schema.Any)))), Schema.Any), Schema.Term("NotT",Schema.Any), Schema.Term("OrT",Schema.Set(true)), Schema.Term("AndT",Schema.Any), Schema.Term("ArrayT",Schema.Any), Schema.Term("TupleT",Schema.List(true))),Schema.Any))
	});

	// =========================================================================
	// Types
	// =========================================================================

	// AnyT
	private static Type type0 = Runtime.Type("2G0tLTJCWDggIk2");
	// VoidT
	private static Type type1 = Runtime.Type("2KLxLPZGp3ukmD0E");
	// $11<Type<Atom<NotT($13<^Proton<TupleT(^[$13...])|ArrayT($13)|Quark<AnyT|NullT|VoidT|BoolT|IntT|RealT|StringT|VarT(^string)|NominalT(^string)>>>)|Proton<TupleT(^[$13...])|ArrayT($13)|Quark<AnyT|NullT|VoidT|BoolT|IntT|RealT|StringT|VarT(^string)|NominalT(^string)>>>|NotT(^$11)|OrT(^{^$11...})|AndT(^{^$11...})|ArrayT(^$11)|TupleT(^[^$11...])|FunctionT(^[^$11,^$11,^$11...])>>
	private static Type type2 = Runtime.Type("j53GKTkK5G0GrQhGZIjG6KowZRJGJFiG5KZ4ZRm4LTJG5Kp06Q_G4_WGptqNo_qQiGKRSlQZRgRoRcSVTgWHYcnHhk3OF8rQoxaQeZr7ww3AN4HLthWLYgnLhk4KGKMNmhq7ElHDUd1PYVJPgcq7zw3Ag4nPh_QgWQYsoQhV6G0tLTJCWTgg6KDK6QgGp3xlXUJOpQdG5KIVNkHX0K1xqQgGp3A5gkNFJHiG6KIsNkmY0KHKLNgGp3O5gcOFrJo8MPiS5KIkOkHb0GL4aRJdH5YwOVPkHe0WWIjpLPi45QJCme0e0Ag5G5wxbXGY0alaWbWeGfl5i5YspfGAs5eoo7wcQkmil7u5fwHjW9y5Yonj0A76Ysnj0A96YwYi0AB6YcQkHDD6ewRB1HN6gZSBXiWil7u5Q6tkScHrl78tSkmrGo3");
	// $15<Proton<TupleT(^[^$15...])|ArrayT(^$15)|Quark<AnyT|NullT|VoidT|BoolT|IntT|RealT|StringT|VarT(^string)|NominalT(^string)>>>
	private static Type type3 = Runtime.Type("cG5Jmx5Sjt5KGKMNmh5OJK6RgK5KeZp7xkHDycmEYk2HgZ3O08bRW_6KYgJEgkJB9pJal5DCXDEp1L34ZQtGp3PlmLJtJSgl5KIo4ATG_Kj_5OJC0PgZ5K1xqQgGp3fl1Q3_ZQoGp3ilmQJ8KOWl5KIZ6AuGrJo8MPiS5KIk6AxGZKW86KeZl7zWNkHX0WWIjpLPi45QJCmX0X0AB5G5Rx_PhWrTydNoNgWYl7vwNo1aGZ4");
	// ^AnyT
	private static Type type4 = Runtime.Type("3G0tLTJCWDggY9w3x$");
	// Quark<AnyT|NullT|VoidT|BoolT|IntT|RealT|StringT|VarT(^string)|NominalT(^string)>
	private static Type type5 = Runtime.Type("8GKJp4aRfGJFi_6KIg2AwF_Ipl5QJCWEgw2KLxLPZGp38lXHJ8oQjl5KIk3ACGJHiG6KIw3ANG_J_45QJCWLgg4SIGbRdtqOJCGMgs4GL4aRJdH5YVLPgc5WWIjpLPi45QJC1QdlHQG5xVoHD_4MUhaQQwq7uVMAt4ux");

	// =========================================================================
	// Patterns
	// =========================================================================

	private final static Pattern.Term pattern0 = new Pattern.Term("NotT",
		new Pattern.Leaf(type0),
		null);
	private final static Pattern.Term pattern1 = new Pattern.Term("NotT",
		new Pattern.Leaf(type1),
		null);
	private final static Pattern.Term pattern2 = new Pattern.Term("NotT",
		new Pattern.Term("NotT",
			new Pattern.Leaf(type2),
			"t"),
		null);
	private final static Pattern.Term pattern3 = new Pattern.Term("NotT",
		new Pattern.Term("OrT",
			new Pattern.Set(true, new Pair[]{
				new Pair(new Pattern.Leaf(type2), "es")}),
			null),
		null);
	private final static Pattern.Term pattern4 = new Pattern.Term("NotT",
		new Pattern.Term("AndT",
			new Pattern.Set(true, new Pair[]{
				new Pair(new Pattern.Leaf(type2), "es")}),
			null),
		null);
	private final static Pattern.Term pattern5 = new Pattern.Term("AndT",
		new Pattern.Set(false, new Pair[]{}),
		null);
	private final static Pattern.Term pattern6 = new Pattern.Term("AndT",
		new Pattern.Set(false, new Pair[]{
			new Pair(new Pattern.Leaf(type2), "t")}),
		null);
	private final static Pattern.Term pattern7 = new Pattern.Term("AndT",
		new Pattern.Set(true, new Pair[]{
			new Pair(new Pattern.Term("AndT",
				new Pattern.Set(true, new Pair[]{
					new Pair(new Pattern.Leaf(type2), "xs")}),
				null),null), 
			new Pair(new Pattern.Leaf(type2), "ys")}),
		null);
	private final static Pattern.Term pattern8 = new Pattern.Term("AndT",
		new Pattern.Set(true, new Pair[]{
			new Pair(new Pattern.Term("OrT",
				new Pattern.Set(true, new Pair[]{
					new Pair(new Pattern.Leaf(type2), "xs")}),
				null),null), 
			new Pair(new Pattern.Leaf(type2), "ys")}),
		null);
	private final static Pattern.Term pattern9 = new Pattern.Term("OrT",
		new Pattern.Set(false, new Pair[]{}),
		null);
	private final static Pattern.Term pattern10 = new Pattern.Term("OrT",
		new Pattern.Set(false, new Pair[]{
			new Pair(new Pattern.Leaf(type2), "t")}),
		null);
	private final static Pattern.Term pattern11 = new Pattern.Term("OrT",
		new Pattern.Set(true, new Pair[]{
			new Pair(new Pattern.Term("OrT",
				new Pattern.Set(true, new Pair[]{
					new Pair(new Pattern.Leaf(type2), "xs")}),
				null),null), 
			new Pair(new Pattern.Leaf(type2), "ys")}),
		null);
	private final static Pattern.Term pattern12 = new Pattern.Term("TupleT",
		new Pattern.List(true, new Pair[]{
			new Pair(new Pattern.Leaf(type2), "ts")}),
		null);
	private final static Pattern.Term pattern13 = new Pattern.Term("TupleT",
		new Pattern.List(true, new Pair[]{
			new Pair(new Pattern.Leaf(type2), "ts")}),
		null);
	private final static Pattern.Term pattern14 = new Pattern.Term("TupleT",
		new Pattern.List(false, new Pair[]{
			new Pair(new Pattern.Leaf(type2), "t")}),
		null);
	private final static Pattern.Term pattern15 = new Pattern.Term("AndT",
		new Pattern.Set(true, new Pair[]{
			new Pair(new Pattern.Term("TupleT",
				new Pattern.List(true, new Pair[]{
					new Pair(new Pattern.Leaf(type2), "t1s")}),
				null),null), 
			new Pair(new Pattern.Term("TupleT",
				new Pattern.List(true, new Pair[]{
					new Pair(new Pattern.Leaf(type2), "t2s")}),
				null),null), 
			new Pair(new Pattern.Leaf(type2), "ts")}),
		null);
	private final static Pattern.Term pattern16 = new Pattern.Term("AndT",
		new Pattern.Set(true, new Pair[]{
			new Pair(new Pattern.Term("TupleT",
				new Pattern.List(true, new Pair[]{
					new Pair(new Pattern.Leaf(type2), "t1s")}),
				null), "t1"), 
			new Pair(new Pattern.Term("NotT",
				new Pattern.Term("TupleT",
					new Pattern.List(true, new Pair[]{
						new Pair(new Pattern.Leaf(type2), "t2s")}),
					null),
				null),null), 
			new Pair(new Pattern.Leaf(type2), "ts")}),
		null);
	private final static Pattern.Term pattern17 = new Pattern.Term("AndT",
		new Pattern.Set(true, new Pair[]{
			new Pair(new Pattern.Term("TupleT",
				new Pattern.List(true, new Pair[]{
					new Pair(new Pattern.Leaf(type2),null)}),
				null), "t1"), 
			new Pair(new Pattern.Term("NotT",
				new Pattern.Term("ArrayT",
					new Pattern.Leaf(type2),
					null),
				null),null), 
			new Pair(new Pattern.Leaf(type2), "ts")}),
		null);
	private final static Pattern.Term pattern18 = new Pattern.Term("ArrayT",
		new Pattern.Leaf(type1),
		null);
	private final static Pattern.Term pattern19 = new Pattern.Term("AndT",
		new Pattern.Set(true, new Pair[]{
			new Pair(new Pattern.Term("ArrayT",
				new Pattern.Leaf(type2),
				"t1"),null), 
			new Pair(new Pattern.Term("ArrayT",
				new Pattern.Leaf(type2),
				"t2"),null), 
			new Pair(new Pattern.Leaf(type2), "ts")}),
		null);
	private final static Pattern.Term pattern20 = new Pattern.Term("AndT",
		new Pattern.Set(true, new Pair[]{
			new Pair(new Pattern.Term("ArrayT",
				new Pattern.Leaf(type2),
				"t1"),null), 
			new Pair(new Pattern.Term("NotT",
				new Pattern.Term("ArrayT",
					new Pattern.Leaf(type2),
					"t2"),
				null),null), 
			new Pair(new Pattern.Leaf(type2), "ts")}),
		null);
	private final static Pattern.Term pattern21 = new Pattern.Term("AndT",
		new Pattern.Set(true, new Pair[]{
			new Pair(new Pattern.Term("ArrayT",
				new Pattern.Leaf(type2),
				null), "t1"), 
			new Pair(new Pattern.Term("NotT",
				new Pattern.Term("TupleT",
					new Pattern.List(true, new Pair[]{
						new Pair(new Pattern.Leaf(type2),null)}),
					null),
				null),null), 
			new Pair(new Pattern.Leaf(type2), "ts")}),
		null);
	private final static Pattern.Term pattern22 = new Pattern.Term("AndT",
		new Pattern.Set(true, new Pair[]{
			new Pair(new Pattern.Term("ArrayT",
				new Pattern.Leaf(type2),
				null), "s"), 
			new Pair(new Pattern.Leaf(type3), "p"), 
			new Pair(new Pattern.Leaf(type2), "ts")}),
		null);
	private final static Pattern.Term pattern23 = new Pattern.Term("OrT",
		new Pattern.Set(true, new Pair[]{
			new Pair(new Pattern.Term("ArrayT",
				new Pattern.Leaf(type2),
				"t1"), "s1"), 
			new Pair(new Pattern.Term("ArrayT",
				new Pattern.Leaf(type2),
				"t2"), "s2"), 
			new Pair(new Pattern.Leaf(type2), "ts")}),
		null);
	private final static Pattern.Term pattern24 = new Pattern.Term("AndT",
		new Pattern.Set(true, new Pair[]{
			new Pair(new Pattern.Leaf(type1),null), 
			new Pair(new Pattern.Leaf(type2), "xs")}),
		null);
	private final static Pattern.Term pattern25 = new Pattern.Term("AndT",
		new Pattern.Set(true, new Pair[]{
			new Pair(new Pattern.Leaf(type0),null), 
			new Pair(new Pattern.Leaf(type2), "xs")}),
		null);
	private final static Pattern.Term pattern26 = new Pattern.Term("AndT",
		new Pattern.Set(true, new Pair[]{
			new Pair(new Pattern.Leaf(type5), "a1"), 
			new Pair(new Pattern.Leaf(type3), "a2"), 
			new Pair(new Pattern.Leaf(type2), "ts")}),
		null);
	private final static Pattern.Term pattern27 = new Pattern.Term("AndT",
		new Pattern.Set(true, new Pair[]{
			new Pair(new Pattern.Leaf(type5), "a1"), 
			new Pair(new Pattern.Term("NotT",
				new Pattern.Leaf(type3),
				"a2"),null), 
			new Pair(new Pattern.Leaf(type2), "ts")}),
		null);
	private final static Pattern.Term pattern28 = new Pattern.Term("AndT",
		new Pattern.Set(true, new Pair[]{
			new Pair(new Pattern.Leaf(type5), "a1"), 
			new Pair(new Pattern.Term("NotT",
				new Pattern.Leaf(type3),
				"a2"),null), 
			new Pair(new Pattern.Leaf(type2), "ts")}),
		null);
	private final static Pattern.Term pattern29 = new Pattern.Term("OrT",
		new Pattern.Set(true, new Pair[]{
			new Pair(new Pattern.Leaf(type0),null), 
			new Pair(new Pattern.Leaf(type2), "xs")}),
		null);
	private final static Pattern.Term pattern30 = new Pattern.Term("OrT",
		new Pattern.Set(true, new Pair[]{
			new Pair(new Pattern.Leaf(type1),null), 
			new Pair(new Pattern.Leaf(type2), "xs")}),
		null);
	// =========================================================================
	// rules
	// =========================================================================

	public static final InferenceRule[] inferences = new InferenceRule[]{

	};
	public static final ReductionRule[] reductions = new ReductionRule[]{
		new Reduction_0(pattern0),
		new Reduction_1(pattern1),
		new Reduction_2(pattern2),
		new Reduction_3(pattern3),
		new Reduction_4(pattern4),
		new Reduction_5(pattern5),
		new Reduction_6(pattern6),
		new Reduction_7(pattern7),
		new Reduction_8(pattern8),
		new Reduction_9(pattern9),
		new Reduction_10(pattern10),
		new Reduction_11(pattern11),
		new Reduction_12(pattern12),
		new Reduction_13(pattern13),
		new Reduction_14(pattern14),
		new Reduction_15(pattern15),
		new Reduction_16(pattern16),
		new Reduction_17(pattern17),
		new Reduction_18(pattern18),
		new Reduction_19(pattern19),
		new Reduction_20(pattern20),
		new Reduction_21(pattern21),
		new Reduction_22(pattern22),
		new Reduction_23(pattern23),
		new Reduction_24(pattern24),
		new Reduction_25(pattern25),
		new Reduction_26(pattern26),
		new Reduction_27(pattern27),
		new Reduction_28(pattern28),
		new Reduction_29(pattern29),
		new Reduction_30(pattern30)
	};


	// =========================================================================
	// Main Method
	// =========================================================================

	public static void main(String[] args) throws IOException {
		new wyrl.ConsoleRewriter(SCHEMA,inferences,reductions).readEvaluatePrintLoop();
	}
}
