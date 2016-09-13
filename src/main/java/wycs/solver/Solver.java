package wycs.solver;

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

public final class Solver {
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

	// term Null
	public final static int K_Null = 15;
	public final static Automaton.Term Null = new Automaton.Term(K_Null);

	// term True
	public final static int K_True = 16;
	public final static Automaton.Term True = new Automaton.Term(K_True);

	// term False
	public final static int K_False = 17;
	public final static Automaton.Term False = new Automaton.Term(K_False);

	// term Num(^real)
	public final static int K_Num = 18;
	public final static int Num(Automaton automaton, long r0) {
		int r1 = automaton.add(new Automaton.Real(r0));
		return automaton.add(new Automaton.Term(K_Num, r1));
	}
	public final static int Num(Automaton automaton, BigRational r0) {
		int r1 = automaton.add(new Automaton.Real(r0));
		return automaton.add(new Automaton.Term(K_Num, r1));
	}

	// term Var(^string)
	public final static int K_Var = 19;
	public final static int Var(Automaton automaton, String r0) {
		int r1 = automaton.add(new Automaton.Strung(r0));
		return automaton.add(new Automaton.Term(K_Var, r1));
	}

	// term $7<Tuple($5<^[$2<^Expr<$7|$49<Value<Null|Tuple(^[^$49...])|Bool<True|False>|Num(^real)|String(^string)|Array(^[^$49...])|ArrayGen(^[^$49,^$49])>>|$86<BExpr<Bool<True|False>|VExpr<Var(^string)|Fn(^[^string,$2...])|Load(^[$2,^int])|LengthOf($2)|IndexOf(^[$2,$2])>|And(^{^$86...})|Or(^{^$86...})|Not(^$86)|Equals(^[$132<^Type<Atom<NotT($155<^Proton<TupleT(^[$155...])|ArrayT($155)|Quark<AnyT|NullT|VoidT|BoolT|IntT|RealT|StringT|VarT(^string)|NominalT(^string)>>>)|Proton<TupleT(^[$155...])|ArrayT($155)|Quark<AnyT|NullT|VoidT|BoolT|IntT|RealT|StringT|VarT(^string)|NominalT(^string)>>>|NotT($132)|OrT(^{$132...})|AndT(^{$132...})|ArrayT($132)|TupleT(^[$132...])|FunctionT(^[$132,$132,$132...])>>,^{|$2,$2|}[$2,$2]])|Inequality(^[^AType<IntT|RealT>,$229<^AExpr<Num(^real)|VExpr<Var(^string)|Fn(^[^string,$2...])|Load(^[$2,^int])|LengthOf($2)|IndexOf(^[$2,$2])>|Sum(^[^real,^{|$229...|}[$229...]])|Mul(^[^real,^{|$229...|}[$229...]])|Div(^[$229,$229])>>])|Equation(^[^AType<IntT|RealT>,$229])|ForAll(^[^{^[^Var(^string),$132]...},^$86])|Exists(^[^{^[^Var(^string),$132]...},^$86])>>|AExpr<Num(^real)|VExpr<Var(^string)|Fn(^[^string,$2...])|Load(^[$2,^int])|LengthOf($2)|IndexOf(^[$2,$2])>|Sum(^[^real,^{|$229...|}[$229...]])|Mul(^[^real,^{|$229...|}[$229...]])|Div(^[$229,$229])>|SExpr<VExpr<Var(^string)|Fn(^[^string,$2...])|Load(^[$2,^int])|LengthOf($2)|IndexOf(^[$2,$2])>|Array($5)|ArrayGen(^[$2,$2])>>>...]>)>
	public final static int K_Tuple = 20;
	public final static int Tuple(Automaton automaton, int... r0) {
		int r1 = automaton.add(new Automaton.List(r0));
		return automaton.add(new Automaton.Term(K_Tuple, r1));
	}
	public final static int Tuple(Automaton automaton, List<Integer> r0) {
		int r1 = automaton.add(new Automaton.List(r0));
		return automaton.add(new Automaton.Term(K_Tuple, r1));
	}

	// term $9<Load(^[$2<^Expr<$52<Value<Null|Tuple(^[^$52...])|Bool<True|False>|Num(^real)|String(^string)|Array(^[^$52...])|ArrayGen(^[^$52,^$52])>>|Tuple(^[$2...])|$94<BExpr<Bool<True|False>|VExpr<$9|Var(^string)|Fn(^[^string,$2...])|LengthOf($2)|IndexOf(^[$2,$2])>|And(^{^$94...})|Or(^{^$94...})|Not(^$94)|Equals(^[$132<^Type<Atom<NotT($155<^Proton<TupleT(^[$155...])|ArrayT($155)|Quark<AnyT|NullT|VoidT|BoolT|IntT|RealT|StringT|VarT(^string)|NominalT(^string)>>>)|Proton<TupleT(^[$155...])|ArrayT($155)|Quark<AnyT|NullT|VoidT|BoolT|IntT|RealT|StringT|VarT(^string)|NominalT(^string)>>>|NotT($132)|OrT(^{$132...})|AndT(^{$132...})|ArrayT($132)|TupleT(^[$132...])|FunctionT(^[$132,$132,$132...])>>,^{|$2,$2|}[$2,$2]])|Inequality(^[^AType<IntT|RealT>,$229<^AExpr<Num(^real)|VExpr<$9|Var(^string)|Fn(^[^string,$2...])|LengthOf($2)|IndexOf(^[$2,$2])>|Sum(^[^real,^{|$229...|}[$229...]])|Mul(^[^real,^{|$229...|}[$229...]])|Div(^[$229,$229])>>])|Equation(^[^AType<IntT|RealT>,$229])|ForAll(^[^{^[^Var(^string),$132]...},^$94])|Exists(^[^{^[^Var(^string),$132]...},^$94])>>|AExpr<Num(^real)|VExpr<$9|Var(^string)|Fn(^[^string,$2...])|LengthOf($2)|IndexOf(^[$2,$2])>|Sum(^[^real,^{|$229...|}[$229...]])|Mul(^[^real,^{|$229...|}[$229...]])|Div(^[$229,$229])>|SExpr<VExpr<$9|Var(^string)|Fn(^[^string,$2...])|LengthOf($2)|IndexOf(^[$2,$2])>|Array(^[$2...])|ArrayGen(^[$2,$2])>>>,^int])>
	public final static int K_Load = 21;
	public final static int Load(Automaton automaton, int... r0) {
		int r1 = automaton.add(new Automaton.List(r0));
		return automaton.add(new Automaton.Term(K_Load, r1));
	}
	public final static int Load(Automaton automaton, List<Integer> r0) {
		int r1 = automaton.add(new Automaton.List(r0));
		return automaton.add(new Automaton.Term(K_Load, r1));
	}

	private final static class Reduction_31 extends AbstractRewriteRule implements ReductionRule {

		public Reduction_31(Pattern.Term pattern) {
			super(pattern);
			put("name","Load[Tuple[Expr...],int]");
			put("rank",1);
		}

		public final void probe(Automaton automaton, int target, List<Reduction.Activation> activations) {
			int r0 = target;
			Automaton.State s0 = automaton.get(r0);
			if(s0.kind == K_Load) {
				Automaton.Term t0 = (Automaton.Term) s0;
				int r1 = t0.contents;
				Automaton.State s1 = automaton.get(r1);
				Automaton.List l1 = (Automaton.List) s1;
				int r2 = l1.get(0);
				Automaton.State s2 = automaton.get(r2);
				if(s2.kind == K_Tuple) {
					Automaton.Term t2 = (Automaton.Term) s2;
					int r3 = t2.contents;
					Automaton.State s3 = automaton.get(r3);
					Automaton.List l3 = (Automaton.List) s3;
					int r5 = l1.get(1);
					Automaton.List r4 = l3;
					Automaton.Int r6 = new Automaton.Int(0); // 0
					Automaton.Int r7 = (Automaton.Int) automaton.get(r5);
					boolean r8 = r7.compareTo(r6)>=0; // idx ge 0
					boolean r9 = false;            // idx ge 0 && idx lt |ls|
					if(r8) {
						Automaton.Int r10 = r4.lengthOf(); // |ls|
						Automaton.Int r11 = (Automaton.Int) automaton.get(r5);
						boolean r12 = r11.compareTo(r10)<0; // idx lt |ls|
						r9 = r12;
					}
					if(r9) { // REQUIRES
						int[] state = {r0, r1, r2, r3, 0, r5};
						activations.add(new Reduction.Activation(this,null,state));
					}
				}
			}
		}

		public final int apply(Automaton automaton, int[] state) {
			int nStates = automaton.nStates();
			int r0 = state[0];
			Automaton.List r4 = ((Automaton.List) automaton.get(state[3])).sublist(0);
			int r5 = state[5]; // idx
			Automaton.Int r6 = (Automaton.Int) automaton.get(r5);
			int r7 = r4.indexOf(r6);       // ls[idx]
			if(r0 != r7) {
				return automaton.rewrite(r0, r7);
			}
			automaton.resize(nStates);
			return Automaton.K_VOID;
		}

	}
	// term $4<LengthOf($2<^Expr<$47<Value<Null|Tuple(^[^$47...])|Bool<True|False>|Num(^real)|String(^string)|Array(^[^$47...])|ArrayGen(^[^$47,^$47])>>|Tuple(^[$2...])|$89<BExpr<Bool<True|False>|VExpr<$4|Var(^string)|Fn(^[^string,$2...])|Load(^[$2,^int])|IndexOf(^[$2,$2])>|And(^{^$89...})|Or(^{^$89...})|Not(^$89)|Equals(^[$132<^Type<Atom<NotT($155<^Proton<TupleT(^[$155...])|ArrayT($155)|Quark<AnyT|NullT|VoidT|BoolT|IntT|RealT|StringT|VarT(^string)|NominalT(^string)>>>)|Proton<TupleT(^[$155...])|ArrayT($155)|Quark<AnyT|NullT|VoidT|BoolT|IntT|RealT|StringT|VarT(^string)|NominalT(^string)>>>|NotT($132)|OrT(^{$132...})|AndT(^{$132...})|ArrayT($132)|TupleT(^[$132...])|FunctionT(^[$132,$132,$132...])>>,^{|$2,$2|}[$2,$2]])|Inequality(^[^AType<IntT|RealT>,$229<^AExpr<Num(^real)|VExpr<$4|Var(^string)|Fn(^[^string,$2...])|Load(^[$2,^int])|IndexOf(^[$2,$2])>|Sum(^[^real,^{|$229...|}[$229...]])|Mul(^[^real,^{|$229...|}[$229...]])|Div(^[$229,$229])>>])|Equation(^[^AType<IntT|RealT>,$229])|ForAll(^[^{^[^Var(^string),$132]...},^$89])|Exists(^[^{^[^Var(^string),$132]...},^$89])>>|AExpr<Num(^real)|VExpr<$4|Var(^string)|Fn(^[^string,$2...])|Load(^[$2,^int])|IndexOf(^[$2,$2])>|Sum(^[^real,^{|$229...|}[$229...]])|Mul(^[^real,^{|$229...|}[$229...]])|Div(^[$229,$229])>|SExpr<VExpr<$4|Var(^string)|Fn(^[^string,$2...])|Load(^[$2,^int])|IndexOf(^[$2,$2])>|Array(^[$2...])|ArrayGen(^[$2,$2])>>>)>
	public final static int K_LengthOf = 22;
	public final static int LengthOf(Automaton automaton, int r0) {
		return automaton.add(new Automaton.Term(K_LengthOf, r0));
	}

	private final static class Reduction_32 extends AbstractRewriteRule implements ReductionRule {

		public Reduction_32(Pattern.Term pattern) {
			super(pattern);
			put("name","LengthOf(Tuple[Expr...])");
			put("rank",0);
		}

		public final void probe(Automaton automaton, int target, List<Reduction.Activation> activations) {
			int r0 = target;
			Automaton.State s0 = automaton.get(r0);
			if(s0.kind == K_LengthOf) {
				Automaton.Term t0 = (Automaton.Term) s0;
				int r1 = t0.contents;
				Automaton.State s1 = automaton.get(r1);
				if(s1.kind == K_Tuple) {
					Automaton.Term t1 = (Automaton.Term) s1;
					int r2 = t1.contents;
					Automaton.State s2 = automaton.get(r2);
					Automaton.List l2 = (Automaton.List) s2;
					int[] state = {r0, r1, r2, 0};
					activations.add(new Reduction.Activation(this,null,state));
				}
			}
		}

		public final int apply(Automaton automaton, int[] state) {
			int nStates = automaton.nStates();
			int r0 = state[0];
			Automaton.List r3 = ((Automaton.List) automaton.get(state[2])).sublist(0);
			Automaton.Int r4 = r3.lengthOf(); // |xs|
			Automaton.Real r5 = new Automaton.Real(r4.value);
			int r6 = automaton.add(r5);
			Automaton.Term r7 = new Automaton.Term(K_Num, r6);
			int r8 = automaton.add(r7);
			if(r0 != r8) {
				return automaton.rewrite(r0, r8);
			}
			automaton.resize(nStates);
			return Automaton.K_VOID;
		}

	}
	private final static class Reduction_33 extends AbstractRewriteRule implements ReductionRule {

		public Reduction_33(Pattern.Term pattern) {
			super(pattern);
			put("name","EqualsTuple[Tuple,Tuple]");
			put("rank",2);
		}

		public final void probe(Automaton automaton, int target, List<Reduction.Activation> activations) {
			int r0 = target;
			Automaton.State s0 = automaton.get(r0);
			if(s0.kind == K_Equals) {
				Automaton.Term t0 = (Automaton.Term) s0;
				int r1 = t0.contents;
				Automaton.State s1 = automaton.get(r1);
				Automaton.List l1 = (Automaton.List) s1;
				int r2 = l1.get(0);
				Automaton.State s2 = automaton.get(r2);
				if(s2.kind == K_TupleT) {
					Automaton.Term t2 = (Automaton.Term) s2;
					int r3 = t2.contents;
					Automaton.State s3 = automaton.get(r3);
					Automaton.List l3 = (Automaton.List) s3;
					int r5 = l1.get(1);
					Automaton.State s5 = automaton.get(r5);
					Automaton.Collection c5 = (Automaton.Collection) s5;
					for(int r7=0;r7!=c5.size();++r7) {
						int r6 = c5.get(r7);
						Automaton.State s6 = automaton.get(r6);
						if(s6.kind == K_Tuple) {
							Automaton.Term t6 = (Automaton.Term) s6;
							int r8 = t6.contents;
							Automaton.State s8 = automaton.get(r8);
							Automaton.List l8 = (Automaton.List) s8;
							for(int r11=0;r11!=c5.size();++r11) {
								if(r11 == r7) { continue; }
								int r10 = c5.get(r11);
								Automaton.State s10 = automaton.get(r10);
								if(s10.kind == K_Tuple) {
									Automaton.Term t10 = (Automaton.Term) s10;
									int r12 = t10.contents;
									Automaton.State s12 = automaton.get(r12);
									Automaton.List l12 = (Automaton.List) s12;
									int[] state = {r0, r1, r2, r3, 0, r5, r6, r7, r8, 0, r10, r11, r12, 0};
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
			Automaton.List r4 = ((Automaton.List) automaton.get(state[3])).sublist(0);
			int r7 = state[7];
			Automaton.List r9 = ((Automaton.List) automaton.get(state[8])).sublist(0);
			int r11 = state[11];
			Automaton.List r13 = ((Automaton.List) automaton.get(state[12])).sublist(0);
			Automaton.Int r14 = r9.lengthOf(); // |xs|
			Automaton.Int r15 = r13.lengthOf(); // |ys|
			boolean r16 = !r14.equals(r15); // |xs| neq |ys|
			if(r16) {
				Automaton.Term r17 = False;
				int r18 = automaton.add(r17);
				if(r0 != r18) {
					return automaton.rewrite(r0, r18);
				}
			}
			Automaton.Int r20 = new Automaton.Int(0); // 0
			Automaton.Int r21 = r9.lengthOf(); // |xs|
			Automaton.List r22 = Runtime.rangeOf(automaton,r20,r21); // 0 range |xs|
			Automaton.List t19 = new Automaton.List();
			for(int i23=0;i23<r22.size();i23++) {
				Automaton.Int r23 = (Automaton.Int) automaton.get(r22.get(i23));;
				int r24 = r4.indexOf(r23);     // ts[i]
				int r25 = r9.indexOf(r23);     // xs[i]
				int r26 = r13.indexOf(r23);    // ys[i]
				Automaton.Bag r27 = new Automaton.Bag(r25, r26); // {|xs[i]ys[i]|}
				int r28 = automaton.add(r27);
				Automaton.List r29 = new Automaton.List(r24, r28); // [ts[i]{|xs[i]ys[i]|}]
				int r30 = automaton.add(r29);
				Automaton.Term r31 = new Automaton.Term(K_Equals, r30);
				int r32 = automaton.add(r31);
				t19.add(r32);
			}
			Automaton.Set r19 = new Automaton.Set(t19.toArray());
			int r33 = automaton.add(r19);
			Automaton.Term r34 = new Automaton.Term(K_And, r33);
			int r35 = automaton.add(r34);
			if(r0 != r35) {
				return automaton.rewrite(r0, r35);
			}
			automaton.resize(nStates);
			return Automaton.K_VOID;
		}

	}
	private final static class Reduction_34 extends AbstractRewriteRule implements ReductionRule {

		public Reduction_34(Pattern.Term pattern) {
			super(pattern);
			put("name","And{Equals[VExpr,Tuple],BExpr...}");
			put("rank",2);
		}

		public final void probe(Automaton automaton, int target, List<Reduction.Activation> activations) {
			int r0 = target;
			Automaton.State s0 = automaton.get(r0);
			if(s0.kind == K_And) {
				Automaton.Term t0 = (Automaton.Term) s0;
				int r1 = t0.contents;
				Automaton.State s1 = automaton.get(r1);
				Automaton.Collection c1 = (Automaton.Collection) s1;
				if(c1.size() >= 1) {
					for(int r3=0;r3!=c1.size();++r3) {
						int r2 = c1.get(r3);
						Automaton.State s2 = automaton.get(r2);
						if(s2.kind == K_Equals) {
							Automaton.Term t2 = (Automaton.Term) s2;
							int r4 = t2.contents;
							Automaton.State s4 = automaton.get(r4);
							Automaton.List l4 = (Automaton.List) s4;
							int r5 = l4.get(0);
							int r6 = l4.get(1);
							Automaton.State s6 = automaton.get(r6);
							Automaton.Collection c6 = (Automaton.Collection) s6;
							for(int r8=0;r8!=c6.size();++r8) {
								int r7 = c6.get(r8);
								if(Runtime.accepts(type8,automaton,automaton.get(r7), SCHEMA)) {
									for(int r10=0;r10!=c6.size();++r10) {
										if(r10 == r8) { continue; }
										int r9 = c6.get(r10);
										if(Runtime.accepts(type9,automaton,automaton.get(r9), SCHEMA)) {
											int[] state = {r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, 0};
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
			int r2 = state[2]; // eq
			int r3 = state[3];
			int r5 = state[5]; // t
			int r7 = state[7]; // x
			int r8 = state[8];
			int r9 = state[9]; // y
			int r10 = state[10];
			Automaton.Collection c1 = (Automaton.Collection) automaton.get(state[1]);
			int[] c1children = new int[c1.size() - 1];
			for(int s1i=0, s1j=0; s1i != c1.size();++s1i) {
				if(s1i == r3) { continue; }
				c1children[s1j++] = c1.get(s1i);
			}
			Automaton.Set r11 = new Automaton.Set(c1children);
			Automaton.List t12 = new Automaton.List();
			for(int i13=0;i13<r11.size();i13++) {
				int r13 = (int) r11.get(i13);
				int r14 = automaton.substitute(r13, r7, r9);
				t12.add(r14);
			}
			Automaton.Set r12 = new Automaton.Set(t12.toArray());
			Automaton.Set r15 = r12.appendFront(r2); // eq append cs
			int r16 = automaton.add(r15);
			Automaton.Term r17 = new Automaton.Term(K_And, r16);
			int r18 = automaton.add(r17);
			if(r0 != r18) {
				return automaton.rewrite(r0, r18);
			}
			automaton.resize(nStates);
			return Automaton.K_VOID;
		}

	}
	// term $9<Fn(^[^string,$3<^Expr<$52<Value<Null|Tuple(^[^$52...])|Bool<True|False>|Num(^real)|String(^string)|Array(^[^$52...])|ArrayGen(^[^$52,^$52])>>|Tuple(^[$3...])|$93<BExpr<Bool<True|False>|VExpr<$9|Var(^string)|Load(^[$3,^int])|LengthOf($3)|IndexOf(^[$3,$3])>|And(^{^$93...})|Or(^{^$93...})|Not(^$93)|Equals(^[$132<^Type<Atom<NotT($155<^Proton<TupleT(^[$155...])|ArrayT($155)|Quark<AnyT|NullT|VoidT|BoolT|IntT|RealT|StringT|VarT(^string)|NominalT(^string)>>>)|Proton<TupleT(^[$155...])|ArrayT($155)|Quark<AnyT|NullT|VoidT|BoolT|IntT|RealT|StringT|VarT(^string)|NominalT(^string)>>>|NotT($132)|OrT(^{$132...})|AndT(^{$132...})|ArrayT($132)|TupleT(^[$132...])|FunctionT(^[$132,$132,$132...])>>,^{|$3,$3|}[$3,$3]])|Inequality(^[^AType<IntT|RealT>,$229<^AExpr<Num(^real)|VExpr<$9|Var(^string)|Load(^[$3,^int])|LengthOf($3)|IndexOf(^[$3,$3])>|Sum(^[^real,^{|$229...|}[$229...]])|Mul(^[^real,^{|$229...|}[$229...]])|Div(^[$229,$229])>>])|Equation(^[^AType<IntT|RealT>,$229])|ForAll(^[^{^[^Var(^string),$132]...},^$93])|Exists(^[^{^[^Var(^string),$132]...},^$93])>>|AExpr<Num(^real)|VExpr<$9|Var(^string)|Load(^[$3,^int])|LengthOf($3)|IndexOf(^[$3,$3])>|Sum(^[^real,^{|$229...|}[$229...]])|Mul(^[^real,^{|$229...|}[$229...]])|Div(^[$229,$229])>|SExpr<VExpr<$9|Var(^string)|Load(^[$3,^int])|LengthOf($3)|IndexOf(^[$3,$3])>|Array(^[$3...])|ArrayGen(^[$3,$3])>>>...])>
	public final static int K_Fn = 23;
	public final static int Fn(Automaton automaton, int... r0) {
		int r1 = automaton.add(new Automaton.List(r0));
		return automaton.add(new Automaton.Term(K_Fn, r1));
	}
	public final static int Fn(Automaton automaton, List<Integer> r0) {
		int r1 = automaton.add(new Automaton.List(r0));
		return automaton.add(new Automaton.Term(K_Fn, r1));
	}

	// term String(^string)
	public final static int K_String = 24;
	public final static int String(Automaton automaton, String r0) {
		int r1 = automaton.add(new Automaton.Strung(r0));
		return automaton.add(new Automaton.Term(K_String, r1));
	}

	// term $4<Not($2<^$25<BExpr<$4|$36<VExpr<Var(^string)|Fn(^[^string,$41<^Expr<$25|$88<Value<Null|Tuple(^[^$88...])|Bool<True|False>|Num(^real)|String(^string)|Array(^[^$88...])|ArrayGen(^[^$88,^$88])>>|Tuple(^[$41...])|$115<AExpr<$36|Num(^real)|Sum(^[^real,^{|^$115...|}[^$115...]])|Mul(^[^real,^{|^$115...|}[^$115...]])|Div(^[^$115,^$115])>>|SExpr<$36|Array(^[$41...])|ArrayGen(^[$41,$41])>>>...])|Load(^[$41,^int])|LengthOf($41)|IndexOf(^[$41,$41])>>|Bool<True|False>|And(^{$2...})|Or(^{$2...})|Equals(^[$165<^Type<Atom<NotT($188<^Proton<TupleT(^[$188...])|ArrayT($188)|Quark<AnyT|NullT|VoidT|BoolT|IntT|RealT|StringT|VarT(^string)|NominalT(^string)>>>)|Proton<TupleT(^[$188...])|ArrayT($188)|Quark<AnyT|NullT|VoidT|BoolT|IntT|RealT|StringT|VarT(^string)|NominalT(^string)>>>|NotT($165)|OrT(^{$165...})|AndT(^{$165...})|ArrayT($165)|TupleT(^[$165...])|FunctionT(^[$165,$165,$165...])>>,^{|$41,$41|}[$41,$41]])|Inequality(^[^AType<IntT|RealT>,^$115])|Equation(^[^AType<IntT|RealT>,^$115])|ForAll(^[^{^[^Var(^string),$165]...},$2])|Exists(^[^{^[^Var(^string),$165]...},$2])>>>)>
	public final static int K_Not = 25;
	public final static int Not(Automaton automaton, int r0) {
		return automaton.add(new Automaton.Term(K_Not, r0));
	}

	private final static class Reduction_35 extends AbstractRewriteRule implements ReductionRule {

		public Reduction_35(Pattern.Term pattern) {
			super(pattern);
			put("name","Not(Bool)");
			put("rank",0);
		}

		public final void probe(Automaton automaton, int target, List<Reduction.Activation> activations) {
			int r0 = target;
			Automaton.State s0 = automaton.get(r0);
			if(s0.kind == K_Not) {
				Automaton.Term t0 = (Automaton.Term) s0;
				int r1 = t0.contents;
				if(Runtime.accepts(type11,automaton,automaton.get(r1), SCHEMA)) {
					int[] state = {r0, r1};
					activations.add(new Reduction.Activation(this,null,state));
				}
			}
		}

		public final int apply(Automaton automaton, int[] state) {
			int nStates = automaton.nStates();
			int r0 = state[0];
			int r1 = state[1]; // b
			Automaton.Term r2 = True;
			Object r3 = (Object) automaton.get(r1);
			boolean r4 = r3.equals(r2);    // b eq True
			if(r4) {
				Automaton.Term r5 = False;
				int r6 = automaton.add(r5);
				if(r0 != r6) {
					return automaton.rewrite(r0, r6);
				}
			}
			Automaton.Term r7 = True;
			int r8 = automaton.add(r7);
			if(r0 != r8) {
				return automaton.rewrite(r0, r8);
			}
			automaton.resize(nStates);
			return Automaton.K_VOID;
		}

	}
	private final static class Reduction_36 extends AbstractRewriteRule implements ReductionRule {

		public Reduction_36(Pattern.Term pattern) {
			super(pattern);
			put("name","Not(Not(BExpr))");
			put("rank",0);
		}

		public final void probe(Automaton automaton, int target, List<Reduction.Activation> activations) {
			int r0 = target;
			Automaton.State s0 = automaton.get(r0);
			if(s0.kind == K_Not) {
				Automaton.Term t0 = (Automaton.Term) s0;
				int r1 = t0.contents;
				Automaton.State s1 = automaton.get(r1);
				if(s1.kind == K_Not) {
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
			int r2 = state[2]; // x
			if(r0 != r2) {
				return automaton.rewrite(r0, r2);
			}
			automaton.resize(nStates);
			return Automaton.K_VOID;
		}

	}
	private final static class Reduction_37 extends AbstractRewriteRule implements ReductionRule {

		public Reduction_37(Pattern.Term pattern) {
			super(pattern);
			put("name","Not(And{BExpr...})");
			put("rank",2);
		}

		public final void probe(Automaton automaton, int target, List<Reduction.Activation> activations) {
			int r0 = target;
			Automaton.State s0 = automaton.get(r0);
			if(s0.kind == K_Not) {
				Automaton.Term t0 = (Automaton.Term) s0;
				int r1 = t0.contents;
				Automaton.State s1 = automaton.get(r1);
				if(s1.kind == K_And) {
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
				Automaton.Term r6 = new Automaton.Term(K_Not, r5);
				int r7 = automaton.add(r6);
				t4.add(r7);
			}
			Automaton.Set r4 = new Automaton.Set(t4.toArray());
			int r8 = automaton.add(r4);
			Automaton.Term r9 = new Automaton.Term(K_Or, r8);
			int r10 = automaton.add(r9);
			if(r0 != r10) {
				return automaton.rewrite(r0, r10);
			}
			automaton.resize(nStates);
			return Automaton.K_VOID;
		}

	}
	private final static class Reduction_38 extends AbstractRewriteRule implements ReductionRule {

		public Reduction_38(Pattern.Term pattern) {
			super(pattern);
			put("name","Not(Or{BExpr...})");
			put("rank",1);
		}

		public final void probe(Automaton automaton, int target, List<Reduction.Activation> activations) {
			int r0 = target;
			Automaton.State s0 = automaton.get(r0);
			if(s0.kind == K_Not) {
				Automaton.Term t0 = (Automaton.Term) s0;
				int r1 = t0.contents;
				Automaton.State s1 = automaton.get(r1);
				if(s1.kind == K_Or) {
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
				Automaton.Term r6 = new Automaton.Term(K_Not, r5);
				int r7 = automaton.add(r6);
				t4.add(r7);
			}
			Automaton.Set r4 = new Automaton.Set(t4.toArray());
			int r8 = automaton.add(r4);
			Automaton.Term r9 = new Automaton.Term(K_And, r8);
			int r10 = automaton.add(r9);
			if(r0 != r10) {
				return automaton.rewrite(r0, r10);
			}
			automaton.resize(nStates);
			return Automaton.K_VOID;
		}

	}
	// term $7<And($5<^{$2<^$28<BExpr<$7|$39<VExpr<Var(^string)|Fn(^[^string,$44<^Expr<$28|$91<Value<Null|Tuple(^[^$91...])|Bool<True|False>|Num(^real)|String(^string)|Array(^[^$91...])|ArrayGen(^[^$91,^$91])>>|Tuple(^[$44...])|$118<AExpr<$39|Num(^real)|Sum(^[^real,^{|^$118...|}[^$118...]])|Mul(^[^real,^{|^$118...|}[^$118...]])|Div(^[^$118,^$118])>>|SExpr<$39|Array(^[$44...])|ArrayGen(^[$44,$44])>>>...])|Load(^[$44,^int])|LengthOf($44)|IndexOf(^[$44,$44])>>|Bool<True|False>|Or($5)|Not($2)|Equals(^[$165<^Type<Atom<NotT($188<^Proton<TupleT(^[$188...])|ArrayT($188)|Quark<AnyT|NullT|VoidT|BoolT|IntT|RealT|StringT|VarT(^string)|NominalT(^string)>>>)|Proton<TupleT(^[$188...])|ArrayT($188)|Quark<AnyT|NullT|VoidT|BoolT|IntT|RealT|StringT|VarT(^string)|NominalT(^string)>>>|NotT($165)|OrT(^{$165...})|AndT(^{$165...})|ArrayT($165)|TupleT(^[$165...])|FunctionT(^[$165,$165,$165...])>>,^{|$44,$44|}[$44,$44]])|Inequality(^[^AType<IntT|RealT>,^$118])|Equation(^[^AType<IntT|RealT>,^$118])|ForAll(^[^{^[^Var(^string),$165]...},$2])|Exists(^[^{^[^Var(^string),$165]...},$2])>>>...}>)>
	public final static int K_And = 26;
	public final static int And(Automaton automaton, int... r0) {
		int r1 = automaton.add(new Automaton.Set(r0));
		return automaton.add(new Automaton.Term(K_And, r1));
	}
	public final static int And(Automaton automaton, List<Integer> r0) {
		int r1 = automaton.add(new Automaton.Set(r0));
		return automaton.add(new Automaton.Term(K_And, r1));
	}

	private final static class Reduction_39 extends AbstractRewriteRule implements ReductionRule {

		public Reduction_39(Pattern.Term pattern) {
			super(pattern);
			put("name","And{BExpr}");
			put("rank",1);
		}

		public final void probe(Automaton automaton, int target, List<Reduction.Activation> activations) {
			int r0 = target;
			Automaton.State s0 = automaton.get(r0);
			if(s0.kind == K_And) {
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
			int r2 = state[2]; // x
			int r3 = state[3];
			if(r0 != r2) {
				return automaton.rewrite(r0, r2);
			}
			automaton.resize(nStates);
			return Automaton.K_VOID;
		}

	}
	private final static class Reduction_40 extends AbstractRewriteRule implements ReductionRule {

		public Reduction_40(Pattern.Term pattern) {
			super(pattern);
			put("name","And{False,BExpr...}");
			put("rank",1);
		}

		public final void probe(Automaton automaton, int target, List<Reduction.Activation> activations) {
			int r0 = target;
			Automaton.State s0 = automaton.get(r0);
			if(s0.kind == K_And) {
				Automaton.Term t0 = (Automaton.Term) s0;
				int r1 = t0.contents;
				Automaton.State s1 = automaton.get(r1);
				Automaton.Collection c1 = (Automaton.Collection) s1;
				if(c1.size() >= 1) {
					for(int r3=0;r3!=c1.size();++r3) {
						int r2 = c1.get(r3);
						if(Runtime.accepts(type13,automaton,automaton.get(r2), SCHEMA)) {
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
			Automaton.Term r5 = False;
			int r6 = automaton.add(r5);
			if(r0 != r6) {
				return automaton.rewrite(r0, r6);
			}
			automaton.resize(nStates);
			return Automaton.K_VOID;
		}

	}
	private final static class Reduction_41 extends AbstractRewriteRule implements ReductionRule {

		public Reduction_41(Pattern.Term pattern) {
			super(pattern);
			put("name","And{True,BExpr...}");
			put("rank",1);
		}

		public final void probe(Automaton automaton, int target, List<Reduction.Activation> activations) {
			int r0 = target;
			Automaton.State s0 = automaton.get(r0);
			if(s0.kind == K_And) {
				Automaton.Term t0 = (Automaton.Term) s0;
				int r1 = t0.contents;
				Automaton.State s1 = automaton.get(r1);
				Automaton.Collection c1 = (Automaton.Collection) s1;
				if(c1.size() >= 1) {
					for(int r3=0;r3!=c1.size();++r3) {
						int r2 = c1.get(r3);
						if(Runtime.accepts(type14,automaton,automaton.get(r2), SCHEMA)) {
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
			Automaton.Int r5 = r4.lengthOf(); // |xs|
			Automaton.Int r6 = new Automaton.Int(0); // 0
			boolean r7 = r5.compareTo(r6)>0; // |xs| gt 0
			if(r7) {
				int r8 = automaton.add(r4);
				Automaton.Term r9 = new Automaton.Term(K_And, r8);
				int r10 = automaton.add(r9);
				if(r0 != r10) {
					return automaton.rewrite(r0, r10);
				}
			}
			Automaton.Term r11 = True;
			int r12 = automaton.add(r11);
			if(r0 != r12) {
				return automaton.rewrite(r0, r12);
			}
			automaton.resize(nStates);
			return Automaton.K_VOID;
		}

	}
	private final static class Reduction_42 extends AbstractRewriteRule implements ReductionRule {

		public Reduction_42(Pattern.Term pattern) {
			super(pattern);
			put("name","And{And{BExpr...},BExpr...}");
			put("rank",1);
		}

		public final void probe(Automaton automaton, int target, List<Reduction.Activation> activations) {
			int r0 = target;
			Automaton.State s0 = automaton.get(r0);
			if(s0.kind == K_And) {
				Automaton.Term t0 = (Automaton.Term) s0;
				int r1 = t0.contents;
				Automaton.State s1 = automaton.get(r1);
				Automaton.Collection c1 = (Automaton.Collection) s1;
				if(c1.size() >= 1) {
					for(int r3=0;r3!=c1.size();++r3) {
						int r2 = c1.get(r3);
						Automaton.State s2 = automaton.get(r2);
						if(s2.kind == K_And) {
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
			Automaton.Term r9 = new Automaton.Term(K_And, r8);
			int r10 = automaton.add(r9);
			if(r0 != r10) {
				return automaton.rewrite(r0, r10);
			}
			automaton.resize(nStates);
			return Automaton.K_VOID;
		}

	}
	private final static class Reduction_43 extends AbstractRewriteRule implements ReductionRule {

		public Reduction_43(Pattern.Term pattern) {
			super(pattern);
			put("name","And{Not(BExpr x),BExpr x,BExpr...}");
			put("rank",2);
		}

		public final void probe(Automaton automaton, int target, List<Reduction.Activation> activations) {
			int r0 = target;
			Automaton.State s0 = automaton.get(r0);
			if(s0.kind == K_And) {
				Automaton.Term t0 = (Automaton.Term) s0;
				int r1 = t0.contents;
				Automaton.State s1 = automaton.get(r1);
				Automaton.Collection c1 = (Automaton.Collection) s1;
				if(c1.size() >= 2) {
					for(int r3=0;r3!=c1.size();++r3) {
						int r2 = c1.get(r3);
						Automaton.State s2 = automaton.get(r2);
						if(s2.kind == K_Not) {
							Automaton.Term t2 = (Automaton.Term) s2;
							int r4 = t2.contents;
							for(int r6=0;r6!=c1.size();++r6) {
								if(r6 == r3) { continue; }
								int r5 = c1.get(r6);
								int[] c1children = new int[c1.size() - 2];
								for(int s1i=0, s1j=0; s1i != c1.size();++s1i) {
									if(s1i == r3 || s1i == r6) { continue; }
									c1children[s1j++] = c1.get(s1i);
								}
								Automaton.Set r7 = new Automaton.Set(c1children);
								boolean r8 = r4 == r5;         // x eq y
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

		public final int apply(Automaton automaton, int[] state) {
			int nStates = automaton.nStates();
			int r0 = state[0];
			int r3 = state[3];
			int r4 = state[4]; // x
			int r5 = state[5]; // y
			int r6 = state[6];
			Automaton.Collection c1 = (Automaton.Collection) automaton.get(state[1]);
			int[] c1children = new int[c1.size() - 2];
			for(int s1i=0, s1j=0; s1i != c1.size();++s1i) {
				if(s1i == r3 || s1i == r6) { continue; }
				c1children[s1j++] = c1.get(s1i);
			}
			Automaton.Set r7 = new Automaton.Set(c1children);
			Automaton.Term r8 = False;
			int r9 = automaton.add(r8);
			if(r0 != r9) {
				return automaton.rewrite(r0, r9);
			}
			automaton.resize(nStates);
			return Automaton.K_VOID;
		}

	}
	private final static class Reduction_44 extends AbstractRewriteRule implements ReductionRule {

		public Reduction_44(Pattern.Term pattern) {
			super(pattern);
			put("name","And{Or{BExpr...},BExpr...}");
			put("rank",3);
		}

		public final void probe(Automaton automaton, int target, List<Reduction.Activation> activations) {
			int r0 = target;
			Automaton.State s0 = automaton.get(r0);
			if(s0.kind == K_And) {
				Automaton.Term t0 = (Automaton.Term) s0;
				int r1 = t0.contents;
				Automaton.State s1 = automaton.get(r1);
				Automaton.Collection c1 = (Automaton.Collection) s1;
				if(c1.size() >= 1) {
					for(int r3=0;r3!=c1.size();++r3) {
						int r2 = c1.get(r3);
						Automaton.State s2 = automaton.get(r2);
						if(s2.kind == K_Or) {
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
				Automaton.Term r11 = new Automaton.Term(K_And, r10);
				int r12 = automaton.add(r11);
				t7.add(r12);
			}
			Automaton.Set r7 = new Automaton.Set(t7.toArray());
			int r13 = automaton.add(r7);
			Automaton.Term r14 = new Automaton.Term(K_Or, r13);
			int r15 = automaton.add(r14);
			if(r0 != r15) {
				return automaton.rewrite(r0, r15);
			}
			automaton.resize(nStates);
			return Automaton.K_VOID;
		}

	}
	// term $7<Or($5<^{$2<^$28<BExpr<$7|$39<VExpr<Var(^string)|Fn(^[^string,$44<^Expr<$28|$91<Value<Null|Tuple(^[^$91...])|Bool<True|False>|Num(^real)|String(^string)|Array(^[^$91...])|ArrayGen(^[^$91,^$91])>>|Tuple(^[$44...])|$118<AExpr<$39|Num(^real)|Sum(^[^real,^{|^$118...|}[^$118...]])|Mul(^[^real,^{|^$118...|}[^$118...]])|Div(^[^$118,^$118])>>|SExpr<$39|Array(^[$44...])|ArrayGen(^[$44,$44])>>>...])|Load(^[$44,^int])|LengthOf($44)|IndexOf(^[$44,$44])>>|Bool<True|False>|And($5)|Not($2)|Equals(^[$165<^Type<Atom<NotT($188<^Proton<TupleT(^[$188...])|ArrayT($188)|Quark<AnyT|NullT|VoidT|BoolT|IntT|RealT|StringT|VarT(^string)|NominalT(^string)>>>)|Proton<TupleT(^[$188...])|ArrayT($188)|Quark<AnyT|NullT|VoidT|BoolT|IntT|RealT|StringT|VarT(^string)|NominalT(^string)>>>|NotT($165)|OrT(^{$165...})|AndT(^{$165...})|ArrayT($165)|TupleT(^[$165...])|FunctionT(^[$165,$165,$165...])>>,^{|$44,$44|}[$44,$44]])|Inequality(^[^AType<IntT|RealT>,^$118])|Equation(^[^AType<IntT|RealT>,^$118])|ForAll(^[^{^[^Var(^string),$165]...},$2])|Exists(^[^{^[^Var(^string),$165]...},$2])>>>...}>)>
	public final static int K_Or = 27;
	public final static int Or(Automaton automaton, int... r0) {
		int r1 = automaton.add(new Automaton.Set(r0));
		return automaton.add(new Automaton.Term(K_Or, r1));
	}
	public final static int Or(Automaton automaton, List<Integer> r0) {
		int r1 = automaton.add(new Automaton.Set(r0));
		return automaton.add(new Automaton.Term(K_Or, r1));
	}

	private final static class Reduction_45 extends AbstractRewriteRule implements ReductionRule {

		public Reduction_45(Pattern.Term pattern) {
			super(pattern);
			put("name","Or{BExpr}");
			put("rank",0);
		}

		public final void probe(Automaton automaton, int target, List<Reduction.Activation> activations) {
			int r0 = target;
			Automaton.State s0 = automaton.get(r0);
			if(s0.kind == K_Or) {
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
			int r2 = state[2]; // x
			int r3 = state[3];
			if(r0 != r2) {
				return automaton.rewrite(r0, r2);
			}
			automaton.resize(nStates);
			return Automaton.K_VOID;
		}

	}
	private final static class Reduction_46 extends AbstractRewriteRule implements ReductionRule {

		public Reduction_46(Pattern.Term pattern) {
			super(pattern);
			put("name","Or{True,BExpr...}");
			put("rank",1);
		}

		public final void probe(Automaton automaton, int target, List<Reduction.Activation> activations) {
			int r0 = target;
			Automaton.State s0 = automaton.get(r0);
			if(s0.kind == K_Or) {
				Automaton.Term t0 = (Automaton.Term) s0;
				int r1 = t0.contents;
				Automaton.State s1 = automaton.get(r1);
				Automaton.Collection c1 = (Automaton.Collection) s1;
				if(c1.size() >= 1) {
					for(int r3=0;r3!=c1.size();++r3) {
						int r2 = c1.get(r3);
						if(Runtime.accepts(type14,automaton,automaton.get(r2), SCHEMA)) {
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
			Automaton.Term r5 = True;
			int r6 = automaton.add(r5);
			if(r0 != r6) {
				return automaton.rewrite(r0, r6);
			}
			automaton.resize(nStates);
			return Automaton.K_VOID;
		}

	}
	private final static class Reduction_47 extends AbstractRewriteRule implements ReductionRule {

		public Reduction_47(Pattern.Term pattern) {
			super(pattern);
			put("name","Or{False,BExpr...}");
			put("rank",1);
		}

		public final void probe(Automaton automaton, int target, List<Reduction.Activation> activations) {
			int r0 = target;
			Automaton.State s0 = automaton.get(r0);
			if(s0.kind == K_Or) {
				Automaton.Term t0 = (Automaton.Term) s0;
				int r1 = t0.contents;
				Automaton.State s1 = automaton.get(r1);
				Automaton.Collection c1 = (Automaton.Collection) s1;
				if(c1.size() >= 1) {
					for(int r3=0;r3!=c1.size();++r3) {
						int r2 = c1.get(r3);
						if(Runtime.accepts(type13,automaton,automaton.get(r2), SCHEMA)) {
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
			Automaton.Int r5 = r4.lengthOf(); // |xs|
			Automaton.Int r6 = new Automaton.Int(0); // 0
			boolean r7 = r5.compareTo(r6)>0; // |xs| gt 0
			if(r7) {
				int r8 = automaton.add(r4);
				Automaton.Term r9 = new Automaton.Term(K_Or, r8);
				int r10 = automaton.add(r9);
				if(r0 != r10) {
					return automaton.rewrite(r0, r10);
				}
			}
			Automaton.Term r11 = False;
			int r12 = automaton.add(r11);
			if(r0 != r12) {
				return automaton.rewrite(r0, r12);
			}
			automaton.resize(nStates);
			return Automaton.K_VOID;
		}

	}
	private final static class Reduction_48 extends AbstractRewriteRule implements ReductionRule {

		public Reduction_48(Pattern.Term pattern) {
			super(pattern);
			put("name","Or{Not(BExpr x),BExpr x,BExpr...}");
			put("rank",2);
		}

		public final void probe(Automaton automaton, int target, List<Reduction.Activation> activations) {
			int r0 = target;
			Automaton.State s0 = automaton.get(r0);
			if(s0.kind == K_Or) {
				Automaton.Term t0 = (Automaton.Term) s0;
				int r1 = t0.contents;
				Automaton.State s1 = automaton.get(r1);
				Automaton.Collection c1 = (Automaton.Collection) s1;
				if(c1.size() >= 2) {
					for(int r3=0;r3!=c1.size();++r3) {
						int r2 = c1.get(r3);
						Automaton.State s2 = automaton.get(r2);
						if(s2.kind == K_Not) {
							Automaton.Term t2 = (Automaton.Term) s2;
							int r4 = t2.contents;
							for(int r6=0;r6!=c1.size();++r6) {
								if(r6 == r3) { continue; }
								int r5 = c1.get(r6);
								int[] c1children = new int[c1.size() - 2];
								for(int s1i=0, s1j=0; s1i != c1.size();++s1i) {
									if(s1i == r3 || s1i == r6) { continue; }
									c1children[s1j++] = c1.get(s1i);
								}
								Automaton.Set r7 = new Automaton.Set(c1children);
								boolean r8 = r4 == r5;         // x eq y
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

		public final int apply(Automaton automaton, int[] state) {
			int nStates = automaton.nStates();
			int r0 = state[0];
			int r3 = state[3];
			int r4 = state[4]; // x
			int r5 = state[5]; // y
			int r6 = state[6];
			Automaton.Collection c1 = (Automaton.Collection) automaton.get(state[1]);
			int[] c1children = new int[c1.size() - 2];
			for(int s1i=0, s1j=0; s1i != c1.size();++s1i) {
				if(s1i == r3 || s1i == r6) { continue; }
				c1children[s1j++] = c1.get(s1i);
			}
			Automaton.Set r7 = new Automaton.Set(c1children);
			Automaton.Term r8 = True;
			int r9 = automaton.add(r8);
			if(r0 != r9) {
				return automaton.rewrite(r0, r9);
			}
			automaton.resize(nStates);
			return Automaton.K_VOID;
		}

	}
	private final static class Reduction_49 extends AbstractRewriteRule implements ReductionRule {

		public Reduction_49(Pattern.Term pattern) {
			super(pattern);
			put("name","Or{Or{BExpr...},BExpr...}");
			put("rank",1);
		}

		public final void probe(Automaton automaton, int target, List<Reduction.Activation> activations) {
			int r0 = target;
			Automaton.State s0 = automaton.get(r0);
			if(s0.kind == K_Or) {
				Automaton.Term t0 = (Automaton.Term) s0;
				int r1 = t0.contents;
				Automaton.State s1 = automaton.get(r1);
				Automaton.Collection c1 = (Automaton.Collection) s1;
				if(c1.size() >= 1) {
					for(int r3=0;r3!=c1.size();++r3) {
						int r2 = c1.get(r3);
						Automaton.State s2 = automaton.get(r2);
						if(s2.kind == K_Or) {
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
			Automaton.Term r9 = new Automaton.Term(K_Or, r8);
			int r10 = automaton.add(r9);
			if(r0 != r10) {
				return automaton.rewrite(r0, r10);
			}
			automaton.resize(nStates);
			return Automaton.K_VOID;
		}

	}
	// term $14<Equals(^[$2<^Type<Atom<NotT($27<^Proton<TupleT(^[$27...])|ArrayT($27)|Quark<AnyT|NullT|VoidT|BoolT|IntT|RealT|StringT|VarT(^string)|NominalT(^string)>>>)|Proton<TupleT(^[$27...])|ArrayT($27)|Quark<AnyT|NullT|VoidT|BoolT|IntT|RealT|StringT|VarT(^string)|NominalT(^string)>>>|NotT($2)|OrT(^{$2...})|AndT(^{$2...})|ArrayT($2)|TupleT(^[$2...])|FunctionT(^[$2,$2,$2...])>>,^{|$4<^Expr<$142<Value<Null|Tuple(^[^$142...])|Bool<True|False>|Num(^real)|String(^string)|Array(^[^$142...])|ArrayGen(^[^$142,^$142])>>|Tuple(^[$4...])|$182<BExpr<$14|Bool<True|False>|VExpr<Var(^string)|Fn(^[^string,$4...])|Load(^[$4,^int])|LengthOf($4)|IndexOf(^[$4,$4])>|And(^{^$182...})|Or(^{^$182...})|Not(^$182)|Inequality(^[^AType<IntT|RealT>,$229<^AExpr<Num(^real)|VExpr<Var(^string)|Fn(^[^string,$4...])|Load(^[$4,^int])|LengthOf($4)|IndexOf(^[$4,$4])>|Sum(^[^real,^{|$229...|}[$229...]])|Mul(^[^real,^{|$229...|}[$229...]])|Div(^[$229,$229])>>])|Equation(^[^AType<IntT|RealT>,$229])|ForAll(^[^{^[^Var(^string),$2]...},^$182])|Exists(^[^{^[^Var(^string),$2]...},^$182])>>|AExpr<Num(^real)|VExpr<Var(^string)|Fn(^[^string,$4...])|Load(^[$4,^int])|LengthOf($4)|IndexOf(^[$4,$4])>|Sum(^[^real,^{|$229...|}[$229...]])|Mul(^[^real,^{|$229...|}[$229...]])|Div(^[$229,$229])>|SExpr<VExpr<Var(^string)|Fn(^[^string,$4...])|Load(^[$4,^int])|LengthOf($4)|IndexOf(^[$4,$4])>|Array(^[$4...])|ArrayGen(^[$4,$4])>>>,$4|}[$4<^Expr<$142<Value<Null|Tuple(^[^$142...])|Bool<True|False>|Num(^real)|String(^string)|Array(^[^$142...])|ArrayGen(^[^$142,^$142])>>|Tuple(^[$4...])|$182<BExpr<$14|Bool<True|False>|VExpr<Var(^string)|Fn(^[^string,$4...])|Load(^[$4,^int])|LengthOf($4)|IndexOf(^[$4,$4])>|And(^{^$182...})|Or(^{^$182...})|Not(^$182)|Inequality(^[^AType<IntT|RealT>,$229<^AExpr<Num(^real)|VExpr<Var(^string)|Fn(^[^string,$4...])|Load(^[$4,^int])|LengthOf($4)|IndexOf(^[$4,$4])>|Sum(^[^real,^{|$229...|}[$229...]])|Mul(^[^real,^{|$229...|}[$229...]])|Div(^[$229,$229])>>])|Equation(^[^AType<IntT|RealT>,$229])|ForAll(^[^{^[^Var(^string),$2]...},^$182])|Exists(^[^{^[^Var(^string),$2]...},^$182])>>|AExpr<Num(^real)|VExpr<Var(^string)|Fn(^[^string,$4...])|Load(^[$4,^int])|LengthOf($4)|IndexOf(^[$4,$4])>|Sum(^[^real,^{|$229...|}[$229...]])|Mul(^[^real,^{|$229...|}[$229...]])|Div(^[$229,$229])>|SExpr<VExpr<Var(^string)|Fn(^[^string,$4...])|Load(^[$4,^int])|LengthOf($4)|IndexOf(^[$4,$4])>|Array(^[$4...])|ArrayGen(^[$4,$4])>>>,$4]])>
	public final static int K_Equals = 28;
	public final static int Equals(Automaton automaton, int... r0) {
		int r1 = automaton.add(new Automaton.List(r0));
		return automaton.add(new Automaton.Term(K_Equals, r1));
	}
	public final static int Equals(Automaton automaton, List<Integer> r0) {
		int r1 = automaton.add(new Automaton.List(r0));
		return automaton.add(new Automaton.Term(K_Equals, r1));
	}

	private final static class Reduction_50 extends AbstractRewriteRule implements ReductionRule {

		public Reduction_50(Pattern.Term pattern) {
			super(pattern);
			put("name","Equals{|Expr,Expr|}");
			put("rank",1);
		}

		public final void probe(Automaton automaton, int target, List<Reduction.Activation> activations) {
			int r0 = target;
			Automaton.State s0 = automaton.get(r0);
			if(s0.kind == K_Equals) {
				Automaton.Term t0 = (Automaton.Term) s0;
				int r1 = t0.contents;
				Automaton.State s1 = automaton.get(r1);
				Automaton.List l1 = (Automaton.List) s1;
				int r2 = l1.get(0);
				int r3 = l1.get(1);
				Automaton.State s3 = automaton.get(r3);
				Automaton.Collection c3 = (Automaton.Collection) s3;
				for(int r5=0;r5!=c3.size();++r5) {
					int r4 = c3.get(r5);
					for(int r7=0;r7!=c3.size();++r7) {
						if(r7 == r5) { continue; }
						int r6 = c3.get(r7);
						boolean r8 = r4 == r6;         // x eq y
						if(r8) { // REQUIRES
							int[] state = {r0, r1, r2, r3, r4, r5, r6, r7};
							activations.add(new Reduction.Activation(this,null,state));
						}
					}
				}
			}
		}

		public final int apply(Automaton automaton, int[] state) {
			int nStates = automaton.nStates();
			int r0 = state[0];
			int r2 = state[2]; // t
			int r4 = state[4]; // x
			int r5 = state[5];
			int r6 = state[6]; // y
			int r7 = state[7];
			Automaton.Term r8 = True;
			int r9 = automaton.add(r8);
			if(r0 != r9) {
				return automaton.rewrite(r0, r9);
			}
			automaton.resize(nStates);
			return Automaton.K_VOID;
		}

	}
	private final static class Reduction_51 extends AbstractRewriteRule implements ReductionRule {

		public Reduction_51(Pattern.Term pattern) {
			super(pattern);
			put("name","Equals{|Value,Value|}");
			put("rank",1);
		}

		public final void probe(Automaton automaton, int target, List<Reduction.Activation> activations) {
			int r0 = target;
			Automaton.State s0 = automaton.get(r0);
			if(s0.kind == K_Equals) {
				Automaton.Term t0 = (Automaton.Term) s0;
				int r1 = t0.contents;
				Automaton.State s1 = automaton.get(r1);
				Automaton.List l1 = (Automaton.List) s1;
				int r2 = l1.get(0);
				int r3 = l1.get(1);
				Automaton.State s3 = automaton.get(r3);
				Automaton.Collection c3 = (Automaton.Collection) s3;
				for(int r5=0;r5!=c3.size();++r5) {
					int r4 = c3.get(r5);
					if(Runtime.accepts(type15,automaton,automaton.get(r4), SCHEMA)) {
						for(int r7=0;r7!=c3.size();++r7) {
							if(r7 == r5) { continue; }
							int r6 = c3.get(r7);
							if(Runtime.accepts(type15,automaton,automaton.get(r6), SCHEMA)) {
								boolean r8 = r4 != r6;         // x neq y
								if(r8) { // REQUIRES
									int[] state = {r0, r1, r2, r3, r4, r5, r6, r7};
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
			int r2 = state[2]; // t
			int r4 = state[4]; // x
			int r5 = state[5];
			int r6 = state[6]; // y
			int r7 = state[7];
			Automaton.Term r8 = False;
			int r9 = automaton.add(r8);
			if(r0 != r9) {
				return automaton.rewrite(r0, r9);
			}
			automaton.resize(nStates);
			return Automaton.K_VOID;
		}

	}
	private final static class Reduction_52 extends AbstractRewriteRule implements ReductionRule {

		public Reduction_52(Pattern.Term pattern) {
			super(pattern);
			put("name","And{Equals{|VExpr,Value|},BExpr...}");
			put("rank",2);
		}

		public final void probe(Automaton automaton, int target, List<Reduction.Activation> activations) {
			int r0 = target;
			Automaton.State s0 = automaton.get(r0);
			if(s0.kind == K_And) {
				Automaton.Term t0 = (Automaton.Term) s0;
				int r1 = t0.contents;
				Automaton.State s1 = automaton.get(r1);
				Automaton.Collection c1 = (Automaton.Collection) s1;
				if(c1.size() >= 1) {
					for(int r3=0;r3!=c1.size();++r3) {
						int r2 = c1.get(r3);
						Automaton.State s2 = automaton.get(r2);
						if(s2.kind == K_Equals) {
							Automaton.Term t2 = (Automaton.Term) s2;
							int r4 = t2.contents;
							Automaton.State s4 = automaton.get(r4);
							Automaton.List l4 = (Automaton.List) s4;
							int r5 = l4.get(0);
							int r6 = l4.get(1);
							Automaton.State s6 = automaton.get(r6);
							Automaton.Collection c6 = (Automaton.Collection) s6;
							for(int r8=0;r8!=c6.size();++r8) {
								int r7 = c6.get(r8);
								if(Runtime.accepts(type8,automaton,automaton.get(r7), SCHEMA)) {
									for(int r10=0;r10!=c6.size();++r10) {
										if(r10 == r8) { continue; }
										int r9 = c6.get(r10);
										if(Runtime.accepts(type15,automaton,automaton.get(r9), SCHEMA)) {
											int[] state = {r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, 0};
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
			int r2 = state[2]; // eq
			int r3 = state[3];
			int r5 = state[5]; // t
			int r7 = state[7]; // x
			int r8 = state[8];
			int r9 = state[9]; // y
			int r10 = state[10];
			Automaton.Collection c1 = (Automaton.Collection) automaton.get(state[1]);
			int[] c1children = new int[c1.size() - 1];
			for(int s1i=0, s1j=0; s1i != c1.size();++s1i) {
				if(s1i == r3) { continue; }
				c1children[s1j++] = c1.get(s1i);
			}
			Automaton.Set r11 = new Automaton.Set(c1children);
			Automaton.List t12 = new Automaton.List();
			for(int i13=0;i13<r11.size();i13++) {
				int r13 = (int) r11.get(i13);
				int r14 = automaton.substitute(r13, r7, r9);
				t12.add(r14);
			}
			Automaton.Set r12 = new Automaton.Set(t12.toArray());
			Automaton.Set r15 = r12.appendFront(r2); // eq append cs
			int r16 = automaton.add(r15);
			Automaton.Term r17 = new Automaton.Term(K_And, r16);
			int r18 = automaton.add(r17);
			if(r0 != r18) {
				return automaton.rewrite(r0, r18);
			}
			automaton.resize(nStates);
			return Automaton.K_VOID;
		}

	}
	private final static class Inference_0 extends AbstractRewriteRule implements InferenceRule {

		public Inference_0(Pattern.Term pattern) {
			super(pattern);
			put("name","And{Equals{|VExpr,VExpr|},BExpr...}");
		}

		public final void probe(Automaton automaton, int root, int target, List<Inference.Activation> activations) {
			int r0 = target;
			Automaton.State s0 = automaton.get(r0);
			if(s0.kind == K_And) {
				Automaton.Term t0 = (Automaton.Term) s0;
				int r1 = t0.contents;
				Automaton.State s1 = automaton.get(r1);
				Automaton.Collection c1 = (Automaton.Collection) s1;
				if(c1.size() >= 1) {
					for(int r3=0;r3!=c1.size();++r3) {
						int r2 = c1.get(r3);
						Automaton.State s2 = automaton.get(r2);
						if(s2.kind == K_Equals) {
							Automaton.Term t2 = (Automaton.Term) s2;
							int r4 = t2.contents;
							Automaton.State s4 = automaton.get(r4);
							Automaton.List l4 = (Automaton.List) s4;
							int r5 = l4.get(0);
							int r6 = l4.get(1);
							Automaton.State s6 = automaton.get(r6);
							Automaton.Collection c6 = (Automaton.Collection) s6;
							for(int r8=0;r8!=c6.size();++r8) {
								int r7 = c6.get(r8);
								if(Runtime.accepts(type8,automaton,automaton.get(r7), SCHEMA)) {
									for(int r10=0;r10!=c6.size();++r10) {
										if(r10 == r8) { continue; }
										int r9 = c6.get(r10);
										if(Runtime.accepts(type8,automaton,automaton.get(r9), SCHEMA)) {
											int[] state = {r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, 0};
											activations.add(new Inference.Activation(this,root,null,state));
										}
									}
								}
							}
						}
					}
				}
			}
		}

		public final int apply(Automaton automaton, int root, int[] state) {
			int nStates = automaton.nStates();
			int r0 = state[0];
			int r2 = state[2]; // eq
			int r3 = state[3];
			int r5 = state[5]; // t
			int r6 = state[6]; // vs
			int r8 = state[8];
			int r10 = state[10];
			Automaton.Collection c1 = (Automaton.Collection) automaton.get(state[1]);
			int[] c1children = new int[c1.size() - 1];
			for(int s1i=0, s1j=0; s1i != c1.size();++s1i) {
				if(s1i == r3) { continue; }
				c1children[s1j++] = c1.get(s1i);
			}
			Automaton.Set r11 = new Automaton.Set(c1children);
			Automaton.Term r12 = Solver$native.max(automaton, r6);
			Automaton.Term r13 = Solver$native.min(automaton, r6);
			boolean r14 = !r12.equals(r13); // x neq y
			if(r14) {
				Automaton.List t15 = new Automaton.List();
				for(int i16=0;i16<r11.size();i16++) {
					int r16 = (int) r11.get(i16);
					int r17 = automaton.add(r12);
					int r18 = automaton.add(r13);
					int r19 = automaton.substitute(r16, r17, r18);
					t15.add(r19);
				}
				Automaton.Set r15 = new Automaton.Set(t15.toArray());
				Automaton.Set r20 = r15.appendFront(r2); // eq append cs
				int r21 = automaton.add(r20);
				Automaton.Term r22 = new Automaton.Term(K_And, r21);
				int r23 = automaton.add(r22);
				if(r0 != r23) {
					return automaton.substitute(root,r0, r23);
				}
			}
			automaton.resize(nStates);
			return Automaton.K_VOID;
		}

	}
	// term $12<Mul($10<^[^real,^{|$3<^$20<AExpr<$12|Num(^real)|Sum($10)|Div(^[$3,$3])|$41<VExpr<Var(^string)|Fn(^[^string,$46<^Expr<$20|$93<Value<Num(^real)|Null|Tuple(^[^$93...])|Bool<True|False>|String(^string)|Array(^[^$93...])|ArrayGen(^[^$93,^$93])>>|Tuple(^[$46...])|$130<BExpr<$41|Bool<True|False>|And(^{^$130...})|Or(^{^$130...})|Not(^$130)|Equals(^[$142<^Type<Atom<NotT($165<^Proton<TupleT(^[$165...])|ArrayT($165)|Quark<AnyT|NullT|VoidT|BoolT|IntT|RealT|StringT|VarT(^string)|NominalT(^string)>>>)|Proton<TupleT(^[$165...])|ArrayT($165)|Quark<AnyT|NullT|VoidT|BoolT|IntT|RealT|StringT|VarT(^string)|NominalT(^string)>>>|NotT($142)|OrT(^{$142...})|AndT(^{$142...})|ArrayT($142)|TupleT(^[$142...])|FunctionT(^[$142,$142,$142...])>>,^{|$46,$46|}[$46,$46]])|Inequality(^[^AType<IntT|RealT>,$3])|Equation(^[^AType<IntT|RealT>,$3])|ForAll(^[^{^[^Var(^string),$142]...},^$130])|Exists(^[^{^[^Var(^string),$142]...},^$130])>>|SExpr<$41|Array(^[$46...])|ArrayGen(^[$46,$46])>>>...])|Load(^[$46,^int])|LengthOf($46)|IndexOf(^[$46,$46])>>>>>...|}[$3<^$20<AExpr<$12|Num(^real)|Sum($10)|Div(^[$3,$3])|$41<VExpr<Var(^string)|Fn(^[^string,$46<^Expr<$20|$93<Value<Num(^real)|Null|Tuple(^[^$93...])|Bool<True|False>|String(^string)|Array(^[^$93...])|ArrayGen(^[^$93,^$93])>>|Tuple(^[$46...])|$130<BExpr<$41|Bool<True|False>|And(^{^$130...})|Or(^{^$130...})|Not(^$130)|Equals(^[$142<^Type<Atom<NotT($165<^Proton<TupleT(^[$165...])|ArrayT($165)|Quark<AnyT|NullT|VoidT|BoolT|IntT|RealT|StringT|VarT(^string)|NominalT(^string)>>>)|Proton<TupleT(^[$165...])|ArrayT($165)|Quark<AnyT|NullT|VoidT|BoolT|IntT|RealT|StringT|VarT(^string)|NominalT(^string)>>>|NotT($142)|OrT(^{$142...})|AndT(^{$142...})|ArrayT($142)|TupleT(^[$142...])|FunctionT(^[$142,$142,$142...])>>,^{|$46,$46|}[$46,$46]])|Inequality(^[^AType<IntT|RealT>,$3])|Equation(^[^AType<IntT|RealT>,$3])|ForAll(^[^{^[^Var(^string),$142]...},^$130])|Exists(^[^{^[^Var(^string),$142]...},^$130])>>|SExpr<$41|Array(^[$46...])|ArrayGen(^[$46,$46])>>>...])|Load(^[$46,^int])|LengthOf($46)|IndexOf(^[$46,$46])>>>>>...]]>)>
	public final static int K_Mul = 29;
	public final static int Mul(Automaton automaton, int... r0) {
		int r1 = automaton.add(new Automaton.List(r0));
		return automaton.add(new Automaton.Term(K_Mul, r1));
	}
	public final static int Mul(Automaton automaton, List<Integer> r0) {
		int r1 = automaton.add(new Automaton.List(r0));
		return automaton.add(new Automaton.Term(K_Mul, r1));
	}

	private final static class Reduction_53 extends AbstractRewriteRule implements ReductionRule {

		public Reduction_53(Pattern.Term pattern) {
			super(pattern);
			put("name","Mul[0.0,{||}]");
			put("rank",0);
		}

		public final void probe(Automaton automaton, int target, List<Reduction.Activation> activations) {
			int r0 = target;
			Automaton.State s0 = automaton.get(r0);
			if(s0.kind == K_Mul) {
				Automaton.Term t0 = (Automaton.Term) s0;
				int r1 = t0.contents;
				Automaton.State s1 = automaton.get(r1);
				Automaton.List l1 = (Automaton.List) s1;
				int r2 = l1.get(0);
				int r3 = l1.get(1);
				Automaton.State s3 = automaton.get(r3);
				Automaton.Collection c3 = (Automaton.Collection) s3;
				int[] c3children = new int[c3.size() - 0];
				for(int s3i=0, s3j=0; s3i != c3.size();++s3i) {
					c3children[s3j++] = c3.get(s3i);
				}
				Automaton.Bag r4 = new Automaton.Bag(c3children);
				Automaton.Real r5 = new Automaton.Real(0); // 0.0
				Automaton.Real r6 = (Automaton.Real) automaton.get(r2);
				boolean r7 = r6.equals(r5);    // n eq 0.0
				Automaton.Int r8 = r4.lengthOf(); // |rest|
				Automaton.Int r9 = new Automaton.Int(0); // 0
				boolean r10 = r8.equals(r9);   // |rest| eq 0
				boolean r11 = r7 || r10;       // n eq 0.0 || |rest| eq 0
				if(r11) { // REQUIRES
					int[] state = {r0, r1, r2, r3, 0};
					activations.add(new Reduction.Activation(this,null,state));
				}
			}
		}

		public final int apply(Automaton automaton, int[] state) {
			int nStates = automaton.nStates();
			int r0 = state[0];
			int r2 = state[2]; // n
			Automaton.Collection c3 = (Automaton.Collection) automaton.get(state[3]);
			int[] c3children = new int[c3.size() - 0];
			for(int s3i=0, s3j=0; s3i != c3.size();++s3i) {
				c3children[s3j++] = c3.get(s3i);
			}
			Automaton.Bag r4 = new Automaton.Bag(c3children);
			Automaton.Term r5 = new Automaton.Term(K_Num, r2);
			int r6 = automaton.add(r5);
			if(r0 != r6) {
				return automaton.rewrite(r0, r6);
			}
			automaton.resize(nStates);
			return Automaton.K_VOID;
		}

	}
	private final static class Reduction_54 extends AbstractRewriteRule implements ReductionRule {

		public Reduction_54(Pattern.Term pattern) {
			super(pattern);
			put("name","Mul{|Num,AExpr|}");
			put("rank",0);
		}

		public final void probe(Automaton automaton, int target, List<Reduction.Activation> activations) {
			int r0 = target;
			Automaton.State s0 = automaton.get(r0);
			if(s0.kind == K_Mul) {
				Automaton.Term t0 = (Automaton.Term) s0;
				int r1 = t0.contents;
				Automaton.State s1 = automaton.get(r1);
				Automaton.List l1 = (Automaton.List) s1;
				int r2 = l1.get(0);
				int r3 = l1.get(1);
				Automaton.State s3 = automaton.get(r3);
				Automaton.Collection c3 = (Automaton.Collection) s3;
				if(c3.size() >= 1) {
					for(int r5=0;r5!=c3.size();++r5) {
						int r4 = c3.get(r5);
						Automaton.State s4 = automaton.get(r4);
						if(s4.kind == K_Num) {
							Automaton.Term t4 = (Automaton.Term) s4;
							int r6 = t4.contents;
							int[] state = {r0, r1, r2, r3, r4, r5, r6, 0};
							activations.add(new Reduction.Activation(this,null,state));
						}
					}
				}
			}
		}

		public final int apply(Automaton automaton, int[] state) {
			int nStates = automaton.nStates();
			int r0 = state[0];
			int r2 = state[2]; // x
			int r5 = state[5];
			int r6 = state[6]; // y
			Automaton.Collection c3 = (Automaton.Collection) automaton.get(state[3]);
			int[] c3children = new int[c3.size() - 1];
			for(int s3i=0, s3j=0; s3i != c3.size();++s3i) {
				if(s3i == r5) { continue; }
				c3children[s3j++] = c3.get(s3i);
			}
			Automaton.Bag r7 = new Automaton.Bag(c3children);
			Automaton.Real r8 = (Automaton.Real) automaton.get(r2);
			Automaton.Real r9 = (Automaton.Real) automaton.get(r6);
			Automaton.Real r10 = r8.multiply(r9); // x mul y
			int r11 = automaton.add(r10);
			int r12 = automaton.add(r7);
			Automaton.List r13 = new Automaton.List(r11, r12); // [x mul yrest]
			int r14 = automaton.add(r13);
			Automaton.Term r15 = new Automaton.Term(K_Mul, r14);
			int r16 = automaton.add(r15);
			if(r0 != r16) {
				return automaton.rewrite(r0, r16);
			}
			automaton.resize(nStates);
			return Automaton.K_VOID;
		}

	}
	private final static class Reduction_55 extends AbstractRewriteRule implements ReductionRule {

		public Reduction_55(Pattern.Term pattern) {
			super(pattern);
			put("name","Mul{|Mul,AExpr...|}");
			put("rank",1);
		}

		public final void probe(Automaton automaton, int target, List<Reduction.Activation> activations) {
			int r0 = target;
			Automaton.State s0 = automaton.get(r0);
			if(s0.kind == K_Mul) {
				Automaton.Term t0 = (Automaton.Term) s0;
				int r1 = t0.contents;
				Automaton.State s1 = automaton.get(r1);
				Automaton.List l1 = (Automaton.List) s1;
				int r2 = l1.get(0);
				int r3 = l1.get(1);
				Automaton.State s3 = automaton.get(r3);
				Automaton.Collection c3 = (Automaton.Collection) s3;
				if(c3.size() >= 1) {
					for(int r5=0;r5!=c3.size();++r5) {
						int r4 = c3.get(r5);
						Automaton.State s4 = automaton.get(r4);
						if(s4.kind == K_Mul) {
							Automaton.Term t4 = (Automaton.Term) s4;
							int r6 = t4.contents;
							Automaton.State s6 = automaton.get(r6);
							Automaton.List l6 = (Automaton.List) s6;
							int r7 = l6.get(0);
							int r8 = l6.get(1);
							Automaton.State s8 = automaton.get(r8);
							Automaton.Collection c8 = (Automaton.Collection) s8;
							int[] state = {r0, r1, r2, r3, r4, r5, r6, r7, r8, 0, 0};
							activations.add(new Reduction.Activation(this,null,state));
						}
					}
				}
			}
		}

		public final int apply(Automaton automaton, int[] state) {
			int nStates = automaton.nStates();
			int r0 = state[0];
			int r2 = state[2]; // n1
			int r5 = state[5];
			int r7 = state[7]; // n2
			Automaton.Collection c8 = (Automaton.Collection) automaton.get(state[8]);
			int[] c8children = new int[c8.size() - 0];
			for(int s8i=0, s8j=0; s8i != c8.size();++s8i) {
				c8children[s8j++] = c8.get(s8i);
			}
			Automaton.Bag r9 = new Automaton.Bag(c8children);
			Automaton.Collection c3 = (Automaton.Collection) automaton.get(state[3]);
			int[] c3children = new int[c3.size() - 1];
			for(int s3i=0, s3j=0; s3i != c3.size();++s3i) {
				if(s3i == r5) { continue; }
				c3children[s3j++] = c3.get(s3i);
			}
			Automaton.Bag r10 = new Automaton.Bag(c3children);
			Automaton.Real r11 = (Automaton.Real) automaton.get(r2);
			Automaton.Real r12 = (Automaton.Real) automaton.get(r7);
			Automaton.Real r13 = r11.multiply(r12); // n1 mul n2
			int r14 = automaton.add(r13);
			Automaton.Bag r15 = r9.append(r10); // xs append ys
			int r16 = automaton.add(r15);
			Automaton.List r17 = new Automaton.List(r14, r16); // [n1 mul n2xs append ys]
			int r18 = automaton.add(r17);
			Automaton.Term r19 = new Automaton.Term(K_Mul, r18);
			int r20 = automaton.add(r19);
			if(r0 != r20) {
				return automaton.rewrite(r0, r20);
			}
			automaton.resize(nStates);
			return Automaton.K_VOID;
		}

	}
	private final static class Reduction_56 extends AbstractRewriteRule implements ReductionRule {

		public Reduction_56(Pattern.Term pattern) {
			super(pattern);
			put("name","Mul{|Sum,AExpr...|}");
			put("rank",1);
		}

		public final void probe(Automaton automaton, int target, List<Reduction.Activation> activations) {
			int r0 = target;
			Automaton.State s0 = automaton.get(r0);
			if(s0.kind == K_Mul) {
				Automaton.Term t0 = (Automaton.Term) s0;
				int r1 = t0.contents;
				Automaton.State s1 = automaton.get(r1);
				Automaton.List l1 = (Automaton.List) s1;
				int r2 = l1.get(0);
				int r3 = l1.get(1);
				Automaton.State s3 = automaton.get(r3);
				Automaton.Collection c3 = (Automaton.Collection) s3;
				if(c3.size() >= 1) {
					for(int r5=0;r5!=c3.size();++r5) {
						int r4 = c3.get(r5);
						Automaton.State s4 = automaton.get(r4);
						if(s4.kind == K_Sum) {
							Automaton.Term t4 = (Automaton.Term) s4;
							int r6 = t4.contents;
							Automaton.State s6 = automaton.get(r6);
							Automaton.List l6 = (Automaton.List) s6;
							int r7 = l6.get(0);
							int r8 = l6.get(1);
							Automaton.State s8 = automaton.get(r8);
							Automaton.Collection c8 = (Automaton.Collection) s8;
							int[] state = {r0, r1, r2, r3, r4, r5, r6, r7, r8, 0, 0};
							activations.add(new Reduction.Activation(this,null,state));
						}
					}
				}
			}
		}

		public final int apply(Automaton automaton, int[] state) {
			int nStates = automaton.nStates();
			int r0 = state[0];
			int r2 = state[2]; // n1
			int r5 = state[5];
			int r7 = state[7]; // n2
			Automaton.Collection c8 = (Automaton.Collection) automaton.get(state[8]);
			int[] c8children = new int[c8.size() - 0];
			for(int s8i=0, s8j=0; s8i != c8.size();++s8i) {
				c8children[s8j++] = c8.get(s8i);
			}
			Automaton.Bag r9 = new Automaton.Bag(c8children);
			Automaton.Collection c3 = (Automaton.Collection) automaton.get(state[3]);
			int[] c3children = new int[c3.size() - 1];
			for(int s3i=0, s3j=0; s3i != c3.size();++s3i) {
				if(s3i == r5) { continue; }
				c3children[s3j++] = c3.get(s3i);
			}
			Automaton.Bag r10 = new Automaton.Bag(c3children);
			Automaton.List t11 = new Automaton.List();
			for(int i12=0;i12<r9.size();i12++) {
				int r12 = (int) r9.get(i12);
				Automaton.Bag r13 = r10.appendFront(r12); // x append ys
				int r14 = automaton.add(r13);
				Automaton.List r15 = new Automaton.List(r2, r14); // [n1x append ys]
				int r16 = automaton.add(r15);
				Automaton.Term r17 = new Automaton.Term(K_Mul, r16);
				int r18 = automaton.add(r17);
				t11.add(r18);
			}
			Automaton.Bag r11 = new Automaton.Bag(t11.toArray());
			Automaton.Real r19 = (Automaton.Real) automaton.get(r2);
			Automaton.Real r20 = (Automaton.Real) automaton.get(r7);
			Automaton.Real r21 = r19.multiply(r20); // n1 mul n2
			int r22 = automaton.add(r21);
			int r23 = automaton.add(r10);
			Automaton.List r24 = new Automaton.List(r22, r23); // [n1 mul n2ys]
			int r25 = automaton.add(r24);
			Automaton.Term r26 = new Automaton.Term(K_Mul, r25);
			Automaton.Real r27 = new Automaton.Real(0); // 0.0
			int r28 = automaton.add(r27);
			int r29 = automaton.add(r26);
			Automaton.Bag r30 = r11.appendFront(r29); // z append zs
			int r31 = automaton.add(r30);
			Automaton.List r32 = new Automaton.List(r28, r31); // [0.0z append zs]
			int r33 = automaton.add(r32);
			Automaton.Term r34 = new Automaton.Term(K_Sum, r33);
			int r35 = automaton.add(r34);
			if(r0 != r35) {
				return automaton.rewrite(r0, r35);
			}
			automaton.resize(nStates);
			return Automaton.K_VOID;
		}

	}
	// term $8<Div(^[$2<^$16<AExpr<$8|Num(^real)|Sum(^[^real,^{|$2...|}[$2...]])|Mul(^[^real,^{|$2...|}[$2...]])|$41<VExpr<Var(^string)|Fn(^[^string,$46<^Expr<$16|$93<Value<Num(^real)|Null|Tuple(^[^$93...])|Bool<True|False>|String(^string)|Array(^[^$93...])|ArrayGen(^[^$93,^$93])>>|Tuple(^[$46...])|$130<BExpr<$41|Bool<True|False>|And(^{^$130...})|Or(^{^$130...})|Not(^$130)|Equals(^[$142<^Type<Atom<NotT($165<^Proton<TupleT(^[$165...])|ArrayT($165)|Quark<AnyT|NullT|VoidT|BoolT|IntT|RealT|StringT|VarT(^string)|NominalT(^string)>>>)|Proton<TupleT(^[$165...])|ArrayT($165)|Quark<AnyT|NullT|VoidT|BoolT|IntT|RealT|StringT|VarT(^string)|NominalT(^string)>>>|NotT($142)|OrT(^{$142...})|AndT(^{$142...})|ArrayT($142)|TupleT(^[$142...])|FunctionT(^[$142,$142,$142...])>>,^{|$46,$46|}[$46,$46]])|Inequality(^[^AType<IntT|RealT>,$2])|Equation(^[^AType<IntT|RealT>,$2])|ForAll(^[^{^[^Var(^string),$142]...},^$130])|Exists(^[^{^[^Var(^string),$142]...},^$130])>>|SExpr<$41|Array(^[$46...])|ArrayGen(^[$46,$46])>>>...])|Load(^[$46,^int])|LengthOf($46)|IndexOf(^[$46,$46])>>>>>,$2])>
	public final static int K_Div = 30;
	public final static int Div(Automaton automaton, int... r0) {
		int r1 = automaton.add(new Automaton.List(r0));
		return automaton.add(new Automaton.Term(K_Div, r1));
	}
	public final static int Div(Automaton automaton, List<Integer> r0) {
		int r1 = automaton.add(new Automaton.List(r0));
		return automaton.add(new Automaton.Term(K_Div, r1));
	}

	private final static class Reduction_57 extends AbstractRewriteRule implements ReductionRule {

		public Reduction_57(Pattern.Term pattern) {
			super(pattern);
			put("name","Div[Num,Num]");
			put("rank",0);
		}

		public final void probe(Automaton automaton, int target, List<Reduction.Activation> activations) {
			int r0 = target;
			Automaton.State s0 = automaton.get(r0);
			if(s0.kind == K_Div) {
				Automaton.Term t0 = (Automaton.Term) s0;
				int r1 = t0.contents;
				Automaton.State s1 = automaton.get(r1);
				Automaton.List l1 = (Automaton.List) s1;
				int r2 = l1.get(0);
				Automaton.State s2 = automaton.get(r2);
				if(s2.kind == K_Num) {
					Automaton.Term t2 = (Automaton.Term) s2;
					int r3 = t2.contents;
					int r4 = l1.get(1);
					Automaton.State s4 = automaton.get(r4);
					if(s4.kind == K_Num) {
						Automaton.Term t4 = (Automaton.Term) s4;
						int r5 = t4.contents;
						int[] state = {r0, r1, r2, r3, r4, r5};
						activations.add(new Reduction.Activation(this,null,state));
					}
				}
			}
		}

		public final int apply(Automaton automaton, int[] state) {
			int nStates = automaton.nStates();
			int r0 = state[0];
			int r3 = state[3]; // x
			int r5 = state[5]; // y
			Automaton.Real r6 = (Automaton.Real) automaton.get(r3);
			Automaton.Real r7 = (Automaton.Real) automaton.get(r5);
			Automaton.Real r8 = r6.divide(r7); // x div y
			int r9 = automaton.add(r8);
			Automaton.Term r10 = new Automaton.Term(K_Num, r9);
			int r11 = automaton.add(r10);
			if(r0 != r11) {
				return automaton.rewrite(r0, r11);
			}
			automaton.resize(nStates);
			return Automaton.K_VOID;
		}

	}
	private final static class Reduction_58 extends AbstractRewriteRule implements ReductionRule {

		public Reduction_58(Pattern.Term pattern) {
			super(pattern);
			put("name","Div[AExpr,Div]");
			put("rank",0);
		}

		public final void probe(Automaton automaton, int target, List<Reduction.Activation> activations) {
			int r0 = target;
			Automaton.State s0 = automaton.get(r0);
			if(s0.kind == K_Div) {
				Automaton.Term t0 = (Automaton.Term) s0;
				int r1 = t0.contents;
				Automaton.State s1 = automaton.get(r1);
				Automaton.List l1 = (Automaton.List) s1;
				int r2 = l1.get(0);
				int r3 = l1.get(1);
				Automaton.State s3 = automaton.get(r3);
				if(s3.kind == K_Div) {
					Automaton.Term t3 = (Automaton.Term) s3;
					int r4 = t3.contents;
					Automaton.State s4 = automaton.get(r4);
					Automaton.List l4 = (Automaton.List) s4;
					int r5 = l4.get(0);
					int r6 = l4.get(1);
					int[] state = {r0, r1, r2, r3, r4, r5, r6};
					activations.add(new Reduction.Activation(this,null,state));
				}
			}
		}

		public final int apply(Automaton automaton, int[] state) {
			int nStates = automaton.nStates();
			int r0 = state[0];
			int r2 = state[2]; // x
			int r5 = state[5]; // y
			int r6 = state[6]; // z
			Automaton.Real r7 = new Automaton.Real(1); // 1.0
			int r8 = automaton.add(r7);
			Automaton.Bag r9 = new Automaton.Bag(r2, r6); // {|xz|}
			int r10 = automaton.add(r9);
			Automaton.List r11 = new Automaton.List(r8, r10); // [1.0{|xz|}]
			int r12 = automaton.add(r11);
			Automaton.Term r13 = new Automaton.Term(K_Mul, r12);
			int r14 = automaton.add(r13);
			Automaton.List r15 = new Automaton.List(r14, r5); // [Mul([1.0{|xz|}])y]
			int r16 = automaton.add(r15);
			Automaton.Term r17 = new Automaton.Term(K_Div, r16);
			int r18 = automaton.add(r17);
			if(r0 != r18) {
				return automaton.rewrite(r0, r18);
			}
			automaton.resize(nStates);
			return Automaton.K_VOID;
		}

	}
	private final static class Reduction_59 extends AbstractRewriteRule implements ReductionRule {

		public Reduction_59(Pattern.Term pattern) {
			super(pattern);
			put("name","Div[Div,AExpr]");
			put("rank",0);
		}

		public final void probe(Automaton automaton, int target, List<Reduction.Activation> activations) {
			int r0 = target;
			Automaton.State s0 = automaton.get(r0);
			if(s0.kind == K_Div) {
				Automaton.Term t0 = (Automaton.Term) s0;
				int r1 = t0.contents;
				Automaton.State s1 = automaton.get(r1);
				Automaton.List l1 = (Automaton.List) s1;
				int r2 = l1.get(0);
				Automaton.State s2 = automaton.get(r2);
				if(s2.kind == K_Div) {
					Automaton.Term t2 = (Automaton.Term) s2;
					int r3 = t2.contents;
					Automaton.State s3 = automaton.get(r3);
					Automaton.List l3 = (Automaton.List) s3;
					int r4 = l3.get(0);
					int r5 = l3.get(1);
					int r6 = l1.get(1);
					int[] state = {r0, r1, r2, r3, r4, r5, r6};
					activations.add(new Reduction.Activation(this,null,state));
				}
			}
		}

		public final int apply(Automaton automaton, int[] state) {
			int nStates = automaton.nStates();
			int r0 = state[0];
			int r4 = state[4]; // x
			int r5 = state[5]; // y
			int r6 = state[6]; // z
			Automaton.Real r7 = new Automaton.Real(1); // 1.0
			int r8 = automaton.add(r7);
			Automaton.Bag r9 = new Automaton.Bag(r5, r6); // {|yz|}
			int r10 = automaton.add(r9);
			Automaton.List r11 = new Automaton.List(r8, r10); // [1.0{|yz|}]
			int r12 = automaton.add(r11);
			Automaton.Term r13 = new Automaton.Term(K_Mul, r12);
			int r14 = automaton.add(r13);
			Automaton.List r15 = new Automaton.List(r4, r14); // [xMul([1.0{|yz|}])]
			int r16 = automaton.add(r15);
			Automaton.Term r17 = new Automaton.Term(K_Div, r16);
			int r18 = automaton.add(r17);
			if(r0 != r18) {
				return automaton.rewrite(r0, r18);
			}
			automaton.resize(nStates);
			return Automaton.K_VOID;
		}

	}
	private final static class Reduction_60 extends AbstractRewriteRule implements ReductionRule {

		public Reduction_60(Pattern.Term pattern) {
			super(pattern);
			put("name","Div[AExpr,Num]");
			put("rank",1);
		}

		public final void probe(Automaton automaton, int target, List<Reduction.Activation> activations) {
			int r0 = target;
			Automaton.State s0 = automaton.get(r0);
			if(s0.kind == K_Div) {
				Automaton.Term t0 = (Automaton.Term) s0;
				int r1 = t0.contents;
				Automaton.State s1 = automaton.get(r1);
				Automaton.List l1 = (Automaton.List) s1;
				int r2 = l1.get(0);
				int r3 = l1.get(1);
				Automaton.State s3 = automaton.get(r3);
				if(s3.kind == K_Num) {
					Automaton.Term t3 = (Automaton.Term) s3;
					int r4 = t3.contents;
					Automaton.Real r5 = new Automaton.Real(0); // 0.0
					Automaton.Real r6 = (Automaton.Real) automaton.get(r4);
					boolean r7 = r6.compareTo(r5)<0; // n lt 0.0
					if(r7) { // REQUIRES
						int[] state = {r0, r1, r2, r3, r4};
						activations.add(new Reduction.Activation(this,null,state));
					}
				}
			}
		}

		public final int apply(Automaton automaton, int[] state) {
			int nStates = automaton.nStates();
			int r0 = state[0];
			int r2 = state[2]; // x
			int r4 = state[4]; // n
			Automaton.Real r5 = new Automaton.Real(1); // 1.0
			Automaton.Real r6 = r5.negate(); // -1.0
			int r7 = automaton.add(r6);
			Automaton.Bag r8 = new Automaton.Bag(r2); // {|x|}
			int r9 = automaton.add(r8);
			Automaton.List r10 = new Automaton.List(r7, r9); // [-1.0{|x|}]
			int r11 = automaton.add(r10);
			Automaton.Term r12 = new Automaton.Term(K_Mul, r11);
			int r13 = automaton.add(r12);
			Automaton.Real r14 = (Automaton.Real) automaton.get(r4);
			Automaton.Real r15 = r14.negate(); // -n
			int r16 = automaton.add(r15);
			Automaton.Term r17 = new Automaton.Term(K_Num, r16);
			int r18 = automaton.add(r17);
			Automaton.List r19 = new Automaton.List(r13, r18); // [Mul([-1.0{|x|}])Num(-n)]
			int r20 = automaton.add(r19);
			Automaton.Term r21 = new Automaton.Term(K_Div, r20);
			int r22 = automaton.add(r21);
			if(r0 != r22) {
				return automaton.rewrite(r0, r22);
			}
			automaton.resize(nStates);
			return Automaton.K_VOID;
		}

	}
	private final static class Reduction_61 extends AbstractRewriteRule implements ReductionRule {

		public Reduction_61(Pattern.Term pattern) {
			super(pattern);
			put("name","Div[AExpr,Num]");
			put("rank",1);
		}

		public final void probe(Automaton automaton, int target, List<Reduction.Activation> activations) {
			int r0 = target;
			Automaton.State s0 = automaton.get(r0);
			if(s0.kind == K_Div) {
				Automaton.Term t0 = (Automaton.Term) s0;
				int r1 = t0.contents;
				Automaton.State s1 = automaton.get(r1);
				Automaton.List l1 = (Automaton.List) s1;
				int r2 = l1.get(0);
				int r3 = l1.get(1);
				Automaton.State s3 = automaton.get(r3);
				if(s3.kind == K_Num) {
					Automaton.Term t3 = (Automaton.Term) s3;
					int r4 = t3.contents;
					Automaton.Real r5 = new Automaton.Real(1); // 1.0
					Automaton.Real r6 = (Automaton.Real) automaton.get(r4);
					boolean r7 = r6.equals(r5);    // n eq 1.0
					if(r7) { // REQUIRES
						int[] state = {r0, r1, r2, r3, r4};
						activations.add(new Reduction.Activation(this,null,state));
					}
				}
			}
		}

		public final int apply(Automaton automaton, int[] state) {
			int nStates = automaton.nStates();
			int r0 = state[0];
			int r2 = state[2]; // x
			int r4 = state[4]; // n
			if(r0 != r2) {
				return automaton.rewrite(r0, r2);
			}
			automaton.resize(nStates);
			return Automaton.K_VOID;
		}

	}
	private final static class Reduction_62 extends AbstractRewriteRule implements ReductionRule {

		public Reduction_62(Pattern.Term pattern) {
			super(pattern);
			put("name","Div[Mul,AExpr]");
			put("rank",1);
		}

		public final void probe(Automaton automaton, int target, List<Reduction.Activation> activations) {
			int r0 = target;
			Automaton.State s0 = automaton.get(r0);
			if(s0.kind == K_Div) {
				Automaton.Term t0 = (Automaton.Term) s0;
				int r1 = t0.contents;
				Automaton.State s1 = automaton.get(r1);
				Automaton.List l1 = (Automaton.List) s1;
				int r2 = l1.get(0);
				Automaton.State s2 = automaton.get(r2);
				if(s2.kind == K_Mul) {
					Automaton.Term t2 = (Automaton.Term) s2;
					int r3 = t2.contents;
					Automaton.State s3 = automaton.get(r3);
					Automaton.List l3 = (Automaton.List) s3;
					int r4 = l3.get(0);
					int r5 = l3.get(1);
					Automaton.State s5 = automaton.get(r5);
					Automaton.Collection c5 = (Automaton.Collection) s5;
					if(c5.size() >= 1) {
						for(int r7=0;r7!=c5.size();++r7) {
							int r6 = c5.get(r7);
							int r9 = l1.get(1);
							int[] c5children = new int[c5.size() - 1];
							for(int s5i=0, s5j=0; s5i != c5.size();++s5i) {
								if(s5i == r7) { continue; }
								c5children[s5j++] = c5.get(s5i);
							}
							Automaton.Bag r8 = new Automaton.Bag(c5children);
							boolean r10 = r6 == r9;        // x eq y
							if(r10) { // REQUIRES
								int[] state = {r0, r1, r2, r3, r4, r5, r6, r7, 0, r9};
								activations.add(new Reduction.Activation(this,null,state));
							}
						}
					}
				}
			}
		}

		public final int apply(Automaton automaton, int[] state) {
			int nStates = automaton.nStates();
			int r0 = state[0];
			int r4 = state[4]; // n
			int r6 = state[6]; // x
			int r7 = state[7];
			Automaton.Collection c5 = (Automaton.Collection) automaton.get(state[5]);
			int[] c5children = new int[c5.size() - 1];
			for(int s5i=0, s5j=0; s5i != c5.size();++s5i) {
				if(s5i == r7) { continue; }
				c5children[s5j++] = c5.get(s5i);
			}
			Automaton.Bag r8 = new Automaton.Bag(c5children);
			int r9 = state[9]; // y
			int r10 = automaton.add(r8);
			Automaton.List r11 = new Automaton.List(r4, r10); // [nxs]
			int r12 = automaton.add(r11);
			Automaton.Term r13 = new Automaton.Term(K_Mul, r12);
			int r14 = automaton.add(r13);
			if(r0 != r14) {
				return automaton.rewrite(r0, r14);
			}
			automaton.resize(nStates);
			return Automaton.K_VOID;
		}

	}
	private final static class Reduction_63 extends AbstractRewriteRule implements ReductionRule {

		public Reduction_63(Pattern.Term pattern) {
			super(pattern);
			put("name","Div[Mul,AExpr]");
			put("rank",1);
		}

		public final void probe(Automaton automaton, int target, List<Reduction.Activation> activations) {
			int r0 = target;
			Automaton.State s0 = automaton.get(r0);
			if(s0.kind == K_Div) {
				Automaton.Term t0 = (Automaton.Term) s0;
				int r1 = t0.contents;
				Automaton.State s1 = automaton.get(r1);
				Automaton.List l1 = (Automaton.List) s1;
				int r2 = l1.get(0);
				Automaton.State s2 = automaton.get(r2);
				if(s2.kind == K_Mul) {
					Automaton.Term t2 = (Automaton.Term) s2;
					int r3 = t2.contents;
					Automaton.State s3 = automaton.get(r3);
					Automaton.List l3 = (Automaton.List) s3;
					int r4 = l3.get(0);
					int r5 = l3.get(1);
					Automaton.State s5 = automaton.get(r5);
					Automaton.Collection c5 = (Automaton.Collection) s5;
					int r7 = l1.get(1);
					if(Runtime.accepts(type18,automaton,automaton.get(r7), SCHEMA)) {
						int[] state = {r0, r1, r2, r3, r4, r5, 0, r7};
						activations.add(new Reduction.Activation(this,null,state));
					}
				}
			}
		}

		public final int apply(Automaton automaton, int[] state) {
			int nStates = automaton.nStates();
			int r0 = state[0];
			int r4 = state[4]; // n
			Automaton.Collection c5 = (Automaton.Collection) automaton.get(state[5]);
			int[] c5children = new int[c5.size() - 0];
			for(int s5i=0, s5j=0; s5i != c5.size();++s5i) {
				c5children[s5j++] = c5.get(s5i);
			}
			Automaton.Bag r6 = new Automaton.Bag(c5children);
			int r7 = state[7]; // y
			Automaton.Term r8 = (Automaton.Term) automaton.get(r7);
			int r9 = r8.contents;
			Automaton.Real r10 = (Automaton.Real) automaton.get(r4);
			Automaton.Real r11 = (Automaton.Real) automaton.get(r9);
			Automaton.Real r12 = r10.divide(r11); // n div *y
			int r13 = automaton.add(r12);
			int r14 = automaton.add(r6);
			Automaton.List r15 = new Automaton.List(r13, r14); // [n div *yxs]
			int r16 = automaton.add(r15);
			Automaton.Term r17 = new Automaton.Term(K_Mul, r16);
			int r18 = automaton.add(r17);
			if(r0 != r18) {
				return automaton.rewrite(r0, r18);
			}
			automaton.resize(nStates);
			return Automaton.K_VOID;
		}

	}
	private final static class Reduction_64 extends AbstractRewriteRule implements ReductionRule {

		public Reduction_64(Pattern.Term pattern) {
			super(pattern);
			put("name","Div[Sum,AExpr]");
			put("rank",1);
		}

		public final void probe(Automaton automaton, int target, List<Reduction.Activation> activations) {
			int r0 = target;
			Automaton.State s0 = automaton.get(r0);
			if(s0.kind == K_Div) {
				Automaton.Term t0 = (Automaton.Term) s0;
				int r1 = t0.contents;
				Automaton.State s1 = automaton.get(r1);
				Automaton.List l1 = (Automaton.List) s1;
				int r2 = l1.get(0);
				Automaton.State s2 = automaton.get(r2);
				if(s2.kind == K_Sum) {
					Automaton.Term t2 = (Automaton.Term) s2;
					int r3 = t2.contents;
					Automaton.State s3 = automaton.get(r3);
					Automaton.List l3 = (Automaton.List) s3;
					int r4 = l3.get(0);
					int r5 = l3.get(1);
					Automaton.State s5 = automaton.get(r5);
					Automaton.Collection c5 = (Automaton.Collection) s5;
					int r7 = l1.get(1);
					int[] state = {r0, r1, r2, r3, r4, r5, 0, r7};
					activations.add(new Reduction.Activation(this,null,state));
				}
			}
		}

		public final int apply(Automaton automaton, int[] state) {
			int nStates = automaton.nStates();
			int r0 = state[0];
			int r4 = state[4]; // n
			Automaton.Collection c5 = (Automaton.Collection) automaton.get(state[5]);
			int[] c5children = new int[c5.size() - 0];
			for(int s5i=0, s5j=0; s5i != c5.size();++s5i) {
				c5children[s5j++] = c5.get(s5i);
			}
			Automaton.Bag r6 = new Automaton.Bag(c5children);
			int r7 = state[7]; // y
			Automaton.List t8 = new Automaton.List();
			for(int i9=0;i9<r6.size();i9++) {
				int r9 = (int) r6.get(i9);
				Automaton.List r10 = new Automaton.List(r9, r7); // [xy]
				int r11 = automaton.add(r10);
				Automaton.Term r12 = new Automaton.Term(K_Div, r11);
				int r13 = automaton.add(r12);
				t8.add(r13);
			}
			Automaton.Bag r8 = new Automaton.Bag(t8.toArray());
			Automaton.Real r14 = new Automaton.Real(0); // 0.0
			int r15 = automaton.add(r14);
			Automaton.Term r16 = new Automaton.Term(K_Num, r4);
			int r17 = automaton.add(r16);
			Automaton.List r18 = new Automaton.List(r17, r7); // [Num(n)y]
			int r19 = automaton.add(r18);
			Automaton.Term r20 = new Automaton.Term(K_Div, r19);
			int r21 = automaton.add(r20);
			Automaton.Bag r22 = r8.append(r21); // ys append Div([Num(n)y])
			int r23 = automaton.add(r22);
			Automaton.List r24 = new Automaton.List(r15, r23); // [0.0ys append Div([Num(n)y])]
			int r25 = automaton.add(r24);
			Automaton.Term r26 = new Automaton.Term(K_Sum, r25);
			int r27 = automaton.add(r26);
			if(r0 != r27) {
				return automaton.rewrite(r0, r27);
			}
			automaton.resize(nStates);
			return Automaton.K_VOID;
		}

	}
	private final static class Reduction_65 extends AbstractRewriteRule implements ReductionRule {

		public Reduction_65(Pattern.Term pattern) {
			super(pattern);
			put("name","Div[Mul,AExpr]");
			put("rank",1);
		}

		public final void probe(Automaton automaton, int target, List<Reduction.Activation> activations) {
			int r0 = target;
			Automaton.State s0 = automaton.get(r0);
			if(s0.kind == K_Div) {
				Automaton.Term t0 = (Automaton.Term) s0;
				int r1 = t0.contents;
				Automaton.State s1 = automaton.get(r1);
				Automaton.List l1 = (Automaton.List) s1;
				int r2 = l1.get(0);
				Automaton.State s2 = automaton.get(r2);
				if(s2.kind == K_Mul) {
					Automaton.Term t2 = (Automaton.Term) s2;
					int r3 = t2.contents;
					Automaton.State s3 = automaton.get(r3);
					Automaton.List l3 = (Automaton.List) s3;
					int r4 = l3.get(0);
					int r5 = l3.get(1);
					Automaton.State s5 = automaton.get(r5);
					Automaton.Collection c5 = (Automaton.Collection) s5;
					int r7 = l1.get(1);
					int[] state = {r0, r1, r2, r3, r4, r5, 0, r7};
					activations.add(new Reduction.Activation(this,null,state));
				}
			}
		}

		public final int apply(Automaton automaton, int[] state) {
			int nStates = automaton.nStates();
			int r0 = state[0];
			int r4 = state[4]; // n
			Automaton.Collection c5 = (Automaton.Collection) automaton.get(state[5]);
			int[] c5children = new int[c5.size() - 0];
			for(int s5i=0, s5j=0; s5i != c5.size();++s5i) {
				c5children[s5j++] = c5.get(s5i);
			}
			Automaton.Bag r6 = new Automaton.Bag(c5children);
			int r7 = state[7]; // y
			Automaton.Real r8 = new Automaton.Real(1); // 1.0
			int r9 = automaton.add(r8);
			Automaton.Term r10 = new Automaton.Term(K_Num, r9);
			int r11 = automaton.add(r10);
			Automaton.List r12 = new Automaton.List(r11, r7); // [Num(1.0)y]
			int r13 = automaton.add(r12);
			Automaton.Term r14 = new Automaton.Term(K_Div, r13);
			int r15 = automaton.add(r14);
			Automaton.Bag r16 = r6.append(r15); // xs append Div([Num(1.0)y])
			int r17 = automaton.add(r16);
			Automaton.List r18 = new Automaton.List(r4, r17); // [nxs append Div([Num(1.0)y])]
			int r19 = automaton.add(r18);
			Automaton.Term r20 = new Automaton.Term(K_Mul, r19);
			int r21 = automaton.add(r20);
			if(r0 != r21) {
				return automaton.rewrite(r0, r21);
			}
			automaton.resize(nStates);
			return Automaton.K_VOID;
		}

	}
	// term $12<Sum($10<^[^real,^{|$3<^$20<AExpr<$12|Num(^real)|Mul($10)|Div(^[$3,$3])|$41<VExpr<Var(^string)|Fn(^[^string,$46<^Expr<$20|$93<Value<Num(^real)|Null|Tuple(^[^$93...])|Bool<True|False>|String(^string)|Array(^[^$93...])|ArrayGen(^[^$93,^$93])>>|Tuple(^[$46...])|$130<BExpr<$41|Bool<True|False>|And(^{^$130...})|Or(^{^$130...})|Not(^$130)|Equals(^[$142<^Type<Atom<NotT($165<^Proton<TupleT(^[$165...])|ArrayT($165)|Quark<AnyT|NullT|VoidT|BoolT|IntT|RealT|StringT|VarT(^string)|NominalT(^string)>>>)|Proton<TupleT(^[$165...])|ArrayT($165)|Quark<AnyT|NullT|VoidT|BoolT|IntT|RealT|StringT|VarT(^string)|NominalT(^string)>>>|NotT($142)|OrT(^{$142...})|AndT(^{$142...})|ArrayT($142)|TupleT(^[$142...])|FunctionT(^[$142,$142,$142...])>>,^{|$46,$46|}[$46,$46]])|Inequality(^[^AType<IntT|RealT>,$3])|Equation(^[^AType<IntT|RealT>,$3])|ForAll(^[^{^[^Var(^string),$142]...},^$130])|Exists(^[^{^[^Var(^string),$142]...},^$130])>>|SExpr<$41|Array(^[$46...])|ArrayGen(^[$46,$46])>>>...])|Load(^[$46,^int])|LengthOf($46)|IndexOf(^[$46,$46])>>>>>...|}[$3<^$20<AExpr<$12|Num(^real)|Mul($10)|Div(^[$3,$3])|$41<VExpr<Var(^string)|Fn(^[^string,$46<^Expr<$20|$93<Value<Num(^real)|Null|Tuple(^[^$93...])|Bool<True|False>|String(^string)|Array(^[^$93...])|ArrayGen(^[^$93,^$93])>>|Tuple(^[$46...])|$130<BExpr<$41|Bool<True|False>|And(^{^$130...})|Or(^{^$130...})|Not(^$130)|Equals(^[$142<^Type<Atom<NotT($165<^Proton<TupleT(^[$165...])|ArrayT($165)|Quark<AnyT|NullT|VoidT|BoolT|IntT|RealT|StringT|VarT(^string)|NominalT(^string)>>>)|Proton<TupleT(^[$165...])|ArrayT($165)|Quark<AnyT|NullT|VoidT|BoolT|IntT|RealT|StringT|VarT(^string)|NominalT(^string)>>>|NotT($142)|OrT(^{$142...})|AndT(^{$142...})|ArrayT($142)|TupleT(^[$142...])|FunctionT(^[$142,$142,$142...])>>,^{|$46,$46|}[$46,$46]])|Inequality(^[^AType<IntT|RealT>,$3])|Equation(^[^AType<IntT|RealT>,$3])|ForAll(^[^{^[^Var(^string),$142]...},^$130])|Exists(^[^{^[^Var(^string),$142]...},^$130])>>|SExpr<$41|Array(^[$46...])|ArrayGen(^[$46,$46])>>>...])|Load(^[$46,^int])|LengthOf($46)|IndexOf(^[$46,$46])>>>>>...]]>)>
	public final static int K_Sum = 31;
	public final static int Sum(Automaton automaton, int... r0) {
		int r1 = automaton.add(new Automaton.List(r0));
		return automaton.add(new Automaton.Term(K_Sum, r1));
	}
	public final static int Sum(Automaton automaton, List<Integer> r0) {
		int r1 = automaton.add(new Automaton.List(r0));
		return automaton.add(new Automaton.Term(K_Sum, r1));
	}

	private final static class Reduction_66 extends AbstractRewriteRule implements ReductionRule {

		public Reduction_66(Pattern.Term pattern) {
			super(pattern);
			put("name","Sum{||}");
			put("rank",0);
		}

		public final void probe(Automaton automaton, int target, List<Reduction.Activation> activations) {
			int r0 = target;
			Automaton.State s0 = automaton.get(r0);
			if(s0.kind == K_Sum) {
				Automaton.Term t0 = (Automaton.Term) s0;
				int r1 = t0.contents;
				Automaton.State s1 = automaton.get(r1);
				Automaton.List l1 = (Automaton.List) s1;
				int r2 = l1.get(0);
				int r3 = l1.get(1);
				Automaton.State s3 = automaton.get(r3);
				Automaton.Collection c3 = (Automaton.Collection) s3;
				if(c3.size() == 0) {
					int[] state = {r0, r1, r2, r3};
					activations.add(new Reduction.Activation(this,null,state));
				}
			}
		}

		public final int apply(Automaton automaton, int[] state) {
			int nStates = automaton.nStates();
			int r0 = state[0];
			int r2 = state[2]; // n
			Automaton.Term r4 = new Automaton.Term(K_Num, r2);
			int r5 = automaton.add(r4);
			if(r0 != r5) {
				return automaton.rewrite(r0, r5);
			}
			automaton.resize(nStates);
			return Automaton.K_VOID;
		}

	}
	private final static class Reduction_67 extends AbstractRewriteRule implements ReductionRule {

		public Reduction_67(Pattern.Term pattern) {
			super(pattern);
			put("name","Sum{|Mul{|VExpr|}|}");
			put("rank",0);
		}

		public final void probe(Automaton automaton, int target, List<Reduction.Activation> activations) {
			int r0 = target;
			Automaton.State s0 = automaton.get(r0);
			if(s0.kind == K_Sum) {
				Automaton.Term t0 = (Automaton.Term) s0;
				int r1 = t0.contents;
				Automaton.State s1 = automaton.get(r1);
				Automaton.List l1 = (Automaton.List) s1;
				int r2 = l1.get(0);
				int r3 = l1.get(1);
				Automaton.State s3 = automaton.get(r3);
				Automaton.Collection c3 = (Automaton.Collection) s3;
				if(c3.size() == 1) {
					for(int r5=0;r5!=c3.size();++r5) {
						int r4 = c3.get(r5);
						Automaton.State s4 = automaton.get(r4);
						if(s4.kind == K_Mul) {
							Automaton.Term t4 = (Automaton.Term) s4;
							int r6 = t4.contents;
							Automaton.State s6 = automaton.get(r6);
							Automaton.List l6 = (Automaton.List) s6;
							int r7 = l6.get(0);
							int r8 = l6.get(1);
							Automaton.State s8 = automaton.get(r8);
							Automaton.Collection c8 = (Automaton.Collection) s8;
							if(c8.size() == 1) {
								for(int r10=0;r10!=c8.size();++r10) {
									int r9 = c8.get(r10);
									if(Runtime.accepts(type8,automaton,automaton.get(r9), SCHEMA)) {
										Automaton.Real r11 = new Automaton.Real(0); // 0.0
										Automaton.Real r12 = (Automaton.Real) automaton.get(r2);
										boolean r13 = r12.equals(r11); // n eq 0.0
										boolean r14 = false;           // n eq 0.0 && m eq 1.0
										if(r13) {
											Automaton.Real r15 = new Automaton.Real(1); // 1.0
											Automaton.Real r16 = (Automaton.Real) automaton.get(r7);
											boolean r17 = r16.equals(r15); // m eq 1.0
											r14 = r17;
										}
										if(r14) { // REQUIRES
											int[] state = {r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10};
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
			int r2 = state[2]; // n
			int r5 = state[5];
			int r7 = state[7]; // m
			int r9 = state[9]; // x
			int r10 = state[10];
			if(r0 != r9) {
				return automaton.rewrite(r0, r9);
			}
			automaton.resize(nStates);
			return Automaton.K_VOID;
		}

	}
	private final static class Reduction_68 extends AbstractRewriteRule implements ReductionRule {

		public Reduction_68(Pattern.Term pattern) {
			super(pattern);
			put("name","Sum{|AExpr,AExpr...|}");
			put("rank",1);
		}

		public final void probe(Automaton automaton, int target, List<Reduction.Activation> activations) {
			int r0 = target;
			Automaton.State s0 = automaton.get(r0);
			if(s0.kind == K_Sum) {
				Automaton.Term t0 = (Automaton.Term) s0;
				int r1 = t0.contents;
				Automaton.State s1 = automaton.get(r1);
				Automaton.List l1 = (Automaton.List) s1;
				int r2 = l1.get(0);
				int r3 = l1.get(1);
				Automaton.State s3 = automaton.get(r3);
				Automaton.Collection c3 = (Automaton.Collection) s3;
				if(c3.size() >= 1) {
					for(int r5=0;r5!=c3.size();++r5) {
						int r4 = c3.get(r5);
						int[] c3children = new int[c3.size() - 1];
						for(int s3i=0, s3j=0; s3i != c3.size();++s3i) {
							if(s3i == r5) { continue; }
							c3children[s3j++] = c3.get(s3i);
						}
						Automaton.Bag r6 = new Automaton.Bag(c3children);
						boolean r7 = Runtime.accepts(type19, automaton, r4, SCHEMA); // x is ^Num(^real)
						boolean r8 = Runtime.accepts(type20, automaton, r4, SCHEMA); // x is ^$13<Sum($11<^[^real,^{|$4<^$21<AExpr<$13|Num(^real)|Mul($11)|Div(^[$4,$4])|$42<VExpr<Var(^string)|Fn(^[^string,$47<^Expr<$21|$94<Value<Num(^real)|Null|Tuple(^[^$94...])|Bool<True|False>|String(^string)|Array(^[^$94...])|ArrayGen(^[^$94,^$94])>>|Tuple(^[$47...])|$131<BExpr<$42|Bool<True|False>|And(^{^$131...})|Or(^{^$131...})|Not(^$131)|Equals(^[$143<^Type<Atom<NotT($166<^Proton<TupleT(^[$166...])|ArrayT($166)|Quark<AnyT|NullT|VoidT|BoolT|IntT|RealT|StringT|VarT(^string)|NominalT(^string)>>>)|Proton<TupleT(^[$166...])|ArrayT($166)|Quark<AnyT|NullT|VoidT|BoolT|IntT|RealT|StringT|VarT(^string)|NominalT(^string)>>>|NotT($143)|OrT(^{$143...})|AndT(^{$143...})|ArrayT($143)|TupleT(^[$143...])|FunctionT(^[$143,$143,$143...])>>,^{|$47,$47|}[$47,$47]])|Inequality(^[^AType<IntT|RealT>,$4])|Equation(^[^AType<IntT|RealT>,$4])|ForAll(^[^{^[^Var(^string),$143]...},^$131])|Exists(^[^{^[^Var(^string),$143]...},^$131])>>|SExpr<$42|Array(^[$47...])|ArrayGen(^[$47,$47])>>>...])|Load(^[$47,^int])|LengthOf($47)|IndexOf(^[$47,$47])>>>>>...|}[$4<^$21<AExpr<$13|Num(^real)|Mul($11)|Div(^[$4,$4])|$42<VExpr<Var(^string)|Fn(^[^string,$47<^Expr<$21|$94<Value<Num(^real)|Null|Tuple(^[^$94...])|Bool<True|False>|String(^string)|Array(^[^$94...])|ArrayGen(^[^$94,^$94])>>|Tuple(^[$47...])|$131<BExpr<$42|Bool<True|False>|And(^{^$131...})|Or(^{^$131...})|Not(^$131)|Equals(^[$143<^Type<Atom<NotT($166<^Proton<TupleT(^[$166...])|ArrayT($166)|Quark<AnyT|NullT|VoidT|BoolT|IntT|RealT|StringT|VarT(^string)|NominalT(^string)>>>)|Proton<TupleT(^[$166...])|ArrayT($166)|Quark<AnyT|NullT|VoidT|BoolT|IntT|RealT|StringT|VarT(^string)|NominalT(^string)>>>|NotT($143)|OrT(^{$143...})|AndT(^{$143...})|ArrayT($143)|TupleT(^[$143...])|FunctionT(^[$143,$143,$143...])>>,^{|$47,$47|}[$47,$47]])|Inequality(^[^AType<IntT|RealT>,$4])|Equation(^[^AType<IntT|RealT>,$4])|ForAll(^[^{^[^Var(^string),$143]...},^$131])|Exists(^[^{^[^Var(^string),$143]...},^$131])>>|SExpr<$42|Array(^[$47...])|ArrayGen(^[$47,$47])>>>...])|Load(^[$47,^int])|LengthOf($47)|IndexOf(^[$47,$47])>>>>>...]]>)>
						boolean r9 = Runtime.accepts(type21, automaton, r4, SCHEMA); // x is ^$13<Mul($11<^[^real,^{|$4<^$21<AExpr<$13|Num(^real)|Sum($11)|Div(^[$4,$4])|$42<VExpr<Var(^string)|Fn(^[^string,$47<^Expr<$21|$94<Value<Num(^real)|Null|Tuple(^[^$94...])|Bool<True|False>|String(^string)|Array(^[^$94...])|ArrayGen(^[^$94,^$94])>>|Tuple(^[$47...])|$131<BExpr<$42|Bool<True|False>|And(^{^$131...})|Or(^{^$131...})|Not(^$131)|Equals(^[$143<^Type<Atom<NotT($166<^Proton<TupleT(^[$166...])|ArrayT($166)|Quark<AnyT|NullT|VoidT|BoolT|IntT|RealT|StringT|VarT(^string)|NominalT(^string)>>>)|Proton<TupleT(^[$166...])|ArrayT($166)|Quark<AnyT|NullT|VoidT|BoolT|IntT|RealT|StringT|VarT(^string)|NominalT(^string)>>>|NotT($143)|OrT(^{$143...})|AndT(^{$143...})|ArrayT($143)|TupleT(^[$143...])|FunctionT(^[$143,$143,$143...])>>,^{|$47,$47|}[$47,$47]])|Inequality(^[^AType<IntT|RealT>,$4])|Equation(^[^AType<IntT|RealT>,$4])|ForAll(^[^{^[^Var(^string),$143]...},^$131])|Exists(^[^{^[^Var(^string),$143]...},^$131])>>|SExpr<$42|Array(^[$47...])|ArrayGen(^[$47,$47])>>>...])|Load(^[$47,^int])|LengthOf($47)|IndexOf(^[$47,$47])>>>>>...|}[$4<^$21<AExpr<$13|Num(^real)|Sum($11)|Div(^[$4,$4])|$42<VExpr<Var(^string)|Fn(^[^string,$47<^Expr<$21|$94<Value<Num(^real)|Null|Tuple(^[^$94...])|Bool<True|False>|String(^string)|Array(^[^$94...])|ArrayGen(^[^$94,^$94])>>|Tuple(^[$47...])|$131<BExpr<$42|Bool<True|False>|And(^{^$131...})|Or(^{^$131...})|Not(^$131)|Equals(^[$143<^Type<Atom<NotT($166<^Proton<TupleT(^[$166...])|ArrayT($166)|Quark<AnyT|NullT|VoidT|BoolT|IntT|RealT|StringT|VarT(^string)|NominalT(^string)>>>)|Proton<TupleT(^[$166...])|ArrayT($166)|Quark<AnyT|NullT|VoidT|BoolT|IntT|RealT|StringT|VarT(^string)|NominalT(^string)>>>|NotT($143)|OrT(^{$143...})|AndT(^{$143...})|ArrayT($143)|TupleT(^[$143...])|FunctionT(^[$143,$143,$143...])>>,^{|$47,$47|}[$47,$47]])|Inequality(^[^AType<IntT|RealT>,$4])|Equation(^[^AType<IntT|RealT>,$4])|ForAll(^[^{^[^Var(^string),$143]...},^$131])|Exists(^[^{^[^Var(^string),$143]...},^$131])>>|SExpr<$42|Array(^[$47...])|ArrayGen(^[$47,$47])>>>...])|Load(^[$47,^int])|LengthOf($47)|IndexOf(^[$47,$47])>>>>>...]]>)>
						boolean r10 = r8 || r9;        // x is ^$13<Sum($11<^[^real,^{|$4<^$21<AExpr<$13|Num(^real)|Mul($11)|Div(^[$4,$4])|$42<VExpr<Var(^string)|Fn(^[^string,$47<^Expr<$21|$94<Value<Num(^real)|Null|Tuple(^[^$94...])|Bool<True|False>|String(^string)|Array(^[^$94...])|ArrayGen(^[^$94,^$94])>>|Tuple(^[$47...])|$131<BExpr<$42|Bool<True|False>|And(^{^$131...})|Or(^{^$131...})|Not(^$131)|Equals(^[$143<^Type<Atom<NotT($166<^Proton<TupleT(^[$166...])|ArrayT($166)|Quark<AnyT|NullT|VoidT|BoolT|IntT|RealT|StringT|VarT(^string)|NominalT(^string)>>>)|Proton<TupleT(^[$166...])|ArrayT($166)|Quark<AnyT|NullT|VoidT|BoolT|IntT|RealT|StringT|VarT(^string)|NominalT(^string)>>>|NotT($143)|OrT(^{$143...})|AndT(^{$143...})|ArrayT($143)|TupleT(^[$143...])|FunctionT(^[$143,$143,$143...])>>,^{|$47,$47|}[$47,$47]])|Inequality(^[^AType<IntT|RealT>,$4])|Equation(^[^AType<IntT|RealT>,$4])|ForAll(^[^{^[^Var(^string),$143]...},^$131])|Exists(^[^{^[^Var(^string),$143]...},^$131])>>|SExpr<$42|Array(^[$47...])|ArrayGen(^[$47,$47])>>>...])|Load(^[$47,^int])|LengthOf($47)|IndexOf(^[$47,$47])>>>>>...|}[$4<^$21<AExpr<$13|Num(^real)|Mul($11)|Div(^[$4,$4])|$42<VExpr<Var(^string)|Fn(^[^string,$47<^Expr<$21|$94<Value<Num(^real)|Null|Tuple(^[^$94...])|Bool<True|False>|String(^string)|Array(^[^$94...])|ArrayGen(^[^$94,^$94])>>|Tuple(^[$47...])|$131<BExpr<$42|Bool<True|False>|And(^{^$131...})|Or(^{^$131...})|Not(^$131)|Equals(^[$143<^Type<Atom<NotT($166<^Proton<TupleT(^[$166...])|ArrayT($166)|Quark<AnyT|NullT|VoidT|BoolT|IntT|RealT|StringT|VarT(^string)|NominalT(^string)>>>)|Proton<TupleT(^[$166...])|ArrayT($166)|Quark<AnyT|NullT|VoidT|BoolT|IntT|RealT|StringT|VarT(^string)|NominalT(^string)>>>|NotT($143)|OrT(^{$143...})|AndT(^{$143...})|ArrayT($143)|TupleT(^[$143...])|FunctionT(^[$143,$143,$143...])>>,^{|$47,$47|}[$47,$47]])|Inequality(^[^AType<IntT|RealT>,$4])|Equation(^[^AType<IntT|RealT>,$4])|ForAll(^[^{^[^Var(^string),$143]...},^$131])|Exists(^[^{^[^Var(^string),$143]...},^$131])>>|SExpr<$42|Array(^[$47...])|ArrayGen(^[$47,$47])>>>...])|Load(^[$47,^int])|LengthOf($47)|IndexOf(^[$47,$47])>>>>>...]]>)> || x is ^$13<Mul($11<^[^real,^{|$4<^$21<AExpr<$13|Num(^real)|Sum($11)|Div(^[$4,$4])|$42<VExpr<Var(^string)|Fn(^[^string,$47<^Expr<$21|$94<Value<Num(^real)|Null|Tuple(^[^$94...])|Bool<True|False>|String(^string)|Array(^[^$94...])|ArrayGen(^[^$94,^$94])>>|Tuple(^[$47...])|$131<BExpr<$42|Bool<True|False>|And(^{^$131...})|Or(^{^$131...})|Not(^$131)|Equals(^[$143<^Type<Atom<NotT($166<^Proton<TupleT(^[$166...])|ArrayT($166)|Quark<AnyT|NullT|VoidT|BoolT|IntT|RealT|StringT|VarT(^string)|NominalT(^string)>>>)|Proton<TupleT(^[$166...])|ArrayT($166)|Quark<AnyT|NullT|VoidT|BoolT|IntT|RealT|StringT|VarT(^string)|NominalT(^string)>>>|NotT($143)|OrT(^{$143...})|AndT(^{$143...})|ArrayT($143)|TupleT(^[$143...])|FunctionT(^[$143,$143,$143...])>>,^{|$47,$47|}[$47,$47]])|Inequality(^[^AType<IntT|RealT>,$4])|Equation(^[^AType<IntT|RealT>,$4])|ForAll(^[^{^[^Var(^string),$143]...},^$131])|Exists(^[^{^[^Var(^string),$143]...},^$131])>>|SExpr<$42|Array(^[$47...])|ArrayGen(^[$47,$47])>>>...])|Load(^[$47,^int])|LengthOf($47)|IndexOf(^[$47,$47])>>>>>...|}[$4<^$21<AExpr<$13|Num(^real)|Sum($11)|Div(^[$4,$4])|$42<VExpr<Var(^string)|Fn(^[^string,$47<^Expr<$21|$94<Value<Num(^real)|Null|Tuple(^[^$94...])|Bool<True|False>|String(^string)|Array(^[^$94...])|ArrayGen(^[^$94,^$94])>>|Tuple(^[$47...])|$131<BExpr<$42|Bool<True|False>|And(^{^$131...})|Or(^{^$131...})|Not(^$131)|Equals(^[$143<^Type<Atom<NotT($166<^Proton<TupleT(^[$166...])|ArrayT($166)|Quark<AnyT|NullT|VoidT|BoolT|IntT|RealT|StringT|VarT(^string)|NominalT(^string)>>>)|Proton<TupleT(^[$166...])|ArrayT($166)|Quark<AnyT|NullT|VoidT|BoolT|IntT|RealT|StringT|VarT(^string)|NominalT(^string)>>>|NotT($143)|OrT(^{$143...})|AndT(^{$143...})|ArrayT($143)|TupleT(^[$143...])|FunctionT(^[$143,$143,$143...])>>,^{|$47,$47|}[$47,$47]])|Inequality(^[^AType<IntT|RealT>,$4])|Equation(^[^AType<IntT|RealT>,$4])|ForAll(^[^{^[^Var(^string),$143]...},^$131])|Exists(^[^{^[^Var(^string),$143]...},^$131])>>|SExpr<$42|Array(^[$47...])|ArrayGen(^[$47,$47])>>>...])|Load(^[$47,^int])|LengthOf($47)|IndexOf(^[$47,$47])>>>>>...]]>)>
						boolean r11 = r7 || r10;       // x is ^Num(^real) || x is ^$13<Sum($11<^[^real,^{|$4<^$21<AExpr<$13|Num(^real)|Mul($11)|Div(^[$4,$4])|$42<VExpr<Var(^string)|Fn(^[^string,$47<^Expr<$21|$94<Value<Num(^real)|Null|Tuple(^[^$94...])|Bool<True|False>|String(^string)|Array(^[^$94...])|ArrayGen(^[^$94,^$94])>>|Tuple(^[$47...])|$131<BExpr<$42|Bool<True|False>|And(^{^$131...})|Or(^{^$131...})|Not(^$131)|Equals(^[$143<^Type<Atom<NotT($166<^Proton<TupleT(^[$166...])|ArrayT($166)|Quark<AnyT|NullT|VoidT|BoolT|IntT|RealT|StringT|VarT(^string)|NominalT(^string)>>>)|Proton<TupleT(^[$166...])|ArrayT($166)|Quark<AnyT|NullT|VoidT|BoolT|IntT|RealT|StringT|VarT(^string)|NominalT(^string)>>>|NotT($143)|OrT(^{$143...})|AndT(^{$143...})|ArrayT($143)|TupleT(^[$143...])|FunctionT(^[$143,$143,$143...])>>,^{|$47,$47|}[$47,$47]])|Inequality(^[^AType<IntT|RealT>,$4])|Equation(^[^AType<IntT|RealT>,$4])|ForAll(^[^{^[^Var(^string),$143]...},^$131])|Exists(^[^{^[^Var(^string),$143]...},^$131])>>|SExpr<$42|Array(^[$47...])|ArrayGen(^[$47,$47])>>>...])|Load(^[$47,^int])|LengthOf($47)|IndexOf(^[$47,$47])>>>>>...|}[$4<^$21<AExpr<$13|Num(^real)|Mul($11)|Div(^[$4,$4])|$42<VExpr<Var(^string)|Fn(^[^string,$47<^Expr<$21|$94<Value<Num(^real)|Null|Tuple(^[^$94...])|Bool<True|False>|String(^string)|Array(^[^$94...])|ArrayGen(^[^$94,^$94])>>|Tuple(^[$47...])|$131<BExpr<$42|Bool<True|False>|And(^{^$131...})|Or(^{^$131...})|Not(^$131)|Equals(^[$143<^Type<Atom<NotT($166<^Proton<TupleT(^[$166...])|ArrayT($166)|Quark<AnyT|NullT|VoidT|BoolT|IntT|RealT|StringT|VarT(^string)|NominalT(^string)>>>)|Proton<TupleT(^[$166...])|ArrayT($166)|Quark<AnyT|NullT|VoidT|BoolT|IntT|RealT|StringT|VarT(^string)|NominalT(^string)>>>|NotT($143)|OrT(^{$143...})|AndT(^{$143...})|ArrayT($143)|TupleT(^[$143...])|FunctionT(^[$143,$143,$143...])>>,^{|$47,$47|}[$47,$47]])|Inequality(^[^AType<IntT|RealT>,$4])|Equation(^[^AType<IntT|RealT>,$4])|ForAll(^[^{^[^Var(^string),$143]...},^$131])|Exists(^[^{^[^Var(^string),$143]...},^$131])>>|SExpr<$42|Array(^[$47...])|ArrayGen(^[$47,$47])>>>...])|Load(^[$47,^int])|LengthOf($47)|IndexOf(^[$47,$47])>>>>>...]]>)> || x is ^$13<Mul($11<^[^real,^{|$4<^$21<AExpr<$13|Num(^real)|Sum($11)|Div(^[$4,$4])|$42<VExpr<Var(^string)|Fn(^[^string,$47<^Expr<$21|$94<Value<Num(^real)|Null|Tuple(^[^$94...])|Bool<True|False>|String(^string)|Array(^[^$94...])|ArrayGen(^[^$94,^$94])>>|Tuple(^[$47...])|$131<BExpr<$42|Bool<True|False>|And(^{^$131...})|Or(^{^$131...})|Not(^$131)|Equals(^[$143<^Type<Atom<NotT($166<^Proton<TupleT(^[$166...])|ArrayT($166)|Quark<AnyT|NullT|VoidT|BoolT|IntT|RealT|StringT|VarT(^string)|NominalT(^string)>>>)|Proton<TupleT(^[$166...])|ArrayT($166)|Quark<AnyT|NullT|VoidT|BoolT|IntT|RealT|StringT|VarT(^string)|NominalT(^string)>>>|NotT($143)|OrT(^{$143...})|AndT(^{$143...})|ArrayT($143)|TupleT(^[$143...])|FunctionT(^[$143,$143,$143...])>>,^{|$47,$47|}[$47,$47]])|Inequality(^[^AType<IntT|RealT>,$4])|Equation(^[^AType<IntT|RealT>,$4])|ForAll(^[^{^[^Var(^string),$143]...},^$131])|Exists(^[^{^[^Var(^string),$143]...},^$131])>>|SExpr<$42|Array(^[$47...])|ArrayGen(^[$47,$47])>>>...])|Load(^[$47,^int])|LengthOf($47)|IndexOf(^[$47,$47])>>>>>...|}[$4<^$21<AExpr<$13|Num(^real)|Sum($11)|Div(^[$4,$4])|$42<VExpr<Var(^string)|Fn(^[^string,$47<^Expr<$21|$94<Value<Num(^real)|Null|Tuple(^[^$94...])|Bool<True|False>|String(^string)|Array(^[^$94...])|ArrayGen(^[^$94,^$94])>>|Tuple(^[$47...])|$131<BExpr<$42|Bool<True|False>|And(^{^$131...})|Or(^{^$131...})|Not(^$131)|Equals(^[$143<^Type<Atom<NotT($166<^Proton<TupleT(^[$166...])|ArrayT($166)|Quark<AnyT|NullT|VoidT|BoolT|IntT|RealT|StringT|VarT(^string)|NominalT(^string)>>>)|Proton<TupleT(^[$166...])|ArrayT($166)|Quark<AnyT|NullT|VoidT|BoolT|IntT|RealT|StringT|VarT(^string)|NominalT(^string)>>>|NotT($143)|OrT(^{$143...})|AndT(^{$143...})|ArrayT($143)|TupleT(^[$143...])|FunctionT(^[$143,$143,$143...])>>,^{|$47,$47|}[$47,$47]])|Inequality(^[^AType<IntT|RealT>,$4])|Equation(^[^AType<IntT|RealT>,$4])|ForAll(^[^{^[^Var(^string),$143]...},^$131])|Exists(^[^{^[^Var(^string),$143]...},^$131])>>|SExpr<$42|Array(^[$47...])|ArrayGen(^[$47,$47])>>>...])|Load(^[$47,^int])|LengthOf($47)|IndexOf(^[$47,$47])>>>>>...]]>)>
						boolean r12 = !r11;            // !x is ^Num(^real) || x is ^$13<Sum($11<^[^real,^{|$4<^$21<AExpr<$13|Num(^real)|Mul($11)|Div(^[$4,$4])|$42<VExpr<Var(^string)|Fn(^[^string,$47<^Expr<$21|$94<Value<Num(^real)|Null|Tuple(^[^$94...])|Bool<True|False>|String(^string)|Array(^[^$94...])|ArrayGen(^[^$94,^$94])>>|Tuple(^[$47...])|$131<BExpr<$42|Bool<True|False>|And(^{^$131...})|Or(^{^$131...})|Not(^$131)|Equals(^[$143<^Type<Atom<NotT($166<^Proton<TupleT(^[$166...])|ArrayT($166)|Quark<AnyT|NullT|VoidT|BoolT|IntT|RealT|StringT|VarT(^string)|NominalT(^string)>>>)|Proton<TupleT(^[$166...])|ArrayT($166)|Quark<AnyT|NullT|VoidT|BoolT|IntT|RealT|StringT|VarT(^string)|NominalT(^string)>>>|NotT($143)|OrT(^{$143...})|AndT(^{$143...})|ArrayT($143)|TupleT(^[$143...])|FunctionT(^[$143,$143,$143...])>>,^{|$47,$47|}[$47,$47]])|Inequality(^[^AType<IntT|RealT>,$4])|Equation(^[^AType<IntT|RealT>,$4])|ForAll(^[^{^[^Var(^string),$143]...},^$131])|Exists(^[^{^[^Var(^string),$143]...},^$131])>>|SExpr<$42|Array(^[$47...])|ArrayGen(^[$47,$47])>>>...])|Load(^[$47,^int])|LengthOf($47)|IndexOf(^[$47,$47])>>>>>...|}[$4<^$21<AExpr<$13|Num(^real)|Mul($11)|Div(^[$4,$4])|$42<VExpr<Var(^string)|Fn(^[^string,$47<^Expr<$21|$94<Value<Num(^real)|Null|Tuple(^[^$94...])|Bool<True|False>|String(^string)|Array(^[^$94...])|ArrayGen(^[^$94,^$94])>>|Tuple(^[$47...])|$131<BExpr<$42|Bool<True|False>|And(^{^$131...})|Or(^{^$131...})|Not(^$131)|Equals(^[$143<^Type<Atom<NotT($166<^Proton<TupleT(^[$166...])|ArrayT($166)|Quark<AnyT|NullT|VoidT|BoolT|IntT|RealT|StringT|VarT(^string)|NominalT(^string)>>>)|Proton<TupleT(^[$166...])|ArrayT($166)|Quark<AnyT|NullT|VoidT|BoolT|IntT|RealT|StringT|VarT(^string)|NominalT(^string)>>>|NotT($143)|OrT(^{$143...})|AndT(^{$143...})|ArrayT($143)|TupleT(^[$143...])|FunctionT(^[$143,$143,$143...])>>,^{|$47,$47|}[$47,$47]])|Inequality(^[^AType<IntT|RealT>,$4])|Equation(^[^AType<IntT|RealT>,$4])|ForAll(^[^{^[^Var(^string),$143]...},^$131])|Exists(^[^{^[^Var(^string),$143]...},^$131])>>|SExpr<$42|Array(^[$47...])|ArrayGen(^[$47,$47])>>>...])|Load(^[$47,^int])|LengthOf($47)|IndexOf(^[$47,$47])>>>>>...]]>)> || x is ^$13<Mul($11<^[^real,^{|$4<^$21<AExpr<$13|Num(^real)|Sum($11)|Div(^[$4,$4])|$42<VExpr<Var(^string)|Fn(^[^string,$47<^Expr<$21|$94<Value<Num(^real)|Null|Tuple(^[^$94...])|Bool<True|False>|String(^string)|Array(^[^$94...])|ArrayGen(^[^$94,^$94])>>|Tuple(^[$47...])|$131<BExpr<$42|Bool<True|False>|And(^{^$131...})|Or(^{^$131...})|Not(^$131)|Equals(^[$143<^Type<Atom<NotT($166<^Proton<TupleT(^[$166...])|ArrayT($166)|Quark<AnyT|NullT|VoidT|BoolT|IntT|RealT|StringT|VarT(^string)|NominalT(^string)>>>)|Proton<TupleT(^[$166...])|ArrayT($166)|Quark<AnyT|NullT|VoidT|BoolT|IntT|RealT|StringT|VarT(^string)|NominalT(^string)>>>|NotT($143)|OrT(^{$143...})|AndT(^{$143...})|ArrayT($143)|TupleT(^[$143...])|FunctionT(^[$143,$143,$143...])>>,^{|$47,$47|}[$47,$47]])|Inequality(^[^AType<IntT|RealT>,$4])|Equation(^[^AType<IntT|RealT>,$4])|ForAll(^[^{^[^Var(^string),$143]...},^$131])|Exists(^[^{^[^Var(^string),$143]...},^$131])>>|SExpr<$42|Array(^[$47...])|ArrayGen(^[$47,$47])>>>...])|Load(^[$47,^int])|LengthOf($47)|IndexOf(^[$47,$47])>>>>>...|}[$4<^$21<AExpr<$13|Num(^real)|Sum($11)|Div(^[$4,$4])|$42<VExpr<Var(^string)|Fn(^[^string,$47<^Expr<$21|$94<Value<Num(^real)|Null|Tuple(^[^$94...])|Bool<True|False>|String(^string)|Array(^[^$94...])|ArrayGen(^[^$94,^$94])>>|Tuple(^[$47...])|$131<BExpr<$42|Bool<True|False>|And(^{^$131...})|Or(^{^$131...})|Not(^$131)|Equals(^[$143<^Type<Atom<NotT($166<^Proton<TupleT(^[$166...])|ArrayT($166)|Quark<AnyT|NullT|VoidT|BoolT|IntT|RealT|StringT|VarT(^string)|NominalT(^string)>>>)|Proton<TupleT(^[$166...])|ArrayT($166)|Quark<AnyT|NullT|VoidT|BoolT|IntT|RealT|StringT|VarT(^string)|NominalT(^string)>>>|NotT($143)|OrT(^{$143...})|AndT(^{$143...})|ArrayT($143)|TupleT(^[$143...])|FunctionT(^[$143,$143,$143...])>>,^{|$47,$47|}[$47,$47]])|Inequality(^[^AType<IntT|RealT>,$4])|Equation(^[^AType<IntT|RealT>,$4])|ForAll(^[^{^[^Var(^string),$143]...},^$131])|Exists(^[^{^[^Var(^string),$143]...},^$131])>>|SExpr<$42|Array(^[$47...])|ArrayGen(^[$47,$47])>>>...])|Load(^[$47,^int])|LengthOf($47)|IndexOf(^[$47,$47])>>>>>...]]>)>
						if(r12) { // REQUIRES
							int[] state = {r0, r1, r2, r3, r4, r5, 0};
							activations.add(new Reduction.Activation(this,null,state));
						}
					}
				}
			}
		}

		public final int apply(Automaton automaton, int[] state) {
			int nStates = automaton.nStates();
			int r0 = state[0];
			int r2 = state[2]; // n
			int r4 = state[4]; // x
			int r5 = state[5];
			Automaton.Collection c3 = (Automaton.Collection) automaton.get(state[3]);
			int[] c3children = new int[c3.size() - 1];
			for(int s3i=0, s3j=0; s3i != c3.size();++s3i) {
				if(s3i == r5) { continue; }
				c3children[s3j++] = c3.get(s3i);
			}
			Automaton.Bag r6 = new Automaton.Bag(c3children);
			Automaton.Real r7 = new Automaton.Real(1); // 1.0
			int r8 = automaton.add(r7);
			Automaton.Bag r9 = new Automaton.Bag(r4); // {|x|}
			int r10 = automaton.add(r9);
			Automaton.List r11 = new Automaton.List(r8, r10); // [1.0{|x|}]
			int r12 = automaton.add(r11);
			Automaton.Term r13 = new Automaton.Term(K_Mul, r12);
			int r14 = automaton.add(r13);
			Automaton.Bag r15 = r6.appendFront(r14); // Mul([1.0{|x|}]) append rest
			int r16 = automaton.add(r15);
			Automaton.List r17 = new Automaton.List(r2, r16); // [nMul([1.0{|x|}]) append rest]
			int r18 = automaton.add(r17);
			Automaton.Term r19 = new Automaton.Term(K_Sum, r18);
			int r20 = automaton.add(r19);
			if(r0 != r20) {
				return automaton.rewrite(r0, r20);
			}
			automaton.resize(nStates);
			return Automaton.K_VOID;
		}

	}
	private final static class Reduction_69 extends AbstractRewriteRule implements ReductionRule {

		public Reduction_69(Pattern.Term pattern) {
			super(pattern);
			put("name","Sum{|Num,AExpr...|}");
			put("rank",1);
		}

		public final void probe(Automaton automaton, int target, List<Reduction.Activation> activations) {
			int r0 = target;
			Automaton.State s0 = automaton.get(r0);
			if(s0.kind == K_Sum) {
				Automaton.Term t0 = (Automaton.Term) s0;
				int r1 = t0.contents;
				Automaton.State s1 = automaton.get(r1);
				Automaton.List l1 = (Automaton.List) s1;
				int r2 = l1.get(0);
				int r3 = l1.get(1);
				Automaton.State s3 = automaton.get(r3);
				Automaton.Collection c3 = (Automaton.Collection) s3;
				if(c3.size() >= 1) {
					for(int r5=0;r5!=c3.size();++r5) {
						int r4 = c3.get(r5);
						Automaton.State s4 = automaton.get(r4);
						if(s4.kind == K_Num) {
							Automaton.Term t4 = (Automaton.Term) s4;
							int r6 = t4.contents;
							int[] state = {r0, r1, r2, r3, r4, r5, r6, 0};
							activations.add(new Reduction.Activation(this,null,state));
						}
					}
				}
			}
		}

		public final int apply(Automaton automaton, int[] state) {
			int nStates = automaton.nStates();
			int r0 = state[0];
			int r2 = state[2]; // x
			int r5 = state[5];
			int r6 = state[6]; // y
			Automaton.Collection c3 = (Automaton.Collection) automaton.get(state[3]);
			int[] c3children = new int[c3.size() - 1];
			for(int s3i=0, s3j=0; s3i != c3.size();++s3i) {
				if(s3i == r5) { continue; }
				c3children[s3j++] = c3.get(s3i);
			}
			Automaton.Bag r7 = new Automaton.Bag(c3children);
			Automaton.Real r8 = (Automaton.Real) automaton.get(r2);
			Automaton.Real r9 = (Automaton.Real) automaton.get(r6);
			Automaton.Real r10 = r8.add(r9); // x add y
			int r11 = automaton.add(r10);
			int r12 = automaton.add(r7);
			Automaton.List r13 = new Automaton.List(r11, r12); // [x add yrest]
			int r14 = automaton.add(r13);
			Automaton.Term r15 = new Automaton.Term(K_Sum, r14);
			int r16 = automaton.add(r15);
			if(r0 != r16) {
				return automaton.rewrite(r0, r16);
			}
			automaton.resize(nStates);
			return Automaton.K_VOID;
		}

	}
	private final static class Reduction_70 extends AbstractRewriteRule implements ReductionRule {

		public Reduction_70(Pattern.Term pattern) {
			super(pattern);
			put("name","Sum{|Mul,Mul,AExpr|}");
			put("rank",2);
		}

		public final void probe(Automaton automaton, int target, List<Reduction.Activation> activations) {
			int r0 = target;
			Automaton.State s0 = automaton.get(r0);
			if(s0.kind == K_Sum) {
				Automaton.Term t0 = (Automaton.Term) s0;
				int r1 = t0.contents;
				Automaton.State s1 = automaton.get(r1);
				Automaton.List l1 = (Automaton.List) s1;
				int r2 = l1.get(0);
				int r3 = l1.get(1);
				Automaton.State s3 = automaton.get(r3);
				Automaton.Collection c3 = (Automaton.Collection) s3;
				if(c3.size() >= 2) {
					for(int r5=0;r5!=c3.size();++r5) {
						int r4 = c3.get(r5);
						Automaton.State s4 = automaton.get(r4);
						if(s4.kind == K_Mul) {
							Automaton.Term t4 = (Automaton.Term) s4;
							int r6 = t4.contents;
							Automaton.State s6 = automaton.get(r6);
							Automaton.List l6 = (Automaton.List) s6;
							int r7 = l6.get(0);
							int r8 = l6.get(1);
							Automaton.State s8 = automaton.get(r8);
							Automaton.Collection c8 = (Automaton.Collection) s8;
							for(int r11=0;r11!=c3.size();++r11) {
								if(r11 == r5) { continue; }
								int r10 = c3.get(r11);
								Automaton.State s10 = automaton.get(r10);
								if(s10.kind == K_Mul) {
									Automaton.Term t10 = (Automaton.Term) s10;
									int r12 = t10.contents;
									Automaton.State s12 = automaton.get(r12);
									Automaton.List l12 = (Automaton.List) s12;
									int r13 = l12.get(0);
									int r14 = l12.get(1);
									Automaton.State s14 = automaton.get(r14);
									Automaton.Collection c14 = (Automaton.Collection) s14;
									int[] c3children = new int[c3.size() - 2];
									for(int s3i=0, s3j=0; s3i != c3.size();++s3i) {
										if(s3i == r5 || s3i == r11) { continue; }
										c3children[s3j++] = c3.get(s3i);
									}
									Automaton.Bag r16 = new Automaton.Bag(c3children);
									boolean r17 = r8 == r14;       // xs eq ys
									if(r17) { // REQUIRES
										int[] state = {r0, r1, r2, r3, r4, r5, r6, r7, r8, 0, r10, r11, r12, r13, r14, 0, 0};
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
			int r2 = state[2]; // n
			int r5 = state[5];
			int r7 = state[7]; // x
			int r8 = state[8]; // xs
			int r11 = state[11];
			int r13 = state[13]; // y
			int r14 = state[14]; // ys
			Automaton.Collection c3 = (Automaton.Collection) automaton.get(state[3]);
			int[] c3children = new int[c3.size() - 2];
			for(int s3i=0, s3j=0; s3i != c3.size();++s3i) {
				if(s3i == r5 || s3i == r11) { continue; }
				c3children[s3j++] = c3.get(s3i);
			}
			Automaton.Bag r16 = new Automaton.Bag(c3children);
			Automaton.Real r17 = (Automaton.Real) automaton.get(r7);
			Automaton.Real r18 = (Automaton.Real) automaton.get(r13);
			Automaton.Real r19 = r17.add(r18); // x add y
			int r20 = automaton.add(r19);
			Automaton.List r21 = new Automaton.List(r20, r8); // [x add yxs]
			int r22 = automaton.add(r21);
			Automaton.Term r23 = new Automaton.Term(K_Mul, r22);
			int r24 = automaton.add(r23);
			Automaton.Bag r25 = r16.appendFront(r24); // Mul([x add yxs]) append zs
			int r26 = automaton.add(r25);
			Automaton.List r27 = new Automaton.List(r2, r26); // [nMul([x add yxs]) append zs]
			int r28 = automaton.add(r27);
			Automaton.Term r29 = new Automaton.Term(K_Sum, r28);
			int r30 = automaton.add(r29);
			if(r0 != r30) {
				return automaton.rewrite(r0, r30);
			}
			automaton.resize(nStates);
			return Automaton.K_VOID;
		}

	}
	private final static class Reduction_71 extends AbstractRewriteRule implements ReductionRule {

		public Reduction_71(Pattern.Term pattern) {
			super(pattern);
			put("name","Sum{|Sum,AExpr|}");
			put("rank",2);
		}

		public final void probe(Automaton automaton, int target, List<Reduction.Activation> activations) {
			int r0 = target;
			Automaton.State s0 = automaton.get(r0);
			if(s0.kind == K_Sum) {
				Automaton.Term t0 = (Automaton.Term) s0;
				int r1 = t0.contents;
				Automaton.State s1 = automaton.get(r1);
				Automaton.List l1 = (Automaton.List) s1;
				int r2 = l1.get(0);
				int r3 = l1.get(1);
				Automaton.State s3 = automaton.get(r3);
				Automaton.Collection c3 = (Automaton.Collection) s3;
				if(c3.size() >= 1) {
					for(int r5=0;r5!=c3.size();++r5) {
						int r4 = c3.get(r5);
						Automaton.State s4 = automaton.get(r4);
						if(s4.kind == K_Sum) {
							Automaton.Term t4 = (Automaton.Term) s4;
							int r6 = t4.contents;
							Automaton.State s6 = automaton.get(r6);
							Automaton.List l6 = (Automaton.List) s6;
							int r7 = l6.get(0);
							int r8 = l6.get(1);
							Automaton.State s8 = automaton.get(r8);
							Automaton.Collection c8 = (Automaton.Collection) s8;
							int[] state = {r0, r1, r2, r3, r4, r5, r6, r7, r8, 0, 0};
							activations.add(new Reduction.Activation(this,null,state));
						}
					}
				}
			}
		}

		public final int apply(Automaton automaton, int[] state) {
			int nStates = automaton.nStates();
			int r0 = state[0];
			int r2 = state[2]; // x
			int r5 = state[5];
			int r7 = state[7]; // y
			Automaton.Collection c8 = (Automaton.Collection) automaton.get(state[8]);
			int[] c8children = new int[c8.size() - 0];
			for(int s8i=0, s8j=0; s8i != c8.size();++s8i) {
				c8children[s8j++] = c8.get(s8i);
			}
			Automaton.Bag r9 = new Automaton.Bag(c8children);
			Automaton.Collection c3 = (Automaton.Collection) automaton.get(state[3]);
			int[] c3children = new int[c3.size() - 1];
			for(int s3i=0, s3j=0; s3i != c3.size();++s3i) {
				if(s3i == r5) { continue; }
				c3children[s3j++] = c3.get(s3i);
			}
			Automaton.Bag r10 = new Automaton.Bag(c3children);
			Automaton.Real r11 = (Automaton.Real) automaton.get(r2);
			Automaton.Real r12 = (Automaton.Real) automaton.get(r7);
			Automaton.Real r13 = r11.add(r12); // x add y
			int r14 = automaton.add(r13);
			Automaton.Bag r15 = r10.append(r9); // xs append ys
			int r16 = automaton.add(r15);
			Automaton.List r17 = new Automaton.List(r14, r16); // [x add yxs append ys]
			int r18 = automaton.add(r17);
			Automaton.Term r19 = new Automaton.Term(K_Sum, r18);
			int r20 = automaton.add(r19);
			if(r0 != r20) {
				return automaton.rewrite(r0, r20);
			}
			automaton.resize(nStates);
			return Automaton.K_VOID;
		}

	}
	// term $10<Equation($8<^[^AType<IntT|RealT>,$4<^$29<AExpr<Num(^real)|Sum(^[^real,^{|$4...|}[$4...]])|Mul(^[^real,^{|$4...|}[$4...]])|Div(^[$4,$4])|$60<VExpr<Var(^string)|Fn(^[^string,$65<^Expr<$29|$112<Value<Num(^real)|Null|Tuple(^[^$112...])|Bool<True|False>|String(^string)|Array(^[^$112...])|ArrayGen(^[^$112,^$112])>>|Tuple(^[$65...])|$148<BExpr<$60|Bool<True|False>|And(^{^$148...})|Or(^{^$148...})|Not(^$148)|Equals(^[$160<^Type<Atom<NotT($183<^Proton<TupleT(^[$183...])|ArrayT($183)|Quark<IntT|RealT|AnyT|NullT|VoidT|BoolT|StringT|VarT(^string)|NominalT(^string)>>>)|Proton<TupleT(^[$183...])|ArrayT($183)|Quark<IntT|RealT|AnyT|NullT|VoidT|BoolT|StringT|VarT(^string)|NominalT(^string)>>>|NotT($160)|OrT(^{$160...})|AndT(^{$160...})|ArrayT($160)|TupleT(^[$160...])|FunctionT(^[$160,$160,$160...])>>,^{|$65,$65|}[$65,$65]])|$10|Inequality($8)|ForAll(^[^{^[^Var(^string),$160]...},^$148])|Exists(^[^{^[^Var(^string),$160]...},^$148])>>|SExpr<$60|Array(^[$65...])|ArrayGen(^[$65,$65])>>>...])|Load(^[$65,^int])|LengthOf($65)|IndexOf(^[$65,$65])>>>>>]>)>
	public final static int K_Equation = 32;
	public final static int Equation(Automaton automaton, int... r0) {
		int r1 = automaton.add(new Automaton.List(r0));
		return automaton.add(new Automaton.Term(K_Equation, r1));
	}
	public final static int Equation(Automaton automaton, List<Integer> r0) {
		int r1 = automaton.add(new Automaton.List(r0));
		return automaton.add(new Automaton.Term(K_Equation, r1));
	}

	private final static class Reduction_72 extends AbstractRewriteRule implements ReductionRule {

		public Reduction_72(Pattern.Term pattern) {
			super(pattern);
			put("name","Equation[Num]");
			put("rank",0);
		}

		public final void probe(Automaton automaton, int target, List<Reduction.Activation> activations) {
			int r0 = target;
			Automaton.State s0 = automaton.get(r0);
			if(s0.kind == K_Equation) {
				Automaton.Term t0 = (Automaton.Term) s0;
				int r1 = t0.contents;
				Automaton.State s1 = automaton.get(r1);
				Automaton.List l1 = (Automaton.List) s1;
				int r2 = l1.get(0);
				int r3 = l1.get(1);
				Automaton.State s3 = automaton.get(r3);
				if(s3.kind == K_Num) {
					Automaton.Term t3 = (Automaton.Term) s3;
					int r4 = t3.contents;
					int[] state = {r0, r1, r2, r3, r4};
					activations.add(new Reduction.Activation(this,null,state));
				}
			}
		}

		public final int apply(Automaton automaton, int[] state) {
			int nStates = automaton.nStates();
			int r0 = state[0];
			int r4 = state[4]; // v
			Automaton.Real r5 = new Automaton.Real(0); // 0.0
			Automaton.Real r6 = (Automaton.Real) automaton.get(r4);
			boolean r7 = !r6.equals(r5);   // v neq 0.0
			if(r7) {
				Automaton.Term r8 = False;
				int r9 = automaton.add(r8);
				if(r0 != r9) {
					return automaton.rewrite(r0, r9);
				}
			}
			Automaton.Term r10 = True;
			int r11 = automaton.add(r10);
			if(r0 != r11) {
				return automaton.rewrite(r0, r11);
			}
			automaton.resize(nStates);
			return Automaton.K_VOID;
		}

	}
	private final static class Reduction_73 extends AbstractRewriteRule implements ReductionRule {

		public Reduction_73(Pattern.Term pattern) {
			super(pattern);
			put("name","Equation[Sum{|Mul[-m,{|AExpr...|}]]");
			put("rank",1);
		}

		public final void probe(Automaton automaton, int target, List<Reduction.Activation> activations) {
			int r0 = target;
			Automaton.State s0 = automaton.get(r0);
			if(s0.kind == K_Equation) {
				Automaton.Term t0 = (Automaton.Term) s0;
				int r1 = t0.contents;
				Automaton.State s1 = automaton.get(r1);
				Automaton.List l1 = (Automaton.List) s1;
				int r2 = l1.get(0);
				int r3 = l1.get(1);
				Automaton.State s3 = automaton.get(r3);
				if(s3.kind == K_Sum) {
					Automaton.Term t3 = (Automaton.Term) s3;
					int r4 = t3.contents;
					Automaton.State s4 = automaton.get(r4);
					Automaton.List l4 = (Automaton.List) s4;
					int r5 = l4.get(0);
					int r6 = l4.get(1);
					Automaton.State s6 = automaton.get(r6);
					Automaton.Collection c6 = (Automaton.Collection) s6;
					if(c6.size() == 1) {
						for(int r8=0;r8!=c6.size();++r8) {
							int r7 = c6.get(r8);
							Automaton.State s7 = automaton.get(r7);
							if(s7.kind == K_Mul) {
								Automaton.Term t7 = (Automaton.Term) s7;
								int r9 = t7.contents;
								Automaton.State s9 = automaton.get(r9);
								Automaton.List l9 = (Automaton.List) s9;
								int r10 = l9.get(0);
								int r11 = l9.get(1);
								Automaton.State s11 = automaton.get(r11);
								Automaton.Collection c11 = (Automaton.Collection) s11;
								int[] c11children = new int[c11.size() - 0];
								for(int s11i=0, s11j=0; s11i != c11.size();++s11i) {
									c11children[s11j++] = c11.get(s11i);
								}
								Automaton.Bag r12 = new Automaton.Bag(c11children);
								Automaton.Real r13 = new Automaton.Real(0); // 0.0
								Automaton.Real r14 = (Automaton.Real) automaton.get(r5);
								boolean r15 = r14.equals(r13); // n eq 0.0
								boolean r16 = false;           // n eq 0.0 && m lt 0.0
								if(r15) {
									Automaton.Real r17 = new Automaton.Real(0); // 0.0
									Automaton.Real r18 = (Automaton.Real) automaton.get(r10);
									boolean r19 = r18.compareTo(r17)<0; // m lt 0.0
									r16 = r19;
								}
								if(r16) { // REQUIRES
									int[] state = {r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, 0};
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
			int r2 = state[2]; // t
			int r5 = state[5]; // n
			int r8 = state[8];
			int r10 = state[10]; // m
			Automaton.Collection c11 = (Automaton.Collection) automaton.get(state[11]);
			int[] c11children = new int[c11.size() - 0];
			for(int s11i=0, s11j=0; s11i != c11.size();++s11i) {
				c11children[s11j++] = c11.get(s11i);
			}
			Automaton.Bag r12 = new Automaton.Bag(c11children);
			Automaton.Real r13 = (Automaton.Real) automaton.get(r10);
			Automaton.Real r14 = r13.negate(); // -m
			int r15 = automaton.add(r14);
			int r16 = automaton.add(r12);
			Automaton.List r17 = new Automaton.List(r15, r16); // [-mxs]
			int r18 = automaton.add(r17);
			Automaton.Term r19 = new Automaton.Term(K_Mul, r18);
			int r20 = automaton.add(r19);
			Automaton.Bag r21 = new Automaton.Bag(r20); // {|Mul([-mxs])|}
			int r22 = automaton.add(r21);
			Automaton.List r23 = new Automaton.List(r5, r22); // [n{|Mul([-mxs])|}]
			int r24 = automaton.add(r23);
			Automaton.Term r25 = new Automaton.Term(K_Sum, r24);
			int r26 = automaton.add(r25);
			Automaton.List r27 = new Automaton.List(r2, r26); // [tSum([n{|Mul([-mxs])|}])]
			int r28 = automaton.add(r27);
			Automaton.Term r29 = new Automaton.Term(K_Equation, r28);
			int r30 = automaton.add(r29);
			if(r0 != r30) {
				return automaton.rewrite(r0, r30);
			}
			automaton.resize(nStates);
			return Automaton.K_VOID;
		}

	}
	private final static class Reduction_74 extends AbstractRewriteRule implements ReductionRule {

		public Reduction_74(Pattern.Term pattern) {
			super(pattern);
			put("name","Equation[Sum{|Mul|}]");
			put("rank",2);
		}

		public final void probe(Automaton automaton, int target, List<Reduction.Activation> activations) {
			int r0 = target;
			Automaton.State s0 = automaton.get(r0);
			if(s0.kind == K_Equation) {
				Automaton.Term t0 = (Automaton.Term) s0;
				int r1 = t0.contents;
				Automaton.State s1 = automaton.get(r1);
				Automaton.List l1 = (Automaton.List) s1;
				int r2 = l1.get(0);
				int r3 = l1.get(1);
				Automaton.State s3 = automaton.get(r3);
				if(s3.kind == K_Sum) {
					Automaton.Term t3 = (Automaton.Term) s3;
					int r4 = t3.contents;
					Automaton.State s4 = automaton.get(r4);
					Automaton.List l4 = (Automaton.List) s4;
					int r5 = l4.get(0);
					int r6 = l4.get(1);
					Automaton.State s6 = automaton.get(r6);
					Automaton.Collection c6 = (Automaton.Collection) s6;
					boolean m6_0 = true;
					for(int i7=0;i7!=c6.size();++i7) {
						int r7 = c6.get(i7);
						if(Runtime.accepts(type23,automaton,automaton.get(r7), SCHEMA)) {
							continue;
						}
						m6_0 = false;
						break;
					}
					if(m6_0) {
						int[] state = {r0, r1, r2, r3, r4, r5, r6, 0};
						activations.add(new Reduction.Activation(this,null,state));
					}
				}
			}
		}

		public final int apply(Automaton automaton, int[] state) {
			int nStates = automaton.nStates();
			int r0 = state[0];
			int r2 = state[2]; // t
			int r5 = state[5]; // n
			int r6 = state[6]; // ms
			Automaton.Collection c6 = (Automaton.Collection) automaton.get(state[6]);
			int[] c6children = new int[c6.size() - 0];
			for(int s6i=0, s6j=0; s6i != c6.size();++s6i) {
				c6children[s6j++] = c6.get(s6i);
			}
			Automaton.Bag r7 = new Automaton.Bag(c6children);
			Automaton.List r8 = new Automaton.List(r5, r6); // [nms]
			Automaton.Real r9 = Solver$native.gcd(automaton, r8);
			Automaton.Int r10 = r7.lengthOf(); // |xs|
			Automaton.Int r11 = new Automaton.Int(0); // 0
			boolean r12 = r10.compareTo(r11)>0; // |xs| gt 0
			boolean r13 = false;           // |xs| gt 0 && gcd neq 1.0
			if(r12) {
				Automaton.Real r14 = new Automaton.Real(1); // 1.0
				boolean r15 = !r9.equals(r14); // gcd neq 1.0
				r13 = r15;
			}
			if(r13) {
				Automaton.List t16 = new Automaton.List();
				for(int i17=0;i17<r7.size();i17++) {
					int r17 = (int) r7.get(i17);
					Automaton.Term r18 = (Automaton.Term) automaton.get(r17);
					int r19 = r18.contents;
					Automaton.Int r20 = new Automaton.Int(0); // 0
					Automaton.List r21 = (Automaton.List) automaton.get(r19);
					int r22 = r21.indexOf(r20);    // *x[0]
					Automaton.Real r23 = (Automaton.Real) automaton.get(r22);
					Automaton.Real r24 = r23.divide(r9); // *x[0] div gcd
					int r25 = automaton.add(r24);
					Automaton.Term r26 = (Automaton.Term) automaton.get(r17);
					int r27 = r26.contents;
					Automaton.Int r28 = new Automaton.Int(1); // 1
					Automaton.List r29 = (Automaton.List) automaton.get(r27);
					int r30 = r29.indexOf(r28);    // *x[1]
					Automaton.List r31 = new Automaton.List(r25, r30); // [*x[0] div gcd*x[1]]
					int r32 = automaton.add(r31);
					Automaton.Term r33 = new Automaton.Term(K_Mul, r32);
					int r34 = automaton.add(r33);
					t16.add(r34);
				}
				Automaton.Bag r16 = new Automaton.Bag(t16.toArray());
				Automaton.Real r35 = (Automaton.Real) automaton.get(r5);
				Automaton.Real r36 = r35.divide(r9); // n div gcd
				int r37 = automaton.add(r36);
				int r38 = automaton.add(r16);
				Automaton.List r39 = new Automaton.List(r37, r38); // [n div gcdys]
				int r40 = automaton.add(r39);
				Automaton.Term r41 = new Automaton.Term(K_Sum, r40);
				int r42 = automaton.add(r41);
				Automaton.List r43 = new Automaton.List(r2, r42); // [tSum([n div gcdys])]
				int r44 = automaton.add(r43);
				Automaton.Term r45 = new Automaton.Term(K_Equation, r44);
				int r46 = automaton.add(r45);
				if(r0 != r46) {
					return automaton.rewrite(r0, r46);
				}
			}
			automaton.resize(nStates);
			return Automaton.K_VOID;
		}

	}
	private final static class Reduction_75 extends AbstractRewriteRule implements ReductionRule {

		public Reduction_75(Pattern.Term pattern) {
			super(pattern);
			put("name","Equation[Sum{|Mul,Mul|}]");
			put("rank",1);
		}

		public final void probe(Automaton automaton, int target, List<Reduction.Activation> activations) {
			int r0 = target;
			Automaton.State s0 = automaton.get(r0);
			if(s0.kind == K_And) {
				Automaton.Term t0 = (Automaton.Term) s0;
				int r1 = t0.contents;
				Automaton.State s1 = automaton.get(r1);
				Automaton.Collection c1 = (Automaton.Collection) s1;
				if(c1.size() >= 1) {
					for(int r3=0;r3!=c1.size();++r3) {
						int r2 = c1.get(r3);
						Automaton.State s2 = automaton.get(r2);
						if(s2.kind == K_Equation) {
							Automaton.Term t2 = (Automaton.Term) s2;
							int r4 = t2.contents;
							Automaton.State s4 = automaton.get(r4);
							Automaton.List l4 = (Automaton.List) s4;
							int r5 = l4.get(0);
							int r6 = l4.get(1);
							Automaton.State s6 = automaton.get(r6);
							if(s6.kind == K_Sum) {
								Automaton.Term t6 = (Automaton.Term) s6;
								int r7 = t6.contents;
								Automaton.State s7 = automaton.get(r7);
								Automaton.List l7 = (Automaton.List) s7;
								int r8 = l7.get(0);
								int r9 = l7.get(1);
								Automaton.State s9 = automaton.get(r9);
								Automaton.Collection c9 = (Automaton.Collection) s9;
								if(c9.size() >= 1) {
									for(int r11=0;r11!=c9.size();++r11) {
										int r10 = c9.get(r11);
										Automaton.State s10 = automaton.get(r10);
										if(s10.kind == K_Mul) {
											Automaton.Term t10 = (Automaton.Term) s10;
											int r12 = t10.contents;
											Automaton.State s12 = automaton.get(r12);
											Automaton.List l12 = (Automaton.List) s12;
											int r13 = l12.get(0);
											int r14 = l12.get(1);
											Automaton.State s14 = automaton.get(r14);
											Automaton.Collection c14 = (Automaton.Collection) s14;
											if(c14.size() == 1) {
												for(int r16=0;r16!=c14.size();++r16) {
													int r15 = c14.get(r16);
													boolean m9_1 = true;
													for(int i17=0;i17!=c9.size();++i17) {
														if(i17 == r11) { continue; }
														int r17 = c9.get(i17);
														if(Runtime.accepts(type23,automaton,automaton.get(r17), SCHEMA)) {
															continue;
														}
														m9_1 = false;
														break;
													}
													if(m9_1) {
														int[] state = {r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, 0, 0};
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
				}
			}
		}

		public final int apply(Automaton automaton, int[] state) {
			int nStates = automaton.nStates();
			int r0 = state[0];
			int r2 = state[2]; // eq
			int r3 = state[3];
			int r5 = state[5]; // t
			int r8 = state[8]; // c
			int r9 = state[9]; // xs
			int r11 = state[11];
			int r13 = state[13]; // vc
			int r15 = state[15]; // v
			int r16 = state[16];
			Automaton.Collection c9 = (Automaton.Collection) automaton.get(state[9]);
			int[] c9children = new int[c9.size() - 1];
			for(int s9i=0, s9j=0; s9i != c9.size();++s9i) {
				if(s9i == r11) { continue; }
				c9children[s9j++] = c9.get(s9i);
			}
			Automaton.Bag r17 = new Automaton.Bag(c9children);
			Automaton.Collection c1 = (Automaton.Collection) automaton.get(state[1]);
			int[] c1children = new int[c1.size() - 1];
			for(int s1i=0, s1j=0; s1i != c1.size();++s1i) {
				if(s1i == r3) { continue; }
				c1children[s1j++] = c1.get(s1i);
			}
			Automaton.Set r18 = new Automaton.Set(c1children);
			Automaton.Term r19 = Solver$native.maxMultiplicand(automaton, r9);
			Object r20 = (Object) automaton.get(r15);
			boolean r21 = r20.equals(r19); // v eq var
			boolean r22 = false;           // v eq var && wyrl.core.Expr$Comprehension@1ba9117e
			if(r21) {
				Automaton.List t23 = new Automaton.List();
				boolean r23 = true;
				outer:
				for(int i24=0;i24<r17.size();i24++) {
					int r24 = (int) r17.get(i24);
					Automaton.Term r25 = (Automaton.Term) automaton.get(r24);
					int r26 = r25.contents;
					Automaton.Int r27 = new Automaton.Int(1); // 1
					Automaton.List r28 = (Automaton.List) automaton.get(r26);
					int r29 = r28.indexOf(r27);    // *m[1]
					Automaton.Bag r30 = (Automaton.Bag) automaton.get(r29);
					boolean r31 = r30.contains(r15); // v in *m[1]
					if(r31) {
						r23 = false;
						break outer;
					}
				}
				r22 = r23;
			}
			if(r22) {
				Automaton.Real r32 = new Automaton.Real(0); // 0.0
				int r33 = automaton.add(r32);
				Automaton.Real r34 = new Automaton.Real(1); // 1.0
				Automaton.Real r35 = r34.negate(); // -1.0
				int r36 = automaton.add(r35);
				int r37 = automaton.add(r17);
				Automaton.List r38 = new Automaton.List(r8, r37); // [cms]
				int r39 = automaton.add(r38);
				Automaton.Term r40 = new Automaton.Term(K_Sum, r39);
				int r41 = automaton.add(r40);
				Automaton.Bag r42 = new Automaton.Bag(r41); // {|Sum([cms])|}
				int r43 = automaton.add(r42);
				Automaton.List r44 = new Automaton.List(r36, r43); // [-1.0{|Sum([cms])|}]
				int r45 = automaton.add(r44);
				Automaton.Term r46 = new Automaton.Term(K_Mul, r45);
				int r47 = automaton.add(r46);
				Automaton.Term r48 = new Automaton.Term(K_Num, r13);
				int r49 = automaton.add(r48);
				Automaton.List r50 = new Automaton.List(r47, r49); // [Mul([-1.0{|Sum([cms])|}])Num(vc)]
				int r51 = automaton.add(r50);
				Automaton.Term r52 = new Automaton.Term(K_Div, r51);
				int r53 = automaton.add(r52);
				Automaton.Bag r54 = new Automaton.Bag(r53); // {|Div([Mul([-1.0{|Sum([cms])|}])Num(vc)])|}
				int r55 = automaton.add(r54);
				Automaton.List r56 = new Automaton.List(r33, r55); // [0.0{|Div([Mul([-1.0{|Sum([cms])|}])Num(vc)])|}]
				int r57 = automaton.add(r56);
				Automaton.Term r58 = new Automaton.Term(K_Sum, r57);
				Automaton.List t59 = new Automaton.List();
				for(int i60=0;i60<r18.size();i60++) {
					int r60 = (int) r18.get(i60);
					int r61 = automaton.add(r19);
					int r62 = automaton.add(r58);
					int r63 = automaton.substitute(r60, r61, r62);
					t59.add(r63);
				}
				Automaton.Set r59 = new Automaton.Set(t59.toArray());
				Automaton.Set r64 = r59.appendFront(r2); // eq append cs
				int r65 = automaton.add(r64);
				Automaton.Term r66 = new Automaton.Term(K_And, r65);
				int r67 = automaton.add(r66);
				if(r0 != r67) {
					return automaton.rewrite(r0, r67);
				}
			}
			automaton.resize(nStates);
			return Automaton.K_VOID;
		}

	}
	private final static class Inference_1 extends AbstractRewriteRule implements InferenceRule {

		public Inference_1(Pattern.Term pattern) {
			super(pattern);
			put("name","And{Equation[VExpr],BExpr...}");
			put("rank",1);
		}

		public final void probe(Automaton automaton, int root, int target, List<Inference.Activation> activations) {
			int r0 = target;
			Automaton.State s0 = automaton.get(r0);
			if(s0.kind == K_And) {
				Automaton.Term t0 = (Automaton.Term) s0;
				int r1 = t0.contents;
				Automaton.State s1 = automaton.get(r1);
				Automaton.Collection c1 = (Automaton.Collection) s1;
				if(c1.size() >= 1) {
					for(int r3=0;r3!=c1.size();++r3) {
						int r2 = c1.get(r3);
						Automaton.State s2 = automaton.get(r2);
						if(s2.kind == K_Equation) {
							Automaton.Term t2 = (Automaton.Term) s2;
							int r4 = t2.contents;
							Automaton.State s4 = automaton.get(r4);
							Automaton.List l4 = (Automaton.List) s4;
							int r5 = l4.get(0);
							int r6 = l4.get(1);
							if(Runtime.accepts(type8,automaton,automaton.get(r6), SCHEMA)) {
								int[] state = {r0, r1, r2, r3, r4, r5, r6, 0};
								activations.add(new Inference.Activation(this,root,null,state));
							}
						}
					}
				}
			}
		}

		public final int apply(Automaton automaton, int root, int[] state) {
			int nStates = automaton.nStates();
			int r0 = state[0];
			int r2 = state[2]; // eq
			int r3 = state[3];
			int r5 = state[5]; // t
			int r6 = state[6]; // v
			Automaton.Collection c1 = (Automaton.Collection) automaton.get(state[1]);
			int[] c1children = new int[c1.size() - 1];
			for(int s1i=0, s1j=0; s1i != c1.size();++s1i) {
				if(s1i == r3) { continue; }
				c1children[s1j++] = c1.get(s1i);
			}
			Automaton.Set r7 = new Automaton.Set(c1children);
			Automaton.List t8 = new Automaton.List();
			for(int i9=0;i9<r7.size();i9++) {
				int r9 = (int) r7.get(i9);
				Automaton.Real r10 = new Automaton.Real(0); // 0.0
				int r11 = automaton.add(r10);
				Automaton.Term r12 = new Automaton.Term(K_Num, r11);
				int r13 = automaton.add(r12);
				int r14 = automaton.substitute(r9, r6, r13);
				t8.add(r14);
			}
			Automaton.Set r8 = new Automaton.Set(t8.toArray());
			Automaton.Set r15 = r8.appendFront(r2); // eq append cs
			int r16 = automaton.add(r15);
			Automaton.Term r17 = new Automaton.Term(K_And, r16);
			int r18 = automaton.add(r17);
			if(r0 != r18) {
				return automaton.substitute(root,r0, r18);
			}
			automaton.resize(nStates);
			return Automaton.K_VOID;
		}

	}
	private final static class Reduction_76 extends AbstractRewriteRule implements ReductionRule {

		public Reduction_76(Pattern.Term pattern) {
			super(pattern);
			put("name","Not(Equation[IntT,AExpr])");
			put("rank",1);
		}

		public final void probe(Automaton automaton, int target, List<Reduction.Activation> activations) {
			int r0 = target;
			Automaton.State s0 = automaton.get(r0);
			if(s0.kind == K_Not) {
				Automaton.Term t0 = (Automaton.Term) s0;
				int r1 = t0.contents;
				Automaton.State s1 = automaton.get(r1);
				if(s1.kind == K_Equation) {
					Automaton.Term t1 = (Automaton.Term) s1;
					int r2 = t1.contents;
					Automaton.State s2 = automaton.get(r2);
					Automaton.List l2 = (Automaton.List) s2;
					int r3 = l2.get(0);
					if(Runtime.accepts(type24,automaton,automaton.get(r3), SCHEMA)) {
						int r4 = l2.get(1);
						int[] state = {r0, r1, r2, r3, r4};
						activations.add(new Reduction.Activation(this,null,state));
					}
				}
			}
		}

		public final int apply(Automaton automaton, int[] state) {
			int nStates = automaton.nStates();
			int r0 = state[0];
			int r3 = state[3]; // t
			int r4 = state[4]; // e
			Automaton.Real r5 = new Automaton.Real(1); // 1.0
			Automaton.Real r6 = r5.negate(); // -1.0
			int r7 = automaton.add(r6);
			Automaton.Real r8 = new Automaton.Real(1); // 1.0
			Automaton.Real r9 = r8.negate(); // -1.0
			int r10 = automaton.add(r9);
			Automaton.Bag r11 = new Automaton.Bag(r4); // {|e|}
			int r12 = automaton.add(r11);
			Automaton.List r13 = new Automaton.List(r10, r12); // [-1.0{|e|}]
			int r14 = automaton.add(r13);
			Automaton.Term r15 = new Automaton.Term(K_Mul, r14);
			int r16 = automaton.add(r15);
			Automaton.Bag r17 = new Automaton.Bag(r16); // {|Mul([-1.0{|e|}])|}
			int r18 = automaton.add(r17);
			Automaton.List r19 = new Automaton.List(r7, r18); // [-1.0{|Mul([-1.0{|e|}])|}]
			int r20 = automaton.add(r19);
			Automaton.Term r21 = new Automaton.Term(K_Sum, r20);
			Automaton.Real r22 = new Automaton.Real(1); // 1.0
			Automaton.Real r23 = r22.negate(); // -1.0
			int r24 = automaton.add(r23);
			Automaton.Bag r25 = new Automaton.Bag(r4); // {|e|}
			int r26 = automaton.add(r25);
			Automaton.List r27 = new Automaton.List(r24, r26); // [-1.0{|e|}]
			int r28 = automaton.add(r27);
			Automaton.Term r29 = new Automaton.Term(K_Sum, r28);
			int r30 = automaton.add(r21);
			Automaton.List r31 = new Automaton.List(r3, r30); // [tneg_em1]
			int r32 = automaton.add(r31);
			Automaton.Term r33 = new Automaton.Term(K_Inequality, r32);
			int r34 = automaton.add(r33);
			int r35 = automaton.add(r29);
			Automaton.List r36 = new Automaton.List(r3, r35); // [tem1]
			int r37 = automaton.add(r36);
			Automaton.Term r38 = new Automaton.Term(K_Inequality, r37);
			int r39 = automaton.add(r38);
			Automaton.Set r40 = new Automaton.Set(r34, r39); // {Inequality([tneg_em1])Inequality([tem1])}
			int r41 = automaton.add(r40);
			Automaton.Term r42 = new Automaton.Term(K_Or, r41);
			int r43 = automaton.add(r42);
			if(r0 != r43) {
				return automaton.rewrite(r0, r43);
			}
			automaton.resize(nStates);
			return Automaton.K_VOID;
		}

	}
	private final static class Reduction_77 extends AbstractRewriteRule implements ReductionRule {

		public Reduction_77(Pattern.Term pattern) {
			super(pattern);
			put("name","Not(Equation[RealT,AExpr])");
			put("rank",1);
		}

		public final void probe(Automaton automaton, int target, List<Reduction.Activation> activations) {
			int r0 = target;
			Automaton.State s0 = automaton.get(r0);
			if(s0.kind == K_Not) {
				Automaton.Term t0 = (Automaton.Term) s0;
				int r1 = t0.contents;
				Automaton.State s1 = automaton.get(r1);
				if(s1.kind == K_Equation) {
					Automaton.Term t1 = (Automaton.Term) s1;
					int r2 = t1.contents;
					Automaton.State s2 = automaton.get(r2);
					Automaton.List l2 = (Automaton.List) s2;
					int r3 = l2.get(0);
					if(Runtime.accepts(type25,automaton,automaton.get(r3), SCHEMA)) {
						int r4 = l2.get(1);
						int[] state = {r0, r1, r2, r3, r4};
						activations.add(new Reduction.Activation(this,null,state));
					}
				}
			}
		}

		public final int apply(Automaton automaton, int[] state) {
			int nStates = automaton.nStates();
			int r0 = state[0];
			int r3 = state[3]; // t
			int r4 = state[4]; // e
			Automaton.Real r5 = new Automaton.Real(1); // 1.0
			Automaton.Real r6 = r5.negate(); // -1.0
			int r7 = automaton.add(r6);
			Automaton.Bag r8 = new Automaton.Bag(r4); // {|e|}
			int r9 = automaton.add(r8);
			Automaton.List r10 = new Automaton.List(r7, r9); // [-1.0{|e|}]
			int r11 = automaton.add(r10);
			Automaton.Term r12 = new Automaton.Term(K_Mul, r11);
			int r13 = automaton.add(r12);
			Automaton.List r14 = new Automaton.List(r3, r13); // [tneg_e]
			int r15 = automaton.add(r14);
			Automaton.Term r16 = new Automaton.Term(K_Inequality, r15);
			int r17 = automaton.add(r16);
			Automaton.List r18 = new Automaton.List(r3, r4); // [te]
			int r19 = automaton.add(r18);
			Automaton.Term r20 = new Automaton.Term(K_Inequality, r19);
			int r21 = automaton.add(r20);
			Automaton.Set r22 = new Automaton.Set(r17, r21); // {Inequality([tneg_e])Inequality([te])}
			int r23 = automaton.add(r22);
			Automaton.Term r24 = new Automaton.Term(K_Or, r23);
			int r25 = automaton.add(r24);
			if(r0 != r25) {
				return automaton.rewrite(r0, r25);
			}
			automaton.resize(nStates);
			return Automaton.K_VOID;
		}

	}
	private final static class Reduction_78 extends AbstractRewriteRule implements ReductionRule {

		public Reduction_78(Pattern.Term pattern) {
			super(pattern);
			put("name","Equals{|AExpr,AExpr|}");
			put("rank",1);
		}

		public final void probe(Automaton automaton, int target, List<Reduction.Activation> activations) {
			int r0 = target;
			Automaton.State s0 = automaton.get(r0);
			if(s0.kind == K_Equals) {
				Automaton.Term t0 = (Automaton.Term) s0;
				int r1 = t0.contents;
				Automaton.State s1 = automaton.get(r1);
				Automaton.List l1 = (Automaton.List) s1;
				int r2 = l1.get(0);
				if(Runtime.accepts(type22,automaton,automaton.get(r2), SCHEMA)) {
					int r3 = l1.get(1);
					Automaton.State s3 = automaton.get(r3);
					Automaton.Collection c3 = (Automaton.Collection) s3;
					for(int r5=0;r5!=c3.size();++r5) {
						int r4 = c3.get(r5);
						if(Runtime.accepts(type17,automaton,automaton.get(r4), SCHEMA)) {
							for(int r7=0;r7!=c3.size();++r7) {
								if(r7 == r5) { continue; }
								int r6 = c3.get(r7);
								if(Runtime.accepts(type17,automaton,automaton.get(r6), SCHEMA)) {
									int[] state = {r0, r1, r2, r3, r4, r5, r6, r7};
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
			int r2 = state[2]; // t
			int r4 = state[4]; // e1
			int r5 = state[5];
			int r6 = state[6]; // e2
			int r7 = state[7];
			Automaton.Real r8 = new Automaton.Real(1); // 1.0
			Automaton.Real r9 = r8.negate(); // -1.0
			int r10 = automaton.add(r9);
			Automaton.Bag r11 = new Automaton.Bag(r4); // {|e1|}
			int r12 = automaton.add(r11);
			Automaton.List r13 = new Automaton.List(r10, r12); // [-1.0{|e1|}]
			int r14 = automaton.add(r13);
			Automaton.Term r15 = new Automaton.Term(K_Mul, r14);
			Automaton.Real r16 = new Automaton.Real(0); // 0.0
			int r17 = automaton.add(r16);
			int r18 = automaton.add(r15);
			Automaton.Bag r19 = new Automaton.Bag(r18, r6); // {|neg_e1e2|}
			int r20 = automaton.add(r19);
			Automaton.List r21 = new Automaton.List(r17, r20); // [0.0{|neg_e1e2|}]
			int r22 = automaton.add(r21);
			Automaton.Term r23 = new Automaton.Term(K_Sum, r22);
			int r24 = automaton.add(r23);
			Automaton.List r25 = new Automaton.List(r2, r24); // [tSum([0.0{|neg_e1e2|}])]
			int r26 = automaton.add(r25);
			Automaton.Term r27 = new Automaton.Term(K_Equation, r26);
			int r28 = automaton.add(r27);
			if(r0 != r28) {
				return automaton.rewrite(r0, r28);
			}
			automaton.resize(nStates);
			return Automaton.K_VOID;
		}

	}
	// term $10<Inequality($8<^[^AType<IntT|RealT>,$4<^$29<AExpr<Num(^real)|Sum(^[^real,^{|$4...|}[$4...]])|Mul(^[^real,^{|$4...|}[$4...]])|Div(^[$4,$4])|$60<VExpr<Var(^string)|Fn(^[^string,$65<^Expr<$29|$112<Value<Num(^real)|Null|Tuple(^[^$112...])|Bool<True|False>|String(^string)|Array(^[^$112...])|ArrayGen(^[^$112,^$112])>>|Tuple(^[$65...])|$148<BExpr<$60|Bool<True|False>|And(^{^$148...})|Or(^{^$148...})|Not(^$148)|Equals(^[$160<^Type<Atom<NotT($183<^Proton<TupleT(^[$183...])|ArrayT($183)|Quark<IntT|RealT|AnyT|NullT|VoidT|BoolT|StringT|VarT(^string)|NominalT(^string)>>>)|Proton<TupleT(^[$183...])|ArrayT($183)|Quark<IntT|RealT|AnyT|NullT|VoidT|BoolT|StringT|VarT(^string)|NominalT(^string)>>>|NotT($160)|OrT(^{$160...})|AndT(^{$160...})|ArrayT($160)|TupleT(^[$160...])|FunctionT(^[$160,$160,$160...])>>,^{|$65,$65|}[$65,$65]])|$10|Equation($8)|ForAll(^[^{^[^Var(^string),$160]...},^$148])|Exists(^[^{^[^Var(^string),$160]...},^$148])>>|SExpr<$60|Array(^[$65...])|ArrayGen(^[$65,$65])>>>...])|Load(^[$65,^int])|LengthOf($65)|IndexOf(^[$65,$65])>>>>>]>)>
	public final static int K_Inequality = 33;
	public final static int Inequality(Automaton automaton, int... r0) {
		int r1 = automaton.add(new Automaton.List(r0));
		return automaton.add(new Automaton.Term(K_Inequality, r1));
	}
	public final static int Inequality(Automaton automaton, List<Integer> r0) {
		int r1 = automaton.add(new Automaton.List(r0));
		return automaton.add(new Automaton.Term(K_Inequality, r1));
	}

	private final static class Reduction_79 extends AbstractRewriteRule implements ReductionRule {

		public Reduction_79(Pattern.Term pattern) {
			super(pattern);
			put("name","Inequality[Num]");
			put("rank",0);
		}

		public final void probe(Automaton automaton, int target, List<Reduction.Activation> activations) {
			int r0 = target;
			Automaton.State s0 = automaton.get(r0);
			if(s0.kind == K_Inequality) {
				Automaton.Term t0 = (Automaton.Term) s0;
				int r1 = t0.contents;
				Automaton.State s1 = automaton.get(r1);
				Automaton.List l1 = (Automaton.List) s1;
				int r2 = l1.get(0);
				int r3 = l1.get(1);
				Automaton.State s3 = automaton.get(r3);
				if(s3.kind == K_Num) {
					Automaton.Term t3 = (Automaton.Term) s3;
					int r4 = t3.contents;
					int[] state = {r0, r1, r2, r3, r4};
					activations.add(new Reduction.Activation(this,null,state));
				}
			}
		}

		public final int apply(Automaton automaton, int[] state) {
			int nStates = automaton.nStates();
			int r0 = state[0];
			int r2 = state[2]; // t
			int r4 = state[4]; // v
			Automaton.Real r5 = new Automaton.Real(0); // 0.0
			Automaton.Real r6 = (Automaton.Real) automaton.get(r4);
			boolean r7 = r6.compareTo(r5)<0; // v lt 0.0
			if(r7) {
				Automaton.Term r8 = False;
				int r9 = automaton.add(r8);
				if(r0 != r9) {
					return automaton.rewrite(r0, r9);
				}
			}
			Automaton.Real r10 = new Automaton.Real(0); // 0.0
			Automaton.Real r11 = (Automaton.Real) automaton.get(r4);
			boolean r12 = r11.equals(r10); // v eq 0.0
			boolean r13 = false;           // v eq 0.0 && t eq RealT
			if(r12) {
				Automaton.Term r14 = RealT;
				Object r15 = (Object) automaton.get(r2);
				boolean r16 = r15.equals(r14); // t eq RealT
				r13 = r16;
			}
			if(r13) {
				Automaton.Term r17 = False;
				int r18 = automaton.add(r17);
				if(r0 != r18) {
					return automaton.rewrite(r0, r18);
				}
			}
			Automaton.Term r19 = True;
			int r20 = automaton.add(r19);
			if(r0 != r20) {
				return automaton.rewrite(r0, r20);
			}
			automaton.resize(nStates);
			return Automaton.K_VOID;
		}

	}
	private final static class Reduction_80 extends AbstractRewriteRule implements ReductionRule {

		public Reduction_80(Pattern.Term pattern) {
			super(pattern);
			put("name","Not(Inequality)");
			put("rank",1);
		}

		public final void probe(Automaton automaton, int target, List<Reduction.Activation> activations) {
			int r0 = target;
			Automaton.State s0 = automaton.get(r0);
			if(s0.kind == K_Not) {
				Automaton.Term t0 = (Automaton.Term) s0;
				int r1 = t0.contents;
				Automaton.State s1 = automaton.get(r1);
				if(s1.kind == K_Inequality) {
					Automaton.Term t1 = (Automaton.Term) s1;
					int r2 = t1.contents;
					Automaton.State s2 = automaton.get(r2);
					Automaton.List l2 = (Automaton.List) s2;
					int r3 = l2.get(0);
					if(Runtime.accepts(type24,automaton,automaton.get(r3), SCHEMA)) {
						int r4 = l2.get(1);
						int[] state = {r0, r1, r2, r3, r4};
						activations.add(new Reduction.Activation(this,null,state));
					}
				}
			}
		}

		public final int apply(Automaton automaton, int[] state) {
			int nStates = automaton.nStates();
			int r0 = state[0];
			int r3 = state[3]; // t
			int r4 = state[4]; // e
			Automaton.Real r5 = new Automaton.Real(1); // 1.0
			Automaton.Real r6 = r5.negate(); // -1.0
			int r7 = automaton.add(r6);
			Automaton.Bag r8 = new Automaton.Bag(r4); // {|e|}
			int r9 = automaton.add(r8);
			Automaton.List r10 = new Automaton.List(r7, r9); // [-1.0{|e|}]
			int r11 = automaton.add(r10);
			Automaton.Term r12 = new Automaton.Term(K_Mul, r11);
			Automaton.Real r13 = new Automaton.Real(1); // 1.0
			Automaton.Real r14 = r13.negate(); // -1.0
			int r15 = automaton.add(r14);
			int r16 = automaton.add(r12);
			Automaton.Bag r17 = new Automaton.Bag(r16); // {|neg_e|}
			int r18 = automaton.add(r17);
			Automaton.List r19 = new Automaton.List(r15, r18); // [-1.0{|neg_e|}]
			int r20 = automaton.add(r19);
			Automaton.Term r21 = new Automaton.Term(K_Sum, r20);
			int r22 = automaton.add(r21);
			Automaton.List r23 = new Automaton.List(r3, r22); // [tSum([-1.0{|neg_e|}])]
			int r24 = automaton.add(r23);
			Automaton.Term r25 = new Automaton.Term(K_Inequality, r24);
			int r26 = automaton.add(r25);
			if(r0 != r26) {
				return automaton.rewrite(r0, r26);
			}
			automaton.resize(nStates);
			return Automaton.K_VOID;
		}

	}
	private final static class Reduction_81 extends AbstractRewriteRule implements ReductionRule {

		public Reduction_81(Pattern.Term pattern) {
			super(pattern);
			put("name","Inequality[Sum]");
			put("rank",2);
		}

		public final void probe(Automaton automaton, int target, List<Reduction.Activation> activations) {
			int r0 = target;
			Automaton.State s0 = automaton.get(r0);
			if(s0.kind == K_Inequality) {
				Automaton.Term t0 = (Automaton.Term) s0;
				int r1 = t0.contents;
				Automaton.State s1 = automaton.get(r1);
				Automaton.List l1 = (Automaton.List) s1;
				int r2 = l1.get(0);
				int r3 = l1.get(1);
				Automaton.State s3 = automaton.get(r3);
				if(s3.kind == K_Sum) {
					Automaton.Term t3 = (Automaton.Term) s3;
					int r4 = t3.contents;
					Automaton.State s4 = automaton.get(r4);
					Automaton.List l4 = (Automaton.List) s4;
					int r5 = l4.get(0);
					int r6 = l4.get(1);
					Automaton.State s6 = automaton.get(r6);
					Automaton.Collection c6 = (Automaton.Collection) s6;
					boolean m6_0 = true;
					for(int i7=0;i7!=c6.size();++i7) {
						int r7 = c6.get(i7);
						if(Runtime.accepts(type23,automaton,automaton.get(r7), SCHEMA)) {
							continue;
						}
						m6_0 = false;
						break;
					}
					if(m6_0) {
						int[] state = {r0, r1, r2, r3, r4, r5, r6, 0};
						activations.add(new Reduction.Activation(this,null,state));
					}
				}
			}
		}

		public final int apply(Automaton automaton, int[] state) {
			int nStates = automaton.nStates();
			int r0 = state[0];
			int r2 = state[2]; // t
			int r5 = state[5]; // n
			int r6 = state[6]; // ms
			Automaton.Collection c6 = (Automaton.Collection) automaton.get(state[6]);
			int[] c6children = new int[c6.size() - 0];
			for(int s6i=0, s6j=0; s6i != c6.size();++s6i) {
				c6children[s6j++] = c6.get(s6i);
			}
			Automaton.Bag r7 = new Automaton.Bag(c6children);
			Automaton.List r8 = new Automaton.List(r5, r6); // [nms]
			Automaton.Real r9 = Solver$native.gcd(automaton, r8);
			Automaton.Int r10 = r7.lengthOf(); // |xs|
			Automaton.Int r11 = new Automaton.Int(0); // 0
			boolean r12 = r10.compareTo(r11)>0; // |xs| gt 0
			boolean r13 = false;           // |xs| gt 0 && gcd neq 1.0
			if(r12) {
				Automaton.Real r14 = new Automaton.Real(1); // 1.0
				boolean r15 = !r9.equals(r14); // gcd neq 1.0
				r13 = r15;
			}
			if(r13) {
				Automaton.List t16 = new Automaton.List();
				for(int i17=0;i17<r7.size();i17++) {
					int r17 = (int) r7.get(i17);
					Automaton.Term r18 = (Automaton.Term) automaton.get(r17);
					int r19 = r18.contents;
					Automaton.Int r20 = new Automaton.Int(0); // 0
					Automaton.List r21 = (Automaton.List) automaton.get(r19);
					int r22 = r21.indexOf(r20);    // *x[0]
					Automaton.Real r23 = (Automaton.Real) automaton.get(r22);
					Automaton.Real r24 = r23.divide(r9); // *x[0] div gcd
					int r25 = automaton.add(r24);
					Automaton.Term r26 = (Automaton.Term) automaton.get(r17);
					int r27 = r26.contents;
					Automaton.Int r28 = new Automaton.Int(1); // 1
					Automaton.List r29 = (Automaton.List) automaton.get(r27);
					int r30 = r29.indexOf(r28);    // *x[1]
					Automaton.List r31 = new Automaton.List(r25, r30); // [*x[0] div gcd*x[1]]
					int r32 = automaton.add(r31);
					Automaton.Term r33 = new Automaton.Term(K_Mul, r32);
					int r34 = automaton.add(r33);
					t16.add(r34);
				}
				Automaton.Bag r16 = new Automaton.Bag(t16.toArray());
				Automaton.Real r35 = (Automaton.Real) automaton.get(r5);
				Automaton.Real r36 = r35.divide(r9); // n div gcd
				int r37 = automaton.add(r36);
				int r38 = automaton.add(r16);
				Automaton.List r39 = new Automaton.List(r37, r38); // [n div gcdys]
				int r40 = automaton.add(r39);
				Automaton.Term r41 = new Automaton.Term(K_Sum, r40);
				int r42 = automaton.add(r41);
				Automaton.List r43 = new Automaton.List(r2, r42); // [tSum([n div gcdys])]
				int r44 = automaton.add(r43);
				Automaton.Term r45 = new Automaton.Term(K_Inequality, r44);
				int r46 = automaton.add(r45);
				if(r0 != r46) {
					return automaton.rewrite(r0, r46);
				}
			}
			automaton.resize(nStates);
			return Automaton.K_VOID;
		}

	}
	private final static class Reduction_82 extends AbstractRewriteRule implements ReductionRule {

		public Reduction_82(Pattern.Term pattern) {
			super(pattern);
			put("name","And{Inequality,Intequality,BExpr...}");
			put("rank",1);
		}

		public final void probe(Automaton automaton, int target, List<Reduction.Activation> activations) {
			int r0 = target;
			Automaton.State s0 = automaton.get(r0);
			if(s0.kind == K_And) {
				Automaton.Term t0 = (Automaton.Term) s0;
				int r1 = t0.contents;
				Automaton.State s1 = automaton.get(r1);
				Automaton.Collection c1 = (Automaton.Collection) s1;
				if(c1.size() >= 2) {
					for(int r3=0;r3!=c1.size();++r3) {
						int r2 = c1.get(r3);
						Automaton.State s2 = automaton.get(r2);
						if(s2.kind == K_Inequality) {
							Automaton.Term t2 = (Automaton.Term) s2;
							int r4 = t2.contents;
							Automaton.State s4 = automaton.get(r4);
							Automaton.List l4 = (Automaton.List) s4;
							int r5 = l4.get(0);
							if(Runtime.accepts(type24,automaton,automaton.get(r5), SCHEMA)) {
								int r6 = l4.get(1);
								Automaton.State s6 = automaton.get(r6);
								if(s6.kind == K_Sum) {
									Automaton.Term t6 = (Automaton.Term) s6;
									int r7 = t6.contents;
									Automaton.State s7 = automaton.get(r7);
									Automaton.List l7 = (Automaton.List) s7;
									int r8 = l7.get(0);
									int r9 = l7.get(1);
									Automaton.State s9 = automaton.get(r9);
									Automaton.Collection c9 = (Automaton.Collection) s9;
									if(c9.size() == 2) {
										for(int r11=0;r11!=c9.size();++r11) {
											int r10 = c9.get(r11);
											Automaton.State s10 = automaton.get(r10);
											if(s10.kind == K_Mul) {
												Automaton.Term t10 = (Automaton.Term) s10;
												int r12 = t10.contents;
												Automaton.State s12 = automaton.get(r12);
												Automaton.List l12 = (Automaton.List) s12;
												int r13 = l12.get(0);
												int r14 = l12.get(1);
												Automaton.State s14 = automaton.get(r14);
												Automaton.Collection c14 = (Automaton.Collection) s14;
												if(c14.size() == 1) {
													for(int r16=0;r16!=c14.size();++r16) {
														int r15 = c14.get(r16);
														for(int r18=0;r18!=c9.size();++r18) {
															if(r18 == r11) { continue; }
															int r17 = c9.get(r18);
															Automaton.State s17 = automaton.get(r17);
															if(s17.kind == K_Mul) {
																Automaton.Term t17 = (Automaton.Term) s17;
																int r19 = t17.contents;
																Automaton.State s19 = automaton.get(r19);
																Automaton.List l19 = (Automaton.List) s19;
																int r20 = l19.get(0);
																int r21 = l19.get(1);
																Automaton.State s21 = automaton.get(r21);
																Automaton.Collection c21 = (Automaton.Collection) s21;
																if(c21.size() == 1) {
																	for(int r23=0;r23!=c21.size();++r23) {
																		int r22 = c21.get(r23);
																		for(int r25=0;r25!=c1.size();++r25) {
																			if(r25 == r3) { continue; }
																			int r24 = c1.get(r25);
																			Automaton.State s24 = automaton.get(r24);
																			if(s24.kind == K_Inequality) {
																				Automaton.Term t24 = (Automaton.Term) s24;
																				int r26 = t24.contents;
																				Automaton.State s26 = automaton.get(r26);
																				Automaton.List l26 = (Automaton.List) s26;
																				int r27 = l26.get(0);
																				if(Runtime.accepts(type24,automaton,automaton.get(r27), SCHEMA)) {
																					int r28 = l26.get(1);
																					Automaton.State s28 = automaton.get(r28);
																					if(s28.kind == K_Sum) {
																						Automaton.Term t28 = (Automaton.Term) s28;
																						int r29 = t28.contents;
																						Automaton.State s29 = automaton.get(r29);
																						Automaton.List l29 = (Automaton.List) s29;
																						int r30 = l29.get(0);
																						int r31 = l29.get(1);
																						Automaton.State s31 = automaton.get(r31);
																						Automaton.Collection c31 = (Automaton.Collection) s31;
																						if(c31.size() == 2) {
																							for(int r33=0;r33!=c31.size();++r33) {
																								int r32 = c31.get(r33);
																								Automaton.State s32 = automaton.get(r32);
																								if(s32.kind == K_Mul) {
																									Automaton.Term t32 = (Automaton.Term) s32;
																									int r34 = t32.contents;
																									Automaton.State s34 = automaton.get(r34);
																									Automaton.List l34 = (Automaton.List) s34;
																									int r35 = l34.get(0);
																									int r36 = l34.get(1);
																									Automaton.State s36 = automaton.get(r36);
																									Automaton.Collection c36 = (Automaton.Collection) s36;
																									if(c36.size() == 1) {
																										for(int r38=0;r38!=c36.size();++r38) {
																											int r37 = c36.get(r38);
																											for(int r40=0;r40!=c31.size();++r40) {
																												if(r40 == r33) { continue; }
																												int r39 = c31.get(r40);
																												Automaton.State s39 = automaton.get(r39);
																												if(s39.kind == K_Mul) {
																													Automaton.Term t39 = (Automaton.Term) s39;
																													int r41 = t39.contents;
																													Automaton.State s41 = automaton.get(r41);
																													Automaton.List l41 = (Automaton.List) s41;
																													int r42 = l41.get(0);
																													int r43 = l41.get(1);
																													Automaton.State s43 = automaton.get(r43);
																													Automaton.Collection c43 = (Automaton.Collection) s43;
																													if(c43.size() == 1) {
																														for(int r45=0;r45!=c43.size();++r45) {
																															int r44 = c43.get(r45);
																															int[] c1children = new int[c1.size() - 2];
																															for(int s1i=0, s1j=0; s1i != c1.size();++s1i) {
																																if(s1i == r3 || s1i == r25) { continue; }
																																c1children[s1j++] = c1.get(s1i);
																															}
																															Automaton.Set r46 = new Automaton.Set(c1children);
																															Automaton.Real r47 = (Automaton.Real) automaton.get(r30);
																															Automaton.Real r48 = r47.negate(); // -y1
																															Automaton.Real r49 = (Automaton.Real) automaton.get(r8);
																															boolean r50 = r49.equals(r48); // x1 eq -y1
																															boolean r51 = false;           // x1 eq -y1 && x2 eq -y2 && x3 eq -y3 && vx1 eq vy1 && vx2 eq vy2
																															if(r50) {
																																Automaton.Real r52 = (Automaton.Real) automaton.get(r35);
																																Automaton.Real r53 = r52.negate(); // -y2
																																Automaton.Real r54 = (Automaton.Real) automaton.get(r13);
																																boolean r55 = r54.equals(r53); // x2 eq -y2
																																boolean r56 = false;           // x2 eq -y2 && x3 eq -y3 && vx1 eq vy1 && vx2 eq vy2
																																if(r55) {
																																	Automaton.Real r57 = (Automaton.Real) automaton.get(r42);
																																	Automaton.Real r58 = r57.negate(); // -y3
																																	Automaton.Real r59 = (Automaton.Real) automaton.get(r20);
																																	boolean r60 = r59.equals(r58); // x3 eq -y3
																																	boolean r61 = false;           // x3 eq -y3 && vx1 eq vy1 && vx2 eq vy2
																																	if(r60) {
																																		boolean r62 = r15 == r37;      // vx1 eq vy1
																																		boolean r63 = false;           // vx1 eq vy1 && vx2 eq vy2
																																		if(r62) {
																																			boolean r64 = r22 == r44;      // vx2 eq vy2
																																			r63 = r64;
																																		}
																																		r61 = r63;
																																	}
																																	r56 = r61;
																																}
																																r51 = r56;
																															}
																															if(r51) { // REQUIRES
																																int[] state = {r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, 0};
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
																						}
																					}
																				}
																			}
																		}
																	}
																}
															}
														}
													}
												}
											}
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
			int r2 = state[2]; // ieq1
			int r3 = state[3];
			int r6 = state[6]; // s1
			int r8 = state[8]; // x1
			int r11 = state[11];
			int r13 = state[13]; // x2
			int r15 = state[15]; // vx1
			int r16 = state[16];
			int r18 = state[18];
			int r20 = state[20]; // x3
			int r22 = state[22]; // vx2
			int r23 = state[23];
			int r24 = state[24]; // ieq2
			int r25 = state[25];
			int r28 = state[28]; // s2
			int r30 = state[30]; // y1
			int r33 = state[33];
			int r35 = state[35]; // y2
			int r37 = state[37]; // vy1
			int r38 = state[38];
			int r40 = state[40];
			int r42 = state[42]; // y3
			int r44 = state[44]; // vy2
			int r45 = state[45];
			Automaton.Collection c1 = (Automaton.Collection) automaton.get(state[1]);
			int[] c1children = new int[c1.size() - 2];
			for(int s1i=0, s1j=0; s1i != c1.size();++s1i) {
				if(s1i == r3 || s1i == r25) { continue; }
				c1children[s1j++] = c1.get(s1i);
			}
			Automaton.Set r46 = new Automaton.Set(c1children);
			Automaton.Term r47 = IntT;
			int r48 = automaton.add(r47);
			Automaton.List r49 = new Automaton.List(r48, r6); // [IntTs1]
			int r50 = automaton.add(r49);
			Automaton.Term r51 = new Automaton.Term(K_Equation, r50);
			int r52 = automaton.add(r51);
			Automaton.Set r53 = r46.appendFront(r52); // Equation([IntTs1]) append rest
			int r54 = automaton.add(r53);
			Automaton.Term r55 = new Automaton.Term(K_And, r54);
			int r56 = automaton.add(r55);
			if(r0 != r56) {
				return automaton.rewrite(r0, r56);
			}
			automaton.resize(nStates);
			return Automaton.K_VOID;
		}

	}
	private final static class Inference_2 extends AbstractRewriteRule implements InferenceRule {

		public Inference_2(Pattern.Term pattern) {
			super(pattern);
			put("name","And{Inequality,Inequality,BExpr...}");
			put("rank",1);
		}

		public final void probe(Automaton automaton, int root, int target, List<Inference.Activation> activations) {
			int r0 = target;
			Automaton.State s0 = automaton.get(r0);
			if(s0.kind == K_And) {
				Automaton.Term t0 = (Automaton.Term) s0;
				int r1 = t0.contents;
				Automaton.State s1 = automaton.get(r1);
				Automaton.Collection c1 = (Automaton.Collection) s1;
				if(c1.size() >= 2) {
					for(int r3=0;r3!=c1.size();++r3) {
						int r2 = c1.get(r3);
						Automaton.State s2 = automaton.get(r2);
						if(s2.kind == K_Inequality) {
							Automaton.Term t2 = (Automaton.Term) s2;
							int r4 = t2.contents;
							Automaton.State s4 = automaton.get(r4);
							Automaton.List l4 = (Automaton.List) s4;
							int r5 = l4.get(0);
							int r6 = l4.get(1);
							Automaton.State s6 = automaton.get(r6);
							if(s6.kind == K_Sum) {
								Automaton.Term t6 = (Automaton.Term) s6;
								int r7 = t6.contents;
								Automaton.State s7 = automaton.get(r7);
								Automaton.List l7 = (Automaton.List) s7;
								int r8 = l7.get(0);
								int r9 = l7.get(1);
								Automaton.State s9 = automaton.get(r9);
								Automaton.Collection c9 = (Automaton.Collection) s9;
								if(c9.size() >= 1) {
									for(int r11=0;r11!=c9.size();++r11) {
										int r10 = c9.get(r11);
										Automaton.State s10 = automaton.get(r10);
										if(s10.kind == K_Mul) {
											Automaton.Term t10 = (Automaton.Term) s10;
											int r12 = t10.contents;
											Automaton.State s12 = automaton.get(r12);
											Automaton.List l12 = (Automaton.List) s12;
											int r13 = l12.get(0);
											int r14 = l12.get(1);
											Automaton.State s14 = automaton.get(r14);
											Automaton.Collection c14 = (Automaton.Collection) s14;
											if(c14.size() == 1) {
												for(int r16=0;r16!=c14.size();++r16) {
													int r15 = c14.get(r16);
													boolean m9_1 = true;
													for(int i17=0;i17!=c9.size();++i17) {
														if(i17 == r11) { continue; }
														int r17 = c9.get(i17);
														if(Runtime.accepts(type23,automaton,automaton.get(r17), SCHEMA)) {
															continue;
														}
														m9_1 = false;
														break;
													}
													if(m9_1) {
														for(int r19=0;r19!=c1.size();++r19) {
															if(r19 == r3) { continue; }
															int r18 = c1.get(r19);
															Automaton.State s18 = automaton.get(r18);
															if(s18.kind == K_Inequality) {
																Automaton.Term t18 = (Automaton.Term) s18;
																int r20 = t18.contents;
																Automaton.State s20 = automaton.get(r20);
																Automaton.List l20 = (Automaton.List) s20;
																int r21 = l20.get(0);
																int r22 = l20.get(1);
																Automaton.State s22 = automaton.get(r22);
																if(s22.kind == K_Sum) {
																	Automaton.Term t22 = (Automaton.Term) s22;
																	int r23 = t22.contents;
																	Automaton.State s23 = automaton.get(r23);
																	Automaton.List l23 = (Automaton.List) s23;
																	int r24 = l23.get(0);
																	int r25 = l23.get(1);
																	Automaton.State s25 = automaton.get(r25);
																	Automaton.Collection c25 = (Automaton.Collection) s25;
																	if(c25.size() >= 1) {
																		for(int r27=0;r27!=c25.size();++r27) {
																			int r26 = c25.get(r27);
																			Automaton.State s26 = automaton.get(r26);
																			if(s26.kind == K_Mul) {
																				Automaton.Term t26 = (Automaton.Term) s26;
																				int r28 = t26.contents;
																				Automaton.State s28 = automaton.get(r28);
																				Automaton.List l28 = (Automaton.List) s28;
																				int r29 = l28.get(0);
																				int r30 = l28.get(1);
																				Automaton.State s30 = automaton.get(r30);
																				Automaton.Collection c30 = (Automaton.Collection) s30;
																				if(c30.size() == 1) {
																					for(int r32=0;r32!=c30.size();++r32) {
																						int r31 = c30.get(r32);
																						boolean m25_1 = true;
																						for(int i33=0;i33!=c25.size();++i33) {
																							if(i33 == r27) { continue; }
																							int r33 = c25.get(i33);
																							if(Runtime.accepts(type23,automaton,automaton.get(r33), SCHEMA)) {
																								continue;
																							}
																							m25_1 = false;
																							break;
																						}
																						if(m25_1) {
																							int[] c9children = new int[c9.size() - 1];
																							for(int s9i=0, s9j=0; s9i != c9.size();++s9i) {
																								if(s9i == r11) { continue; }
																								c9children[s9j++] = c9.get(s9i);
																							}
																							Automaton.Bag r17 = new Automaton.Bag(c9children);
																							int[] c25children = new int[c25.size() - 1];
																							for(int s25i=0, s25j=0; s25i != c25.size();++s25i) {
																								if(s25i == r27) { continue; }
																								c25children[s25j++] = c25.get(s25i);
																							}
																							Automaton.Bag r33 = new Automaton.Bag(c25children);
																							int[] c1children = new int[c1.size() - 2];
																							for(int s1i=0, s1j=0; s1i != c1.size();++s1i) {
																								if(s1i == r3 || s1i == r19) { continue; }
																								c1children[s1j++] = c1.get(s1i);
																							}
																							Automaton.Set r34 = new Automaton.Set(c1children);
																							boolean r35 = r15 == r31;      // v1 eq v2
																							boolean r36 = false;           // v1 eq v2 && t1 eq t2 && x2 lt 0.0 && y2 gt 0.0
																							if(r35) {
																								boolean r37 = r5 == r21;       // t1 eq t2
																								boolean r38 = false;           // t1 eq t2 && x2 lt 0.0 && y2 gt 0.0
																								if(r37) {
																									Automaton.Real r39 = new Automaton.Real(0); // 0.0
																									Automaton.Real r40 = (Automaton.Real) automaton.get(r13);
																									boolean r41 = r40.compareTo(r39)<0; // x2 lt 0.0
																									boolean r42 = false;           // x2 lt 0.0 && y2 gt 0.0
																									if(r41) {
																										Automaton.Real r43 = new Automaton.Real(0); // 0.0
																										Automaton.Real r44 = (Automaton.Real) automaton.get(r29);
																										boolean r45 = r44.compareTo(r43)>0; // y2 gt 0.0
																										r42 = r45;
																									}
																									r38 = r42;
																								}
																								r36 = r38;
																							}
																							if(r36) { // REQUIRES
																								int[] state = {r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, 0, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, 0, 0};
																								activations.add(new Inference.Activation(this,root,null,state));
																							}
																						}
																					}
																				}
																			}
																		}
																	}
																}
															}
														}
													}
												}
											}
										}
									}
								}
							}
						}
					}
				}
			}
		}

		public final int apply(Automaton automaton, int root, int[] state) {
			int nStates = automaton.nStates();
			int r0 = state[0];
			int r2 = state[2]; // eq1
			int r3 = state[3];
			int r5 = state[5]; // t1
			int r6 = state[6]; // s1
			int r8 = state[8]; // x1
			int r9 = state[9]; // xxs
			int r11 = state[11];
			int r13 = state[13]; // x2
			int r15 = state[15]; // v1
			int r16 = state[16];
			Automaton.Collection c9 = (Automaton.Collection) automaton.get(state[9]);
			int[] c9children = new int[c9.size() - 1];
			for(int s9i=0, s9j=0; s9i != c9.size();++s9i) {
				if(s9i == r11) { continue; }
				c9children[s9j++] = c9.get(s9i);
			}
			Automaton.Bag r17 = new Automaton.Bag(c9children);
			int r18 = state[18]; // eq2
			int r19 = state[19];
			int r21 = state[21]; // t2
			int r22 = state[22]; // s2
			int r24 = state[24]; // y1
			int r25 = state[25]; // yys
			int r27 = state[27];
			int r29 = state[29]; // y2
			int r31 = state[31]; // v2
			int r32 = state[32];
			Automaton.Collection c25 = (Automaton.Collection) automaton.get(state[25]);
			int[] c25children = new int[c25.size() - 1];
			for(int s25i=0, s25j=0; s25i != c25.size();++s25i) {
				if(s25i == r27) { continue; }
				c25children[s25j++] = c25.get(s25i);
			}
			Automaton.Bag r33 = new Automaton.Bag(c25children);
			Automaton.Collection c1 = (Automaton.Collection) automaton.get(state[1]);
			int[] c1children = new int[c1.size() - 2];
			for(int s1i=0, s1j=0; s1i != c1.size();++s1i) {
				if(s1i == r3 || s1i == r19) { continue; }
				c1children[s1j++] = c1.get(s1i);
			}
			Automaton.Set r34 = new Automaton.Set(c1children);
			Automaton.Term r35 = Solver$native.maxMultiplicand(automaton, r9);
			Automaton.Term r36 = Solver$native.maxMultiplicand(automaton, r25);
			Object r37 = (Object) automaton.get(r15);
			boolean r38 = r35.equals(r37); // vx eq v1
			boolean r39 = false;           // vx eq v1 && vy eq v1
			if(r38) {
				Object r40 = (Object) automaton.get(r15);
				boolean r41 = r36.equals(r40); // vy eq v1
				r39 = r41;
			}
			if(r39) {
				int r42 = automaton.add(r17);
				Automaton.List r43 = new Automaton.List(r8, r42); // [x1xs]
				int r44 = automaton.add(r43);
				Automaton.Term r45 = new Automaton.Term(K_Sum, r44);
				int r46 = automaton.add(r45);
				Automaton.Bag r47 = new Automaton.Bag(r46); // {|Sum([x1xs])|}
				int r48 = automaton.add(r47);
				Automaton.List r49 = new Automaton.List(r29, r48); // [y2{|Sum([x1xs])|}]
				int r50 = automaton.add(r49);
				Automaton.Term r51 = new Automaton.Term(K_Mul, r50);
				Automaton.Real r52 = (Automaton.Real) automaton.get(r13);
				Automaton.Real r53 = r52.negate(); // -x2
				int r54 = automaton.add(r53);
				int r55 = automaton.add(r33);
				Automaton.List r56 = new Automaton.List(r24, r55); // [y1ys]
				int r57 = automaton.add(r56);
				Automaton.Term r58 = new Automaton.Term(K_Sum, r57);
				int r59 = automaton.add(r58);
				Automaton.Bag r60 = new Automaton.Bag(r59); // {|Sum([y1ys])|}
				int r61 = automaton.add(r60);
				Automaton.List r62 = new Automaton.List(r54, r61); // [-x2{|Sum([y1ys])|}]
				int r63 = automaton.add(r62);
				Automaton.Term r64 = new Automaton.Term(K_Mul, r63);
				Automaton.Real r65 = new Automaton.Real(0); // 0.0
				int r66 = automaton.add(r65);
				int r67 = automaton.add(r51);
				int r68 = automaton.add(r64);
				Automaton.Bag r69 = new Automaton.Bag(r67, r68); // {|s3s4|}
				int r70 = automaton.add(r69);
				Automaton.List r71 = new Automaton.List(r66, r70); // [0.0{|s3s4|}]
				int r72 = automaton.add(r71);
				Automaton.Term r73 = new Automaton.Term(K_Sum, r72);
				int r74 = automaton.add(r73);
				Automaton.List r75 = new Automaton.List(r5, r74); // [t1Sum([0.0{|s3s4|}])]
				int r76 = automaton.add(r75);
				Automaton.Term r77 = new Automaton.Term(K_Inequality, r76);
				int r78 = automaton.add(r77);
				Automaton.Set r79 = new Automaton.Set(r2, r18, r78); // {eq1eq2eq3}
				Automaton.Set r80 = r79.append(r34); // {eq1eq2eq3} append rest
				int r81 = automaton.add(r80);
				Automaton.Term r82 = new Automaton.Term(K_And, r81);
				int r83 = automaton.add(r82);
				if(r0 != r83) {
					return automaton.substitute(root,r0, r83);
				}
			}
			automaton.resize(nStates);
			return Automaton.K_VOID;
		}

	}
	private final static class Inference_3 extends AbstractRewriteRule implements InferenceRule {

		public Inference_3(Pattern.Term pattern) {
			super(pattern);
			put("name","Inequality{Inequality,Inequality,BExpr...}");
			put("rank",1);
		}

		public final void probe(Automaton automaton, int root, int target, List<Inference.Activation> activations) {
			int r0 = target;
			Automaton.State s0 = automaton.get(r0);
			if(s0.kind == K_And) {
				Automaton.Term t0 = (Automaton.Term) s0;
				int r1 = t0.contents;
				Automaton.State s1 = automaton.get(r1);
				Automaton.Collection c1 = (Automaton.Collection) s1;
				if(c1.size() >= 2) {
					for(int r3=0;r3!=c1.size();++r3) {
						int r2 = c1.get(r3);
						Automaton.State s2 = automaton.get(r2);
						if(s2.kind == K_Inequality) {
							Automaton.Term t2 = (Automaton.Term) s2;
							int r4 = t2.contents;
							Automaton.State s4 = automaton.get(r4);
							Automaton.List l4 = (Automaton.List) s4;
							int r5 = l4.get(0);
							int r6 = l4.get(1);
							Automaton.State s6 = automaton.get(r6);
							if(s6.kind == K_Sum) {
								Automaton.Term t6 = (Automaton.Term) s6;
								int r7 = t6.contents;
								Automaton.State s7 = automaton.get(r7);
								Automaton.List l7 = (Automaton.List) s7;
								int r8 = l7.get(0);
								int r9 = l7.get(1);
								Automaton.State s9 = automaton.get(r9);
								Automaton.Collection c9 = (Automaton.Collection) s9;
								if(c9.size() >= 1) {
									for(int r11=0;r11!=c9.size();++r11) {
										int r10 = c9.get(r11);
										Automaton.State s10 = automaton.get(r10);
										if(s10.kind == K_Mul) {
											Automaton.Term t10 = (Automaton.Term) s10;
											int r12 = t10.contents;
											Automaton.State s12 = automaton.get(r12);
											Automaton.List l12 = (Automaton.List) s12;
											int r13 = l12.get(0);
											int r14 = l12.get(1);
											Automaton.State s14 = automaton.get(r14);
											Automaton.Collection c14 = (Automaton.Collection) s14;
											if(c14.size() == 1) {
												for(int r16=0;r16!=c14.size();++r16) {
													int r15 = c14.get(r16);
													boolean m9_1 = true;
													for(int i17=0;i17!=c9.size();++i17) {
														if(i17 == r11) { continue; }
														int r17 = c9.get(i17);
														if(Runtime.accepts(type23,automaton,automaton.get(r17), SCHEMA)) {
															continue;
														}
														m9_1 = false;
														break;
													}
													if(m9_1) {
														for(int r19=0;r19!=c1.size();++r19) {
															if(r19 == r3) { continue; }
															int r18 = c1.get(r19);
															Automaton.State s18 = automaton.get(r18);
															if(s18.kind == K_Inequality) {
																Automaton.Term t18 = (Automaton.Term) s18;
																int r20 = t18.contents;
																Automaton.State s20 = automaton.get(r20);
																Automaton.List l20 = (Automaton.List) s20;
																int r21 = l20.get(0);
																int r22 = l20.get(1);
																if(Runtime.accepts(type8,automaton,automaton.get(r22), SCHEMA)) {
																	int[] c9children = new int[c9.size() - 1];
																	for(int s9i=0, s9j=0; s9i != c9.size();++s9i) {
																		if(s9i == r11) { continue; }
																		c9children[s9j++] = c9.get(s9i);
																	}
																	Automaton.Bag r17 = new Automaton.Bag(c9children);
																	int[] c1children = new int[c1.size() - 2];
																	for(int s1i=0, s1j=0; s1i != c1.size();++s1i) {
																		if(s1i == r3 || s1i == r19) { continue; }
																		c1children[s1j++] = c1.get(s1i);
																	}
																	Automaton.Set r23 = new Automaton.Set(c1children);
																	boolean r24 = r15 == r22;      // v1 eq v2
																	boolean r25 = false;           // v1 eq v2 && t1 eq t2 && x2 lt 0.0
																	if(r24) {
																		boolean r26 = r5 == r21;       // t1 eq t2
																		boolean r27 = false;           // t1 eq t2 && x2 lt 0.0
																		if(r26) {
																			Automaton.Real r28 = new Automaton.Real(0); // 0.0
																			Automaton.Real r29 = (Automaton.Real) automaton.get(r13);
																			boolean r30 = r29.compareTo(r28)<0; // x2 lt 0.0
																			r27 = r30;
																		}
																		r25 = r27;
																	}
																	if(r25) { // REQUIRES
																		int[] state = {r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, 0, r18, r19, r20, r21, r22, 0};
																		activations.add(new Inference.Activation(this,root,null,state));
																	}
																}
															}
														}
													}
												}
											}
										}
									}
								}
							}
						}
					}
				}
			}
		}

		public final int apply(Automaton automaton, int root, int[] state) {
			int nStates = automaton.nStates();
			int r0 = state[0];
			int r2 = state[2]; // eq1
			int r3 = state[3];
			int r5 = state[5]; // t1
			int r6 = state[6]; // s1
			int r8 = state[8]; // x1
			int r9 = state[9]; // xxs
			int r11 = state[11];
			int r13 = state[13]; // x2
			int r15 = state[15]; // v1
			int r16 = state[16];
			Automaton.Collection c9 = (Automaton.Collection) automaton.get(state[9]);
			int[] c9children = new int[c9.size() - 1];
			for(int s9i=0, s9j=0; s9i != c9.size();++s9i) {
				if(s9i == r11) { continue; }
				c9children[s9j++] = c9.get(s9i);
			}
			Automaton.Bag r17 = new Automaton.Bag(c9children);
			int r18 = state[18]; // eq2
			int r19 = state[19];
			int r21 = state[21]; // t2
			int r22 = state[22]; // v2
			Automaton.Collection c1 = (Automaton.Collection) automaton.get(state[1]);
			int[] c1children = new int[c1.size() - 2];
			for(int s1i=0, s1j=0; s1i != c1.size();++s1i) {
				if(s1i == r3 || s1i == r19) { continue; }
				c1children[s1j++] = c1.get(s1i);
			}
			Automaton.Set r23 = new Automaton.Set(c1children);
			Automaton.Term r24 = Solver$native.maxMultiplicand(automaton, r9);
			Object r25 = (Object) automaton.get(r15);
			boolean r26 = r24.equals(r25); // vx eq v1
			if(r26) {
				int r27 = automaton.add(r17);
				Automaton.List r28 = new Automaton.List(r8, r27); // [x1xs]
				int r29 = automaton.add(r28);
				Automaton.Term r30 = new Automaton.Term(K_Sum, r29);
				int r31 = automaton.add(r30);
				Automaton.List r32 = new Automaton.List(r5, r31); // [t1Sum([x1xs])]
				int r33 = automaton.add(r32);
				Automaton.Term r34 = new Automaton.Term(K_Inequality, r33);
				int r35 = automaton.add(r34);
				Automaton.Set r36 = new Automaton.Set(r2, r18, r35); // {eq1eq2eq3}
				Automaton.Set r37 = r36.append(r23); // {eq1eq2eq3} append rest
				int r38 = automaton.add(r37);
				Automaton.Term r39 = new Automaton.Term(K_And, r38);
				int r40 = automaton.add(r39);
				if(r0 != r40) {
					return automaton.substitute(root,r0, r40);
				}
			}
			automaton.resize(nStates);
			return Automaton.K_VOID;
		}

	}
	// term $7<Array($5<^[$2<^Expr<$49<Value<Null|Tuple(^[^$49...])|Bool<True|False>|Num(^real)|String(^string)|Array(^[^$49...])|ArrayGen(^[^$49,^$49])>>|Tuple($5)|$88<BExpr<Bool<True|False>|VExpr<Var(^string)|Fn(^[^string,$2...])|Load(^[$2,^int])|LengthOf($2)|IndexOf(^[$2,$2])>|And(^{^$88...})|Or(^{^$88...})|Not(^$88)|Equals(^[$134<^Type<Atom<NotT($157<^Proton<TupleT(^[$157...])|ArrayT($157)|Quark<AnyT|NullT|VoidT|BoolT|IntT|RealT|StringT|VarT(^string)|NominalT(^string)>>>)|Proton<TupleT(^[$157...])|ArrayT($157)|Quark<AnyT|NullT|VoidT|BoolT|IntT|RealT|StringT|VarT(^string)|NominalT(^string)>>>|NotT($134)|OrT(^{$134...})|AndT(^{$134...})|ArrayT($134)|TupleT(^[$134...])|FunctionT(^[$134,$134,$134...])>>,^{|$2,$2|}[$2,$2]])|Inequality(^[^AType<IntT|RealT>,$231<^AExpr<Num(^real)|VExpr<Var(^string)|Fn(^[^string,$2...])|Load(^[$2,^int])|LengthOf($2)|IndexOf(^[$2,$2])>|Sum(^[^real,^{|$231...|}[$231...]])|Mul(^[^real,^{|$231...|}[$231...]])|Div(^[$231,$231])>>])|Equation(^[^AType<IntT|RealT>,$231])|ForAll(^[^{^[^Var(^string),$134]...},^$88])|Exists(^[^{^[^Var(^string),$134]...},^$88])>>|AExpr<Num(^real)|VExpr<Var(^string)|Fn(^[^string,$2...])|Load(^[$2,^int])|LengthOf($2)|IndexOf(^[$2,$2])>|Sum(^[^real,^{|$231...|}[$231...]])|Mul(^[^real,^{|$231...|}[$231...]])|Div(^[$231,$231])>|SExpr<$7|VExpr<Var(^string)|Fn(^[^string,$2...])|Load(^[$2,^int])|LengthOf($2)|IndexOf(^[$2,$2])>|ArrayGen(^[$2,$2])>>>...]>)>
	public final static int K_Array = 34;
	public final static int Array(Automaton automaton, int... r0) {
		int r1 = automaton.add(new Automaton.List(r0));
		return automaton.add(new Automaton.Term(K_Array, r1));
	}
	public final static int Array(Automaton automaton, List<Integer> r0) {
		int r1 = automaton.add(new Automaton.List(r0));
		return automaton.add(new Automaton.Term(K_Array, r1));
	}

	private final static class Reduction_83 extends AbstractRewriteRule implements ReductionRule {

		public Reduction_83(Pattern.Term pattern) {
			super(pattern);
			put("name","And{Equals[VExpr,Array],BExpr...}");
			put("rank",2);
		}

		public final void probe(Automaton automaton, int target, List<Reduction.Activation> activations) {
			int r0 = target;
			Automaton.State s0 = automaton.get(r0);
			if(s0.kind == K_And) {
				Automaton.Term t0 = (Automaton.Term) s0;
				int r1 = t0.contents;
				Automaton.State s1 = automaton.get(r1);
				Automaton.Collection c1 = (Automaton.Collection) s1;
				if(c1.size() >= 1) {
					for(int r3=0;r3!=c1.size();++r3) {
						int r2 = c1.get(r3);
						Automaton.State s2 = automaton.get(r2);
						if(s2.kind == K_Equals) {
							Automaton.Term t2 = (Automaton.Term) s2;
							int r4 = t2.contents;
							Automaton.State s4 = automaton.get(r4);
							Automaton.List l4 = (Automaton.List) s4;
							int r5 = l4.get(0);
							int r6 = l4.get(1);
							Automaton.State s6 = automaton.get(r6);
							Automaton.Collection c6 = (Automaton.Collection) s6;
							for(int r8=0;r8!=c6.size();++r8) {
								int r7 = c6.get(r8);
								if(Runtime.accepts(type8,automaton,automaton.get(r7), SCHEMA)) {
									for(int r10=0;r10!=c6.size();++r10) {
										if(r10 == r8) { continue; }
										int r9 = c6.get(r10);
										if(Runtime.accepts(type26,automaton,automaton.get(r9), SCHEMA)) {
											int[] state = {r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, 0};
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
			int r2 = state[2]; // eq
			int r3 = state[3];
			int r5 = state[5]; // t
			int r7 = state[7]; // x
			int r8 = state[8];
			int r9 = state[9]; // y
			int r10 = state[10];
			Automaton.Collection c1 = (Automaton.Collection) automaton.get(state[1]);
			int[] c1children = new int[c1.size() - 1];
			for(int s1i=0, s1j=0; s1i != c1.size();++s1i) {
				if(s1i == r3) { continue; }
				c1children[s1j++] = c1.get(s1i);
			}
			Automaton.Set r11 = new Automaton.Set(c1children);
			Automaton.List t12 = new Automaton.List();
			for(int i13=0;i13<r11.size();i13++) {
				int r13 = (int) r11.get(i13);
				int r14 = automaton.substitute(r13, r7, r9);
				t12.add(r14);
			}
			Automaton.Set r12 = new Automaton.Set(t12.toArray());
			Automaton.Set r15 = r12.appendFront(r2); // eq append cs
			int r16 = automaton.add(r15);
			Automaton.Term r17 = new Automaton.Term(K_And, r16);
			int r18 = automaton.add(r17);
			if(r0 != r18) {
				return automaton.rewrite(r0, r18);
			}
			automaton.resize(nStates);
			return Automaton.K_VOID;
		}

	}
	// term $8<ArrayGen($6<^[$2<^Expr<$50<Value<Null|Tuple(^[^$50...])|Bool<True|False>|Num(^real)|String(^string)|Array(^[^$50...])|ArrayGen(^[^$50,^$50])>>|Tuple(^[$2...])|$92<BExpr<Bool<True|False>|VExpr<Var(^string)|Fn(^[^string,$2...])|Load(^[$2,^int])|LengthOf($2)|IndexOf($6)>|And(^{^$92...})|Or(^{^$92...})|Not(^$92)|Equals(^[$134<^Type<Atom<NotT($157<^Proton<TupleT(^[$157...])|ArrayT($157)|Quark<AnyT|NullT|VoidT|BoolT|IntT|RealT|StringT|VarT(^string)|NominalT(^string)>>>)|Proton<TupleT(^[$157...])|ArrayT($157)|Quark<AnyT|NullT|VoidT|BoolT|IntT|RealT|StringT|VarT(^string)|NominalT(^string)>>>|NotT($134)|OrT(^{$134...})|AndT(^{$134...})|ArrayT($134)|TupleT(^[$134...])|FunctionT(^[$134,$134,$134...])>>,^{|$2,$2|}[$2,$2]])|Inequality(^[^AType<IntT|RealT>,$231<^AExpr<Num(^real)|VExpr<Var(^string)|Fn(^[^string,$2...])|Load(^[$2,^int])|LengthOf($2)|IndexOf($6)>|Sum(^[^real,^{|$231...|}[$231...]])|Mul(^[^real,^{|$231...|}[$231...]])|Div(^[$231,$231])>>])|Equation(^[^AType<IntT|RealT>,$231])|ForAll(^[^{^[^Var(^string),$134]...},^$92])|Exists(^[^{^[^Var(^string),$134]...},^$92])>>|AExpr<Num(^real)|VExpr<Var(^string)|Fn(^[^string,$2...])|Load(^[$2,^int])|LengthOf($2)|IndexOf($6)>|Sum(^[^real,^{|$231...|}[$231...]])|Mul(^[^real,^{|$231...|}[$231...]])|Div(^[$231,$231])>|SExpr<$8|VExpr<Var(^string)|Fn(^[^string,$2...])|Load(^[$2,^int])|LengthOf($2)|IndexOf($6)>|Array(^[$2...])>>>,$2]>)>
	public final static int K_ArrayGen = 35;
	public final static int ArrayGen(Automaton automaton, int... r0) {
		int r1 = automaton.add(new Automaton.List(r0));
		return automaton.add(new Automaton.Term(K_ArrayGen, r1));
	}
	public final static int ArrayGen(Automaton automaton, List<Integer> r0) {
		int r1 = automaton.add(new Automaton.List(r0));
		return automaton.add(new Automaton.Term(K_ArrayGen, r1));
	}

	private final static class Reduction_84 extends AbstractRewriteRule implements ReductionRule {

		public Reduction_84(Pattern.Term pattern) {
			super(pattern);
			put("name","ArrayGen[Expr,Num]");
			put("rank",2);
		}

		public final void probe(Automaton automaton, int target, List<Reduction.Activation> activations) {
			int r0 = target;
			Automaton.State s0 = automaton.get(r0);
			if(s0.kind == K_ArrayGen) {
				Automaton.Term t0 = (Automaton.Term) s0;
				int r1 = t0.contents;
				Automaton.State s1 = automaton.get(r1);
				Automaton.List l1 = (Automaton.List) s1;
				int r2 = l1.get(0);
				int r3 = l1.get(1);
				Automaton.State s3 = automaton.get(r3);
				if(s3.kind == K_Num) {
					Automaton.Term t3 = (Automaton.Term) s3;
					int r4 = t3.contents;
					int[] state = {r0, r1, r2, r3, r4};
					activations.add(new Reduction.Activation(this,null,state));
				}
			}
		}

		public final int apply(Automaton automaton, int[] state) {
			int nStates = automaton.nStates();
			int r0 = state[0];
			int r2 = state[2]; // x
			int r4 = state[4]; // r
			Automaton.Real r5 = (Automaton.Real) automaton.get(r4);
			Automaton.Int r6 = r5.numerator(); // |r|
			Automaton.Int r8 = new Automaton.Int(0); // 0
			Automaton.List r9 = Runtime.rangeOf(automaton,r8,r6); // 0 range n
			Automaton.List t7 = new Automaton.List();
			for(int i10=0;i10<r9.size();i10++) {
				Automaton.Int r10 = (Automaton.Int) automaton.get(r9.get(i10));;
				t7.add(r2);
			}
			Automaton.List r7 = t7;
			int r11 = automaton.add(r7);
			Automaton.Term r12 = new Automaton.Term(K_Array, r11);
			int r13 = automaton.add(r12);
			if(r0 != r13) {
				return automaton.rewrite(r0, r13);
			}
			automaton.resize(nStates);
			return Automaton.K_VOID;
		}

	}
	private final static class Reduction_85 extends AbstractRewriteRule implements ReductionRule {

		public Reduction_85(Pattern.Term pattern) {
			super(pattern);
			put("name","And{Equals[VExpr,ArrayGen],BExpr...}");
			put("rank",2);
		}

		public final void probe(Automaton automaton, int target, List<Reduction.Activation> activations) {
			int r0 = target;
			Automaton.State s0 = automaton.get(r0);
			if(s0.kind == K_And) {
				Automaton.Term t0 = (Automaton.Term) s0;
				int r1 = t0.contents;
				Automaton.State s1 = automaton.get(r1);
				Automaton.Collection c1 = (Automaton.Collection) s1;
				if(c1.size() >= 1) {
					for(int r3=0;r3!=c1.size();++r3) {
						int r2 = c1.get(r3);
						Automaton.State s2 = automaton.get(r2);
						if(s2.kind == K_Equals) {
							Automaton.Term t2 = (Automaton.Term) s2;
							int r4 = t2.contents;
							Automaton.State s4 = automaton.get(r4);
							Automaton.List l4 = (Automaton.List) s4;
							int r5 = l4.get(0);
							int r6 = l4.get(1);
							Automaton.State s6 = automaton.get(r6);
							Automaton.Collection c6 = (Automaton.Collection) s6;
							for(int r8=0;r8!=c6.size();++r8) {
								int r7 = c6.get(r8);
								if(Runtime.accepts(type8,automaton,automaton.get(r7), SCHEMA)) {
									for(int r10=0;r10!=c6.size();++r10) {
										if(r10 == r8) { continue; }
										int r9 = c6.get(r10);
										if(Runtime.accepts(type27,automaton,automaton.get(r9), SCHEMA)) {
											int[] state = {r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, 0};
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
			int r2 = state[2]; // eq
			int r3 = state[3];
			int r5 = state[5]; // t
			int r7 = state[7]; // x
			int r8 = state[8];
			int r9 = state[9]; // y
			int r10 = state[10];
			Automaton.Collection c1 = (Automaton.Collection) automaton.get(state[1]);
			int[] c1children = new int[c1.size() - 1];
			for(int s1i=0, s1j=0; s1i != c1.size();++s1i) {
				if(s1i == r3) { continue; }
				c1children[s1j++] = c1.get(s1i);
			}
			Automaton.Set r11 = new Automaton.Set(c1children);
			Automaton.List t12 = new Automaton.List();
			for(int i13=0;i13<r11.size();i13++) {
				int r13 = (int) r11.get(i13);
				int r14 = automaton.substitute(r13, r7, r9);
				t12.add(r14);
			}
			Automaton.Set r12 = new Automaton.Set(t12.toArray());
			Automaton.Set r15 = r12.appendFront(r2); // eq append cs
			int r16 = automaton.add(r15);
			Automaton.Term r17 = new Automaton.Term(K_And, r16);
			int r18 = automaton.add(r17);
			if(r0 != r18) {
				return automaton.rewrite(r0, r18);
			}
			automaton.resize(nStates);
			return Automaton.K_VOID;
		}

	}
	private final static class Reduction_86 extends AbstractRewriteRule implements ReductionRule {

		public Reduction_86(Pattern.Term pattern) {
			super(pattern);
			put("name","LengthOf(Array)");
			put("rank",0);
		}

		public final void probe(Automaton automaton, int target, List<Reduction.Activation> activations) {
			int r0 = target;
			Automaton.State s0 = automaton.get(r0);
			if(s0.kind == K_LengthOf) {
				Automaton.Term t0 = (Automaton.Term) s0;
				int r1 = t0.contents;
				Automaton.State s1 = automaton.get(r1);
				if(s1.kind == K_Array) {
					Automaton.Term t1 = (Automaton.Term) s1;
					int r2 = t1.contents;
					Automaton.State s2 = automaton.get(r2);
					Automaton.List l2 = (Automaton.List) s2;
					int[] state = {r0, r1, r2, 0};
					activations.add(new Reduction.Activation(this,null,state));
				}
			}
		}

		public final int apply(Automaton automaton, int[] state) {
			int nStates = automaton.nStates();
			int r0 = state[0];
			Automaton.List r3 = ((Automaton.List) automaton.get(state[2])).sublist(0);
			Automaton.Int r4 = r3.lengthOf(); // |xs|
			Automaton.Real r5 = new Automaton.Real(r4.value);
			int r6 = automaton.add(r5);
			Automaton.Term r7 = new Automaton.Term(K_Num, r6);
			int r8 = automaton.add(r7);
			if(r0 != r8) {
				return automaton.rewrite(r0, r8);
			}
			automaton.resize(nStates);
			return Automaton.K_VOID;
		}

	}
	private final static class Reduction_87 extends AbstractRewriteRule implements ReductionRule {

		public Reduction_87(Pattern.Term pattern) {
			super(pattern);
			put("name","LengthOf(ArrayGen)");
			put("rank",2);
		}

		public final void probe(Automaton automaton, int target, List<Reduction.Activation> activations) {
			int r0 = target;
			Automaton.State s0 = automaton.get(r0);
			if(s0.kind == K_LengthOf) {
				Automaton.Term t0 = (Automaton.Term) s0;
				int r1 = t0.contents;
				Automaton.State s1 = automaton.get(r1);
				if(s1.kind == K_ArrayGen) {
					Automaton.Term t1 = (Automaton.Term) s1;
					int r2 = t1.contents;
					Automaton.State s2 = automaton.get(r2);
					Automaton.List l2 = (Automaton.List) s2;
					int r3 = l2.get(0);
					int r4 = l2.get(1);
					int[] state = {r0, r1, r2, r3, r4};
					activations.add(new Reduction.Activation(this,null,state));
				}
			}
		}

		public final int apply(Automaton automaton, int[] state) {
			int nStates = automaton.nStates();
			int r0 = state[0];
			int r3 = state[3]; // v
			int r4 = state[4]; // n
			if(r0 != r4) {
				return automaton.rewrite(r0, r4);
			}
			automaton.resize(nStates);
			return Automaton.K_VOID;
		}

	}
	// term $8<IndexOf($6<^[$2<^Expr<$51<Value<Null|Tuple(^[^$51...])|Bool<True|False>|Num(^real)|String(^string)|Array(^[^$51...])|ArrayGen(^[^$51,^$51])>>|Tuple(^[$2...])|$93<BExpr<Bool<True|False>|VExpr<$8|Var(^string)|Fn(^[^string,$2...])|Load(^[$2,^int])|LengthOf($2)>|And(^{^$93...})|Or(^{^$93...})|Not(^$93)|Equals(^[$132<^Type<Atom<NotT($155<^Proton<TupleT(^[$155...])|ArrayT($155)|Quark<AnyT|NullT|VoidT|BoolT|IntT|RealT|StringT|VarT(^string)|NominalT(^string)>>>)|Proton<TupleT(^[$155...])|ArrayT($155)|Quark<AnyT|NullT|VoidT|BoolT|IntT|RealT|StringT|VarT(^string)|NominalT(^string)>>>|NotT($132)|OrT(^{$132...})|AndT(^{$132...})|ArrayT($132)|TupleT(^[$132...])|FunctionT(^[$132,$132,$132...])>>,^{|$2,$2|}[$2,$2]])|Inequality(^[^AType<IntT|RealT>,$229<^AExpr<Num(^real)|VExpr<$8|Var(^string)|Fn(^[^string,$2...])|Load(^[$2,^int])|LengthOf($2)>|Sum(^[^real,^{|$229...|}[$229...]])|Mul(^[^real,^{|$229...|}[$229...]])|Div(^[$229,$229])>>])|Equation(^[^AType<IntT|RealT>,$229])|ForAll(^[^{^[^Var(^string),$132]...},^$93])|Exists(^[^{^[^Var(^string),$132]...},^$93])>>|AExpr<Num(^real)|VExpr<$8|Var(^string)|Fn(^[^string,$2...])|Load(^[$2,^int])|LengthOf($2)>|Sum(^[^real,^{|$229...|}[$229...]])|Mul(^[^real,^{|$229...|}[$229...]])|Div(^[$229,$229])>|SExpr<VExpr<$8|Var(^string)|Fn(^[^string,$2...])|Load(^[$2,^int])|LengthOf($2)>|Array(^[$2...])|ArrayGen($6)>>>,$2]>)>
	public final static int K_IndexOf = 36;
	public final static int IndexOf(Automaton automaton, int... r0) {
		int r1 = automaton.add(new Automaton.List(r0));
		return automaton.add(new Automaton.Term(K_IndexOf, r1));
	}
	public final static int IndexOf(Automaton automaton, List<Integer> r0) {
		int r1 = automaton.add(new Automaton.List(r0));
		return automaton.add(new Automaton.Term(K_IndexOf, r1));
	}

	private final static class Reduction_88 extends AbstractRewriteRule implements ReductionRule {

		public Reduction_88(Pattern.Term pattern) {
			super(pattern);
			put("name","IndexOf[Array]");
			put("rank",0);
		}

		public final void probe(Automaton automaton, int target, List<Reduction.Activation> activations) {
			int r0 = target;
			Automaton.State s0 = automaton.get(r0);
			if(s0.kind == K_IndexOf) {
				Automaton.Term t0 = (Automaton.Term) s0;
				int r1 = t0.contents;
				Automaton.State s1 = automaton.get(r1);
				Automaton.List l1 = (Automaton.List) s1;
				int r2 = l1.get(0);
				Automaton.State s2 = automaton.get(r2);
				if(s2.kind == K_Array) {
					Automaton.Term t2 = (Automaton.Term) s2;
					int r3 = t2.contents;
					Automaton.State s3 = automaton.get(r3);
					Automaton.List l3 = (Automaton.List) s3;
					int r5 = l1.get(1);
					Automaton.State s5 = automaton.get(r5);
					if(s5.kind == K_Num) {
						Automaton.Term t5 = (Automaton.Term) s5;
						int r6 = t5.contents;
						int[] state = {r0, r1, r2, r3, 0, r5, r6};
						activations.add(new Reduction.Activation(this,null,state));
					}
				}
			}
		}

		public final int apply(Automaton automaton, int[] state) {
			int nStates = automaton.nStates();
			int r0 = state[0];
			Automaton.List r4 = ((Automaton.List) automaton.get(state[3])).sublist(0);
			int r6 = state[6]; // i
			Automaton.Real r7 = (Automaton.Real) automaton.get(r6);
			Automaton.Int r8 = r7.numerator(); // |i|
			Automaton.Int r9 = new Automaton.Int(0); // 0
			boolean r10 = r8.compareTo(r9)>=0; // j ge 0
			boolean r11 = false;           // j ge 0 && j lt |xs|
			if(r10) {
				Automaton.Int r12 = r4.lengthOf(); // |xs|
				boolean r13 = r8.compareTo(r12)<0; // j lt |xs|
				r11 = r13;
			}
			if(r11) {
				int r14 = r4.indexOf(r8);      // xs[j]
				if(r0 != r14) {
					return automaton.rewrite(r0, r14);
				}
			}
			automaton.resize(nStates);
			return Automaton.K_VOID;
		}

	}
	private final static class Reduction_89 extends AbstractRewriteRule implements ReductionRule {

		public Reduction_89(Pattern.Term pattern) {
			super(pattern);
			put("name","IndexOf[ArrayGen]");
			put("rank",0);
		}

		public final void probe(Automaton automaton, int target, List<Reduction.Activation> activations) {
			int r0 = target;
			Automaton.State s0 = automaton.get(r0);
			if(s0.kind == K_IndexOf) {
				Automaton.Term t0 = (Automaton.Term) s0;
				int r1 = t0.contents;
				Automaton.State s1 = automaton.get(r1);
				Automaton.List l1 = (Automaton.List) s1;
				int r2 = l1.get(0);
				Automaton.State s2 = automaton.get(r2);
				if(s2.kind == K_ArrayGen) {
					Automaton.Term t2 = (Automaton.Term) s2;
					int r3 = t2.contents;
					Automaton.State s3 = automaton.get(r3);
					Automaton.List l3 = (Automaton.List) s3;
					int r4 = l3.get(0);
					int r5 = l3.get(1);
					int r6 = l1.get(1);
					int[] state = {r0, r1, r2, r3, r4, r5, r6};
					activations.add(new Reduction.Activation(this,null,state));
				}
			}
		}

		public final int apply(Automaton automaton, int[] state) {
			int nStates = automaton.nStates();
			int r0 = state[0];
			int r4 = state[4]; // v
			int r5 = state[5]; // n
			if(r0 != r4) {
				return automaton.rewrite(r0, r4);
			}
			automaton.resize(nStates);
			return Automaton.K_VOID;
		}

	}
	// term $19<ForAll($17<^[^{^[^Var(^string),$4<^Type<Atom<NotT($35<^Proton<TupleT(^[$35...])|ArrayT($35)|Quark<AnyT|NullT|VoidT|BoolT|IntT|RealT|StringT|VarT(^string)|NominalT(^string)>>>)|Proton<TupleT(^[$35...])|ArrayT($35)|Quark<AnyT|NullT|VoidT|BoolT|IntT|RealT|StringT|VarT(^string)|NominalT(^string)>>>|NotT($4)|OrT(^{$4...})|AndT(^{$4...})|ArrayT($4)|TupleT(^[$4...])|FunctionT(^[$4,$4,$4...])>>]...},$13<^$127<BExpr<$137<VExpr<Var(^string)|Fn(^[^string,$139<^Expr<$127|$186<Value<Null|Tuple(^[^$186...])|Bool<True|False>|Num(^real)|String(^string)|Array(^[^$186...])|ArrayGen(^[^$186,^$186])>>|Tuple(^[$139...])|$213<AExpr<$137|Num(^real)|Sum(^[^real,^{|^$213...|}[^$213...]])|Mul(^[^real,^{|^$213...|}[^$213...]])|Div(^[^$213,^$213])>>|SExpr<$137|Array(^[$139...])|ArrayGen(^[$139,$139])>>>...])|Load(^[$139,^int])|LengthOf($139)|IndexOf(^[$139,$139])>>|Bool<True|False>|And(^{$13...})|Or(^{$13...})|Not($13)|Equals(^[$4,^{|$139,$139|}[$139,$139]])|Inequality(^[^AType<IntT|RealT>,^$213])|Equation(^[^AType<IntT|RealT>,^$213])|$19|Exists($17)>>>]>)>
	public final static int K_ForAll = 37;
	public final static int ForAll(Automaton automaton, int... r0) {
		int r1 = automaton.add(new Automaton.List(r0));
		return automaton.add(new Automaton.Term(K_ForAll, r1));
	}
	public final static int ForAll(Automaton automaton, List<Integer> r0) {
		int r1 = automaton.add(new Automaton.List(r0));
		return automaton.add(new Automaton.Term(K_ForAll, r1));
	}

	private final static class Reduction_90 extends AbstractRewriteRule implements ReductionRule {

		public Reduction_90(Pattern.Term pattern) {
			super(pattern);
			put("name","ForAll({},Bool)");
			put("rank",1);
		}

		public final void probe(Automaton automaton, int target, List<Reduction.Activation> activations) {
			int r0 = target;
			Automaton.State s0 = automaton.get(r0);
			if(s0.kind == K_ForAll) {
				Automaton.Term t0 = (Automaton.Term) s0;
				int r1 = t0.contents;
				Automaton.State s1 = automaton.get(r1);
				Automaton.List l1 = (Automaton.List) s1;
				int r2 = l1.get(0);
				Automaton.State s2 = automaton.get(r2);
				Automaton.Collection c2 = (Automaton.Collection) s2;
				int r4 = l1.get(1);
				int[] c2children = new int[c2.size() - 0];
				for(int s2i=0, s2j=0; s2i != c2.size();++s2i) {
					c2children[s2j++] = c2.get(s2i);
				}
				Automaton.Set r3 = new Automaton.Set(c2children);
				boolean r5 = Runtime.accepts(type29, automaton, r4, SCHEMA); // be is ^Bool<True|False>
				Automaton.Int r6 = r3.lengthOf(); // |qs|
				Automaton.Int r7 = new Automaton.Int(0); // 0
				boolean r8 = r6.equals(r7);    // |qs| eq 0
				boolean r9 = r5 || r8;         // be is ^Bool<True|False> || |qs| eq 0
				if(r9) { // REQUIRES
					int[] state = {r0, r1, r2, 0, r4};
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
			int r4 = state[4]; // be
			if(r0 != r4) {
				return automaton.rewrite(r0, r4);
			}
			automaton.resize(nStates);
			return Automaton.K_VOID;
		}

	}
	private final static class Reduction_91 extends AbstractRewriteRule implements ReductionRule {

		public Reduction_91(Pattern.Term pattern) {
			super(pattern);
			put("name","Not(ForAll)");
			put("rank",0);
		}

		public final void probe(Automaton automaton, int target, List<Reduction.Activation> activations) {
			int r0 = target;
			Automaton.State s0 = automaton.get(r0);
			if(s0.kind == K_Not) {
				Automaton.Term t0 = (Automaton.Term) s0;
				int r1 = t0.contents;
				Automaton.State s1 = automaton.get(r1);
				if(s1.kind == K_ForAll) {
					Automaton.Term t1 = (Automaton.Term) s1;
					int r2 = t1.contents;
					Automaton.State s2 = automaton.get(r2);
					Automaton.List l2 = (Automaton.List) s2;
					int r3 = l2.get(0);
					Automaton.State s3 = automaton.get(r3);
					Automaton.Collection c3 = (Automaton.Collection) s3;
					int r5 = l2.get(1);
					int[] state = {r0, r1, r2, r3, 0, r5};
					activations.add(new Reduction.Activation(this,null,state));
				}
			}
		}

		public final int apply(Automaton automaton, int[] state) {
			int nStates = automaton.nStates();
			int r0 = state[0];
			int r3 = state[3]; // vars
			int r5 = state[5]; // be
			Automaton.Term r6 = new Automaton.Term(K_Not, r5);
			int r7 = automaton.add(r6);
			Automaton.List r8 = new Automaton.List(r3, r7); // [varsNot(be)]
			int r9 = automaton.add(r8);
			Automaton.Term r10 = new Automaton.Term(K_Exists, r9);
			int r11 = automaton.add(r10);
			if(r0 != r11) {
				return automaton.rewrite(r0, r11);
			}
			automaton.resize(nStates);
			return Automaton.K_VOID;
		}

	}
	private final static class Reduction_92 extends AbstractRewriteRule implements ReductionRule {

		public Reduction_92(Pattern.Term pattern) {
			super(pattern);
			put("name","ForAll[ForAll]");
			put("rank",1);
		}

		public final void probe(Automaton automaton, int target, List<Reduction.Activation> activations) {
			int r0 = target;
			Automaton.State s0 = automaton.get(r0);
			if(s0.kind == K_ForAll) {
				Automaton.Term t0 = (Automaton.Term) s0;
				int r1 = t0.contents;
				Automaton.State s1 = automaton.get(r1);
				Automaton.List l1 = (Automaton.List) s1;
				int r2 = l1.get(0);
				Automaton.State s2 = automaton.get(r2);
				Automaton.Collection c2 = (Automaton.Collection) s2;
				int r4 = l1.get(1);
				Automaton.State s4 = automaton.get(r4);
				if(s4.kind == K_ForAll) {
					Automaton.Term t4 = (Automaton.Term) s4;
					int r5 = t4.contents;
					Automaton.State s5 = automaton.get(r5);
					Automaton.List l5 = (Automaton.List) s5;
					int r6 = l5.get(0);
					Automaton.State s6 = automaton.get(r6);
					Automaton.Collection c6 = (Automaton.Collection) s6;
					int r8 = l5.get(1);
					int[] state = {r0, r1, r2, 0, r4, r5, r6, 0, r8};
					activations.add(new Reduction.Activation(this,null,state));
				}
			}
		}

		public final int apply(Automaton automaton, int[] state) {
			int nStates = automaton.nStates();
			int r0 = state[0];
			int r2 = state[2]; // xs
			int r6 = state[6]; // ys
			int r8 = state[8]; // e
			Automaton.Set r9 = (Automaton.Set) automaton.get(r2);
			Automaton.Set r10 = (Automaton.Set) automaton.get(r6);
			Automaton.Set r11 = r9.append(r10); // xs append ys
			int r12 = automaton.add(r11);
			Automaton.List r13 = new Automaton.List(r12, r8); // [xs append yse]
			int r14 = automaton.add(r13);
			Automaton.Term r15 = new Automaton.Term(K_ForAll, r14);
			int r16 = automaton.add(r15);
			if(r0 != r16) {
				return automaton.rewrite(r0, r16);
			}
			automaton.resize(nStates);
			return Automaton.K_VOID;
		}

	}
	private final static class Reduction_93 extends AbstractRewriteRule implements ReductionRule {

		public Reduction_93(Pattern.Term pattern) {
			super(pattern);
			put("name","ForAll[{Var,Var...},BExpr]");
			put("rank",1);
		}

		public final void probe(Automaton automaton, int target, List<Reduction.Activation> activations) {
			int r0 = target;
			Automaton.State s0 = automaton.get(r0);
			if(s0.kind == K_ForAll) {
				Automaton.Term t0 = (Automaton.Term) s0;
				int r1 = t0.contents;
				Automaton.State s1 = automaton.get(r1);
				Automaton.List l1 = (Automaton.List) s1;
				int r2 = l1.get(0);
				Automaton.State s2 = automaton.get(r2);
				Automaton.Collection c2 = (Automaton.Collection) s2;
				if(c2.size() >= 1) {
					for(int r4=0;r4!=c2.size();++r4) {
						int r3 = c2.get(r4);
						Automaton.State s3 = automaton.get(r3);
						Automaton.List l3 = (Automaton.List) s3;
						int r5 = l3.get(0);
						int r6 = l3.get(1);
						int r8 = l1.get(1);
						int[] state = {r0, r1, r2, r3, r4, r5, r6, 0, r8};
						activations.add(new Reduction.Activation(this,null,state));
					}
				}
			}
		}

		public final int apply(Automaton automaton, int[] state) {
			int nStates = automaton.nStates();
			int r0 = state[0];
			int r4 = state[4];
			int r5 = state[5]; // v
			Automaton.Collection c2 = (Automaton.Collection) automaton.get(state[2]);
			int[] c2children = new int[c2.size() - 1];
			for(int s2i=0, s2j=0; s2i != c2.size();++s2i) {
				if(s2i == r4) { continue; }
				c2children[s2j++] = c2.get(s2i);
			}
			Automaton.Set r7 = new Automaton.Set(c2children);
			int r8 = state[8]; // e
			Automaton.List r9 = new Automaton.List(r8, r5); // [ev]
			boolean r10 = Solver$native.contains(automaton, r9);
			boolean r11 = !r10;            // !contains([ev])
			if(r11) {
				int r12 = automaton.add(r7);
				Automaton.List r13 = new Automaton.List(r12, r8); // [xse]
				int r14 = automaton.add(r13);
				Automaton.Term r15 = new Automaton.Term(K_ForAll, r14);
				int r16 = automaton.add(r15);
				if(r0 != r16) {
					return automaton.rewrite(r0, r16);
				}
			}
			automaton.resize(nStates);
			return Automaton.K_VOID;
		}

	}
	private final static class Inference_4 extends AbstractRewriteRule implements InferenceRule {

		public Inference_4(Pattern.Term pattern) {
			super(pattern);
			put("name","And{BExpr,ForAll,BExpr...}");
			put("rank",3);
		}

		public final void probe(Automaton automaton, int root, int target, List<Inference.Activation> activations) {
			int r0 = target;
			Automaton.State s0 = automaton.get(r0);
			if(s0.kind == K_And) {
				Automaton.Term t0 = (Automaton.Term) s0;
				int r1 = t0.contents;
				Automaton.State s1 = automaton.get(r1);
				Automaton.Collection c1 = (Automaton.Collection) s1;
				if(c1.size() >= 2) {
					for(int r3=0;r3!=c1.size();++r3) {
						int r2 = c1.get(r3);
						for(int r5=0;r5!=c1.size();++r5) {
							if(r5 == r3) { continue; }
							int r4 = c1.get(r5);
							Automaton.State s4 = automaton.get(r4);
							if(s4.kind == K_ForAll) {
								Automaton.Term t4 = (Automaton.Term) s4;
								int r6 = t4.contents;
								Automaton.State s6 = automaton.get(r6);
								Automaton.List l6 = (Automaton.List) s6;
								int r7 = l6.get(0);
								Automaton.State s7 = automaton.get(r7);
								Automaton.Collection c7 = (Automaton.Collection) s7;
								if(c7.size() >= 1) {
									for(int r9=0;r9!=c7.size();++r9) {
										int r8 = c7.get(r9);
										Automaton.State s8 = automaton.get(r8);
										Automaton.List l8 = (Automaton.List) s8;
										int r10 = l8.get(0);
										int r11 = l8.get(1);
										int r13 = l6.get(1);
										int[] c1children = new int[c1.size() - 2];
										for(int s1i=0, s1j=0; s1i != c1.size();++s1i) {
											if(s1i == r3 || s1i == r5) { continue; }
											c1children[s1j++] = c1.get(s1i);
										}
										Automaton.Set r14 = new Automaton.Set(c1children);
										boolean r15 = Runtime.accepts(type30, automaton, r2, SCHEMA); // e1 is ^$20<ForAll($18<^[^{^[^Var(^string),$5<^Type<Atom<NotT($36<^Proton<TupleT(^[$36...])|ArrayT($36)|Quark<AnyT|NullT|VoidT|BoolT|IntT|RealT|StringT|VarT(^string)|NominalT(^string)>>>)|Proton<TupleT(^[$36...])|ArrayT($36)|Quark<AnyT|NullT|VoidT|BoolT|IntT|RealT|StringT|VarT(^string)|NominalT(^string)>>>|NotT($5)|OrT(^{$5...})|AndT(^{$5...})|ArrayT($5)|TupleT(^[$5...])|FunctionT(^[$5,$5,$5...])>>]...},$14<^$128<BExpr<$138<VExpr<Var(^string)|Fn(^[^string,$140<^Expr<$128|$187<Value<Null|Tuple(^[^$187...])|Bool<True|False>|Num(^real)|String(^string)|Array(^[^$187...])|ArrayGen(^[^$187,^$187])>>|Tuple(^[$140...])|$214<AExpr<$138|Num(^real)|Sum(^[^real,^{|^$214...|}[^$214...]])|Mul(^[^real,^{|^$214...|}[^$214...]])|Div(^[^$214,^$214])>>|SExpr<$138|Array(^[$140...])|ArrayGen(^[$140,$140])>>>...])|Load(^[$140,^int])|LengthOf($140)|IndexOf(^[$140,$140])>>|Bool<True|False>|And(^{$14...})|Or(^{$14...})|Not($14)|Equals(^[$5,^{|$140,$140|}[$140,$140]])|Inequality(^[^AType<IntT|RealT>,^$214])|Equation(^[^AType<IntT|RealT>,^$214])|$20|Exists($18)>>>]>)>
										boolean r16 = !r15;            // !e1 is ^$20<ForAll($18<^[^{^[^Var(^string),$5<^Type<Atom<NotT($36<^Proton<TupleT(^[$36...])|ArrayT($36)|Quark<AnyT|NullT|VoidT|BoolT|IntT|RealT|StringT|VarT(^string)|NominalT(^string)>>>)|Proton<TupleT(^[$36...])|ArrayT($36)|Quark<AnyT|NullT|VoidT|BoolT|IntT|RealT|StringT|VarT(^string)|NominalT(^string)>>>|NotT($5)|OrT(^{$5...})|AndT(^{$5...})|ArrayT($5)|TupleT(^[$5...])|FunctionT(^[$5,$5,$5...])>>]...},$14<^$128<BExpr<$138<VExpr<Var(^string)|Fn(^[^string,$140<^Expr<$128|$187<Value<Null|Tuple(^[^$187...])|Bool<True|False>|Num(^real)|String(^string)|Array(^[^$187...])|ArrayGen(^[^$187,^$187])>>|Tuple(^[$140...])|$214<AExpr<$138|Num(^real)|Sum(^[^real,^{|^$214...|}[^$214...]])|Mul(^[^real,^{|^$214...|}[^$214...]])|Div(^[^$214,^$214])>>|SExpr<$138|Array(^[$140...])|ArrayGen(^[$140,$140])>>>...])|Load(^[$140,^int])|LengthOf($140)|IndexOf(^[$140,$140])>>|Bool<True|False>|And(^{$14...})|Or(^{$14...})|Not($14)|Equals(^[$5,^{|$140,$140|}[$140,$140]])|Inequality(^[^AType<IntT|RealT>,^$214])|Equation(^[^AType<IntT|RealT>,^$214])|$20|Exists($18)>>>]>)>
										if(r16) { // REQUIRES
											int[] state = {r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, 0, r13, 0};
											activations.add(new Inference.Activation(this,root,null,state));
										}
									}
								}
							}
						}
					}
				}
			}
		}

		public final int apply(Automaton automaton, int root, int[] state) {
			int nStates = automaton.nStates();
			int r0 = state[0];
			int r2 = state[2]; // e1
			int r3 = state[3];
			int r4 = state[4]; // qf
			int r5 = state[5];
			int r7 = state[7]; // vs
			int r9 = state[9];
			int r13 = state[13]; // e2
			Automaton.Collection c1 = (Automaton.Collection) automaton.get(state[1]);
			int[] c1children = new int[c1.size() - 2];
			for(int s1i=0, s1j=0; s1i != c1.size();++s1i) {
				if(s1i == r3 || s1i == r5) { continue; }
				c1children[s1j++] = c1.get(s1i);
			}
			Automaton.Set r14 = new Automaton.Set(c1children);
			Automaton.List r15 = new Automaton.List(r2, r7, r13); // [e1vse2]
			Automaton.Set r16 = Solver$native.instantiate(automaton, r15);
			Automaton.Int r17 = r16.lengthOf(); // |instantiations|
			Automaton.Int r18 = new Automaton.Int(0); // 0
			boolean r19 = r17.compareTo(r18)>0; // |instantiations| gt 0
			if(r19) {
				Automaton.Set r20 = new Automaton.Set(r2, r4); // {e1qf}
				Automaton.Set r21 = r14.append(r16); // es append instantiations
				Automaton.Set r22 = r20.append(r21); // {e1qf} append es append instantiations
				int r23 = automaton.add(r22);
				Automaton.Term r24 = new Automaton.Term(K_And, r23);
				int r25 = automaton.add(r24);
				if(r0 != r25) {
					return automaton.substitute(root,r0, r25);
				}
			}
			automaton.resize(nStates);
			return Automaton.K_VOID;
		}

	}
	// term $19<Exists($17<^[^{^[^Var(^string),$4<^Type<Atom<NotT($35<^Proton<TupleT(^[$35...])|ArrayT($35)|Quark<AnyT|NullT|VoidT|BoolT|IntT|RealT|StringT|VarT(^string)|NominalT(^string)>>>)|Proton<TupleT(^[$35...])|ArrayT($35)|Quark<AnyT|NullT|VoidT|BoolT|IntT|RealT|StringT|VarT(^string)|NominalT(^string)>>>|NotT($4)|OrT(^{$4...})|AndT(^{$4...})|ArrayT($4)|TupleT(^[$4...])|FunctionT(^[$4,$4,$4...])>>]...},$13<^$127<BExpr<$137<VExpr<Var(^string)|Fn(^[^string,$139<^Expr<$127|$186<Value<Null|Tuple(^[^$186...])|Bool<True|False>|Num(^real)|String(^string)|Array(^[^$186...])|ArrayGen(^[^$186,^$186])>>|Tuple(^[$139...])|$213<AExpr<$137|Num(^real)|Sum(^[^real,^{|^$213...|}[^$213...]])|Mul(^[^real,^{|^$213...|}[^$213...]])|Div(^[^$213,^$213])>>|SExpr<$137|Array(^[$139...])|ArrayGen(^[$139,$139])>>>...])|Load(^[$139,^int])|LengthOf($139)|IndexOf(^[$139,$139])>>|Bool<True|False>|And(^{$13...})|Or(^{$13...})|Not($13)|Equals(^[$4,^{|$139,$139|}[$139,$139]])|Inequality(^[^AType<IntT|RealT>,^$213])|Equation(^[^AType<IntT|RealT>,^$213])|$19|ForAll($17)>>>]>)>
	public final static int K_Exists = 38;
	public final static int Exists(Automaton automaton, int... r0) {
		int r1 = automaton.add(new Automaton.List(r0));
		return automaton.add(new Automaton.Term(K_Exists, r1));
	}
	public final static int Exists(Automaton automaton, List<Integer> r0) {
		int r1 = automaton.add(new Automaton.List(r0));
		return automaton.add(new Automaton.Term(K_Exists, r1));
	}

	private final static class Reduction_94 extends AbstractRewriteRule implements ReductionRule {

		public Reduction_94(Pattern.Term pattern) {
			super(pattern);
			put("name","Exists[{},Bool]");
			put("rank",1);
		}

		public final void probe(Automaton automaton, int target, List<Reduction.Activation> activations) {
			int r0 = target;
			Automaton.State s0 = automaton.get(r0);
			if(s0.kind == K_Exists) {
				Automaton.Term t0 = (Automaton.Term) s0;
				int r1 = t0.contents;
				Automaton.State s1 = automaton.get(r1);
				Automaton.List l1 = (Automaton.List) s1;
				int r2 = l1.get(0);
				Automaton.State s2 = automaton.get(r2);
				Automaton.Collection c2 = (Automaton.Collection) s2;
				int r4 = l1.get(1);
				int[] c2children = new int[c2.size() - 0];
				for(int s2i=0, s2j=0; s2i != c2.size();++s2i) {
					c2children[s2j++] = c2.get(s2i);
				}
				Automaton.Set r3 = new Automaton.Set(c2children);
				boolean r5 = Runtime.accepts(type29, automaton, r4, SCHEMA); // be is ^Bool<True|False>
				Automaton.Int r6 = r3.lengthOf(); // |qs|
				Automaton.Int r7 = new Automaton.Int(0); // 0
				boolean r8 = r6.equals(r7);    // |qs| eq 0
				boolean r9 = r5 || r8;         // be is ^Bool<True|False> || |qs| eq 0
				if(r9) { // REQUIRES
					int[] state = {r0, r1, r2, 0, r4};
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
			int r4 = state[4]; // be
			if(r0 != r4) {
				return automaton.rewrite(r0, r4);
			}
			automaton.resize(nStates);
			return Automaton.K_VOID;
		}

	}
	private final static class Reduction_95 extends AbstractRewriteRule implements ReductionRule {

		public Reduction_95(Pattern.Term pattern) {
			super(pattern);
			put("name","Not(Exists)");
			put("rank",2);
		}

		public final void probe(Automaton automaton, int target, List<Reduction.Activation> activations) {
			int r0 = target;
			Automaton.State s0 = automaton.get(r0);
			if(s0.kind == K_Not) {
				Automaton.Term t0 = (Automaton.Term) s0;
				int r1 = t0.contents;
				Automaton.State s1 = automaton.get(r1);
				if(s1.kind == K_Exists) {
					Automaton.Term t1 = (Automaton.Term) s1;
					int r2 = t1.contents;
					Automaton.State s2 = automaton.get(r2);
					Automaton.List l2 = (Automaton.List) s2;
					int r3 = l2.get(0);
					Automaton.State s3 = automaton.get(r3);
					Automaton.Collection c3 = (Automaton.Collection) s3;
					int r5 = l2.get(1);
					int[] state = {r0, r1, r2, r3, 0, r5};
					activations.add(new Reduction.Activation(this,null,state));
				}
			}
		}

		public final int apply(Automaton automaton, int[] state) {
			int nStates = automaton.nStates();
			int r0 = state[0];
			int r3 = state[3]; // vars
			int r5 = state[5]; // be
			Automaton.Term r6 = new Automaton.Term(K_Not, r5);
			int r7 = automaton.add(r6);
			Automaton.List r8 = new Automaton.List(r3, r7); // [varsNot(be)]
			int r9 = automaton.add(r8);
			Automaton.Term r10 = new Automaton.Term(K_ForAll, r9);
			int r11 = automaton.add(r10);
			if(r0 != r11) {
				return automaton.rewrite(r0, r11);
			}
			automaton.resize(nStates);
			return Automaton.K_VOID;
		}

	}
	private final static class Reduction_96 extends AbstractRewriteRule implements ReductionRule {

		public Reduction_96(Pattern.Term pattern) {
			super(pattern);
			put("name","Exists[Exists,BExpr]");
			put("rank",1);
		}

		public final void probe(Automaton automaton, int target, List<Reduction.Activation> activations) {
			int r0 = target;
			Automaton.State s0 = automaton.get(r0);
			if(s0.kind == K_Exists) {
				Automaton.Term t0 = (Automaton.Term) s0;
				int r1 = t0.contents;
				Automaton.State s1 = automaton.get(r1);
				Automaton.List l1 = (Automaton.List) s1;
				int r2 = l1.get(0);
				Automaton.State s2 = automaton.get(r2);
				Automaton.Collection c2 = (Automaton.Collection) s2;
				int r4 = l1.get(1);
				Automaton.State s4 = automaton.get(r4);
				if(s4.kind == K_Exists) {
					Automaton.Term t4 = (Automaton.Term) s4;
					int r5 = t4.contents;
					Automaton.State s5 = automaton.get(r5);
					Automaton.List l5 = (Automaton.List) s5;
					int r6 = l5.get(0);
					Automaton.State s6 = automaton.get(r6);
					Automaton.Collection c6 = (Automaton.Collection) s6;
					int r8 = l5.get(1);
					int[] state = {r0, r1, r2, 0, r4, r5, r6, 0, r8};
					activations.add(new Reduction.Activation(this,null,state));
				}
			}
		}

		public final int apply(Automaton automaton, int[] state) {
			int nStates = automaton.nStates();
			int r0 = state[0];
			int r2 = state[2]; // xs
			int r6 = state[6]; // ys
			int r8 = state[8]; // e
			Automaton.Set r9 = (Automaton.Set) automaton.get(r2);
			Automaton.Set r10 = (Automaton.Set) automaton.get(r6);
			Automaton.Set r11 = r9.append(r10); // xs append ys
			int r12 = automaton.add(r11);
			Automaton.List r13 = new Automaton.List(r12, r8); // [xs append yse]
			int r14 = automaton.add(r13);
			Automaton.Term r15 = new Automaton.Term(K_Exists, r14);
			int r16 = automaton.add(r15);
			if(r0 != r16) {
				return automaton.rewrite(r0, r16);
			}
			automaton.resize(nStates);
			return Automaton.K_VOID;
		}

	}
	private final static class Reduction_97 extends AbstractRewriteRule implements ReductionRule {

		public Reduction_97(Pattern.Term pattern) {
			super(pattern);
			put("name","And{Exists,BExpr...}");
			put("rank",1);
		}

		public final void probe(Automaton automaton, int target, List<Reduction.Activation> activations) {
			int r0 = target;
			Automaton.State s0 = automaton.get(r0);
			if(s0.kind == K_And) {
				Automaton.Term t0 = (Automaton.Term) s0;
				int r1 = t0.contents;
				Automaton.State s1 = automaton.get(r1);
				Automaton.Collection c1 = (Automaton.Collection) s1;
				if(c1.size() >= 1) {
					for(int r3=0;r3!=c1.size();++r3) {
						int r2 = c1.get(r3);
						Automaton.State s2 = automaton.get(r2);
						if(s2.kind == K_Exists) {
							Automaton.Term t2 = (Automaton.Term) s2;
							int r4 = t2.contents;
							Automaton.State s4 = automaton.get(r4);
							Automaton.List l4 = (Automaton.List) s4;
							int r5 = l4.get(0);
							Automaton.State s5 = automaton.get(r5);
							Automaton.Collection c5 = (Automaton.Collection) s5;
							int r7 = l4.get(1);
							int[] state = {r0, r1, r2, r3, r4, r5, 0, r7, 0};
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
			int r5 = state[5]; // vs
			int r7 = state[7]; // e
			Automaton.Collection c1 = (Automaton.Collection) automaton.get(state[1]);
			int[] c1children = new int[c1.size() - 1];
			for(int s1i=0, s1j=0; s1i != c1.size();++s1i) {
				if(s1i == r3) { continue; }
				c1children[s1j++] = c1.get(s1i);
			}
			Automaton.Set r8 = new Automaton.Set(c1children);
			Automaton.Set r9 = r8.appendFront(r7); // e append es
			int r10 = automaton.add(r9);
			Automaton.Term r11 = new Automaton.Term(K_And, r10);
			int r12 = automaton.add(r11);
			Automaton.List r13 = new Automaton.List(r5, r12); // [vsAnd(e append es)]
			int r14 = automaton.add(r13);
			Automaton.Term r15 = new Automaton.Term(K_Exists, r14);
			int r16 = automaton.add(r15);
			if(r0 != r16) {
				return automaton.rewrite(r0, r16);
			}
			automaton.resize(nStates);
			return Automaton.K_VOID;
		}

	}
	// term Is(^[$2<^Expr<$53<Value<Null|Tuple(^[^$53...])|Bool<True|False>|Num(^real)|String(^string)|Array(^[^$53...])|ArrayGen(^[^$53,^$53])>>|Tuple(^[$2...])|$95<BExpr<Bool<True|False>|VExpr<Var(^string)|Fn(^[^string,$2...])|Load(^[$2,^int])|LengthOf($2)|IndexOf(^[$2,$2])>|And(^{^$95...})|Or(^{^$95...})|Not(^$95)|Equals(^[$4<^Type<Atom<NotT($162<^Proton<TupleT(^[$162...])|ArrayT($162)|Quark<AnyT|NullT|VoidT|BoolT|IntT|RealT|StringT|VarT(^string)|NominalT(^string)>>>)|Proton<TupleT(^[$162...])|ArrayT($162)|Quark<AnyT|NullT|VoidT|BoolT|IntT|RealT|StringT|VarT(^string)|NominalT(^string)>>>|NotT($4)|OrT(^{$4...})|AndT(^{$4...})|ArrayT($4)|TupleT(^[$4...])|FunctionT(^[$4,$4,$4...])>>,^{|$2,$2|}[$2,$2]])|Inequality(^[^AType<IntT|RealT>,$236<^AExpr<Num(^real)|VExpr<Var(^string)|Fn(^[^string,$2...])|Load(^[$2,^int])|LengthOf($2)|IndexOf(^[$2,$2])>|Sum(^[^real,^{|$236...|}[$236...]])|Mul(^[^real,^{|$236...|}[$236...]])|Div(^[$236,$236])>>])|Equation(^[^AType<IntT|RealT>,$236])|ForAll(^[^{^[^Var(^string),$4]...},^$95])|Exists(^[^{^[^Var(^string),$4]...},^$95])>>|AExpr<Num(^real)|VExpr<Var(^string)|Fn(^[^string,$2...])|Load(^[$2,^int])|LengthOf($2)|IndexOf(^[$2,$2])>|Sum(^[^real,^{|$236...|}[$236...]])|Mul(^[^real,^{|$236...|}[$236...]])|Div(^[$236,$236])>|SExpr<VExpr<Var(^string)|Fn(^[^string,$2...])|Load(^[$2,^int])|LengthOf($2)|IndexOf(^[$2,$2])>|Array(^[$2...])|ArrayGen(^[$2,$2])>>>,$4])
	public final static int K_Is = 39;
	public final static int Is(Automaton automaton, int... r0) {
		int r1 = automaton.add(new Automaton.List(r0));
		return automaton.add(new Automaton.Term(K_Is, r1));
	}
	public final static int Is(Automaton automaton, List<Integer> r0) {
		int r1 = automaton.add(new Automaton.List(r0));
		return automaton.add(new Automaton.Term(K_Is, r1));
	}

	private final static class Reduction_98 extends AbstractRewriteRule implements ReductionRule {

		public Reduction_98(Pattern.Term pattern) {
			super(pattern);
			put("name","Is_1");
		}

		public final void probe(Automaton automaton, int target, List<Reduction.Activation> activations) {
			int r0 = target;
			Automaton.State s0 = automaton.get(r0);
			if(s0.kind == K_Is) {
				Automaton.Term t0 = (Automaton.Term) s0;
				int r1 = t0.contents;
				Automaton.State s1 = automaton.get(r1);
				Automaton.List l1 = (Automaton.List) s1;
				int r2 = l1.get(0);
				int r3 = l1.get(1);
				if(Runtime.accepts(type1,automaton,automaton.get(r3), SCHEMA)) {
					int[] state = {r0, r1, r2, r3};
					activations.add(new Reduction.Activation(this,null,state));
				}
			}
		}

		public final int apply(Automaton automaton, int[] state) {
			int nStates = automaton.nStates();
			int r0 = state[0];
			int r2 = state[2]; // e
			Automaton.Term r4 = False;
			int r5 = automaton.add(r4);
			if(r0 != r5) {
				return automaton.rewrite(r0, r5);
			}
			automaton.resize(nStates);
			return Automaton.K_VOID;
		}

	}
	private final static class Reduction_99 extends AbstractRewriteRule implements ReductionRule {

		public Reduction_99(Pattern.Term pattern) {
			super(pattern);
			put("name","Is_2");
		}

		public final void probe(Automaton automaton, int target, List<Reduction.Activation> activations) {
			int r0 = target;
			Automaton.State s0 = automaton.get(r0);
			if(s0.kind == K_Not) {
				Automaton.Term t0 = (Automaton.Term) s0;
				int r1 = t0.contents;
				Automaton.State s1 = automaton.get(r1);
				if(s1.kind == K_Is) {
					Automaton.Term t1 = (Automaton.Term) s1;
					int r2 = t1.contents;
					Automaton.State s2 = automaton.get(r2);
					Automaton.List l2 = (Automaton.List) s2;
					int r3 = l2.get(0);
					int r4 = l2.get(1);
					int[] state = {r0, r1, r2, r3, r4};
					activations.add(new Reduction.Activation(this,null,state));
				}
			}
		}

		public final int apply(Automaton automaton, int[] state) {
			int nStates = automaton.nStates();
			int r0 = state[0];
			int r3 = state[3]; // e
			int r4 = state[4]; // t
			Automaton.Term r5 = new Automaton.Term(K_NotT, r4);
			int r6 = automaton.add(r5);
			Automaton.List r7 = new Automaton.List(r3, r6); // [eNotT(t)]
			int r8 = automaton.add(r7);
			Automaton.Term r9 = new Automaton.Term(K_Is, r8);
			int r10 = automaton.add(r9);
			if(r0 != r10) {
				return automaton.rewrite(r0, r10);
			}
			automaton.resize(nStates);
			return Automaton.K_VOID;
		}

	}
	private final static class Reduction_100 extends AbstractRewriteRule implements ReductionRule {

		public Reduction_100(Pattern.Term pattern) {
			super(pattern);
			put("name","Is_3");
		}

		public final void probe(Automaton automaton, int target, List<Reduction.Activation> activations) {
			int r0 = target;
			Automaton.State s0 = automaton.get(r0);
			if(s0.kind == K_And) {
				Automaton.Term t0 = (Automaton.Term) s0;
				int r1 = t0.contents;
				Automaton.State s1 = automaton.get(r1);
				Automaton.Collection c1 = (Automaton.Collection) s1;
				if(c1.size() >= 2) {
					for(int r3=0;r3!=c1.size();++r3) {
						int r2 = c1.get(r3);
						Automaton.State s2 = automaton.get(r2);
						if(s2.kind == K_Is) {
							Automaton.Term t2 = (Automaton.Term) s2;
							int r4 = t2.contents;
							Automaton.State s4 = automaton.get(r4);
							Automaton.List l4 = (Automaton.List) s4;
							int r5 = l4.get(0);
							int r6 = l4.get(1);
							for(int r8=0;r8!=c1.size();++r8) {
								if(r8 == r3) { continue; }
								int r7 = c1.get(r8);
								Automaton.State s7 = automaton.get(r7);
								if(s7.kind == K_Is) {
									Automaton.Term t7 = (Automaton.Term) s7;
									int r9 = t7.contents;
									Automaton.State s9 = automaton.get(r9);
									Automaton.List l9 = (Automaton.List) s9;
									int r10 = l9.get(0);
									int r11 = l9.get(1);
									int[] c1children = new int[c1.size() - 2];
									for(int s1i=0, s1j=0; s1i != c1.size();++s1i) {
										if(s1i == r3 || s1i == r8) { continue; }
										c1children[s1j++] = c1.get(s1i);
									}
									Automaton.Set r12 = new Automaton.Set(c1children);
									boolean r13 = r5 == r10;       // e1 eq e2
									if(r13) { // REQUIRES
										int[] state = {r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, 0};
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
			int r5 = state[5]; // e1
			int r6 = state[6]; // t1
			int r8 = state[8];
			int r10 = state[10]; // e2
			int r11 = state[11]; // t2
			Automaton.Collection c1 = (Automaton.Collection) automaton.get(state[1]);
			int[] c1children = new int[c1.size() - 2];
			for(int s1i=0, s1j=0; s1i != c1.size();++s1i) {
				if(s1i == r3 || s1i == r8) { continue; }
				c1children[s1j++] = c1.get(s1i);
			}
			Automaton.Set r12 = new Automaton.Set(c1children);
			Automaton.Set r13 = new Automaton.Set(r6, r11); // {t1t2}
			int r14 = automaton.add(r13);
			Automaton.Term r15 = new Automaton.Term(K_AndT, r14);
			int r16 = automaton.add(r15);
			Automaton.List r17 = new Automaton.List(r5, r16); // [e1AndT({t1t2})]
			int r18 = automaton.add(r17);
			Automaton.Term r19 = new Automaton.Term(K_Is, r18);
			int r20 = automaton.add(r19);
			Automaton.Set r21 = new Automaton.Set(r20); // {Is([e1AndT({t1t2})])}
			Automaton.Set r22 = r21.append(r12); // {Is([e1AndT({t1t2})])} append bs
			int r23 = automaton.add(r22);
			Automaton.Term r24 = new Automaton.Term(K_And, r23);
			int r25 = automaton.add(r24);
			if(r0 != r25) {
				return automaton.rewrite(r0, r25);
			}
			automaton.resize(nStates);
			return Automaton.K_VOID;
		}

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
		Schema.Term("FunctionT",Schema.List(true,Schema.Or(Schema.Any, Schema.Or(Schema.Term("NotT",Schema.Or(Schema.Term("TupleT",Schema.List(true)), Schema.Term("ArrayT",Schema.Any), Schema.Or(Schema.Term("AnyT"), Schema.Term("NullT"), Schema.Term("VoidT"), Schema.Term("BoolT"), Schema.Term("IntT"), Schema.Term("RealT"), Schema.Term("StringT"), Schema.Term("VarT",Schema.String), Schema.Term("NominalT",Schema.Any)))), Schema.Any), Schema.Term("NotT",Schema.Any), Schema.Term("OrT",Schema.Set(true)), Schema.Term("AndT",Schema.Any), Schema.Term("ArrayT",Schema.Any), Schema.Term("TupleT",Schema.List(true))),Schema.Any)),
		// Null
		Schema.Term("Null"),
		// True
		Schema.Term("True"),
		// False
		Schema.Term("False"),
		// Num(^real)
		Schema.Term("Num",Schema.Real),
		// Var(^string)
		Schema.Term("Var",Schema.String),
		// $7<Tuple($5<^[$2<^Expr<$7|$49<Value<Null|Tuple(^[^$49...])|Bool<True|False>|Num(^real)|String(^string)|Array(^[^$49...])|ArrayGen(^[^$49,^$49])>>|$86<BExpr<Bool<True|False>|VExpr<Var(^string)|Fn(^[^string,$2...])|Load(^[$2,^int])|LengthOf($2)|IndexOf(^[$2,$2])>|And(^{^$86...})|Or(^{^$86...})|Not(^$86)|Equals(^[$132<^Type<Atom<NotT($155<^Proton<TupleT(^[$155...])|ArrayT($155)|Quark<AnyT|NullT|VoidT|BoolT|IntT|RealT|StringT|VarT(^string)|NominalT(^string)>>>)|Proton<TupleT(^[$155...])|ArrayT($155)|Quark<AnyT|NullT|VoidT|BoolT|IntT|RealT|StringT|VarT(^string)|NominalT(^string)>>>|NotT($132)|OrT(^{$132...})|AndT(^{$132...})|ArrayT($132)|TupleT(^[$132...])|FunctionT(^[$132,$132,$132...])>>,^{|$2,$2|}[$2,$2]])|Inequality(^[^AType<IntT|RealT>,$229<^AExpr<Num(^real)|VExpr<Var(^string)|Fn(^[^string,$2...])|Load(^[$2,^int])|LengthOf($2)|IndexOf(^[$2,$2])>|Sum(^[^real,^{|$229...|}[$229...]])|Mul(^[^real,^{|$229...|}[$229...]])|Div(^[$229,$229])>>])|Equation(^[^AType<IntT|RealT>,$229])|ForAll(^[^{^[^Var(^string),$132]...},^$86])|Exists(^[^{^[^Var(^string),$132]...},^$86])>>|AExpr<Num(^real)|VExpr<Var(^string)|Fn(^[^string,$2...])|Load(^[$2,^int])|LengthOf($2)|IndexOf(^[$2,$2])>|Sum(^[^real,^{|$229...|}[$229...]])|Mul(^[^real,^{|$229...|}[$229...]])|Div(^[$229,$229])>|SExpr<VExpr<Var(^string)|Fn(^[^string,$2...])|Load(^[$2,^int])|LengthOf($2)|IndexOf(^[$2,$2])>|Array($5)|ArrayGen(^[$2,$2])>>>...]>)>
		Schema.Term("Tuple",Schema.List(true)),
		// $9<Load(^[$2<^Expr<$52<Value<Null|Tuple(^[^$52...])|Bool<True|False>|Num(^real)|String(^string)|Array(^[^$52...])|ArrayGen(^[^$52,^$52])>>|Tuple(^[$2...])|$94<BExpr<Bool<True|False>|VExpr<$9|Var(^string)|Fn(^[^string,$2...])|LengthOf($2)|IndexOf(^[$2,$2])>|And(^{^$94...})|Or(^{^$94...})|Not(^$94)|Equals(^[$132<^Type<Atom<NotT($155<^Proton<TupleT(^[$155...])|ArrayT($155)|Quark<AnyT|NullT|VoidT|BoolT|IntT|RealT|StringT|VarT(^string)|NominalT(^string)>>>)|Proton<TupleT(^[$155...])|ArrayT($155)|Quark<AnyT|NullT|VoidT|BoolT|IntT|RealT|StringT|VarT(^string)|NominalT(^string)>>>|NotT($132)|OrT(^{$132...})|AndT(^{$132...})|ArrayT($132)|TupleT(^[$132...])|FunctionT(^[$132,$132,$132...])>>,^{|$2,$2|}[$2,$2]])|Inequality(^[^AType<IntT|RealT>,$229<^AExpr<Num(^real)|VExpr<$9|Var(^string)|Fn(^[^string,$2...])|LengthOf($2)|IndexOf(^[$2,$2])>|Sum(^[^real,^{|$229...|}[$229...]])|Mul(^[^real,^{|$229...|}[$229...]])|Div(^[$229,$229])>>])|Equation(^[^AType<IntT|RealT>,$229])|ForAll(^[^{^[^Var(^string),$132]...},^$94])|Exists(^[^{^[^Var(^string),$132]...},^$94])>>|AExpr<Num(^real)|VExpr<$9|Var(^string)|Fn(^[^string,$2...])|LengthOf($2)|IndexOf(^[$2,$2])>|Sum(^[^real,^{|$229...|}[$229...]])|Mul(^[^real,^{|$229...|}[$229...]])|Div(^[$229,$229])>|SExpr<VExpr<$9|Var(^string)|Fn(^[^string,$2...])|LengthOf($2)|IndexOf(^[$2,$2])>|Array(^[$2...])|ArrayGen(^[$2,$2])>>>,^int])>
		Schema.Term("Load",Schema.List(true,Schema.Or(Schema.Or(Schema.Or(Schema.Or(Schema.Or(Schema.Term("Null"), Schema.Term("Tuple",Schema.List(true)), Schema.Or(Schema.Term("True"), Schema.Term("False")), Schema.Term("Num",Schema.Real), Schema.Term("String",Schema.String)), Schema.Or(Schema.Term("Array",Schema.Any), Schema.Term("ArrayGen",Schema.List(true,Schema.Any,Schema.Any)))), Schema.Term("Tuple",Schema.List(true)), Schema.Or(Schema.Or(Schema.Or(Schema.Any, Schema.Or(Schema.Or(Schema.Any, Schema.Term("Var",Schema.Any), Schema.Term("Fn",Schema.List(true,Schema.Any)), Schema.Term("LengthOf",Schema.Any)), Schema.Term("IndexOf",Schema.List(true,Schema.Any,Schema.Any))), Schema.Term("And",Schema.Set(true)), Schema.Term("Or",Schema.Any), Schema.Term("Not",Schema.Any), Schema.Term("Equals",Schema.List(true,Schema.Or(Schema.Or(Schema.Term("NotT",Schema.Or(Schema.Term("TupleT",Schema.List(true)), Schema.Term("ArrayT",Schema.Any), Schema.Or(Schema.Term("AnyT"), Schema.Term("NullT"), Schema.Term("VoidT"), Schema.Term("BoolT"), Schema.Term("IntT"), Schema.Term("RealT"), Schema.Term("StringT"), Schema.Term("VarT",Schema.Any), Schema.Term("NominalT",Schema.Any)))), Schema.Any), Schema.Term("NotT",Schema.Any), Schema.Term("OrT",Schema.Set(true)), Schema.Term("AndT",Schema.Any), Schema.Term("ArrayT",Schema.Any), Schema.Term("TupleT",Schema.List(true)), Schema.Term("FunctionT",Schema.List(true,Schema.Any,Schema.Any))),Schema.Bag(true,Schema.Any,Schema.Any)))), Schema.Or(Schema.Term("Inequality",Schema.List(true,Schema.Or(Schema.Any, Schema.Any),Schema.Or(Schema.Any, Schema.Any, Schema.Term("Sum",Schema.List(true,Schema.Any,Schema.Bag(true))), Schema.Term("Mul",Schema.Any), Schema.Term("Div",Schema.List(true,Schema.Any,Schema.Any))))), Schema.Term("Equation",Schema.Any))), Schema.Or(Schema.Term("ForAll",Schema.List(true,Schema.Set(true),Schema.Any)), Schema.Term("Exists",Schema.Any)))), Schema.Any), Schema.Or(Schema.Any, Schema.Term("Array",Schema.Any), Schema.Term("ArrayGen",Schema.Any))),Schema.Int)),
		// $4<LengthOf($2<^Expr<$47<Value<Null|Tuple(^[^$47...])|Bool<True|False>|Num(^real)|String(^string)|Array(^[^$47...])|ArrayGen(^[^$47,^$47])>>|Tuple(^[$2...])|$89<BExpr<Bool<True|False>|VExpr<$4|Var(^string)|Fn(^[^string,$2...])|Load(^[$2,^int])|IndexOf(^[$2,$2])>|And(^{^$89...})|Or(^{^$89...})|Not(^$89)|Equals(^[$132<^Type<Atom<NotT($155<^Proton<TupleT(^[$155...])|ArrayT($155)|Quark<AnyT|NullT|VoidT|BoolT|IntT|RealT|StringT|VarT(^string)|NominalT(^string)>>>)|Proton<TupleT(^[$155...])|ArrayT($155)|Quark<AnyT|NullT|VoidT|BoolT|IntT|RealT|StringT|VarT(^string)|NominalT(^string)>>>|NotT($132)|OrT(^{$132...})|AndT(^{$132...})|ArrayT($132)|TupleT(^[$132...])|FunctionT(^[$132,$132,$132...])>>,^{|$2,$2|}[$2,$2]])|Inequality(^[^AType<IntT|RealT>,$229<^AExpr<Num(^real)|VExpr<$4|Var(^string)|Fn(^[^string,$2...])|Load(^[$2,^int])|IndexOf(^[$2,$2])>|Sum(^[^real,^{|$229...|}[$229...]])|Mul(^[^real,^{|$229...|}[$229...]])|Div(^[$229,$229])>>])|Equation(^[^AType<IntT|RealT>,$229])|ForAll(^[^{^[^Var(^string),$132]...},^$89])|Exists(^[^{^[^Var(^string),$132]...},^$89])>>|AExpr<Num(^real)|VExpr<$4|Var(^string)|Fn(^[^string,$2...])|Load(^[$2,^int])|IndexOf(^[$2,$2])>|Sum(^[^real,^{|$229...|}[$229...]])|Mul(^[^real,^{|$229...|}[$229...]])|Div(^[$229,$229])>|SExpr<VExpr<$4|Var(^string)|Fn(^[^string,$2...])|Load(^[$2,^int])|IndexOf(^[$2,$2])>|Array(^[$2...])|ArrayGen(^[$2,$2])>>>)>
		Schema.Term("LengthOf",Schema.Or(Schema.Or(Schema.Or(Schema.Or(Schema.Or(Schema.Term("Null"), Schema.Term("Tuple",Schema.List(true)), Schema.Or(Schema.Term("True"), Schema.Term("False")), Schema.Term("Num",Schema.Real), Schema.Term("String",Schema.String)), Schema.Or(Schema.Term("Array",Schema.Any), Schema.Term("ArrayGen",Schema.List(true,Schema.Any,Schema.Any)))), Schema.Term("Tuple",Schema.List(true)), Schema.Or(Schema.Or(Schema.Or(Schema.Any, Schema.Or(Schema.Or(Schema.Any, Schema.Term("Var",Schema.Any), Schema.Term("Fn",Schema.List(true,Schema.Any)), Schema.Term("Load",Schema.List(true,Schema.Any,Schema.Int))), Schema.Term("IndexOf",Schema.List(true,Schema.Any,Schema.Any))), Schema.Term("And",Schema.Set(true)), Schema.Term("Or",Schema.Any), Schema.Term("Not",Schema.Any), Schema.Term("Equals",Schema.List(true,Schema.Or(Schema.Or(Schema.Term("NotT",Schema.Or(Schema.Term("TupleT",Schema.List(true)), Schema.Term("ArrayT",Schema.Any), Schema.Or(Schema.Term("AnyT"), Schema.Term("NullT"), Schema.Term("VoidT"), Schema.Term("BoolT"), Schema.Term("IntT"), Schema.Term("RealT"), Schema.Term("StringT"), Schema.Term("VarT",Schema.Any), Schema.Term("NominalT",Schema.Any)))), Schema.Any), Schema.Term("NotT",Schema.Any), Schema.Term("OrT",Schema.Set(true)), Schema.Term("AndT",Schema.Any), Schema.Term("ArrayT",Schema.Any), Schema.Term("TupleT",Schema.List(true)), Schema.Term("FunctionT",Schema.List(true,Schema.Any,Schema.Any))),Schema.Bag(true,Schema.Any,Schema.Any)))), Schema.Or(Schema.Term("Inequality",Schema.List(true,Schema.Or(Schema.Any, Schema.Any),Schema.Or(Schema.Any, Schema.Any, Schema.Term("Sum",Schema.List(true,Schema.Any,Schema.Bag(true))), Schema.Term("Mul",Schema.Any), Schema.Term("Div",Schema.List(true,Schema.Any,Schema.Any))))), Schema.Term("Equation",Schema.Any))), Schema.Or(Schema.Term("ForAll",Schema.List(true,Schema.Set(true),Schema.Any)), Schema.Term("Exists",Schema.Any)))), Schema.Any), Schema.Or(Schema.Any, Schema.Term("Array",Schema.Any), Schema.Term("ArrayGen",Schema.Any)))),
		// $9<Fn(^[^string,$3<^Expr<$52<Value<Null|Tuple(^[^$52...])|Bool<True|False>|Num(^real)|String(^string)|Array(^[^$52...])|ArrayGen(^[^$52,^$52])>>|Tuple(^[$3...])|$93<BExpr<Bool<True|False>|VExpr<$9|Var(^string)|Load(^[$3,^int])|LengthOf($3)|IndexOf(^[$3,$3])>|And(^{^$93...})|Or(^{^$93...})|Not(^$93)|Equals(^[$132<^Type<Atom<NotT($155<^Proton<TupleT(^[$155...])|ArrayT($155)|Quark<AnyT|NullT|VoidT|BoolT|IntT|RealT|StringT|VarT(^string)|NominalT(^string)>>>)|Proton<TupleT(^[$155...])|ArrayT($155)|Quark<AnyT|NullT|VoidT|BoolT|IntT|RealT|StringT|VarT(^string)|NominalT(^string)>>>|NotT($132)|OrT(^{$132...})|AndT(^{$132...})|ArrayT($132)|TupleT(^[$132...])|FunctionT(^[$132,$132,$132...])>>,^{|$3,$3|}[$3,$3]])|Inequality(^[^AType<IntT|RealT>,$229<^AExpr<Num(^real)|VExpr<$9|Var(^string)|Load(^[$3,^int])|LengthOf($3)|IndexOf(^[$3,$3])>|Sum(^[^real,^{|$229...|}[$229...]])|Mul(^[^real,^{|$229...|}[$229...]])|Div(^[$229,$229])>>])|Equation(^[^AType<IntT|RealT>,$229])|ForAll(^[^{^[^Var(^string),$132]...},^$93])|Exists(^[^{^[^Var(^string),$132]...},^$93])>>|AExpr<Num(^real)|VExpr<$9|Var(^string)|Load(^[$3,^int])|LengthOf($3)|IndexOf(^[$3,$3])>|Sum(^[^real,^{|$229...|}[$229...]])|Mul(^[^real,^{|$229...|}[$229...]])|Div(^[$229,$229])>|SExpr<VExpr<$9|Var(^string)|Load(^[$3,^int])|LengthOf($3)|IndexOf(^[$3,$3])>|Array(^[$3...])|ArrayGen(^[$3,$3])>>>...])>
		Schema.Term("Fn",Schema.List(true,Schema.String)),
		// String(^string)
		Schema.Term("String",Schema.String),
		// $4<Not($2<^$25<BExpr<$4|$36<VExpr<Var(^string)|Fn(^[^string,$41<^Expr<$25|$88<Value<Null|Tuple(^[^$88...])|Bool<True|False>|Num(^real)|String(^string)|Array(^[^$88...])|ArrayGen(^[^$88,^$88])>>|Tuple(^[$41...])|$115<AExpr<$36|Num(^real)|Sum(^[^real,^{|^$115...|}[^$115...]])|Mul(^[^real,^{|^$115...|}[^$115...]])|Div(^[^$115,^$115])>>|SExpr<$36|Array(^[$41...])|ArrayGen(^[$41,$41])>>>...])|Load(^[$41,^int])|LengthOf($41)|IndexOf(^[$41,$41])>>|Bool<True|False>|And(^{$2...})|Or(^{$2...})|Equals(^[$165<^Type<Atom<NotT($188<^Proton<TupleT(^[$188...])|ArrayT($188)|Quark<AnyT|NullT|VoidT|BoolT|IntT|RealT|StringT|VarT(^string)|NominalT(^string)>>>)|Proton<TupleT(^[$188...])|ArrayT($188)|Quark<AnyT|NullT|VoidT|BoolT|IntT|RealT|StringT|VarT(^string)|NominalT(^string)>>>|NotT($165)|OrT(^{$165...})|AndT(^{$165...})|ArrayT($165)|TupleT(^[$165...])|FunctionT(^[$165,$165,$165...])>>,^{|$41,$41|}[$41,$41]])|Inequality(^[^AType<IntT|RealT>,^$115])|Equation(^[^AType<IntT|RealT>,^$115])|ForAll(^[^{^[^Var(^string),$165]...},$2])|Exists(^[^{^[^Var(^string),$165]...},$2])>>>)>
		Schema.Term("Not",Schema.Or(Schema.Or(Schema.Or(Schema.Any, Schema.Or(Schema.Or(Schema.Term("Var",Schema.String), Schema.Term("Fn",Schema.List(true,Schema.Any)), Schema.Term("Load",Schema.List(true,Schema.Or(Schema.Or(Schema.Or(Schema.Any, Schema.Or(Schema.Or(Schema.Term("Null"), Schema.Term("Tuple",Schema.List(true)), Schema.Or(Schema.Term("True"), Schema.Term("False")), Schema.Term("Num",Schema.Real), Schema.Term("String",Schema.Any)), Schema.Or(Schema.Term("Array",Schema.Any), Schema.Term("ArrayGen",Schema.List(true,Schema.Any,Schema.Any)))), Schema.Term("Tuple",Schema.List(true))), Schema.Or(Schema.Any, Schema.Any, Schema.Term("Sum",Schema.List(true,Schema.Any,Schema.Bag(true))), Schema.Term("Mul",Schema.Any), Schema.Term("Div",Schema.List(true,Schema.Any,Schema.Any)))), Schema.Or(Schema.Any, Schema.Term("Array",Schema.Any), Schema.Term("ArrayGen",Schema.List(true,Schema.Any,Schema.Any)))),Schema.Int)), Schema.Term("LengthOf",Schema.Any)), Schema.Term("IndexOf",Schema.Any)), Schema.Any, Schema.Term("And",Schema.Set(true)), Schema.Term("Or",Schema.Any), Schema.Term("Equals",Schema.List(true,Schema.Or(Schema.Or(Schema.Term("NotT",Schema.Or(Schema.Term("TupleT",Schema.List(true)), Schema.Term("ArrayT",Schema.Any), Schema.Or(Schema.Term("AnyT"), Schema.Term("NullT"), Schema.Term("VoidT"), Schema.Term("BoolT"), Schema.Term("IntT"), Schema.Term("RealT"), Schema.Term("StringT"), Schema.Term("VarT",Schema.Any), Schema.Term("NominalT",Schema.Any)))), Schema.Any), Schema.Term("NotT",Schema.Any), Schema.Term("OrT",Schema.Set(true)), Schema.Term("AndT",Schema.Any), Schema.Term("ArrayT",Schema.Any), Schema.Term("TupleT",Schema.List(true)), Schema.Term("FunctionT",Schema.List(true,Schema.Any,Schema.Any))),Schema.Bag(true,Schema.Any,Schema.Any)))), Schema.Or(Schema.Term("Inequality",Schema.List(true,Schema.Or(Schema.Any, Schema.Any),Schema.Any)), Schema.Term("Equation",Schema.Any))), Schema.Or(Schema.Term("ForAll",Schema.List(true,Schema.Set(true),Schema.Any)), Schema.Term("Exists",Schema.Any)))),
		// $7<And($5<^{$2<^$28<BExpr<$7|$39<VExpr<Var(^string)|Fn(^[^string,$44<^Expr<$28|$91<Value<Null|Tuple(^[^$91...])|Bool<True|False>|Num(^real)|String(^string)|Array(^[^$91...])|ArrayGen(^[^$91,^$91])>>|Tuple(^[$44...])|$118<AExpr<$39|Num(^real)|Sum(^[^real,^{|^$118...|}[^$118...]])|Mul(^[^real,^{|^$118...|}[^$118...]])|Div(^[^$118,^$118])>>|SExpr<$39|Array(^[$44...])|ArrayGen(^[$44,$44])>>>...])|Load(^[$44,^int])|LengthOf($44)|IndexOf(^[$44,$44])>>|Bool<True|False>|Or($5)|Not($2)|Equals(^[$165<^Type<Atom<NotT($188<^Proton<TupleT(^[$188...])|ArrayT($188)|Quark<AnyT|NullT|VoidT|BoolT|IntT|RealT|StringT|VarT(^string)|NominalT(^string)>>>)|Proton<TupleT(^[$188...])|ArrayT($188)|Quark<AnyT|NullT|VoidT|BoolT|IntT|RealT|StringT|VarT(^string)|NominalT(^string)>>>|NotT($165)|OrT(^{$165...})|AndT(^{$165...})|ArrayT($165)|TupleT(^[$165...])|FunctionT(^[$165,$165,$165...])>>,^{|$44,$44|}[$44,$44]])|Inequality(^[^AType<IntT|RealT>,^$118])|Equation(^[^AType<IntT|RealT>,^$118])|ForAll(^[^{^[^Var(^string),$165]...},$2])|Exists(^[^{^[^Var(^string),$165]...},$2])>>>...}>)>
		Schema.Term("And",Schema.Set(true)),
		// $7<Or($5<^{$2<^$28<BExpr<$7|$39<VExpr<Var(^string)|Fn(^[^string,$44<^Expr<$28|$91<Value<Null|Tuple(^[^$91...])|Bool<True|False>|Num(^real)|String(^string)|Array(^[^$91...])|ArrayGen(^[^$91,^$91])>>|Tuple(^[$44...])|$118<AExpr<$39|Num(^real)|Sum(^[^real,^{|^$118...|}[^$118...]])|Mul(^[^real,^{|^$118...|}[^$118...]])|Div(^[^$118,^$118])>>|SExpr<$39|Array(^[$44...])|ArrayGen(^[$44,$44])>>>...])|Load(^[$44,^int])|LengthOf($44)|IndexOf(^[$44,$44])>>|Bool<True|False>|And($5)|Not($2)|Equals(^[$165<^Type<Atom<NotT($188<^Proton<TupleT(^[$188...])|ArrayT($188)|Quark<AnyT|NullT|VoidT|BoolT|IntT|RealT|StringT|VarT(^string)|NominalT(^string)>>>)|Proton<TupleT(^[$188...])|ArrayT($188)|Quark<AnyT|NullT|VoidT|BoolT|IntT|RealT|StringT|VarT(^string)|NominalT(^string)>>>|NotT($165)|OrT(^{$165...})|AndT(^{$165...})|ArrayT($165)|TupleT(^[$165...])|FunctionT(^[$165,$165,$165...])>>,^{|$44,$44|}[$44,$44]])|Inequality(^[^AType<IntT|RealT>,^$118])|Equation(^[^AType<IntT|RealT>,^$118])|ForAll(^[^{^[^Var(^string),$165]...},$2])|Exists(^[^{^[^Var(^string),$165]...},$2])>>>...}>)>
		Schema.Term("Or",Schema.Set(true)),
		// $14<Equals(^[$2<^Type<Atom<NotT($27<^Proton<TupleT(^[$27...])|ArrayT($27)|Quark<AnyT|NullT|VoidT|BoolT|IntT|RealT|StringT|VarT(^string)|NominalT(^string)>>>)|Proton<TupleT(^[$27...])|ArrayT($27)|Quark<AnyT|NullT|VoidT|BoolT|IntT|RealT|StringT|VarT(^string)|NominalT(^string)>>>|NotT($2)|OrT(^{$2...})|AndT(^{$2...})|ArrayT($2)|TupleT(^[$2...])|FunctionT(^[$2,$2,$2...])>>,^{|$4<^Expr<$142<Value<Null|Tuple(^[^$142...])|Bool<True|False>|Num(^real)|String(^string)|Array(^[^$142...])|ArrayGen(^[^$142,^$142])>>|Tuple(^[$4...])|$182<BExpr<$14|Bool<True|False>|VExpr<Var(^string)|Fn(^[^string,$4...])|Load(^[$4,^int])|LengthOf($4)|IndexOf(^[$4,$4])>|And(^{^$182...})|Or(^{^$182...})|Not(^$182)|Inequality(^[^AType<IntT|RealT>,$229<^AExpr<Num(^real)|VExpr<Var(^string)|Fn(^[^string,$4...])|Load(^[$4,^int])|LengthOf($4)|IndexOf(^[$4,$4])>|Sum(^[^real,^{|$229...|}[$229...]])|Mul(^[^real,^{|$229...|}[$229...]])|Div(^[$229,$229])>>])|Equation(^[^AType<IntT|RealT>,$229])|ForAll(^[^{^[^Var(^string),$2]...},^$182])|Exists(^[^{^[^Var(^string),$2]...},^$182])>>|AExpr<Num(^real)|VExpr<Var(^string)|Fn(^[^string,$4...])|Load(^[$4,^int])|LengthOf($4)|IndexOf(^[$4,$4])>|Sum(^[^real,^{|$229...|}[$229...]])|Mul(^[^real,^{|$229...|}[$229...]])|Div(^[$229,$229])>|SExpr<VExpr<Var(^string)|Fn(^[^string,$4...])|Load(^[$4,^int])|LengthOf($4)|IndexOf(^[$4,$4])>|Array(^[$4...])|ArrayGen(^[$4,$4])>>>,$4|}[$4<^Expr<$142<Value<Null|Tuple(^[^$142...])|Bool<True|False>|Num(^real)|String(^string)|Array(^[^$142...])|ArrayGen(^[^$142,^$142])>>|Tuple(^[$4...])|$182<BExpr<$14|Bool<True|False>|VExpr<Var(^string)|Fn(^[^string,$4...])|Load(^[$4,^int])|LengthOf($4)|IndexOf(^[$4,$4])>|And(^{^$182...})|Or(^{^$182...})|Not(^$182)|Inequality(^[^AType<IntT|RealT>,$229<^AExpr<Num(^real)|VExpr<Var(^string)|Fn(^[^string,$4...])|Load(^[$4,^int])|LengthOf($4)|IndexOf(^[$4,$4])>|Sum(^[^real,^{|$229...|}[$229...]])|Mul(^[^real,^{|$229...|}[$229...]])|Div(^[$229,$229])>>])|Equation(^[^AType<IntT|RealT>,$229])|ForAll(^[^{^[^Var(^string),$2]...},^$182])|Exists(^[^{^[^Var(^string),$2]...},^$182])>>|AExpr<Num(^real)|VExpr<Var(^string)|Fn(^[^string,$4...])|Load(^[$4,^int])|LengthOf($4)|IndexOf(^[$4,$4])>|Sum(^[^real,^{|$229...|}[$229...]])|Mul(^[^real,^{|$229...|}[$229...]])|Div(^[$229,$229])>|SExpr<VExpr<Var(^string)|Fn(^[^string,$4...])|Load(^[$4,^int])|LengthOf($4)|IndexOf(^[$4,$4])>|Array(^[$4...])|ArrayGen(^[$4,$4])>>>,$4]])>
		Schema.Term("Equals",Schema.List(true,Schema.Or(Schema.Or(Schema.Term("NotT",Schema.Or(Schema.Term("TupleT",Schema.List(true)), Schema.Term("ArrayT",Schema.Any), Schema.Or(Schema.Term("AnyT"), Schema.Term("NullT"), Schema.Term("VoidT"), Schema.Term("BoolT"), Schema.Term("IntT"), Schema.Term("RealT"), Schema.Term("StringT"), Schema.Term("VarT",Schema.String), Schema.Term("NominalT",Schema.Any)))), Schema.Any), Schema.Term("NotT",Schema.Any), Schema.Term("OrT",Schema.Set(true)), Schema.Term("AndT",Schema.Any), Schema.Term("ArrayT",Schema.Any), Schema.Term("TupleT",Schema.List(true)), Schema.Term("FunctionT",Schema.List(true,Schema.Any,Schema.Any))),Schema.Bag(true,Schema.Or(Schema.Or(Schema.Or(Schema.Or(Schema.Or(Schema.Term("Null"), Schema.Term("Tuple",Schema.List(true)), Schema.Or(Schema.Term("True"), Schema.Term("False")), Schema.Term("Num",Schema.Real), Schema.Term("String",Schema.Any)), Schema.Or(Schema.Term("Array",Schema.Any), Schema.Term("ArrayGen",Schema.List(true,Schema.Any,Schema.Any)))), Schema.Term("Tuple",Schema.List(true)), Schema.Or(Schema.Or(Schema.Or(Schema.Any, Schema.Any, Schema.Or(Schema.Or(Schema.Term("Var",Schema.Any), Schema.Term("Fn",Schema.List(true,Schema.Any)), Schema.Term("Load",Schema.List(true,Schema.Any,Schema.Int)), Schema.Term("LengthOf",Schema.Any)), Schema.Term("IndexOf",Schema.List(true,Schema.Any,Schema.Any))), Schema.Term("And",Schema.Set(true)), Schema.Term("Or",Schema.Any), Schema.Term("Not",Schema.Any)), Schema.Or(Schema.Term("Inequality",Schema.List(true,Schema.Or(Schema.Any, Schema.Any),Schema.Or(Schema.Any, Schema.Any, Schema.Term("Sum",Schema.List(true,Schema.Any,Schema.Bag(true))), Schema.Term("Mul",Schema.Any), Schema.Term("Div",Schema.List(true,Schema.Any,Schema.Any))))), Schema.Term("Equation",Schema.Any))), Schema.Or(Schema.Term("ForAll",Schema.List(true,Schema.Set(true),Schema.Any)), Schema.Term("Exists",Schema.Any)))), Schema.Any), Schema.Or(Schema.Any, Schema.Term("Array",Schema.Any), Schema.Term("ArrayGen",Schema.Any))),Schema.Any))),
		// $12<Mul($10<^[^real,^{|$3<^$20<AExpr<$12|Num(^real)|Sum($10)|Div(^[$3,$3])|$41<VExpr<Var(^string)|Fn(^[^string,$46<^Expr<$20|$93<Value<Num(^real)|Null|Tuple(^[^$93...])|Bool<True|False>|String(^string)|Array(^[^$93...])|ArrayGen(^[^$93,^$93])>>|Tuple(^[$46...])|$130<BExpr<$41|Bool<True|False>|And(^{^$130...})|Or(^{^$130...})|Not(^$130)|Equals(^[$142<^Type<Atom<NotT($165<^Proton<TupleT(^[$165...])|ArrayT($165)|Quark<AnyT|NullT|VoidT|BoolT|IntT|RealT|StringT|VarT(^string)|NominalT(^string)>>>)|Proton<TupleT(^[$165...])|ArrayT($165)|Quark<AnyT|NullT|VoidT|BoolT|IntT|RealT|StringT|VarT(^string)|NominalT(^string)>>>|NotT($142)|OrT(^{$142...})|AndT(^{$142...})|ArrayT($142)|TupleT(^[$142...])|FunctionT(^[$142,$142,$142...])>>,^{|$46,$46|}[$46,$46]])|Inequality(^[^AType<IntT|RealT>,$3])|Equation(^[^AType<IntT|RealT>,$3])|ForAll(^[^{^[^Var(^string),$142]...},^$130])|Exists(^[^{^[^Var(^string),$142]...},^$130])>>|SExpr<$41|Array(^[$46...])|ArrayGen(^[$46,$46])>>>...])|Load(^[$46,^int])|LengthOf($46)|IndexOf(^[$46,$46])>>>>>...|}[$3<^$20<AExpr<$12|Num(^real)|Sum($10)|Div(^[$3,$3])|$41<VExpr<Var(^string)|Fn(^[^string,$46<^Expr<$20|$93<Value<Num(^real)|Null|Tuple(^[^$93...])|Bool<True|False>|String(^string)|Array(^[^$93...])|ArrayGen(^[^$93,^$93])>>|Tuple(^[$46...])|$130<BExpr<$41|Bool<True|False>|And(^{^$130...})|Or(^{^$130...})|Not(^$130)|Equals(^[$142<^Type<Atom<NotT($165<^Proton<TupleT(^[$165...])|ArrayT($165)|Quark<AnyT|NullT|VoidT|BoolT|IntT|RealT|StringT|VarT(^string)|NominalT(^string)>>>)|Proton<TupleT(^[$165...])|ArrayT($165)|Quark<AnyT|NullT|VoidT|BoolT|IntT|RealT|StringT|VarT(^string)|NominalT(^string)>>>|NotT($142)|OrT(^{$142...})|AndT(^{$142...})|ArrayT($142)|TupleT(^[$142...])|FunctionT(^[$142,$142,$142...])>>,^{|$46,$46|}[$46,$46]])|Inequality(^[^AType<IntT|RealT>,$3])|Equation(^[^AType<IntT|RealT>,$3])|ForAll(^[^{^[^Var(^string),$142]...},^$130])|Exists(^[^{^[^Var(^string),$142]...},^$130])>>|SExpr<$41|Array(^[$46...])|ArrayGen(^[$46,$46])>>>...])|Load(^[$46,^int])|LengthOf($46)|IndexOf(^[$46,$46])>>>>>...]]>)>
		Schema.Term("Mul",Schema.List(true,Schema.Real,Schema.Bag(true))),
		// $8<Div(^[$2<^$16<AExpr<$8|Num(^real)|Sum(^[^real,^{|$2...|}[$2...]])|Mul(^[^real,^{|$2...|}[$2...]])|$41<VExpr<Var(^string)|Fn(^[^string,$46<^Expr<$16|$93<Value<Num(^real)|Null|Tuple(^[^$93...])|Bool<True|False>|String(^string)|Array(^[^$93...])|ArrayGen(^[^$93,^$93])>>|Tuple(^[$46...])|$130<BExpr<$41|Bool<True|False>|And(^{^$130...})|Or(^{^$130...})|Not(^$130)|Equals(^[$142<^Type<Atom<NotT($165<^Proton<TupleT(^[$165...])|ArrayT($165)|Quark<AnyT|NullT|VoidT|BoolT|IntT|RealT|StringT|VarT(^string)|NominalT(^string)>>>)|Proton<TupleT(^[$165...])|ArrayT($165)|Quark<AnyT|NullT|VoidT|BoolT|IntT|RealT|StringT|VarT(^string)|NominalT(^string)>>>|NotT($142)|OrT(^{$142...})|AndT(^{$142...})|ArrayT($142)|TupleT(^[$142...])|FunctionT(^[$142,$142,$142...])>>,^{|$46,$46|}[$46,$46]])|Inequality(^[^AType<IntT|RealT>,$2])|Equation(^[^AType<IntT|RealT>,$2])|ForAll(^[^{^[^Var(^string),$142]...},^$130])|Exists(^[^{^[^Var(^string),$142]...},^$130])>>|SExpr<$41|Array(^[$46...])|ArrayGen(^[$46,$46])>>>...])|Load(^[$46,^int])|LengthOf($46)|IndexOf(^[$46,$46])>>>>>,$2])>
		Schema.Term("Div",Schema.List(true,Schema.Or(Schema.Any, Schema.Term("Num",Schema.Real), Schema.Term("Sum",Schema.List(true,Schema.Any,Schema.Bag(true))), Schema.Term("Mul",Schema.Any), Schema.Or(Schema.Or(Schema.Term("Var",Schema.String), Schema.Term("Fn",Schema.List(true,Schema.Any)), Schema.Term("Load",Schema.List(true,Schema.Or(Schema.Or(Schema.Any, Schema.Or(Schema.Or(Schema.Or(Schema.Any, Schema.Term("Null"), Schema.Term("Tuple",Schema.List(true)), Schema.Or(Schema.Term("True"), Schema.Term("False")), Schema.Term("String",Schema.Any)), Schema.Or(Schema.Term("Array",Schema.Any), Schema.Term("ArrayGen",Schema.List(true,Schema.Any,Schema.Any)))), Schema.Term("Tuple",Schema.List(true)), Schema.Or(Schema.Or(Schema.Or(Schema.Any, Schema.Any, Schema.Term("And",Schema.Set(true)), Schema.Term("Or",Schema.Any), Schema.Term("Not",Schema.Any), Schema.Term("Equals",Schema.List(true,Schema.Or(Schema.Or(Schema.Term("NotT",Schema.Or(Schema.Term("TupleT",Schema.List(true)), Schema.Term("ArrayT",Schema.Any), Schema.Or(Schema.Term("AnyT"), Schema.Term("NullT"), Schema.Term("VoidT"), Schema.Term("BoolT"), Schema.Term("IntT"), Schema.Term("RealT"), Schema.Term("StringT"), Schema.Term("VarT",Schema.Any), Schema.Term("NominalT",Schema.Any)))), Schema.Any), Schema.Term("NotT",Schema.Any), Schema.Term("OrT",Schema.Set(true)), Schema.Term("AndT",Schema.Any), Schema.Term("ArrayT",Schema.Any), Schema.Term("TupleT",Schema.List(true)), Schema.Term("FunctionT",Schema.List(true,Schema.Any,Schema.Any))),Schema.Bag(true,Schema.Any,Schema.Any)))), Schema.Or(Schema.Term("Inequality",Schema.List(true,Schema.Or(Schema.Any, Schema.Any),Schema.Any)), Schema.Term("Equation",Schema.Any))), Schema.Or(Schema.Term("ForAll",Schema.List(true,Schema.Set(true),Schema.Any)), Schema.Term("Exists",Schema.Any))))), Schema.Or(Schema.Any, Schema.Term("Array",Schema.Any), Schema.Term("ArrayGen",Schema.List(true,Schema.Any,Schema.Any)))),Schema.Int)), Schema.Term("LengthOf",Schema.Any)), Schema.Term("IndexOf",Schema.Any))),Schema.Any)),
		// $12<Sum($10<^[^real,^{|$3<^$20<AExpr<$12|Num(^real)|Mul($10)|Div(^[$3,$3])|$41<VExpr<Var(^string)|Fn(^[^string,$46<^Expr<$20|$93<Value<Num(^real)|Null|Tuple(^[^$93...])|Bool<True|False>|String(^string)|Array(^[^$93...])|ArrayGen(^[^$93,^$93])>>|Tuple(^[$46...])|$130<BExpr<$41|Bool<True|False>|And(^{^$130...})|Or(^{^$130...})|Not(^$130)|Equals(^[$142<^Type<Atom<NotT($165<^Proton<TupleT(^[$165...])|ArrayT($165)|Quark<AnyT|NullT|VoidT|BoolT|IntT|RealT|StringT|VarT(^string)|NominalT(^string)>>>)|Proton<TupleT(^[$165...])|ArrayT($165)|Quark<AnyT|NullT|VoidT|BoolT|IntT|RealT|StringT|VarT(^string)|NominalT(^string)>>>|NotT($142)|OrT(^{$142...})|AndT(^{$142...})|ArrayT($142)|TupleT(^[$142...])|FunctionT(^[$142,$142,$142...])>>,^{|$46,$46|}[$46,$46]])|Inequality(^[^AType<IntT|RealT>,$3])|Equation(^[^AType<IntT|RealT>,$3])|ForAll(^[^{^[^Var(^string),$142]...},^$130])|Exists(^[^{^[^Var(^string),$142]...},^$130])>>|SExpr<$41|Array(^[$46...])|ArrayGen(^[$46,$46])>>>...])|Load(^[$46,^int])|LengthOf($46)|IndexOf(^[$46,$46])>>>>>...|}[$3<^$20<AExpr<$12|Num(^real)|Mul($10)|Div(^[$3,$3])|$41<VExpr<Var(^string)|Fn(^[^string,$46<^Expr<$20|$93<Value<Num(^real)|Null|Tuple(^[^$93...])|Bool<True|False>|String(^string)|Array(^[^$93...])|ArrayGen(^[^$93,^$93])>>|Tuple(^[$46...])|$130<BExpr<$41|Bool<True|False>|And(^{^$130...})|Or(^{^$130...})|Not(^$130)|Equals(^[$142<^Type<Atom<NotT($165<^Proton<TupleT(^[$165...])|ArrayT($165)|Quark<AnyT|NullT|VoidT|BoolT|IntT|RealT|StringT|VarT(^string)|NominalT(^string)>>>)|Proton<TupleT(^[$165...])|ArrayT($165)|Quark<AnyT|NullT|VoidT|BoolT|IntT|RealT|StringT|VarT(^string)|NominalT(^string)>>>|NotT($142)|OrT(^{$142...})|AndT(^{$142...})|ArrayT($142)|TupleT(^[$142...])|FunctionT(^[$142,$142,$142...])>>,^{|$46,$46|}[$46,$46]])|Inequality(^[^AType<IntT|RealT>,$3])|Equation(^[^AType<IntT|RealT>,$3])|ForAll(^[^{^[^Var(^string),$142]...},^$130])|Exists(^[^{^[^Var(^string),$142]...},^$130])>>|SExpr<$41|Array(^[$46...])|ArrayGen(^[$46,$46])>>>...])|Load(^[$46,^int])|LengthOf($46)|IndexOf(^[$46,$46])>>>>>...]]>)>
		Schema.Term("Sum",Schema.List(true,Schema.Real,Schema.Bag(true))),
		// $10<Equation($8<^[^AType<IntT|RealT>,$4<^$29<AExpr<Num(^real)|Sum(^[^real,^{|$4...|}[$4...]])|Mul(^[^real,^{|$4...|}[$4...]])|Div(^[$4,$4])|$60<VExpr<Var(^string)|Fn(^[^string,$65<^Expr<$29|$112<Value<Num(^real)|Null|Tuple(^[^$112...])|Bool<True|False>|String(^string)|Array(^[^$112...])|ArrayGen(^[^$112,^$112])>>|Tuple(^[$65...])|$148<BExpr<$60|Bool<True|False>|And(^{^$148...})|Or(^{^$148...})|Not(^$148)|Equals(^[$160<^Type<Atom<NotT($183<^Proton<TupleT(^[$183...])|ArrayT($183)|Quark<IntT|RealT|AnyT|NullT|VoidT|BoolT|StringT|VarT(^string)|NominalT(^string)>>>)|Proton<TupleT(^[$183...])|ArrayT($183)|Quark<IntT|RealT|AnyT|NullT|VoidT|BoolT|StringT|VarT(^string)|NominalT(^string)>>>|NotT($160)|OrT(^{$160...})|AndT(^{$160...})|ArrayT($160)|TupleT(^[$160...])|FunctionT(^[$160,$160,$160...])>>,^{|$65,$65|}[$65,$65]])|$10|Inequality($8)|ForAll(^[^{^[^Var(^string),$160]...},^$148])|Exists(^[^{^[^Var(^string),$160]...},^$148])>>|SExpr<$60|Array(^[$65...])|ArrayGen(^[$65,$65])>>>...])|Load(^[$65,^int])|LengthOf($65)|IndexOf(^[$65,$65])>>>>>]>)>
		Schema.Term("Equation",Schema.List(true,Schema.Or(Schema.Term("IntT"), Schema.Term("RealT")),Schema.Or(Schema.Term("Num",Schema.Real), Schema.Term("Sum",Schema.List(true,Schema.Any,Schema.Bag(true))), Schema.Term("Mul",Schema.Any), Schema.Term("Div",Schema.List(true,Schema.Any,Schema.Any)), Schema.Or(Schema.Or(Schema.Term("Var",Schema.String), Schema.Term("Fn",Schema.List(true,Schema.Any)), Schema.Term("Load",Schema.List(true,Schema.Or(Schema.Or(Schema.Any, Schema.Or(Schema.Or(Schema.Or(Schema.Any, Schema.Term("Null"), Schema.Term("Tuple",Schema.List(true)), Schema.Or(Schema.Term("True"), Schema.Term("False")), Schema.Term("String",Schema.Any)), Schema.Or(Schema.Term("Array",Schema.Any), Schema.Term("ArrayGen",Schema.List(true,Schema.Any,Schema.Any)))), Schema.Term("Tuple",Schema.List(true)), Schema.Or(Schema.Or(Schema.Or(Schema.Any, Schema.Any, Schema.Term("And",Schema.Set(true)), Schema.Term("Or",Schema.Any), Schema.Term("Not",Schema.Any), Schema.Term("Equals",Schema.List(true,Schema.Or(Schema.Or(Schema.Term("NotT",Schema.Or(Schema.Term("TupleT",Schema.List(true)), Schema.Term("ArrayT",Schema.Any), Schema.Or(Schema.Any, Schema.Any, Schema.Term("AnyT"), Schema.Term("NullT"), Schema.Term("VoidT"), Schema.Term("BoolT"), Schema.Term("StringT"), Schema.Term("VarT",Schema.Any), Schema.Term("NominalT",Schema.Any)))), Schema.Any), Schema.Term("NotT",Schema.Any), Schema.Term("OrT",Schema.Set(true)), Schema.Term("AndT",Schema.Any), Schema.Term("ArrayT",Schema.Any), Schema.Term("TupleT",Schema.List(true)), Schema.Term("FunctionT",Schema.List(true,Schema.Any,Schema.Any))),Schema.Bag(true,Schema.Any,Schema.Any)))), Schema.Or(Schema.Any, Schema.Term("Inequality",Schema.Any))), Schema.Or(Schema.Term("ForAll",Schema.List(true,Schema.Set(true),Schema.Any)), Schema.Term("Exists",Schema.Any))))), Schema.Or(Schema.Any, Schema.Term("Array",Schema.Any), Schema.Term("ArrayGen",Schema.List(true,Schema.Any,Schema.Any)))),Schema.Int)), Schema.Term("LengthOf",Schema.Any)), Schema.Term("IndexOf",Schema.Any))))),
		// $10<Inequality($8<^[^AType<IntT|RealT>,$4<^$29<AExpr<Num(^real)|Sum(^[^real,^{|$4...|}[$4...]])|Mul(^[^real,^{|$4...|}[$4...]])|Div(^[$4,$4])|$60<VExpr<Var(^string)|Fn(^[^string,$65<^Expr<$29|$112<Value<Num(^real)|Null|Tuple(^[^$112...])|Bool<True|False>|String(^string)|Array(^[^$112...])|ArrayGen(^[^$112,^$112])>>|Tuple(^[$65...])|$148<BExpr<$60|Bool<True|False>|And(^{^$148...})|Or(^{^$148...})|Not(^$148)|Equals(^[$160<^Type<Atom<NotT($183<^Proton<TupleT(^[$183...])|ArrayT($183)|Quark<IntT|RealT|AnyT|NullT|VoidT|BoolT|StringT|VarT(^string)|NominalT(^string)>>>)|Proton<TupleT(^[$183...])|ArrayT($183)|Quark<IntT|RealT|AnyT|NullT|VoidT|BoolT|StringT|VarT(^string)|NominalT(^string)>>>|NotT($160)|OrT(^{$160...})|AndT(^{$160...})|ArrayT($160)|TupleT(^[$160...])|FunctionT(^[$160,$160,$160...])>>,^{|$65,$65|}[$65,$65]])|$10|Equation($8)|ForAll(^[^{^[^Var(^string),$160]...},^$148])|Exists(^[^{^[^Var(^string),$160]...},^$148])>>|SExpr<$60|Array(^[$65...])|ArrayGen(^[$65,$65])>>>...])|Load(^[$65,^int])|LengthOf($65)|IndexOf(^[$65,$65])>>>>>]>)>
		Schema.Term("Inequality",Schema.List(true,Schema.Or(Schema.Term("IntT"), Schema.Term("RealT")),Schema.Or(Schema.Term("Num",Schema.Real), Schema.Term("Sum",Schema.List(true,Schema.Any,Schema.Bag(true))), Schema.Term("Mul",Schema.Any), Schema.Term("Div",Schema.List(true,Schema.Any,Schema.Any)), Schema.Or(Schema.Or(Schema.Term("Var",Schema.String), Schema.Term("Fn",Schema.List(true,Schema.Any)), Schema.Term("Load",Schema.List(true,Schema.Or(Schema.Or(Schema.Any, Schema.Or(Schema.Or(Schema.Or(Schema.Any, Schema.Term("Null"), Schema.Term("Tuple",Schema.List(true)), Schema.Or(Schema.Term("True"), Schema.Term("False")), Schema.Term("String",Schema.Any)), Schema.Or(Schema.Term("Array",Schema.Any), Schema.Term("ArrayGen",Schema.List(true,Schema.Any,Schema.Any)))), Schema.Term("Tuple",Schema.List(true)), Schema.Or(Schema.Or(Schema.Or(Schema.Any, Schema.Any, Schema.Term("And",Schema.Set(true)), Schema.Term("Or",Schema.Any), Schema.Term("Not",Schema.Any), Schema.Term("Equals",Schema.List(true,Schema.Or(Schema.Or(Schema.Term("NotT",Schema.Or(Schema.Term("TupleT",Schema.List(true)), Schema.Term("ArrayT",Schema.Any), Schema.Or(Schema.Any, Schema.Any, Schema.Term("AnyT"), Schema.Term("NullT"), Schema.Term("VoidT"), Schema.Term("BoolT"), Schema.Term("StringT"), Schema.Term("VarT",Schema.Any), Schema.Term("NominalT",Schema.Any)))), Schema.Any), Schema.Term("NotT",Schema.Any), Schema.Term("OrT",Schema.Set(true)), Schema.Term("AndT",Schema.Any), Schema.Term("ArrayT",Schema.Any), Schema.Term("TupleT",Schema.List(true)), Schema.Term("FunctionT",Schema.List(true,Schema.Any,Schema.Any))),Schema.Bag(true,Schema.Any,Schema.Any)))), Schema.Or(Schema.Any, Schema.Term("Equation",Schema.Any))), Schema.Or(Schema.Term("ForAll",Schema.List(true,Schema.Set(true),Schema.Any)), Schema.Term("Exists",Schema.Any))))), Schema.Or(Schema.Any, Schema.Term("Array",Schema.Any), Schema.Term("ArrayGen",Schema.List(true,Schema.Any,Schema.Any)))),Schema.Int)), Schema.Term("LengthOf",Schema.Any)), Schema.Term("IndexOf",Schema.Any))))),
		// $7<Array($5<^[$2<^Expr<$49<Value<Null|Tuple(^[^$49...])|Bool<True|False>|Num(^real)|String(^string)|Array(^[^$49...])|ArrayGen(^[^$49,^$49])>>|Tuple($5)|$88<BExpr<Bool<True|False>|VExpr<Var(^string)|Fn(^[^string,$2...])|Load(^[$2,^int])|LengthOf($2)|IndexOf(^[$2,$2])>|And(^{^$88...})|Or(^{^$88...})|Not(^$88)|Equals(^[$134<^Type<Atom<NotT($157<^Proton<TupleT(^[$157...])|ArrayT($157)|Quark<AnyT|NullT|VoidT|BoolT|IntT|RealT|StringT|VarT(^string)|NominalT(^string)>>>)|Proton<TupleT(^[$157...])|ArrayT($157)|Quark<AnyT|NullT|VoidT|BoolT|IntT|RealT|StringT|VarT(^string)|NominalT(^string)>>>|NotT($134)|OrT(^{$134...})|AndT(^{$134...})|ArrayT($134)|TupleT(^[$134...])|FunctionT(^[$134,$134,$134...])>>,^{|$2,$2|}[$2,$2]])|Inequality(^[^AType<IntT|RealT>,$231<^AExpr<Num(^real)|VExpr<Var(^string)|Fn(^[^string,$2...])|Load(^[$2,^int])|LengthOf($2)|IndexOf(^[$2,$2])>|Sum(^[^real,^{|$231...|}[$231...]])|Mul(^[^real,^{|$231...|}[$231...]])|Div(^[$231,$231])>>])|Equation(^[^AType<IntT|RealT>,$231])|ForAll(^[^{^[^Var(^string),$134]...},^$88])|Exists(^[^{^[^Var(^string),$134]...},^$88])>>|AExpr<Num(^real)|VExpr<Var(^string)|Fn(^[^string,$2...])|Load(^[$2,^int])|LengthOf($2)|IndexOf(^[$2,$2])>|Sum(^[^real,^{|$231...|}[$231...]])|Mul(^[^real,^{|$231...|}[$231...]])|Div(^[$231,$231])>|SExpr<$7|VExpr<Var(^string)|Fn(^[^string,$2...])|Load(^[$2,^int])|LengthOf($2)|IndexOf(^[$2,$2])>|ArrayGen(^[$2,$2])>>>...]>)>
		Schema.Term("Array",Schema.List(true)),
		// $8<ArrayGen($6<^[$2<^Expr<$50<Value<Null|Tuple(^[^$50...])|Bool<True|False>|Num(^real)|String(^string)|Array(^[^$50...])|ArrayGen(^[^$50,^$50])>>|Tuple(^[$2...])|$92<BExpr<Bool<True|False>|VExpr<Var(^string)|Fn(^[^string,$2...])|Load(^[$2,^int])|LengthOf($2)|IndexOf($6)>|And(^{^$92...})|Or(^{^$92...})|Not(^$92)|Equals(^[$134<^Type<Atom<NotT($157<^Proton<TupleT(^[$157...])|ArrayT($157)|Quark<AnyT|NullT|VoidT|BoolT|IntT|RealT|StringT|VarT(^string)|NominalT(^string)>>>)|Proton<TupleT(^[$157...])|ArrayT($157)|Quark<AnyT|NullT|VoidT|BoolT|IntT|RealT|StringT|VarT(^string)|NominalT(^string)>>>|NotT($134)|OrT(^{$134...})|AndT(^{$134...})|ArrayT($134)|TupleT(^[$134...])|FunctionT(^[$134,$134,$134...])>>,^{|$2,$2|}[$2,$2]])|Inequality(^[^AType<IntT|RealT>,$231<^AExpr<Num(^real)|VExpr<Var(^string)|Fn(^[^string,$2...])|Load(^[$2,^int])|LengthOf($2)|IndexOf($6)>|Sum(^[^real,^{|$231...|}[$231...]])|Mul(^[^real,^{|$231...|}[$231...]])|Div(^[$231,$231])>>])|Equation(^[^AType<IntT|RealT>,$231])|ForAll(^[^{^[^Var(^string),$134]...},^$92])|Exists(^[^{^[^Var(^string),$134]...},^$92])>>|AExpr<Num(^real)|VExpr<Var(^string)|Fn(^[^string,$2...])|Load(^[$2,^int])|LengthOf($2)|IndexOf($6)>|Sum(^[^real,^{|$231...|}[$231...]])|Mul(^[^real,^{|$231...|}[$231...]])|Div(^[$231,$231])>|SExpr<$8|VExpr<Var(^string)|Fn(^[^string,$2...])|Load(^[$2,^int])|LengthOf($2)|IndexOf($6)>|Array(^[$2...])>>>,$2]>)>
		Schema.Term("ArrayGen",Schema.List(true,Schema.Or(Schema.Or(Schema.Or(Schema.Or(Schema.Or(Schema.Term("Null"), Schema.Term("Tuple",Schema.List(true)), Schema.Or(Schema.Term("True"), Schema.Term("False")), Schema.Term("Num",Schema.Real), Schema.Term("String",Schema.String)), Schema.Or(Schema.Term("Array",Schema.Any), Schema.Term("ArrayGen",Schema.List(true,Schema.Any,Schema.Any)))), Schema.Term("Tuple",Schema.List(true)), Schema.Or(Schema.Or(Schema.Or(Schema.Any, Schema.Or(Schema.Or(Schema.Term("Var",Schema.Any), Schema.Term("Fn",Schema.List(true,Schema.Any)), Schema.Term("Load",Schema.List(true,Schema.Any,Schema.Int)), Schema.Term("LengthOf",Schema.Any)), Schema.Term("IndexOf",Schema.Any)), Schema.Term("And",Schema.Set(true)), Schema.Term("Or",Schema.Any), Schema.Term("Not",Schema.Any), Schema.Term("Equals",Schema.List(true,Schema.Or(Schema.Or(Schema.Term("NotT",Schema.Or(Schema.Term("TupleT",Schema.List(true)), Schema.Term("ArrayT",Schema.Any), Schema.Or(Schema.Term("AnyT"), Schema.Term("NullT"), Schema.Term("VoidT"), Schema.Term("BoolT"), Schema.Term("IntT"), Schema.Term("RealT"), Schema.Term("StringT"), Schema.Term("VarT",Schema.Any), Schema.Term("NominalT",Schema.Any)))), Schema.Any), Schema.Term("NotT",Schema.Any), Schema.Term("OrT",Schema.Set(true)), Schema.Term("AndT",Schema.Any), Schema.Term("ArrayT",Schema.Any), Schema.Term("TupleT",Schema.List(true)), Schema.Term("FunctionT",Schema.List(true,Schema.Any,Schema.Any))),Schema.Bag(true,Schema.Any,Schema.Any)))), Schema.Or(Schema.Term("Inequality",Schema.List(true,Schema.Or(Schema.Any, Schema.Any),Schema.Or(Schema.Any, Schema.Any, Schema.Term("Sum",Schema.List(true,Schema.Any,Schema.Bag(true))), Schema.Term("Mul",Schema.Any), Schema.Term("Div",Schema.List(true,Schema.Any,Schema.Any))))), Schema.Term("Equation",Schema.Any))), Schema.Or(Schema.Term("ForAll",Schema.List(true,Schema.Set(true),Schema.Any)), Schema.Term("Exists",Schema.Any)))), Schema.Any), Schema.Or(Schema.Any, Schema.Any, Schema.Term("Array",Schema.Any))),Schema.Any)),
		// $8<IndexOf($6<^[$2<^Expr<$51<Value<Null|Tuple(^[^$51...])|Bool<True|False>|Num(^real)|String(^string)|Array(^[^$51...])|ArrayGen(^[^$51,^$51])>>|Tuple(^[$2...])|$93<BExpr<Bool<True|False>|VExpr<$8|Var(^string)|Fn(^[^string,$2...])|Load(^[$2,^int])|LengthOf($2)>|And(^{^$93...})|Or(^{^$93...})|Not(^$93)|Equals(^[$132<^Type<Atom<NotT($155<^Proton<TupleT(^[$155...])|ArrayT($155)|Quark<AnyT|NullT|VoidT|BoolT|IntT|RealT|StringT|VarT(^string)|NominalT(^string)>>>)|Proton<TupleT(^[$155...])|ArrayT($155)|Quark<AnyT|NullT|VoidT|BoolT|IntT|RealT|StringT|VarT(^string)|NominalT(^string)>>>|NotT($132)|OrT(^{$132...})|AndT(^{$132...})|ArrayT($132)|TupleT(^[$132...])|FunctionT(^[$132,$132,$132...])>>,^{|$2,$2|}[$2,$2]])|Inequality(^[^AType<IntT|RealT>,$229<^AExpr<Num(^real)|VExpr<$8|Var(^string)|Fn(^[^string,$2...])|Load(^[$2,^int])|LengthOf($2)>|Sum(^[^real,^{|$229...|}[$229...]])|Mul(^[^real,^{|$229...|}[$229...]])|Div(^[$229,$229])>>])|Equation(^[^AType<IntT|RealT>,$229])|ForAll(^[^{^[^Var(^string),$132]...},^$93])|Exists(^[^{^[^Var(^string),$132]...},^$93])>>|AExpr<Num(^real)|VExpr<$8|Var(^string)|Fn(^[^string,$2...])|Load(^[$2,^int])|LengthOf($2)>|Sum(^[^real,^{|$229...|}[$229...]])|Mul(^[^real,^{|$229...|}[$229...]])|Div(^[$229,$229])>|SExpr<VExpr<$8|Var(^string)|Fn(^[^string,$2...])|Load(^[$2,^int])|LengthOf($2)>|Array(^[$2...])|ArrayGen($6)>>>,$2]>)>
		Schema.Term("IndexOf",Schema.List(true,Schema.Or(Schema.Or(Schema.Or(Schema.Or(Schema.Or(Schema.Term("Null"), Schema.Term("Tuple",Schema.List(true)), Schema.Or(Schema.Term("True"), Schema.Term("False")), Schema.Term("Num",Schema.Real), Schema.Term("String",Schema.String)), Schema.Or(Schema.Term("Array",Schema.Any), Schema.Term("ArrayGen",Schema.List(true,Schema.Any,Schema.Any)))), Schema.Term("Tuple",Schema.List(true)), Schema.Or(Schema.Or(Schema.Or(Schema.Any, Schema.Or(Schema.Any, Schema.Or(Schema.Term("Var",Schema.Any), Schema.Term("Fn",Schema.List(true,Schema.Any)), Schema.Term("Load",Schema.List(true,Schema.Any,Schema.Int)), Schema.Term("LengthOf",Schema.Any))), Schema.Term("And",Schema.Set(true)), Schema.Term("Or",Schema.Any), Schema.Term("Not",Schema.Any), Schema.Term("Equals",Schema.List(true,Schema.Or(Schema.Or(Schema.Term("NotT",Schema.Or(Schema.Term("TupleT",Schema.List(true)), Schema.Term("ArrayT",Schema.Any), Schema.Or(Schema.Term("AnyT"), Schema.Term("NullT"), Schema.Term("VoidT"), Schema.Term("BoolT"), Schema.Term("IntT"), Schema.Term("RealT"), Schema.Term("StringT"), Schema.Term("VarT",Schema.Any), Schema.Term("NominalT",Schema.Any)))), Schema.Any), Schema.Term("NotT",Schema.Any), Schema.Term("OrT",Schema.Set(true)), Schema.Term("AndT",Schema.Any), Schema.Term("ArrayT",Schema.Any), Schema.Term("TupleT",Schema.List(true)), Schema.Term("FunctionT",Schema.List(true,Schema.Any,Schema.Any))),Schema.Bag(true,Schema.Any,Schema.Any)))), Schema.Or(Schema.Term("Inequality",Schema.List(true,Schema.Or(Schema.Any, Schema.Any),Schema.Or(Schema.Any, Schema.Any, Schema.Term("Sum",Schema.List(true,Schema.Any,Schema.Bag(true))), Schema.Term("Mul",Schema.Any), Schema.Term("Div",Schema.List(true,Schema.Any,Schema.Any))))), Schema.Term("Equation",Schema.Any))), Schema.Or(Schema.Term("ForAll",Schema.List(true,Schema.Set(true),Schema.Any)), Schema.Term("Exists",Schema.Any)))), Schema.Any), Schema.Or(Schema.Any, Schema.Term("Array",Schema.Any), Schema.Term("ArrayGen",Schema.Any))),Schema.Any)),
		// $19<ForAll($17<^[^{^[^Var(^string),$4<^Type<Atom<NotT($35<^Proton<TupleT(^[$35...])|ArrayT($35)|Quark<AnyT|NullT|VoidT|BoolT|IntT|RealT|StringT|VarT(^string)|NominalT(^string)>>>)|Proton<TupleT(^[$35...])|ArrayT($35)|Quark<AnyT|NullT|VoidT|BoolT|IntT|RealT|StringT|VarT(^string)|NominalT(^string)>>>|NotT($4)|OrT(^{$4...})|AndT(^{$4...})|ArrayT($4)|TupleT(^[$4...])|FunctionT(^[$4,$4,$4...])>>]...},$13<^$127<BExpr<$137<VExpr<Var(^string)|Fn(^[^string,$139<^Expr<$127|$186<Value<Null|Tuple(^[^$186...])|Bool<True|False>|Num(^real)|String(^string)|Array(^[^$186...])|ArrayGen(^[^$186,^$186])>>|Tuple(^[$139...])|$213<AExpr<$137|Num(^real)|Sum(^[^real,^{|^$213...|}[^$213...]])|Mul(^[^real,^{|^$213...|}[^$213...]])|Div(^[^$213,^$213])>>|SExpr<$137|Array(^[$139...])|ArrayGen(^[$139,$139])>>>...])|Load(^[$139,^int])|LengthOf($139)|IndexOf(^[$139,$139])>>|Bool<True|False>|And(^{$13...})|Or(^{$13...})|Not($13)|Equals(^[$4,^{|$139,$139|}[$139,$139]])|Inequality(^[^AType<IntT|RealT>,^$213])|Equation(^[^AType<IntT|RealT>,^$213])|$19|Exists($17)>>>]>)>
		Schema.Term("ForAll",Schema.List(true,Schema.Set(true),Schema.Or(Schema.Or(Schema.Or(Schema.Or(Schema.Or(Schema.Term("Var",Schema.String), Schema.Term("Fn",Schema.List(true,Schema.Any)), Schema.Term("Load",Schema.List(true,Schema.Or(Schema.Or(Schema.Or(Schema.Any, Schema.Or(Schema.Or(Schema.Term("Null"), Schema.Term("Tuple",Schema.List(true)), Schema.Or(Schema.Term("True"), Schema.Term("False")), Schema.Term("Num",Schema.Real), Schema.Term("String",Schema.Any)), Schema.Or(Schema.Term("Array",Schema.Any), Schema.Term("ArrayGen",Schema.List(true,Schema.Any,Schema.Any)))), Schema.Term("Tuple",Schema.List(true))), Schema.Or(Schema.Any, Schema.Any, Schema.Term("Sum",Schema.List(true,Schema.Any,Schema.Bag(true))), Schema.Term("Mul",Schema.Any), Schema.Term("Div",Schema.List(true,Schema.Any,Schema.Any)))), Schema.Or(Schema.Any, Schema.Term("Array",Schema.Any), Schema.Term("ArrayGen",Schema.List(true,Schema.Any,Schema.Any)))),Schema.Int)), Schema.Term("LengthOf",Schema.Any)), Schema.Term("IndexOf",Schema.Any)), Schema.Any, Schema.Term("And",Schema.Set(true)), Schema.Term("Or",Schema.Any), Schema.Term("Not",Schema.Any), Schema.Term("Equals",Schema.List(true,Schema.Or(Schema.Or(Schema.Term("NotT",Schema.Or(Schema.Term("TupleT",Schema.List(true)), Schema.Term("ArrayT",Schema.Any), Schema.Or(Schema.Term("AnyT"), Schema.Term("NullT"), Schema.Term("VoidT"), Schema.Term("BoolT"), Schema.Term("IntT"), Schema.Term("RealT"), Schema.Term("StringT"), Schema.Term("VarT",Schema.Any), Schema.Term("NominalT",Schema.Any)))), Schema.Any), Schema.Term("NotT",Schema.Any), Schema.Term("OrT",Schema.Set(true)), Schema.Term("AndT",Schema.Any), Schema.Term("ArrayT",Schema.Any), Schema.Term("TupleT",Schema.List(true)), Schema.Term("FunctionT",Schema.List(true,Schema.Any,Schema.Any))),Schema.Bag(true,Schema.Any,Schema.Any)))), Schema.Or(Schema.Term("Inequality",Schema.List(true,Schema.Or(Schema.Any, Schema.Any),Schema.Any)), Schema.Term("Equation",Schema.Any))), Schema.Or(Schema.Any, Schema.Term("Exists",Schema.Any))))),
		// $19<Exists($17<^[^{^[^Var(^string),$4<^Type<Atom<NotT($35<^Proton<TupleT(^[$35...])|ArrayT($35)|Quark<AnyT|NullT|VoidT|BoolT|IntT|RealT|StringT|VarT(^string)|NominalT(^string)>>>)|Proton<TupleT(^[$35...])|ArrayT($35)|Quark<AnyT|NullT|VoidT|BoolT|IntT|RealT|StringT|VarT(^string)|NominalT(^string)>>>|NotT($4)|OrT(^{$4...})|AndT(^{$4...})|ArrayT($4)|TupleT(^[$4...])|FunctionT(^[$4,$4,$4...])>>]...},$13<^$127<BExpr<$137<VExpr<Var(^string)|Fn(^[^string,$139<^Expr<$127|$186<Value<Null|Tuple(^[^$186...])|Bool<True|False>|Num(^real)|String(^string)|Array(^[^$186...])|ArrayGen(^[^$186,^$186])>>|Tuple(^[$139...])|$213<AExpr<$137|Num(^real)|Sum(^[^real,^{|^$213...|}[^$213...]])|Mul(^[^real,^{|^$213...|}[^$213...]])|Div(^[^$213,^$213])>>|SExpr<$137|Array(^[$139...])|ArrayGen(^[$139,$139])>>>...])|Load(^[$139,^int])|LengthOf($139)|IndexOf(^[$139,$139])>>|Bool<True|False>|And(^{$13...})|Or(^{$13...})|Not($13)|Equals(^[$4,^{|$139,$139|}[$139,$139]])|Inequality(^[^AType<IntT|RealT>,^$213])|Equation(^[^AType<IntT|RealT>,^$213])|$19|ForAll($17)>>>]>)>
		Schema.Term("Exists",Schema.List(true,Schema.Set(true),Schema.Or(Schema.Or(Schema.Or(Schema.Or(Schema.Or(Schema.Term("Var",Schema.String), Schema.Term("Fn",Schema.List(true,Schema.Any)), Schema.Term("Load",Schema.List(true,Schema.Or(Schema.Or(Schema.Or(Schema.Any, Schema.Or(Schema.Or(Schema.Term("Null"), Schema.Term("Tuple",Schema.List(true)), Schema.Or(Schema.Term("True"), Schema.Term("False")), Schema.Term("Num",Schema.Real), Schema.Term("String",Schema.Any)), Schema.Or(Schema.Term("Array",Schema.Any), Schema.Term("ArrayGen",Schema.List(true,Schema.Any,Schema.Any)))), Schema.Term("Tuple",Schema.List(true))), Schema.Or(Schema.Any, Schema.Any, Schema.Term("Sum",Schema.List(true,Schema.Any,Schema.Bag(true))), Schema.Term("Mul",Schema.Any), Schema.Term("Div",Schema.List(true,Schema.Any,Schema.Any)))), Schema.Or(Schema.Any, Schema.Term("Array",Schema.Any), Schema.Term("ArrayGen",Schema.List(true,Schema.Any,Schema.Any)))),Schema.Int)), Schema.Term("LengthOf",Schema.Any)), Schema.Term("IndexOf",Schema.Any)), Schema.Any, Schema.Term("And",Schema.Set(true)), Schema.Term("Or",Schema.Any), Schema.Term("Not",Schema.Any), Schema.Term("Equals",Schema.List(true,Schema.Or(Schema.Or(Schema.Term("NotT",Schema.Or(Schema.Term("TupleT",Schema.List(true)), Schema.Term("ArrayT",Schema.Any), Schema.Or(Schema.Term("AnyT"), Schema.Term("NullT"), Schema.Term("VoidT"), Schema.Term("BoolT"), Schema.Term("IntT"), Schema.Term("RealT"), Schema.Term("StringT"), Schema.Term("VarT",Schema.Any), Schema.Term("NominalT",Schema.Any)))), Schema.Any), Schema.Term("NotT",Schema.Any), Schema.Term("OrT",Schema.Set(true)), Schema.Term("AndT",Schema.Any), Schema.Term("ArrayT",Schema.Any), Schema.Term("TupleT",Schema.List(true)), Schema.Term("FunctionT",Schema.List(true,Schema.Any,Schema.Any))),Schema.Bag(true,Schema.Any,Schema.Any)))), Schema.Or(Schema.Term("Inequality",Schema.List(true,Schema.Or(Schema.Any, Schema.Any),Schema.Any)), Schema.Term("Equation",Schema.Any))), Schema.Or(Schema.Any, Schema.Term("ForAll",Schema.Any))))),
		// Is(^[$2<^Expr<$53<Value<Null|Tuple(^[^$53...])|Bool<True|False>|Num(^real)|String(^string)|Array(^[^$53...])|ArrayGen(^[^$53,^$53])>>|Tuple(^[$2...])|$95<BExpr<Bool<True|False>|VExpr<Var(^string)|Fn(^[^string,$2...])|Load(^[$2,^int])|LengthOf($2)|IndexOf(^[$2,$2])>|And(^{^$95...})|Or(^{^$95...})|Not(^$95)|Equals(^[$4<^Type<Atom<NotT($162<^Proton<TupleT(^[$162...])|ArrayT($162)|Quark<AnyT|NullT|VoidT|BoolT|IntT|RealT|StringT|VarT(^string)|NominalT(^string)>>>)|Proton<TupleT(^[$162...])|ArrayT($162)|Quark<AnyT|NullT|VoidT|BoolT|IntT|RealT|StringT|VarT(^string)|NominalT(^string)>>>|NotT($4)|OrT(^{$4...})|AndT(^{$4...})|ArrayT($4)|TupleT(^[$4...])|FunctionT(^[$4,$4,$4...])>>,^{|$2,$2|}[$2,$2]])|Inequality(^[^AType<IntT|RealT>,$236<^AExpr<Num(^real)|VExpr<Var(^string)|Fn(^[^string,$2...])|Load(^[$2,^int])|LengthOf($2)|IndexOf(^[$2,$2])>|Sum(^[^real,^{|$236...|}[$236...]])|Mul(^[^real,^{|$236...|}[$236...]])|Div(^[$236,$236])>>])|Equation(^[^AType<IntT|RealT>,$236])|ForAll(^[^{^[^Var(^string),$4]...},^$95])|Exists(^[^{^[^Var(^string),$4]...},^$95])>>|AExpr<Num(^real)|VExpr<Var(^string)|Fn(^[^string,$2...])|Load(^[$2,^int])|LengthOf($2)|IndexOf(^[$2,$2])>|Sum(^[^real,^{|$236...|}[$236...]])|Mul(^[^real,^{|$236...|}[$236...]])|Div(^[$236,$236])>|SExpr<VExpr<Var(^string)|Fn(^[^string,$2...])|Load(^[$2,^int])|LengthOf($2)|IndexOf(^[$2,$2])>|Array(^[$2...])|ArrayGen(^[$2,$2])>>>,$4])
		Schema.Term("Is",Schema.List(true,Schema.Or(Schema.Or(Schema.Or(Schema.Or(Schema.Or(Schema.Term("Null"), Schema.Term("Tuple",Schema.List(true)), Schema.Or(Schema.Term("True"), Schema.Term("False")), Schema.Term("Num",Schema.Real), Schema.Term("String",Schema.String)), Schema.Or(Schema.Term("Array",Schema.Any), Schema.Term("ArrayGen",Schema.List(true,Schema.Any,Schema.Any)))), Schema.Term("Tuple",Schema.List(true)), Schema.Or(Schema.Or(Schema.Or(Schema.Any, Schema.Or(Schema.Or(Schema.Term("Var",Schema.Any), Schema.Term("Fn",Schema.List(true,Schema.Any)), Schema.Term("Load",Schema.List(true,Schema.Any,Schema.Int)), Schema.Term("LengthOf",Schema.Any)), Schema.Term("IndexOf",Schema.List(true,Schema.Any,Schema.Any))), Schema.Term("And",Schema.Set(true)), Schema.Term("Or",Schema.Any), Schema.Term("Not",Schema.Any), Schema.Term("Equals",Schema.List(true,Schema.Or(Schema.Or(Schema.Term("NotT",Schema.Or(Schema.Term("TupleT",Schema.List(true)), Schema.Term("ArrayT",Schema.Any), Schema.Or(Schema.Term("AnyT"), Schema.Term("NullT"), Schema.Term("VoidT"), Schema.Term("BoolT"), Schema.Term("IntT"), Schema.Term("RealT"), Schema.Term("StringT"), Schema.Term("VarT",Schema.Any), Schema.Term("NominalT",Schema.Any)))), Schema.Any), Schema.Term("NotT",Schema.Any), Schema.Term("OrT",Schema.Set(true)), Schema.Term("AndT",Schema.Any), Schema.Term("ArrayT",Schema.Any), Schema.Term("TupleT",Schema.List(true)), Schema.Term("FunctionT",Schema.List(true,Schema.Any,Schema.Any))),Schema.Bag(true,Schema.Any,Schema.Any)))), Schema.Or(Schema.Term("Inequality",Schema.List(true,Schema.Or(Schema.Any, Schema.Any),Schema.Or(Schema.Any, Schema.Any, Schema.Term("Sum",Schema.List(true,Schema.Any,Schema.Bag(true))), Schema.Term("Mul",Schema.Any), Schema.Term("Div",Schema.List(true,Schema.Any,Schema.Any))))), Schema.Term("Equation",Schema.Any))), Schema.Or(Schema.Term("ForAll",Schema.List(true,Schema.Set(true),Schema.Any)), Schema.Term("Exists",Schema.Any)))), Schema.Any), Schema.Or(Schema.Any, Schema.Term("Array",Schema.Any), Schema.Term("ArrayGen",Schema.Any))),Schema.Any))
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
	// $13<Expr<$43<Value<Null|Tuple(^[^$43...])|Bool<True|False>|Num(^real)|String(^string)|Array(^[^$43...])|ArrayGen(^[^$43,^$43])>>|Tuple(^[^$13...])|$86<BExpr<Bool<True|False>|VExpr<Var(^string)|Fn(^[^string,^$13...])|Load(^[^$13,^int])|LengthOf(^$13)|IndexOf(^[^$13,^$13])>|And(^{^$86...})|Or(^{^$86...})|Not(^$86)|Equals(^[$132<^Type<Atom<NotT($155<^Proton<TupleT(^[$155...])|ArrayT($155)|Quark<AnyT|NullT|VoidT|BoolT|IntT|RealT|StringT|VarT(^string)|NominalT(^string)>>>)|Proton<TupleT(^[$155...])|ArrayT($155)|Quark<AnyT|NullT|VoidT|BoolT|IntT|RealT|StringT|VarT(^string)|NominalT(^string)>>>|NotT($132)|OrT(^{$132...})|AndT(^{$132...})|ArrayT($132)|TupleT(^[$132...])|FunctionT(^[$132,$132,$132...])>>,^{|^$13,^$13|}[^$13,^$13]])|Inequality(^[^AType<IntT|RealT>,$229<^AExpr<Num(^real)|VExpr<Var(^string)|Fn(^[^string,^$13...])|Load(^[^$13,^int])|LengthOf(^$13)|IndexOf(^[^$13,^$13])>|Sum(^[^real,^{|$229...|}[$229...]])|Mul(^[^real,^{|$229...|}[$229...]])|Div(^[$229,$229])>>])|Equation(^[^AType<IntT|RealT>,$229])|ForAll(^[^{^[^Var(^string),$132]...},^$86])|Exists(^[^{^[^Var(^string),$132]...},^$86])>>|AExpr<Num(^real)|VExpr<Var(^string)|Fn(^[^string,^$13...])|Load(^[^$13,^int])|LengthOf(^$13)|IndexOf(^[^$13,^$13])>|Sum(^[^real,^{|$229...|}[$229...]])|Mul(^[^real,^{|$229...|}[$229...]])|Div(^[$229,$229])>|SExpr<VExpr<Var(^string)|Fn(^[^string,^$13...])|Load(^[^$13,^int])|LengthOf(^$13)|IndexOf(^[^$13,^$13])>|Array(^[^$13...])|ArrayGen(^[^$13,^$13])>>>
	private static Type type6 = Runtime.Type("9I3K3Tk86KL45QpK5KJK6RgK5K1K3Tk8MBC5v5c6Qs2K0K3Tk8M7zV9hGHJCKGs0bRWcovo5BCXDCpXI3tJSglq3NlHL38oQjl5CDKMQZC4Sm_aQbdHYl7TlHDUd1PYkIPgcLJPhqbWeGfl5gGKFm8MNtCXQdlmQ3508bRW_rG_tq7Ttp7ScMDvd1UYZMUgsM7sxr575WoLXl595YgnXGAB53G_RpKq3D5gwNF_GWlqR_CGa0AP5WVOgOg0bl7QpOoXbW9PB1Mc5gZPcH5Yope0Ag5ewo7i5gZnfW9s5YkIi0Au5JOKGs0bRo3ZQZGmImGYIjG6O44MSWlqRWxOgUVfcfkfVhgGm0dGHiKLRp45QdGMT3544MSWGMPjtL7CHAIQoR3XmWnl5E6ZOoQm43QgGLGs_qRoCM7dIfIQgS31q0rl5S6YoYrGAU6oNKNmGXGiG3Ij45O35BKaQbG6PEOLFx6A9P9R9QoTFMHiGLOsxZOWsTceg0yl7w5t6hcUBHule0Aw6IgPBXfWzGDz6eVcBXuGX1A99egl7i5B9YoGYHDD9ewcBmu0a1AO9YkTsPkmam7i5i5YoGbHDT9ewdBmv0e1Ad9eVTBmem9jkecHfm7x5i9gweBXjWf1At9YwQgekmi1GJ_6R_dmuX7i5i5Yolj1D7AeZgBXjXmm7SggZ2nX9CAYVRsgkmn1G0GrQhGZIjG6KowZRJGJFiG5KZ4ZRm4LTJG5Kp06Q_G4_WGptqNo_qQiGKRvANESEUEdEiEwEQViBHjHuHAeAZ0_RjGrQidmYn7PAhAgsi3mvmYn5sAYZhZjoXy1KGKMNmhq7hAgZIzX9yAYshwjk1Xn7SAhAgcs3IXnXYnn5BDYkiosoXY2G0tLTJC0a2AODJtJSgl5KIgtk1b2KLxLPZGp3TDgwtF_Fjx5QJCGe2AeD3_ZQoGp3gDgouF_J_45QJClf2AsDoC4Sm_aQbGp3uDggvFZKW86KYovgPkXj2WWIjpLPi45QJC1mne0A8EG5PDSDcDfDiDtDwDzD9EQgwB1z1nIACEYchsfkmnn7y9fwHqY9PEYghgxk1rn7RAQEgsxBHrXj1AcEYsfkHDeEegyBXr1v2AhEYsfsfBXjmvIDsEeZzBmrXy2AvEJ43Kt0MOeZ8d1eo7yEzEYo0XJD8Hec7CmmlX3ABHWsuZvgWYo7xEEHhV8GnJpp5CCK6QoFJPq4_elyGioiJmo5SHYVZbJAUHYwzg1DdHec9C1eleo7Sk9_IfZ9iHYc8x9l1io7QHjHgcACmznzn7SkA_IjZ9yHYk8xAl1mo7B6AHgcBdHzl7BIy9YoGnJDDIewBC1qo9jZCdXqo7QIf9Yo0rJDSIesCCHqlr3AcIYcSwClXuJBv6tIvIQkDCmHhIhsDCXQt5gVECHTc9gcE4Ex");
	// int
	private static Type type7 = Runtime.Type("Fg0");
	// $11<VExpr<Var(^string)|Fn(^[^string,$16<^Expr<$65<Value<Null|Tuple(^[^$65...])|Bool<True|False>|Num(^real)|String(^string)|Array(^[^$65...])|ArrayGen(^[^$65,^$65])>>|Tuple(^[$16...])|$105<BExpr<$11|Bool<True|False>|And(^{^$105...})|Or(^{^$105...})|Not(^$105)|Equals(^[$117<^Type<Atom<NotT($140<^Proton<TupleT(^[$140...])|ArrayT($140)|Quark<AnyT|NullT|VoidT|BoolT|IntT|RealT|StringT|VarT(^string)|NominalT(^string)>>>)|Proton<TupleT(^[$140...])|ArrayT($140)|Quark<AnyT|NullT|VoidT|BoolT|IntT|RealT|StringT|VarT(^string)|NominalT(^string)>>>|NotT($117)|OrT(^{$117...})|AndT(^{$117...})|ArrayT($117)|TupleT(^[$117...])|FunctionT(^[$117,$117,$117...])>>,^{|$16,$16|}[$16,$16]])|Inequality(^[^AType<IntT|RealT>,$214<^AExpr<$11|Num(^real)|Sum(^[^real,^{|$214...|}[$214...]])|Mul(^[^real,^{|$214...|}[$214...]])|Div(^[$214,$214])>>])|Equation(^[^AType<IntT|RealT>,$214])|ForAll(^[^{^[^Var(^string),$117]...},^$105])|Exists(^[^{^[^Var(^string),$117]...},^$105])>>|AExpr<$11|Num(^real)|Sum(^[^real,^{|$214...|}[$214...]])|Mul(^[^real,^{|$214...|}[$214...]])|Div(^[$214,$214])>|SExpr<$11|Array(^[$16...])|ArrayGen(^[$16,$16])>>>...])|Load(^[$16,^int])|LengthOf($16)|IndexOf(^[$16,$16])>>
	private static Type type8 = Runtime.Type("9IJOKGs0bRoNKNmGXGiG3Ij45O35BKaQbG6PEOLFNWqvJyo5zFMHiGLOsxZOWVoyo59CXDAp1IeZl7vs3AEGJGs0bReor3DCXLQ_2Meop7ws4AUG_KWlLS_G4Kp06Q_G_F4W6Rm4nilrlXm5gGKF4W6Rm4HQ8HQw5KIK3Tk8M7sWChWTYZpThk6GDK6QgCWUgw6G1xqQgGYIpp5OIGbRdtqOegQB1Y0AtoNcXYl7exNk1aGJ75O5C6N6P6QcOFKFm8MNtC1blY0AS53508bRW_rG_tq7B5B5Yo0eGDd5ecPBmble0Ag5WsOoPgWfG7Q5j5QVQBHPt5hcQF3KmKMOIkQkHj0K545QnKq3z5gVR3XjGml596YZNgRo1nW9PBXXWn0AE6YgNs3AO6Yc4AtgSc1rl7epSkXr0C0t5OZwZRosoQoGLGlKMNgCMNCpRZdgdodZfg0v0dGHiKLRp45QdGMT3544MSWGMPjtL7iEgHQVU3HvGyl5u6ZOoQm43QgGLGs_qRoCM79IBIQsU3mylzl579YgLXHA99egcB1Ym9joccXYm7c6E9gVdBHulY1AP9YcTkck1b1GJ_6R_d1nX7Pdp7SVeVIeX9e9YwdgeBH6g9toecXfm7f6j9gVfFJFoxLQ3toQoG4CE86K34ZQZG4O08bRW_6KZGKSklLOJGONJSiC5SdxaQJ46rHiYj2mYmnnIrn58AYsdcgomm1OF8rQoxaQeVjBmiXn1AEAWVhVjgGqm7u9PAhghFKJp4aRfCXn1Atshcmrm7z9cAgZiBXjXn1AfAlcikiwugGvm7CAiAhwiFJFi_6KIZjkXy1KDK6QgGp3wAgojF_Kj_5OJClz1A7DJ8oQjl5KIcskmX2G8t5SJCGY2ADDJ8KOWl5KIVtkHa2SIGbRdtqOJCla2ARD3OKNmGp7TDDlmb2WWIjpLPi45QJCHeYIgcu3OgjsjZskswsctotVugug0fn7SAhDhsuBmimb1AsDYwdgmAuDegvB1j1j2AxDYofkvkmjn7y9U9gZwBmb1Atgwc1nn7z9CEgswBmbmbm7U9NEtZxcXqn77AQEgkxFKFJ_6R_dXyY98HYwxVyBH6dEtcycmun7i6gEgoy3mYYan5jEYsxVzoHy2CIKMQooJSgG2GdOMJCWSc8l8d9hWzn7ixzo1Xo7cEfVYXZ9AHYsRk7CH6CHts7dmYo7vENHgZ8C1z2a3AQHYVyVyBH6SHts8dmbo7xEcHgZ9Cmv0v2AfHeVp7hHU9YoWfJDjHeVACHio9jcAdmio7wHB9YoGjJDyHewAC1z0m3A8IYoUVBlmmJBCdCWDhGno7ttBpmno7R5S6gZCCXLPCH6QItkCdHro7U5TIgwCdm5YcKuo7ScD_nuZ9gIYoIv3AiIYsYLgVECHHTIgcE4C0");
	// $7<Tuple($5<^[$2<^Expr<$7|$49<Value<Null|Tuple(^[^$49...])|Bool<True|False>|Num(^real)|String(^string)|Array(^[^$49...])|ArrayGen(^[^$49,^$49])>>|$86<BExpr<Bool<True|False>|VExpr<Var(^string)|Fn(^[^string,$2...])|Load(^[$2,^int])|LengthOf($2)|IndexOf(^[$2,$2])>|And(^{^$86...})|Or(^{^$86...})|Not(^$86)|Equals(^[$132<^Type<Atom<NotT($155<^Proton<TupleT(^[$155...])|ArrayT($155)|Quark<AnyT|NullT|VoidT|BoolT|IntT|RealT|StringT|VarT(^string)|NominalT(^string)>>>)|Proton<TupleT(^[$155...])|ArrayT($155)|Quark<AnyT|NullT|VoidT|BoolT|IntT|RealT|StringT|VarT(^string)|NominalT(^string)>>>|NotT($132)|OrT(^{$132...})|AndT(^{$132...})|ArrayT($132)|TupleT(^[$132...])|FunctionT(^[$132,$132,$132...])>>,^{|$2,$2|}[$2,$2]])|Inequality(^[^AType<IntT|RealT>,$229<^AExpr<Num(^real)|VExpr<Var(^string)|Fn(^[^string,$2...])|Load(^[$2,^int])|LengthOf($2)|IndexOf(^[$2,$2])>|Sum(^[^real,^{|$229...|}[$229...]])|Mul(^[^real,^{|$229...|}[$229...]])|Div(^[$229,$229])>>])|Equation(^[^AType<IntT|RealT>,$229])|ForAll(^[^{^[^Var(^string),$132]...},^$86])|Exists(^[^{^[^Var(^string),$132]...},^$86])>>|AExpr<Num(^real)|VExpr<Var(^string)|Fn(^[^string,$2...])|Load(^[$2,^int])|LengthOf($2)|IndexOf(^[$2,$2])>|Sum(^[^real,^{|$229...|}[$229...]])|Mul(^[^real,^{|$229...|}[$229...]])|Div(^[$229,$229])>|SExpr<VExpr<Var(^string)|Fn(^[^string,$2...])|Load(^[$2,^int])|LengthOf($2)|IndexOf(^[$2,$2])>|Array($5)|ArrayGen(^[$2,$2])>>>...]>)>
	private static Type type9 = Runtime.Type("9IJGKSklLO3K3Tk8b9SC1EgZIEesn7uw2A7G_KWlLS_G_F4W6Rm4IHQ5c6Qk3K0K3Tk8M7CW9hlIJCKGs0bRWVpvo5PCmDQp1M3tJSglq3TlmM38oQjl5CDKMQZC4Sm_aQbdmal7glHDhdXQYcnQgVMJc_Mf0ilil5uGKFm8MNtC1UjlHU3508bRW_rG_tq7glq7SVNZIXW995YwrX0AB5WsMYl5D5WgrYl5N5YcJaGAP53G_RpKq3R5goOF_GWlqR_Clb0Ac5WsOZPgWel7dhPo1fW9PBXPi5gwPcH5YgLi0Au5JOKGs0bRo3ZQZGmImGYIjG6O44MSWlqRWpPgUVfcfkfVhgGm0dGHiKLRp45QdGMT3544MSWGMPjtL7CHAIQoR3XmWnl5E6ZOoQm43QgGLGs_qRoCM7dIfIQgS31q0rl5S6YgZrGAU6oNKNmGXGiG3Ij45O35BKaQbG6PEOLFx6A9P9R9QoTFMHiGLOsxZOWsTceg0yl7w5t6hcUBHuGi0Aw6IZQB1Ey6twUc1Xm7e689gcccm5Yk2Ym7SocZYYX9E9YgTVdkHam7g6wkmam7wkn7SodZYbX9U9YwTVekHeX9c6YgegmAg9eoeBHjWf1Aj9YsQsekHim7z5f9ggfF3Kt0MOegi71EwBH6z9sVgcHmm7y99AYolmHDBAeogB1mWn1AEA343Sjp5GDx5SJGnImG4G0t5OJGLFm8MNtG4OJK6RgK5KJ55KbQYGMPjt5KlhjVxoxwxZysykzg0um7x9dAhciF5Jmx5Sjta9EDYchoikXvH7jAEDQVjBHqHyHAuAJ4KSW8rPYoikHDxAesjBXrmz1A7DYohoikXXIB8DADDEQksB1vHYIADD34ZQtGp3NDgZtF_Ipl5QJCla2ARDJOpQdG5KIstkmb2K1xqQgGp3dDgcuFJHiG6KIkukHf2KHKLNgGp3jDgVvFrJo8MPiS5KIcvkmi2GL4aRJCHjIi0AyD35DxLQdtLNgGp77Et5gZw3OctotVugusuZvkvwvcwglmn7wABEhowBXqXj1AEEYsfgmAOEecxBmqmq2AREYkhgxkXrn7SAy9gVyBXj1Atcycmun7TAgEgoyBXjXjm7y9jEtVzcHyn7UAuEggzFKFJ_6R_dHaZ9cHYszwzBH67HtZ7dXXo7A6AHgk74XfIin5DHYozw7p1a3CIKMQooJSgG2GdOMJs5v6tHvH8IQo8CXITHhw8Cmzn9sZ9dXeo7i5fHYo0fJDhHes9CXaof3AsHYg8x9lXio7zEzEYo0jJDxHesAC1boj3A7IYkRg7lXmZ9x6YkBtfBH6CItsBdmno7NIfwHqZ9PIYgCheBH6RItoCdXro7O6UIgVDCXqlr3AeIlgUZEhEh0vo7OpDpXvo7wx2AsIYw6e1AuIGHE");
	// $22<BExpr<$33<VExpr<Var(^string)|Fn(^[^string,$38<^Expr<$22|$85<Value<Null|Tuple(^[^$85...])|Bool<True|False>|Num(^real)|String(^string)|Array(^[^$85...])|ArrayGen(^[^$85,^$85])>>|Tuple(^[$38...])|$112<AExpr<$33|Num(^real)|Sum(^[^real,^{|^$112...|}[^$112...]])|Mul(^[^real,^{|^$112...|}[^$112...]])|Div(^[^$112,^$112])>>|SExpr<$33|Array(^[$38...])|ArrayGen(^[$38,$38])>>>...])|Load(^[$38,^int])|LengthOf($38)|IndexOf(^[$38,$38])>>|Bool<True|False>|And(^{^$22...})|Or(^{^$22...})|Not(^$22)|Equals(^[$165<^Type<Atom<NotT($188<^Proton<TupleT(^[$188...])|ArrayT($188)|Quark<AnyT|NullT|VoidT|BoolT|IntT|RealT|StringT|VarT(^string)|NominalT(^string)>>>)|Proton<TupleT(^[$188...])|ArrayT($188)|Quark<AnyT|NullT|VoidT|BoolT|IntT|RealT|StringT|VarT(^string)|NominalT(^string)>>>|NotT($165)|OrT(^{$165...})|AndT(^{$165...})|ArrayT($165)|TupleT(^[$165...])|FunctionT(^[$165,$165,$165...])>>,^{|$38,$38|}[$38,$38]])|Inequality(^[^AType<IntT|RealT>,^$112])|Equation(^[^AType<IntT|RealT>,^$112])|ForAll(^[^{^[^Var(^string),$165]...},^$22])|Exists(^[^{^[^Var(^string),$165]...},^$22])>>
	private static Type type10 = Runtime.Type("9IJ8JGs0bRJOKGs0bR38oQjl5C0t5OZwZRosoQoGLGlKMNgCMNv_UZjgjojZtgGHZ58tLOlKMNg_5StGNJJRp45SdxaQWoBhChGIWcZIQw3O5xaR0l5QZK3TdC6Sn4Hyoyo5Q41LRhGMYcYMhw4CL4aRZNZQ3loQWG5W0I_tqOoWqIa4ZUD5UAdAQo5S8t5O_WrIa4XQfAQVr7vZMAudH5YZ5Ugo6G4W6RmdXel3wC1XGXGD95egNBXPB5goNF_KWlLS_G4Kp06Q_42PU6A9QZOFKF4W6Rm4XaWam5R5JCKGs0bRWoOVgglbl7zWPoHe0GDK6QgCle0Ag5osJShGqJo8MPiSa9U6YVQkHDt5ecQB1ali0Aw5GpPoQZUkUsUgWj0K08bRW_r776v5gZRFN3ZRm4LT6KaQYVQVQBH6B6toRcXnl7A6E6gVS3XmGql5P6WwQgSg0rl7E5S6hsSF3KmKMOIVTkHu0K545QnKq3f6gkT3XuGvl5i6YknvGAs6ecl7i5u6ggUBmf0UgoUB1X0AtwUc1Xm7N589gccFnJpp5CCK6QoFJPq4pTw6g9i9w9QwcBma0aHAO9ecdBmam9skdcHbm7u6T9YolbHDc9eZeB1YXe1Af9YoccekHfm7Q9Q9YolfHDs9eZfBXYXi1Av9lgbm1qm5x9YsOsfomjm77689gZgB1X0Xl7SggZ2nX9CAYgRsgkmnX9QB1XGqm7SchZnqX9RAYgLr1ATAYk5X0AcAYwan1AeAeVq7gAfwHvX9iAYonv1AsAYsnv1AuAYw2v1AwA3GKTkKa9gDXVNVNBH67DsZscXXn7zAADYo0YIDCDessB1HEDgVtFJFoxLQ3toQoG4CE86K34ZQZG4O08bRW_6KZGKSklLOJGONJSiC5SdxaQJ46jIaZb3eZeofJjo5dDYsjcuome2OF8rQoxaQeVxBmaYf2AjDWVvVxgGin7PDuDhgvFKJp4aRfCXf2Atsvcmjn7UD7EgZwBXbYf2AAElcwkww7hGnn7hDDEhwwFJFi_6KIZxkXq2KDK6QgGp3REgoxF_Kj_5OJClr2AcEJ8oQjl5KIcykmu2G8t5SJCGv2AiEJ8KOWl5KIVzkHy2SIGbRdtqOJCly2AwE3OKNmGp7yEwlmz2WWIjpLPi45QJCHX3Ugc74OgxsxZykywyczozV7h7h0Yo7xDCHhs7Cmanz1ANHYwjgmAPHeg8C1b2b3ASHYotk8lmbo7TDzAgZ9Cmz1Atg9d1fo7UDhHgs9Cmzmzm7zAsHtZAdXio7cDvHgkAGKFJ_6R_dHqo7zHQ9Yo0mJD8IecBCmHAIgkB4mvYyn5DIYsAxBp1qo7BhBlXqZ9yC1rozm7SoC_YrZ9UIYVDhmAdIecDCmu3vm7SkD_IvZ9iIYZpv3AsIYcpv3AuI0PE");
	// Bool<True|False>
	private static Type type11 = Runtime.Type("QFZFjx5Q3G_RpKq3vk1EJOJNgCMOIs2Az3HE7hGHYcYHhgJko2");
	// any
	private static Type type12 = Runtime.Type("Fs0");
	// False
	private static Type type13 = Runtime.Type("2K545QnKq3ukmD0E");
	// True
	private static Type type14 = Runtime.Type("2GJ8MS_CWDggIk2");
	// $31<Value<Null|Tuple(^[^$31...])|Bool<True|False>|Num(^real)|String(^string)|Array(^[^$31...])|ArrayGen(^[^$31,^$31])>>
	private static Type type15 = Runtime.Type("cG_KWlLS_GZIpl5QIg2AwFZFjx5QosJShGqJo8MPiS5KJK6RgKa9tCXHgZnHeko78p3AD4KEEhNsNZOg0LJ4ZRm4LTYcKIgg4WGFm8MNtSJOiCXH9CH6T_nMeVq7S_5Ae41Mfh0QWZKQQsq7uwLAsG3KmKMOIc6AvG_GWlqR_CGUgsM7wxr575YsIXGA95ecl7zkNkHYW9OB1HE5gVO3t0");
	// real
	private static Type type16 = Runtime.Type("Fc0");
	// $9<AExpr<Num(^real)|Sum(^[^real,^{|^$9...|}[^$9...]])|Mul(^[^real,^{|^$9...|}[^$9...]])|Div(^[^$9,^$9])|$41<VExpr<Var(^string)|Fn(^[^string,$46<^Expr<$9|$93<Value<Num(^real)|Null|Tuple(^[^$93...])|Bool<True|False>|String(^string)|Array(^[^$93...])|ArrayGen(^[^$93,^$93])>>|Tuple(^[$46...])|$130<BExpr<$41|Bool<True|False>|And(^{^$130...})|Or(^{^$130...})|Not(^$130)|Equals(^[$142<^Type<Atom<NotT($165<^Proton<TupleT(^[$165...])|ArrayT($165)|Quark<AnyT|NullT|VoidT|BoolT|IntT|RealT|StringT|VarT(^string)|NominalT(^string)>>>)|Proton<TupleT(^[$165...])|ArrayT($165)|Quark<AnyT|NullT|VoidT|BoolT|IntT|RealT|StringT|VarT(^string)|NominalT(^string)>>>|NotT($142)|OrT(^{$142...})|AndT(^{$142...})|ArrayT($142)|TupleT(^[$142...])|FunctionT(^[$142,$142,$142...])>>,^{|$46,$46|}[$46,$46]])|Inequality(^[^AType<IntT|RealT>,^$9])|Equation(^[^AType<IntT|RealT>,^$9])|ForAll(^[^{^[^Var(^string),$142]...},^$130])|Exists(^[^{^[^Var(^string),$142]...},^$130])>>|SExpr<$41|Array(^[$46...])|ArrayGen(^[$46,$46])>>>...])|Load(^[$46,^int])|LengthOf($46)|IndexOf(^[$46,$46])>>>>
	private static Type type17 = Runtime.Type("9IJ4JGs0bRosJShGnJpp5CCK6QoFJPqG_K4W6Rm4_Icd5TA5QVo7uZJA9dX5Yg2IgoZ9ACmIfV2LeZp7Bdp7SgKDRdHMYkYMgwp7xs4AdCmIECH6f_2Qeoq7ys5AjGYKW8685t5GBxLNZGNkJOiS5ScxZO0tNsOwD_EhGUo_ZQZK5TEOL7yhEh0Xl7zZNoXXW9OBHTB5goNFJGs0bRecQB0Yl7N5O5tcOcmal7ulOkHb0KL45QpK5KJK6RgK5K1K3Tk8MBj6N9w9QcP3mHf5QkPFpJ4W6Rm4Hf0qo5j5YwNVQoHi0GDK6QgCli0Aw538oQjl5OIGbRdtqOewTB1m0AtZRcXml7c5A6gkR3_Ix5C689A9QsRFKFm8MNtC1qlm0AO63508bRW_rG_tq77676Yo0rGDS6esSBmqlr0Ac6WcSZTgWuG7E6f6QkTBmbGvGAi63G_RpKq3s6gZUF_GWlqR_Cly0Aw6WcUoUgWzl7y5z6hVcBmj0Y0A99YVOkHDB9eocB1eWY1AE9o3ZQZGmImGYIjG6O44MSWlqRWhNZccgkgsgcigGb1dGHiKLRp45QdGMT3544MSWGMPjtL7THgHQZe3XbXem5f9ZOoQm43QgGLGs_qRoCM79IBIQwe31f1im5t9YZPcfomiX9w9YofgmAy9ewfBHa1m1A8AYcdVgkmmm7Q9x9gogF3Kt0MOeoj71a0al7SZhVYqX9QAYVhkhBH6SAtshcmrm7R9cAgZiFJFoxLQ3toQoG4CE86K34ZQZG4O08bRW_6KZGKSklLOJGONJSiC5SdxaQJ4MYYunvIyny2XZYo5uAYwggjo1z1OF8rQoxaQeZuB1vmz1A7DWZsZugWXn7fAADhksFKJp4aRfCmz1Atwsc1an7sAODgctBmvmz1ARDlgtotVygWbn7yAUDhVuFJFi_6KIcukme2KDK6QgGp3hDgsuF_Kj_5OJC0i2AtDJ8oQjl5KIgvk1j2G8t5SJCWj2AzDJ8KOWl5KIZwkXm2SIGbRdtqOJC0n2ACE3OKNmGp7EEB5gVxFNsoQh_aQWl5KYcxkNkmqIZ0fnfYiIj2mnmYnIq2rn5SEYsssxomrn7gANAgZyB1qm9jgyc1vn7hAhEgsyBXvHv2AsEYwiVhkXyn7NAgZ2zY9xEYVjszkmzn7NANAYVhZ7_YXZ9AHYZjk7lHY3K0GKTkKa9eHYV8xo7SZ8_YaZ9QHYwdk8lHbJ77EAEQw8CmY3eJAdHYVek8lmeZ9D5Yo9WhBH6iHtw9d1io7tHfwXiZ9vHYkApfBH6xHtsAdmjo7h97IgZBCXf1m3AAIlgNcCWDhGno7i5DIhwBC1qWY1AOIYVOVOBH6QItkCdHro7Q6TIgwCdm5YVOZDCH6eItgDd1vo7vpDlXvo7wWOk1yo7ztClXyJg3");
	// Num(^real)
	private static Type type18 = Runtime.Type("3CDKMQecl7ug2Aw3x$");
	// ^Num(^real)
	private static Type type19 = Runtime.Type("4CDKMQesY9PBXDwkHElD");
	// ^$13<Sum($11<^[^real,^{|$4<^$21<AExpr<$13|Num(^real)|Mul($11)|Div(^[$4,$4])|$42<VExpr<Var(^string)|Fn(^[^string,$47<^Expr<$21|$94<Value<Num(^real)|Null|Tuple(^[^$94...])|Bool<True|False>|String(^string)|Array(^[^$94...])|ArrayGen(^[^$94,^$94])>>|Tuple(^[$47...])|$131<BExpr<$42|Bool<True|False>|And(^{^$131...})|Or(^{^$131...})|Not(^$131)|Equals(^[$143<^Type<Atom<NotT($166<^Proton<TupleT(^[$166...])|ArrayT($166)|Quark<AnyT|NullT|VoidT|BoolT|IntT|RealT|StringT|VarT(^string)|NominalT(^string)>>>)|Proton<TupleT(^[$166...])|ArrayT($166)|Quark<AnyT|NullT|VoidT|BoolT|IntT|RealT|StringT|VarT(^string)|NominalT(^string)>>>|NotT($143)|OrT(^{$143...})|AndT(^{$143...})|ArrayT($143)|TupleT(^[$143...])|FunctionT(^[$143,$143,$143...])>>,^{|$47,$47|}[$47,$47]])|Inequality(^[^AType<IntT|RealT>,$4])|Equation(^[^AType<IntT|RealT>,$4])|ForAll(^[^{^[^Var(^string),$143]...},^$131])|Exists(^[^{^[^Var(^string),$143]...},^$131])>>|SExpr<$42|Array(^[$47...])|ArrayGen(^[$47,$47])>>>...])|Load(^[$47,^int])|LengthOf($47)|IndexOf(^[$47,$47])>>>>>...|}[$4<^$21<AExpr<$13|Num(^real)|Mul($11)|Div(^[$4,$4])|$42<VExpr<Var(^string)|Fn(^[^string,$47<^Expr<$21|$94<Value<Num(^real)|Null|Tuple(^[^$94...])|Bool<True|False>|String(^string)|Array(^[^$94...])|ArrayGen(^[^$94,^$94])>>|Tuple(^[$47...])|$131<BExpr<$42|Bool<True|False>|And(^{^$131...})|Or(^{^$131...})|Not(^$131)|Equals(^[$143<^Type<Atom<NotT($166<^Proton<TupleT(^[$166...])|ArrayT($166)|Quark<AnyT|NullT|VoidT|BoolT|IntT|RealT|StringT|VarT(^string)|NominalT(^string)>>>)|Proton<TupleT(^[$166...])|ArrayT($166)|Quark<AnyT|NullT|VoidT|BoolT|IntT|RealT|StringT|VarT(^string)|NominalT(^string)>>>|NotT($143)|OrT(^{$143...})|AndT(^{$143...})|ArrayT($143)|TupleT(^[$143...])|FunctionT(^[$143,$143,$143...])>>,^{|$47,$47|}[$47,$47]])|Inequality(^[^AType<IntT|RealT>,$4])|Equation(^[^AType<IntT|RealT>,$4])|ForAll(^[^{^[^Var(^string),$143]...},^$131])|Exists(^[^{^[^Var(^string),$143]...},^$131])>>|SExpr<$42|Array(^[$47...])|ArrayGen(^[$47,$47])>>>...])|Load(^[$47,^int])|LengthOf($47)|IndexOf(^[$47,$47])>>>>>...]]>)>
	private static Type type20 = Runtime.Type("AIoBKShdmIec0K0K3Tk8b9UCXEfVnEeVo7wZo7ScJDAd1IYcIIgs3CDKMQooJSgG2GdO6KLK3Tk8MJE_qPtlNg0MYoIMhsp7Nl2AcCHLClXPYsYEYo0Qtoa9iCXLjl1ToNKNmGXGiG3Ij45O35BKaQbG6PEOLFE5U5sIuIQs6S8t5O_WrIa4mUwIQZNBmL95hgNcH5YcMY0AD53K3Tk8b9v5IoNBHaWaGDQ5ekOBmTS5gsOF_KWlLS_G4Kp06Q_G_F4W6Rm42yGaHjm5f5Ww4fl5h5JCKGs0bRWsPZCh0il7N5t5hcQFZIpl5QIkQkHj0G1xqQgGqJo8MPiSa9s6YZRkHD96egRBHe0n0AC6G_ajWnWX1Ym5E6J4ZRm4LTYZSkRkXq0WGFm8MNtSJOiCHmGml7SoSZYrW9U6YkSVTkHuG7Q6e6QgT31q0vl5h6YVPsTomv0GJ8MS_CGy0Au6JOJNgCMOIkUkHzG7v6y6QwUBmj0XHA89YVRoNkmXm7O5gZIYX9D9YZPwck1a1C0t5OZwZRosoQoGLGlKMNgCMNB599AACAEAfAQsdFPZZQ_4MSWlLPo_6WGGlKMNo_qQi4mbJfo5e9Wwdgeg0f1O5xaR0l5QZK3TdC6Sn4mmJno5s9WoeZfgWim7e5v9hkfcHjm7y9fwmjX97AYcdZgkXmm7Q98AgkgB1bXj1ADA3GKTkKa9yAXZOZOBH6PAsghc1rm7OASAYoWrHDUAeViBHbHu1AeA343Sjp5GDx5SJGnImG4G0t5OJGLFm8MNtG4OJK6RgK5KJ55KbQYGMPjt5KltsgyVzczkzZ7x7hlym7NAwAhojF5Jmx5Sjta9eDYoiVskHXI79DeDQgsB1v1YIACDJ4KSW8rPYVskHDNDeZtBHyXa2AQDYVjVskHbIBRDTDdEQwtBmz1eIAdD34ZQtGp3fDgkuF_Ipl5QJCWf2AjDJOpQdG5KIZvkXi2K1xqQgGp3wDgovFJHiG6KIwvk1m2KHKLNgGp39EggwFrJo8MPiS5KIowkXn2GL4aRJC1qIY0AOE35DxLQdtLNgGp7QEC5gkx3OouVvgvsvZwkwwwcxoxgWrn7EDUEhVyBHvHq1AeEYZhgmAgEeoyBXvXv2AjEYwisykHyn7sAOAggzBHq1AtozcXzn7tAzEgV7CHqHqm7OA9Htg7d1Yo7uACHgs7GKFJ_6R_dmeo7OHyBH6PHtg8d1bo7c9SHgs84Hm2nn5cHYV8_9pXeo7d9SHgk9dmYl7iHOAYolfJDsHeZACXio9jgAd1jo7xHy9YoWjJDzHeVBCXfHm3A9IYweZBl1nJBB5QIdIQsBCmflnJANIYZSwckXqo7O5O5Yo0rJDSIesCC1rlr3AcIegl7O5eIYoluJDgIeoDC1UiIgwDCHUO5gZEC1Xlr3AvIlDE");
	// ^$13<Mul($11<^[^real,^{|$4<^$21<AExpr<$13|Num(^real)|Sum($11)|Div(^[$4,$4])|$42<VExpr<Var(^string)|Fn(^[^string,$47<^Expr<$21|$94<Value<Num(^real)|Null|Tuple(^[^$94...])|Bool<True|False>|String(^string)|Array(^[^$94...])|ArrayGen(^[^$94,^$94])>>|Tuple(^[$47...])|$131<BExpr<$42|Bool<True|False>|And(^{^$131...})|Or(^{^$131...})|Not(^$131)|Equals(^[$143<^Type<Atom<NotT($166<^Proton<TupleT(^[$166...])|ArrayT($166)|Quark<AnyT|NullT|VoidT|BoolT|IntT|RealT|StringT|VarT(^string)|NominalT(^string)>>>)|Proton<TupleT(^[$166...])|ArrayT($166)|Quark<AnyT|NullT|VoidT|BoolT|IntT|RealT|StringT|VarT(^string)|NominalT(^string)>>>|NotT($143)|OrT(^{$143...})|AndT(^{$143...})|ArrayT($143)|TupleT(^[$143...])|FunctionT(^[$143,$143,$143...])>>,^{|$47,$47|}[$47,$47]])|Inequality(^[^AType<IntT|RealT>,$4])|Equation(^[^AType<IntT|RealT>,$4])|ForAll(^[^{^[^Var(^string),$143]...},^$131])|Exists(^[^{^[^Var(^string),$143]...},^$131])>>|SExpr<$42|Array(^[$47...])|ArrayGen(^[$47,$47])>>>...])|Load(^[$47,^int])|LengthOf($47)|IndexOf(^[$47,$47])>>>>>...|}[$4<^$21<AExpr<$13|Num(^real)|Sum($11)|Div(^[$4,$4])|$42<VExpr<Var(^string)|Fn(^[^string,$47<^Expr<$21|$94<Value<Num(^real)|Null|Tuple(^[^$94...])|Bool<True|False>|String(^string)|Array(^[^$94...])|ArrayGen(^[^$94,^$94])>>|Tuple(^[$47...])|$131<BExpr<$42|Bool<True|False>|And(^{^$131...})|Or(^{^$131...})|Not(^$131)|Equals(^[$143<^Type<Atom<NotT($166<^Proton<TupleT(^[$166...])|ArrayT($166)|Quark<AnyT|NullT|VoidT|BoolT|IntT|RealT|StringT|VarT(^string)|NominalT(^string)>>>)|Proton<TupleT(^[$166...])|ArrayT($166)|Quark<AnyT|NullT|VoidT|BoolT|IntT|RealT|StringT|VarT(^string)|NominalT(^string)>>>|NotT($143)|OrT(^{$143...})|AndT(^{$143...})|ArrayT($143)|TupleT(^[$143...])|FunctionT(^[$143,$143,$143...])>>,^{|$47,$47|}[$47,$47]])|Inequality(^[^AType<IntT|RealT>,$4])|Equation(^[^AType<IntT|RealT>,$4])|ForAll(^[^{^[^Var(^string),$143]...},^$131])|Exists(^[^{^[^Var(^string),$143]...},^$131])>>|SExpr<$42|Array(^[$47...])|ArrayGen(^[$47,$47])>>>...])|Load(^[$47,^int])|LengthOf($47)|IndexOf(^[$47,$47])>>>>>...]]>)>
	private static Type type21 = Runtime.Type("AIooJSgdmIec0K0K3Tk8b9UCXEfVnEeVo7wZo7ScJDAd1IYcIIgs3CDKMQoBKShG2GdO6KLK3Tk8MJE_qPtlNg0MYoIMhsp7Nl2AcCHLClXPYsYEYo0Qtoa9iCXLjl1ToNKNmGXGiG3Ij45O35BKaQbG6PEOLFE5U5sIuIQs6S8t5O_WrIa4mUwIQZNBmL95hgNcH5YcMY0AD53K3Tk8b9v5IoNBHaWaGDQ5ekOBmTS5gsOF_KWlLS_G4Kp06Q_G_F4W6Rm42yGaHjm5f5Ww4fl5h5JCKGs0bRWsPZCh0il7N5t5hcQFZIpl5QIkQkHj0G1xqQgGqJo8MPiSa9s6YZRkHD96egRBHe0n0AC6G_ajWnWX1Ym5E6J4ZRm4LTYZSkRkXq0WGFm8MNtSJOiCHmGml7SoSZYrW9U6YkSVTkHuG7Q6e6QgT31q0vl5h6YVPsTomv0GJ8MS_CGy0Au6JOJNgCMOIkUkHzG7v6y6QwUBmj0XHA89YVRoNkmXm7O5gZIYX9D9YZPwck1a1C0t5OZwZRosoQoGLGlKMNgCMNB599AACAEAfAQsdFPZZQ_4MSWlLPo_6WGGlKMNo_qQi4mbJfo5e9Wwdgeg0f1O5xaR0l5QZK3TdC6Sn4mmJno5s9WoeZfgWim7e5v9hkfcHjm7y9fwmjX97AYcdZgkXmm7Q98AgkgB1bXj1ADA3GKTkKa9yAXZOZOBH6PAsghc1rm7OASAYoWrHDUAeViBHbHu1AeA343Sjp5GDx5SJGnImG4G0t5OJGLFm8MNtG4OJK6RgK5KJ55KbQYGMPjt5KltsgyVzczkzZ7x7hlym7NAwAhojF5Jmx5Sjta9eDYoiVskHXI79DeDQgsB1v1YIACDJ4KSW8rPYVskHDNDeZtBHyXa2AQDYVjVskHbIBRDTDdEQwtBmz1eIAdD34ZQtGp3fDgkuF_Ipl5QJCWf2AjDJOpQdG5KIZvkXi2K1xqQgGp3wDgovFJHiG6KIwvk1m2KHKLNgGp39EggwFrJo8MPiS5KIowkXn2GL4aRJC1qIY0AOE35DxLQdtLNgGp7QEC5gkx3OouVvgvsvZwkwwwcxoxgWrn7EDUEhVyBHvHq1AeEYZhgmAgEeoyBXvXv2AjEYwisykHyn7sAOAggzBHq1AtozcXzn7tAzEgV7CHqHqm7OA9Htg7d1Yo7uACHgs7GKFJ_6R_dmeo7OHyBH6PHtg8d1bo7c9SHgs84Hm2nn5cHYV8_9pXeo7d9SHgk9dmYl7iHOAYolfJDsHeZACXio9jgAd1jo7xHy9YoWjJDzHeVBCXfHm3A9IYweZBl1nJBB5QIdIQsBCmflnJANIYZSwckXqo7O5O5Yo0rJDSIesCC1rlr3AcIegl7O5eIYoluJDgIeoDC1UiIgwDCHUO5gZEC1Xlr3AvIlDE");
	// AType<IntT|RealT>
	private static Type type22 = Runtime.Type("QFKFJ_6R_GJHiG6KIg2AwF_J_45QJCWEgwI7xVo58CXD9pmH0IE");
	// $12<Mul($10<^[^real,^{|$3<^$20<AExpr<$12|Num(^real)|Sum($10)|Div(^[$3,$3])|$41<VExpr<Var(^string)|Fn(^[^string,$46<^Expr<$20|$93<Value<Num(^real)|Null|Tuple(^[^$93...])|Bool<True|False>|String(^string)|Array(^[^$93...])|ArrayGen(^[^$93,^$93])>>|Tuple(^[$46...])|$130<BExpr<$41|Bool<True|False>|And(^{^$130...})|Or(^{^$130...})|Not(^$130)|Equals(^[$142<^Type<Atom<NotT($165<^Proton<TupleT(^[$165...])|ArrayT($165)|Quark<AnyT|NullT|VoidT|BoolT|IntT|RealT|StringT|VarT(^string)|NominalT(^string)>>>)|Proton<TupleT(^[$165...])|ArrayT($165)|Quark<AnyT|NullT|VoidT|BoolT|IntT|RealT|StringT|VarT(^string)|NominalT(^string)>>>|NotT($142)|OrT(^{$142...})|AndT(^{$142...})|ArrayT($142)|TupleT(^[$142...])|FunctionT(^[$142,$142,$142...])>>,^{|$46,$46|}[$46,$46]])|Inequality(^[^AType<IntT|RealT>,$3])|Equation(^[^AType<IntT|RealT>,$3])|ForAll(^[^{^[^Var(^string),$142]...},^$130])|Exists(^[^{^[^Var(^string),$142]...},^$130])>>|SExpr<$41|Array(^[$46...])|ArrayGen(^[$46,$46])>>>...])|Load(^[$46,^int])|LengthOf($46)|IndexOf(^[$46,$46])>>>>>...|}[$3<^$20<AExpr<$12|Num(^real)|Sum($10)|Div(^[$3,$3])|$41<VExpr<Var(^string)|Fn(^[^string,$46<^Expr<$20|$93<Value<Num(^real)|Null|Tuple(^[^$93...])|Bool<True|False>|String(^string)|Array(^[^$93...])|ArrayGen(^[^$93,^$93])>>|Tuple(^[$46...])|$130<BExpr<$41|Bool<True|False>|And(^{^$130...})|Or(^{^$130...})|Not(^$130)|Equals(^[$142<^Type<Atom<NotT($165<^Proton<TupleT(^[$165...])|ArrayT($165)|Quark<AnyT|NullT|VoidT|BoolT|IntT|RealT|StringT|VarT(^string)|NominalT(^string)>>>)|Proton<TupleT(^[$165...])|ArrayT($165)|Quark<AnyT|NullT|VoidT|BoolT|IntT|RealT|StringT|VarT(^string)|NominalT(^string)>>>|NotT($142)|OrT(^{$142...})|AndT(^{$142...})|ArrayT($142)|TupleT(^[$142...])|FunctionT(^[$142,$142,$142...])>>,^{|$46,$46|}[$46,$46]])|Inequality(^[^AType<IntT|RealT>,$3])|Equation(^[^AType<IntT|RealT>,$3])|ForAll(^[^{^[^Var(^string),$142]...},^$130])|Exists(^[^{^[^Var(^string),$142]...},^$130])>>|SExpr<$41|Array(^[$46...])|ArrayGen(^[$46,$46])>>>...])|Load(^[$46,^int])|LengthOf($46)|IndexOf(^[$46,$46])>>>>>...]]>)>
	private static Type type23 = Runtime.Type("9IooJSgdX5J4JGs0bResp7xg1DycmEYg2HYoGHtcZ9ACXDBlHIosJShGnJpp5C3_aSJOKGs0bRGt3PeWrXl5QC1ERpHMYwoDgwp7Nl3AdCHExBH6f_2Qeoq7Ot5AjGYKW8685t5GBxLNZGNkJOiS5ScxZO0tNsOwD_EhGUo_ZQZK5TEOL7yhEh0Xl7P_NoXXW9OBHTB5goNFJGs0bRecQB0Yl7N5O5tcOcmal7ulOkHb0KL45QpK5KJK6RgK5K1K3Tk8MBj6N9w9QcP3XMf5QkPFpJ4W6Rm4Hf0qo5j5YwNVQoHi0GDK6QgCli0Aw538oQjl5OIGbRdtqOewTB1m0AtZRcXml7c5A6gkR34Px5C689A9QsRFKFm8MNtC1qlm0AO63508bRW_rG_tq77676Yo0rGDS6esSBmqlr0Ac6WcSZTgWuG7E6f6QkTBmbGvGAi63G_RpKq3s6gZUF_GWlqR_Cly0Aw6WcUoUgWzl7y5z6hVcBmj0Y0A99YVOkHDB9eocB1eWY1AE9o3ZQZGmImGYIjG6O44MSWlqRWhNZccgkgsgcigGb1dGHiKLRp45QdGMT3544MSWGMPjtL7THgHQZe3XbXem5f9ZOoQm43QgGLGs_qRoCM79IBIQwe31f1im5t9YZPcfomiX9w9YofgmAy9ewfBHa1m1A8AYcdVgkmmm7Q9x9gogF3Kt0MOeoj71a0al7SZhVYqX9QAYVhkhBH6SAtshcmrm7R9cAgZiFJFoxLQ3toQoG4CE86K34ZQZG4O08bRW_6KZGKSklLOJGONJSiC5SdxaQJ4MYYunvIyny2XZYo5uAYwggjo1z1OF8rQoxaQeZuB1vmz1A7DWZsZugWXn7fAADhksFKJp4aRfCmz1Atwsc1an7sAODgctBmvmz1ARDlgtotVygWbn7yAUDhVuFJFi_6KIcukme2KDK6QgGp3hDgsuF_Kj_5OJC0i2AtDJ8oQjl5KIgvk1j2G8t5SJCWj2AzDJ8KOWl5KIZwkXm2SIGbRdtqOJC0n2ACE3OKNmGp7EEB5gVxFNsoQh_aQWl5KYcxkNkmqIZ0fnfYiIj2mnmYnIq2rn5SEYsssxomrn7gANAgZyB1qm9jgyc1vn7hAhEgsyBXvHv2AsEYwiVhkXyn7NAgZ2zY9xEYVjszkmzn7NANAYVhZ7_YXZ9AHYZjk7lHY3K0GKTkKa9eHYV8pn7SZ8_YaZ9QHYwdk8lHbJ77EAEQw8CmY3eJAdHYVek8lmeZ9D5Yo9WhBH6iHtw9d1io7tHfwXiZ9vHYkApfBH6xHtsAdmjo7h97IgZBCXf1m3AAIlgNcCWDhGno7i5DIhwBC1qWY1AOIYVOVOBH6QItkCdHro7Q6TIgwCdm5YVOZDCH6eItgDd1vo7vpDlXvo7wWOk1yo7ztClXyJs3");
	// IntT
	private static Type type24 = Runtime.Type("2G8t5SJCWDggIk2");
	// RealT
	private static Type type25 = Runtime.Type("2KHKLNgGp3ukmD0E");
	// $7<Array($5<^[$2<^Expr<$49<Value<Null|Tuple(^[^$49...])|Bool<True|False>|Num(^real)|String(^string)|Array(^[^$49...])|ArrayGen(^[^$49,^$49])>>|Tuple($5)|$88<BExpr<Bool<True|False>|VExpr<Var(^string)|Fn(^[^string,$2...])|Load(^[$2,^int])|LengthOf($2)|IndexOf(^[$2,$2])>|And(^{^$88...})|Or(^{^$88...})|Not(^$88)|Equals(^[$134<^Type<Atom<NotT($157<^Proton<TupleT(^[$157...])|ArrayT($157)|Quark<AnyT|NullT|VoidT|BoolT|IntT|RealT|StringT|VarT(^string)|NominalT(^string)>>>)|Proton<TupleT(^[$157...])|ArrayT($157)|Quark<AnyT|NullT|VoidT|BoolT|IntT|RealT|StringT|VarT(^string)|NominalT(^string)>>>|NotT($134)|OrT(^{$134...})|AndT(^{$134...})|ArrayT($134)|TupleT(^[$134...])|FunctionT(^[$134,$134,$134...])>>,^{|$2,$2|}[$2,$2]])|Inequality(^[^AType<IntT|RealT>,$231<^AExpr<Num(^real)|VExpr<Var(^string)|Fn(^[^string,$2...])|Load(^[$2,^int])|LengthOf($2)|IndexOf(^[$2,$2])>|Sum(^[^real,^{|$231...|}[$231...]])|Mul(^[^real,^{|$231...|}[$231...]])|Div(^[$231,$231])>>])|Equation(^[^AType<IntT|RealT>,$231])|ForAll(^[^{^[^Var(^string),$134]...},^$88])|Exists(^[^{^[^Var(^string),$134]...},^$88])>>|AExpr<Num(^real)|VExpr<Var(^string)|Fn(^[^string,$2...])|Load(^[$2,^int])|LengthOf($2)|IndexOf(^[$2,$2])>|Sum(^[^real,^{|$231...|}[$231...]])|Mul(^[^real,^{|$231...|}[$231...]])|Div(^[$231,$231])>|SExpr<$7|VExpr<Var(^string)|Fn(^[^string,$2...])|Load(^[$2,^int])|LengthOf($2)|IndexOf(^[$2,$2])>|ArrayGen(^[$2,$2])>>>...]>)>
	private static Type type26 = Runtime.Type("9IJ4ZRm4LT3K3Tk8b9TC1EgZIEesn7uw2A7G_KWlLS_G4Kp06Q_G_F4W6Rm4naGjWul5CGKF4W6Rm4XIeHQV4KIK3Tk8M7O_EhlLYg2Mho4GDK6QgClMgV5G1xqQgGYIpp5OIGbRdtqOegOBHQgZYQewq7AW6At4KPupPVQgQglTYc2Tgo6WGFm8MNtSJOiCHQhCH675tZNcXXl7zhNk1YG7ypNgWYG7wxNg0al79_OoXa0GJ8MS_C0b0AS5JOJNgCMOIwOk1eG7T5d5QcPBXPf5hkPcX5Ygaf0Aj5eZl7g_QkXil7Ax2Aw5JOKGs0bRo3ZQZGmImGYIjG6O44MSWlqRWpPoUcfkfsfchglm0dGHiKLRp45QdGMT3544MSWGMPjtL7EHCIQwR31n0ql5O6ZOoQm43QgGLGs_qRoCM7fIhIQoS3XqWrl5U6Yk3uGAd6oNKNmGXGiG3Ij45O35BKaQbG6PEOLFz6C9R9T9QwTFMHiGLOsxZOWVUkegWyl7y5v6hkUBmuGi0Ay6IZQB1E79tZccXXm7g6A9gkccm5YkYYm7SwcZ2aX9O9YoTcdkmam7i6wkHbm7wkn7SwdZ2eX9d9YZUcekmeX9e6YoegmAi9eweBmj0i1At9YVRVfkmim786h9gofF3Kt0MOeoi71EwBH68Ascgcmmm77ABAYoGnHDDAewgBXm0q1AOA343Sjp5GDx5SJGnImG4G0t5OJGLFm8MNtG4OJK6RgK5KJ55KbQYGMPjt5KlpjcxwxZygyVzszgWum7z9fAhkiF5Jmx5Sjta9ODYkhwik1yH7tAODQcjBmqmyHAwAJ4KSW8rPYwikHDzAeVsB1uHX2A9DYwhwik1YIBADCDNEQssBXvmYIAND34ZQtGp3PDggtF_Ipl5QJCGb2ATDJOpQdG5KIVukHe2K1xqQgGp3fDgkuFJHiG6KIsukmf2KHKLNgGp3tDgcvFrJo8MPiS5KIkvkHj2GL4aRJCmjIi0A7E35DxLQdtLNgGp79Et5ggw3OktwtcuouVvgvsvZwkwgGnn7yADEhwwB1r1m1AOEYVggmAQEekxBHrHr2ATEYshoxk1un7UA7AgcyB1m1AtkycHvn7cAiEgwyB1m1mm77AtEtczcmyn7dAwEgozFKFJ_6R_dmaZ9eHYV7_7CH69Htg7d1Yo7C6CHgs741inin5NHYwzZ8pXa3CIKMQooJSgG2GdOMJs5x6vHxHAIQw8CmIcHhZ9CHXo9sg9d1fo7i5hHYoWfJDjHeVAC1bJi3AuHYo8_Al1jo78H8HYoWjJDzHeVBCXbJm3A9IYsRo7l1nZ9z6YsBWgBH6EItVCdHqo7PIfwmqZ9RIYoCpeBH6TItwCd1uo7Q6dIgcDC1rGu3AgIlZJzlyo5iIYcpvJAsIYwbe1AuIGHE");
	// $8<ArrayGen($6<^[$2<^Expr<$50<Value<Null|Tuple(^[^$50...])|Bool<True|False>|Num(^real)|String(^string)|Array(^[^$50...])|ArrayGen(^[^$50,^$50])>>|Tuple(^[$2...])|$92<BExpr<Bool<True|False>|VExpr<Var(^string)|Fn(^[^string,$2...])|Load(^[$2,^int])|LengthOf($2)|IndexOf($6)>|And(^{^$92...})|Or(^{^$92...})|Not(^$92)|Equals(^[$134<^Type<Atom<NotT($157<^Proton<TupleT(^[$157...])|ArrayT($157)|Quark<AnyT|NullT|VoidT|BoolT|IntT|RealT|StringT|VarT(^string)|NominalT(^string)>>>)|Proton<TupleT(^[$157...])|ArrayT($157)|Quark<AnyT|NullT|VoidT|BoolT|IntT|RealT|StringT|VarT(^string)|NominalT(^string)>>>|NotT($134)|OrT(^{$134...})|AndT(^{$134...})|ArrayT($134)|TupleT(^[$134...])|FunctionT(^[$134,$134,$134...])>>,^{|$2,$2|}[$2,$2]])|Inequality(^[^AType<IntT|RealT>,$231<^AExpr<Num(^real)|VExpr<Var(^string)|Fn(^[^string,$2...])|Load(^[$2,^int])|LengthOf($2)|IndexOf($6)>|Sum(^[^real,^{|$231...|}[$231...]])|Mul(^[^real,^{|$231...|}[$231...]])|Div(^[$231,$231])>>])|Equation(^[^AType<IntT|RealT>,$231])|ForAll(^[^{^[^Var(^string),$134]...},^$92])|Exists(^[^{^[^Var(^string),$134]...},^$92])>>|AExpr<Num(^real)|VExpr<Var(^string)|Fn(^[^string,$2...])|Load(^[$2,^int])|LengthOf($2)|IndexOf($6)>|Sum(^[^real,^{|$231...|}[$231...]])|Mul(^[^real,^{|$231...|}[$231...]])|Div(^[$231,$231])>|SExpr<$8|VExpr<Var(^string)|Fn(^[^string,$2...])|Load(^[$2,^int])|LengthOf($2)|IndexOf($6)>|Array(^[$2...])>>>,$2]>)>
	private static Type type27 = Runtime.Type("9I3508bRW_rG_t5G4W6RmdmMYk2EYoGEtsY9zBXD7lHHJOKNgKMOJGKSklLOJ8JGs0bRlkOZRsTgWIJ4JGs0bRWwZeo5OGpJ4W6Rm4XLtIQkp7voKATGZIpl5QIV5AdGZFjx5QosJShGqJo8MPiSa9R5Ys5Atwa9sC1ItlXTGdqTi5t5w5Qk6K08bRW_r7y_6AzCXQiCH685tcNcmXl7ukNkHYG775D5QwN3HUN5QZOBmHP5hgOF3KmKMOIoOkXb0K545QnKq3c5gZP3mbWel5f5Yg5fGAh5ecl7gxPk1iW9OBHQu5ggQB1EgZIjW9y5Ykoj0A76JOKGs0bRo3ZQZGmImGYIjG6O44MSWlqRWtPZccfkfsfchgln0dGHiKLRp45QdGMT3544MSWGMPjtL7EHCIQgS31q0rl5S6ZOoQm43QgGLGs_qRoCM7fIhIQZT3XrWul5f6Yo3vGAh6oNKNmGXGiG3Ij45O35BKaQbG6PEOLFA9O9c9e9QgUFMHiGLOsxZOWkUkegWzl796z6hVcBmvWi0A99IcQB1EB9toccXYm7s6E9gVdcm5YkYam7SgdZ2bX9S9YZUsdkmbm7u6wkHem7x67lmeX9i6YoegmAi9eweBmm0i1At9YkRVfkmim7C6h9gofF3Kt0MOeoi71EwBH68Ascgcmmm77ABAYoGnHDDAewgBXn0q1AOA343Sjp5GDx5SJGnImG4G0t5OJGLFm8MNtG4OJK6RgK5KJ55KbQYGMPjt5KlpjcxwxZygyVzszgWum7z9fAhkiF5Jmx5Sjta9ODYkhwik1yH7tAODQcjBmqmyHAwAJ4KSW8rPYwikHDzAeVsB1uHX2A9DYwhwik1YIBADCDNEQssBXvmYIAND34ZQtGp3PDggtF_Ipl5QJCGb2ATDJOpQdG5KIVukHe2K1xqQgGp3fDgkuFJHiG6KIsukmf2KHKLNgGp3tDgcvFrJo8MPiS5KIkvkHj2GL4aRJCmjYi0A7E35DxLQdtLNgGp79Eu5ggw3OktwtcuouVvgvsvZwkwgGnn7yADEhwwB1r1m1AOEYVggmAQEekxBHrHr2ATEYshoxk1un7UA7AgcyB1m1AtkycHvn7cAiEgwyB1m1mm77AtEtczcmyn7dAwEgozFKFJ_6R_dmaZ9eHYV7_7CH69Htg7d1Yo7O6CHgs741inin5NHYwzZ8pXa3CIKMQooJSgG2GdOMJt589vHxHAIQw8C1LcHhZ9CHXo9sg9d1fo7j5hHYoWfJDjHeVAC1bJi3AuHYo8_Al1jo78H8HYoWjJDzHeVBCXbJm3A9IYcSo7l1nZ9A9YsBWgBH6EItVCdHqo7PIfwmqZ9RIYoCpeBH6TItwCd1uo7U6dIgcDC1uGu3AgIlcJXmyo5iIYgpvJAsIYsrj0AuIWHE");
	// Var(^string)
	private static Type type28 = Runtime.Type("3CL4aReZl7ug2Aw3x$");
	// ^Bool<True|False>
	private static Type type29 = Runtime.Type("RFZFjx5Qeo3GJ8MS_C0Ego2K545QnKq3zk1HWsIHQco7ugJAB4vw");
	// ^$20<ForAll($18<^[^{^[^Var(^string),$5<^Type<Atom<NotT($36<^Proton<TupleT(^[$36...])|ArrayT($36)|Quark<AnyT|NullT|VoidT|BoolT|IntT|RealT|StringT|VarT(^string)|NominalT(^string)>>>)|Proton<TupleT(^[$36...])|ArrayT($36)|Quark<AnyT|NullT|VoidT|BoolT|IntT|RealT|StringT|VarT(^string)|NominalT(^string)>>>|NotT($5)|OrT(^{$5...})|AndT(^{$5...})|ArrayT($5)|TupleT(^[$5...])|FunctionT(^[$5,$5,$5...])>>]...},$14<^$128<BExpr<$138<VExpr<Var(^string)|Fn(^[^string,$140<^Expr<$128|$187<Value<Null|Tuple(^[^$187...])|Bool<True|False>|Num(^real)|String(^string)|Array(^[^$187...])|ArrayGen(^[^$187,^$187])>>|Tuple(^[$140...])|$214<AExpr<$138|Num(^real)|Sum(^[^real,^{|^$214...|}[^$214...]])|Mul(^[^real,^{|^$214...|}[^$214...]])|Div(^[^$214,^$214])>>|SExpr<$138|Array(^[$140...])|ArrayGen(^[$140,$140])>>>...])|Load(^[$140,^int])|LengthOf($140)|IndexOf(^[$140,$140])>>|Bool<True|False>|And(^{$14...})|Or(^{$14...})|Not($14)|Equals(^[$5,^{|$140,$140|}[$140,$140]])|Inequality(^[^AType<IntT|RealT>,^$214])|Equation(^[^AType<IntT|RealT>,^$214])|$20|Exists($18)>>>]>)>
	private static Type type30 = Runtime.Type("AIZOoQm43QgdXMoNKNmdHP3GKTkKa9wCHEzBH67_IHeco7AhmABdHIJ8JGs0bRecfBXINCH6O_YLegp7uk4ASdH5YknMgV5G0GrQhGZIjG6KowZRJGJFiG5KZ4ZRm4LTJG5Kp06Q_G4_WGptqNo_qQiGKRB5d6i6s6u6z6C9QZr7ycMAvG5Jmx5Sjta9c5YgaUgwM775c5QZNBXP95hgNFKJp4aRfCXUgZYYW9E5Yw5a0AO5YsaUggO3Ya0blrl5S5YobbGAU534ZQtGp3d5gcPF_Ipl5QJC0f0Ah5JOpQdG5KIwPk1i0K1xqQgGp3u5ggQFJHiG6KIoQkXj0KHKLNgGp376gZRFrJo8MPiS5KIgRk1n0GL4aRJCXnlMgwRFNsoQh_aQWl5KYZSw4AP6G5f5i5t5w5z596C6N6Q6QkSBHYGrGAT6YgqEgVTBmEfwXuW9f6Yk5v0Ah6Yo5v0Aj6YsqEgZUBmEgZnyW9w6YwLz0Ay6YwnEYw2XHD89eccB1TA9gkcF_K4W6RmGZFjx5Qo3ZQZGmImGYIjG6O44MSWlqRWlgwvsAWBdBlCh0b1dGHiKLRp45QdGMT3544MSWGMPjtL7gIuIQVe3HbHem5e9ZK3TdC6Sn4XMwIQoe3meXfm5j9Yw3iHAt9ZNZQ3loQWG5W0I_tqOoWqIa4JPRAhHjHQsfFMHiGLOsxZOWwfZAhGmm7D99AhggFJGs0bReVjBlMYsgwgZ2qX9OAYgfchkmq1KL45QpK5KJK6RgKLBu9hDOEQwhFKF4W6Rm41u1un5eAJCKGs0bRWgis7hGvm7CAiAhwiFZIpl5QIZjkXy1CDKMQZC4Sm_aQbdHfn7yAgZnzX97DYshZskXXIJvAADzD9EBEQksFKFm8MNtCXYIX2AED3508bRW_rG_tq7yAyAYoWaIDQDektBHaIb2ATDWVtwtg0eI7CDdDQcuBHrmeIAgD3G_RpKq3iDgwuF_GWlqR_CGi2AuDWVvgvg0jn7E9xDhsvcX5YkjVwkHmn7xAUlmmn7DAgZInY9DEYshwwk1q2CIKMQooJSgG2GdOMJBA9EuEwE9HQoxBHuXrIAUEeVyBHun9scycmun77EgEYoGvIDiEewyBXq2y2AtEYgxVzkmyn7dEdEYoGzIDyEewzB1r2X3A8HlkgV8t8hlXo7gABHho7CXYnn2AEHYsgsgBH6OHtc8dmao7ODRHgo8dm5Ysgw8CH6cHtZ9dXeo7w9fHgk9CHjXn1AiHYVgk8l1io7NhmAuHegAC1a1j3AxHYZdkAlmjo7P9NlHmZ7DADAYolm3DBIeoBCmEDIYolnJDNIeZCCmaXq3AQIJ43Kt0MOeVECXrJun7SwC_2uZ9dIYsdcDlmuJ7z596QoDCHrZvJAjIYwdcDlHyo7g9RlmyJgn2");

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
	private final static Pattern.Term pattern31 = new Pattern.Term("Load",
		new Pattern.List(false, new Pair[]{
			new Pair(new Pattern.Term("Tuple",
				new Pattern.List(true, new Pair[]{
					new Pair(new Pattern.Leaf(type6), "ls")}),
				null),null), 
			new Pair(new Pattern.Leaf(type7), "idx")}),
		null);
	private final static Pattern.Term pattern32 = new Pattern.Term("LengthOf",
		new Pattern.Term("Tuple",
			new Pattern.List(true, new Pair[]{
				new Pair(new Pattern.Leaf(type6), "xs")}),
			null),
		null);
	private final static Pattern.Term pattern33 = new Pattern.Term("Equals",
		new Pattern.List(false, new Pair[]{
			new Pair(new Pattern.Term("TupleT",
				new Pattern.List(true, new Pair[]{
					new Pair(new Pattern.Leaf(type2), "ts")}),
				null),null), 
			new Pair(new Pattern.Bag(false, new Pair[]{
				new Pair(new Pattern.Term("Tuple",
					new Pattern.List(true, new Pair[]{
						new Pair(new Pattern.Leaf(type6), "xs")}),
					null),null), 
				new Pair(new Pattern.Term("Tuple",
					new Pattern.List(true, new Pair[]{
						new Pair(new Pattern.Leaf(type6), "ys")}),
					null),null)}),null)}),
		null);
	private final static Pattern.Term pattern34 = new Pattern.Term("And",
		new Pattern.Set(true, new Pair[]{
			new Pair(new Pattern.Term("Equals",
				new Pattern.List(false, new Pair[]{
					new Pair(new Pattern.Leaf(type2), "t"), 
					new Pair(new Pattern.Bag(false, new Pair[]{
						new Pair(new Pattern.Leaf(type8), "x"), 
						new Pair(new Pattern.Leaf(type9), "y")}),null)}),
				null), "eq"), 
			new Pair(new Pattern.Leaf(type10), "bs")}),
		null);
	private final static Pattern.Term pattern35 = new Pattern.Term("Not",
		new Pattern.Leaf(type11),
		"b");
	private final static Pattern.Term pattern36 = new Pattern.Term("Not",
		new Pattern.Term("Not",
			new Pattern.Leaf(type12),
			"x"),
		null);
	private final static Pattern.Term pattern37 = new Pattern.Term("Not",
		new Pattern.Term("And",
			new Pattern.Set(true, new Pair[]{
				new Pair(new Pattern.Leaf(type10), "xs")}),
			null),
		null);
	private final static Pattern.Term pattern38 = new Pattern.Term("Not",
		new Pattern.Term("Or",
			new Pattern.Set(true, new Pair[]{
				new Pair(new Pattern.Leaf(type10), "xs")}),
			null),
		null);
	private final static Pattern.Term pattern39 = new Pattern.Term("And",
		new Pattern.Set(false, new Pair[]{
			new Pair(new Pattern.Leaf(type10), "x")}),
		null);
	private final static Pattern.Term pattern40 = new Pattern.Term("And",
		new Pattern.Set(true, new Pair[]{
			new Pair(new Pattern.Leaf(type13),null), 
			new Pair(new Pattern.Leaf(type10), "xs")}),
		null);
	private final static Pattern.Term pattern41 = new Pattern.Term("And",
		new Pattern.Set(true, new Pair[]{
			new Pair(new Pattern.Leaf(type14),null), 
			new Pair(new Pattern.Leaf(type10), "xs")}),
		null);
	private final static Pattern.Term pattern42 = new Pattern.Term("And",
		new Pattern.Set(true, new Pair[]{
			new Pair(new Pattern.Term("And",
				new Pattern.Set(true, new Pair[]{
					new Pair(new Pattern.Leaf(type10), "xs")}),
				null),null), 
			new Pair(new Pattern.Leaf(type10), "ys")}),
		null);
	private final static Pattern.Term pattern43 = new Pattern.Term("And",
		new Pattern.Set(true, new Pair[]{
			new Pair(new Pattern.Term("Not",
				new Pattern.Leaf(type10),
				"x"),null), 
			new Pair(new Pattern.Leaf(type10), "y"), 
			new Pair(new Pattern.Leaf(type10), "ys")}),
		null);
	private final static Pattern.Term pattern44 = new Pattern.Term("And",
		new Pattern.Set(true, new Pair[]{
			new Pair(new Pattern.Term("Or",
				new Pattern.Set(true, new Pair[]{
					new Pair(new Pattern.Leaf(type10), "xs")}),
				null),null), 
			new Pair(new Pattern.Leaf(type10), "ys")}),
		null);
	private final static Pattern.Term pattern45 = new Pattern.Term("Or",
		new Pattern.Set(false, new Pair[]{
			new Pair(new Pattern.Leaf(type10), "x")}),
		null);
	private final static Pattern.Term pattern46 = new Pattern.Term("Or",
		new Pattern.Set(true, new Pair[]{
			new Pair(new Pattern.Leaf(type14),null), 
			new Pair(new Pattern.Leaf(type10), "xs")}),
		null);
	private final static Pattern.Term pattern47 = new Pattern.Term("Or",
		new Pattern.Set(true, new Pair[]{
			new Pair(new Pattern.Leaf(type13),null), 
			new Pair(new Pattern.Leaf(type10), "xs")}),
		null);
	private final static Pattern.Term pattern48 = new Pattern.Term("Or",
		new Pattern.Set(true, new Pair[]{
			new Pair(new Pattern.Term("Not",
				new Pattern.Leaf(type10),
				"x"),null), 
			new Pair(new Pattern.Leaf(type10), "y"), 
			new Pair(new Pattern.Leaf(type10), "ys")}),
		null);
	private final static Pattern.Term pattern49 = new Pattern.Term("Or",
		new Pattern.Set(true, new Pair[]{
			new Pair(new Pattern.Term("Or",
				new Pattern.Set(true, new Pair[]{
					new Pair(new Pattern.Leaf(type10), "xs")}),
				null),null), 
			new Pair(new Pattern.Leaf(type10), "ys")}),
		null);
	private final static Pattern.Term pattern50 = new Pattern.Term("Equals",
		new Pattern.List(false, new Pair[]{
			new Pair(new Pattern.Leaf(type2), "t"), 
			new Pair(new Pattern.Bag(false, new Pair[]{
				new Pair(new Pattern.Leaf(type6), "x"), 
				new Pair(new Pattern.Leaf(type6), "y")}),null)}),
		null);
	private final static Pattern.Term pattern51 = new Pattern.Term("Equals",
		new Pattern.List(false, new Pair[]{
			new Pair(new Pattern.Leaf(type2), "t"), 
			new Pair(new Pattern.Bag(false, new Pair[]{
				new Pair(new Pattern.Leaf(type15), "x"), 
				new Pair(new Pattern.Leaf(type15), "y")}),null)}),
		null);
	private final static Pattern.Term pattern52 = new Pattern.Term("And",
		new Pattern.Set(true, new Pair[]{
			new Pair(new Pattern.Term("Equals",
				new Pattern.List(false, new Pair[]{
					new Pair(new Pattern.Leaf(type2), "t"), 
					new Pair(new Pattern.Bag(false, new Pair[]{
						new Pair(new Pattern.Leaf(type8), "x"), 
						new Pair(new Pattern.Leaf(type15), "y")}),null)}),
				null), "eq"), 
			new Pair(new Pattern.Leaf(type10), "bs")}),
		null);
	private final static Pattern.Term pattern53 = new Pattern.Term("And",
		new Pattern.Set(true, new Pair[]{
			new Pair(new Pattern.Term("Equals",
				new Pattern.List(false, new Pair[]{
					new Pair(new Pattern.Leaf(type2), "t"), 
					new Pair(new Pattern.Bag(false, new Pair[]{
						new Pair(new Pattern.Leaf(type8),null), 
						new Pair(new Pattern.Leaf(type8),null)}), "vs")}),
				null), "eq"), 
			new Pair(new Pattern.Leaf(type10), "bs")}),
		null);
	private final static Pattern.Term pattern54 = new Pattern.Term("Mul",
		new Pattern.List(false, new Pair[]{
			new Pair(new Pattern.Leaf(type16), "n"), 
			new Pair(new Pattern.Bag(true, new Pair[]{
				new Pair(new Pattern.Leaf(type17), "rest")}),null)}),
		null);
	private final static Pattern.Term pattern55 = new Pattern.Term("Mul",
		new Pattern.List(false, new Pair[]{
			new Pair(new Pattern.Leaf(type16), "x"), 
			new Pair(new Pattern.Bag(true, new Pair[]{
				new Pair(new Pattern.Term("Num",
					new Pattern.Leaf(type16),
					"y"),null), 
				new Pair(new Pattern.Leaf(type17), "rest")}),null)}),
		null);
	private final static Pattern.Term pattern56 = new Pattern.Term("Mul",
		new Pattern.List(false, new Pair[]{
			new Pair(new Pattern.Leaf(type16), "n1"), 
			new Pair(new Pattern.Bag(true, new Pair[]{
				new Pair(new Pattern.Term("Mul",
					new Pattern.List(false, new Pair[]{
						new Pair(new Pattern.Leaf(type16), "n2"), 
						new Pair(new Pattern.Bag(true, new Pair[]{
							new Pair(new Pattern.Leaf(type17), "xs")}),null)}),
					null),null), 
				new Pair(new Pattern.Leaf(type17), "ys")}),null)}),
		null);
	private final static Pattern.Term pattern57 = new Pattern.Term("Mul",
		new Pattern.List(false, new Pair[]{
			new Pair(new Pattern.Leaf(type16), "n1"), 
			new Pair(new Pattern.Bag(true, new Pair[]{
				new Pair(new Pattern.Term("Sum",
					new Pattern.List(false, new Pair[]{
						new Pair(new Pattern.Leaf(type16), "n2"), 
						new Pair(new Pattern.Bag(true, new Pair[]{
							new Pair(new Pattern.Leaf(type17), "xs")}),null)}),
					null),null), 
				new Pair(new Pattern.Leaf(type17), "ys")}),null)}),
		null);
	private final static Pattern.Term pattern58 = new Pattern.Term("Div",
		new Pattern.List(false, new Pair[]{
			new Pair(new Pattern.Term("Num",
				new Pattern.Leaf(type16),
				"x"),null), 
			new Pair(new Pattern.Term("Num",
				new Pattern.Leaf(type16),
				"y"),null)}),
		null);
	private final static Pattern.Term pattern59 = new Pattern.Term("Div",
		new Pattern.List(false, new Pair[]{
			new Pair(new Pattern.Leaf(type17), "x"), 
			new Pair(new Pattern.Term("Div",
				new Pattern.List(false, new Pair[]{
					new Pair(new Pattern.Leaf(type17), "y"), 
					new Pair(new Pattern.Leaf(type17), "z")}),
				null),null)}),
		null);
	private final static Pattern.Term pattern60 = new Pattern.Term("Div",
		new Pattern.List(false, new Pair[]{
			new Pair(new Pattern.Term("Div",
				new Pattern.List(false, new Pair[]{
					new Pair(new Pattern.Leaf(type17), "x"), 
					new Pair(new Pattern.Leaf(type17), "y")}),
				null),null), 
			new Pair(new Pattern.Leaf(type17), "z")}),
		null);
	private final static Pattern.Term pattern61 = new Pattern.Term("Div",
		new Pattern.List(false, new Pair[]{
			new Pair(new Pattern.Leaf(type17), "x"), 
			new Pair(new Pattern.Term("Num",
				new Pattern.Leaf(type16),
				"n"),null)}),
		null);
	private final static Pattern.Term pattern62 = new Pattern.Term("Div",
		new Pattern.List(false, new Pair[]{
			new Pair(new Pattern.Leaf(type17), "x"), 
			new Pair(new Pattern.Term("Num",
				new Pattern.Leaf(type16),
				"n"),null)}),
		null);
	private final static Pattern.Term pattern63 = new Pattern.Term("Div",
		new Pattern.List(false, new Pair[]{
			new Pair(new Pattern.Term("Mul",
				new Pattern.List(false, new Pair[]{
					new Pair(new Pattern.Leaf(type16), "n"), 
					new Pair(new Pattern.Bag(true, new Pair[]{
						new Pair(new Pattern.Leaf(type17), "x"), 
						new Pair(new Pattern.Leaf(type17), "xs")}),null)}),
				null),null), 
			new Pair(new Pattern.Leaf(type17), "y")}),
		null);
	private final static Pattern.Term pattern64 = new Pattern.Term("Div",
		new Pattern.List(false, new Pair[]{
			new Pair(new Pattern.Term("Mul",
				new Pattern.List(false, new Pair[]{
					new Pair(new Pattern.Leaf(type16), "n"), 
					new Pair(new Pattern.Bag(true, new Pair[]{
						new Pair(new Pattern.Leaf(type17), "xs")}),null)}),
				null),null), 
			new Pair(new Pattern.Leaf(type18), "y")}),
		null);
	private final static Pattern.Term pattern65 = new Pattern.Term("Div",
		new Pattern.List(false, new Pair[]{
			new Pair(new Pattern.Term("Sum",
				new Pattern.List(false, new Pair[]{
					new Pair(new Pattern.Leaf(type16), "n"), 
					new Pair(new Pattern.Bag(true, new Pair[]{
						new Pair(new Pattern.Leaf(type17), "xs")}),null)}),
				null),null), 
			new Pair(new Pattern.Leaf(type17), "y")}),
		null);
	private final static Pattern.Term pattern66 = new Pattern.Term("Div",
		new Pattern.List(false, new Pair[]{
			new Pair(new Pattern.Term("Mul",
				new Pattern.List(false, new Pair[]{
					new Pair(new Pattern.Leaf(type16), "n"), 
					new Pair(new Pattern.Bag(true, new Pair[]{
						new Pair(new Pattern.Leaf(type17), "xs")}),null)}),
				null),null), 
			new Pair(new Pattern.Leaf(type17), "y")}),
		null);
	private final static Pattern.Term pattern67 = new Pattern.Term("Sum",
		new Pattern.List(false, new Pair[]{
			new Pair(new Pattern.Leaf(type16), "n"), 
			new Pair(new Pattern.Bag(false, new Pair[]{}),null)}),
		null);
	private final static Pattern.Term pattern68 = new Pattern.Term("Sum",
		new Pattern.List(false, new Pair[]{
			new Pair(new Pattern.Leaf(type16), "n"), 
			new Pair(new Pattern.Bag(false, new Pair[]{
				new Pair(new Pattern.Term("Mul",
					new Pattern.List(false, new Pair[]{
						new Pair(new Pattern.Leaf(type16), "m"), 
						new Pair(new Pattern.Bag(false, new Pair[]{
							new Pair(new Pattern.Leaf(type8), "x")}),null)}),
					null),null)}),null)}),
		null);
	private final static Pattern.Term pattern69 = new Pattern.Term("Sum",
		new Pattern.List(false, new Pair[]{
			new Pair(new Pattern.Leaf(type16), "n"), 
			new Pair(new Pattern.Bag(true, new Pair[]{
				new Pair(new Pattern.Leaf(type17), "x"), 
				new Pair(new Pattern.Leaf(type17), "rest")}),null)}),
		null);
	private final static Pattern.Term pattern70 = new Pattern.Term("Sum",
		new Pattern.List(false, new Pair[]{
			new Pair(new Pattern.Leaf(type16), "x"), 
			new Pair(new Pattern.Bag(true, new Pair[]{
				new Pair(new Pattern.Term("Num",
					new Pattern.Leaf(type16),
					"y"),null), 
				new Pair(new Pattern.Leaf(type17), "rest")}),null)}),
		null);
	private final static Pattern.Term pattern71 = new Pattern.Term("Sum",
		new Pattern.List(false, new Pair[]{
			new Pair(new Pattern.Leaf(type16), "n"), 
			new Pair(new Pattern.Bag(true, new Pair[]{
				new Pair(new Pattern.Term("Mul",
					new Pattern.List(false, new Pair[]{
						new Pair(new Pattern.Leaf(type16), "x"), 
						new Pair(new Pattern.Bag(true, new Pair[]{
							new Pair(new Pattern.Leaf(type17),null)}), "xs")}),
					null),null), 
				new Pair(new Pattern.Term("Mul",
					new Pattern.List(false, new Pair[]{
						new Pair(new Pattern.Leaf(type16), "y"), 
						new Pair(new Pattern.Bag(true, new Pair[]{
							new Pair(new Pattern.Leaf(type17),null)}), "ys")}),
					null),null), 
				new Pair(new Pattern.Leaf(type17), "zs")}),null)}),
		null);
	private final static Pattern.Term pattern72 = new Pattern.Term("Sum",
		new Pattern.List(false, new Pair[]{
			new Pair(new Pattern.Leaf(type16), "x"), 
			new Pair(new Pattern.Bag(true, new Pair[]{
				new Pair(new Pattern.Term("Sum",
					new Pattern.List(false, new Pair[]{
						new Pair(new Pattern.Leaf(type16), "y"), 
						new Pair(new Pattern.Bag(true, new Pair[]{
							new Pair(new Pattern.Leaf(type17), "ys")}),null)}),
					null),null), 
				new Pair(new Pattern.Leaf(type17), "xs")}),null)}),
		null);
	private final static Pattern.Term pattern73 = new Pattern.Term("Equation",
		new Pattern.List(false, new Pair[]{
			new Pair(new Pattern.Leaf(type22),null), 
			new Pair(new Pattern.Term("Num",
				new Pattern.Leaf(type16),
				"v"),null)}),
		null);
	private final static Pattern.Term pattern74 = new Pattern.Term("Equation",
		new Pattern.List(false, new Pair[]{
			new Pair(new Pattern.Leaf(type22), "t"), 
			new Pair(new Pattern.Term("Sum",
				new Pattern.List(false, new Pair[]{
					new Pair(new Pattern.Leaf(type16), "n"), 
					new Pair(new Pattern.Bag(false, new Pair[]{
						new Pair(new Pattern.Term("Mul",
							new Pattern.List(false, new Pair[]{
								new Pair(new Pattern.Leaf(type16), "m"), 
								new Pair(new Pattern.Bag(true, new Pair[]{
									new Pair(new Pattern.Leaf(type17), "xs")}),null)}),
							null),null)}),null)}),
				null),null)}),
		null);
	private final static Pattern.Term pattern75 = new Pattern.Term("Equation",
		new Pattern.List(false, new Pair[]{
			new Pair(new Pattern.Leaf(type22), "t"), 
			new Pair(new Pattern.Term("Sum",
				new Pattern.List(false, new Pair[]{
					new Pair(new Pattern.Leaf(type16), "n"), 
					new Pair(new Pattern.Bag(true, new Pair[]{
						new Pair(new Pattern.Leaf(type23), "xs")}), "ms")}),
				null),null)}),
		null);
	private final static Pattern.Term pattern76 = new Pattern.Term("And",
		new Pattern.Set(true, new Pair[]{
			new Pair(new Pattern.Term("Equation",
				new Pattern.List(false, new Pair[]{
					new Pair(new Pattern.Leaf(type22), "t"), 
					new Pair(new Pattern.Term("Sum",
						new Pattern.List(false, new Pair[]{
							new Pair(new Pattern.Leaf(type16), "c"), 
							new Pair(new Pattern.Bag(true, new Pair[]{
								new Pair(new Pattern.Term("Mul",
									new Pattern.List(false, new Pair[]{
										new Pair(new Pattern.Leaf(type16), "vc"), 
										new Pair(new Pattern.Bag(false, new Pair[]{
											new Pair(new Pattern.Leaf(type17), "v")}),null)}),
									null),null), 
								new Pair(new Pattern.Leaf(type23), "ms")}), "xs")}),
						null),null)}),
				null), "eq"), 
			new Pair(new Pattern.Leaf(type10), "bs")}),
		null);
	private final static Pattern.Term pattern77 = new Pattern.Term("And",
		new Pattern.Set(true, new Pair[]{
			new Pair(new Pattern.Term("Equation",
				new Pattern.List(false, new Pair[]{
					new Pair(new Pattern.Leaf(type22), "t"), 
					new Pair(new Pattern.Leaf(type8), "v")}),
				null), "eq"), 
			new Pair(new Pattern.Leaf(type10), "bs")}),
		null);
	private final static Pattern.Term pattern78 = new Pattern.Term("Not",
		new Pattern.Term("Equation",
			new Pattern.List(false, new Pair[]{
				new Pair(new Pattern.Leaf(type24), "t"), 
				new Pair(new Pattern.Leaf(type17), "e")}),
			null),
		null);
	private final static Pattern.Term pattern79 = new Pattern.Term("Not",
		new Pattern.Term("Equation",
			new Pattern.List(false, new Pair[]{
				new Pair(new Pattern.Leaf(type25), "t"), 
				new Pair(new Pattern.Leaf(type17), "e")}),
			null),
		null);
	private final static Pattern.Term pattern80 = new Pattern.Term("Equals",
		new Pattern.List(false, new Pair[]{
			new Pair(new Pattern.Leaf(type22), "t"), 
			new Pair(new Pattern.Bag(false, new Pair[]{
				new Pair(new Pattern.Leaf(type17), "e1"), 
				new Pair(new Pattern.Leaf(type17), "e2")}),null)}),
		null);
	private final static Pattern.Term pattern81 = new Pattern.Term("Inequality",
		new Pattern.List(false, new Pair[]{
			new Pair(new Pattern.Leaf(type22), "t"), 
			new Pair(new Pattern.Term("Num",
				new Pattern.Leaf(type16),
				"v"),null)}),
		null);
	private final static Pattern.Term pattern82 = new Pattern.Term("Not",
		new Pattern.Term("Inequality",
			new Pattern.List(false, new Pair[]{
				new Pair(new Pattern.Leaf(type24), "t"), 
				new Pair(new Pattern.Leaf(type17), "e")}),
			null),
		null);
	private final static Pattern.Term pattern83 = new Pattern.Term("Inequality",
		new Pattern.List(false, new Pair[]{
			new Pair(new Pattern.Leaf(type22), "t"), 
			new Pair(new Pattern.Term("Sum",
				new Pattern.List(false, new Pair[]{
					new Pair(new Pattern.Leaf(type16), "n"), 
					new Pair(new Pattern.Bag(true, new Pair[]{
						new Pair(new Pattern.Leaf(type23), "xs")}), "ms")}),
				null),null)}),
		null);
	private final static Pattern.Term pattern84 = new Pattern.Term("And",
		new Pattern.Set(true, new Pair[]{
			new Pair(new Pattern.Term("Inequality",
				new Pattern.List(false, new Pair[]{
					new Pair(new Pattern.Leaf(type24),null), 
					new Pair(new Pattern.Term("Sum",
						new Pattern.List(false, new Pair[]{
							new Pair(new Pattern.Leaf(type16), "x1"), 
							new Pair(new Pattern.Bag(false, new Pair[]{
								new Pair(new Pattern.Term("Mul",
									new Pattern.List(false, new Pair[]{
										new Pair(new Pattern.Leaf(type16), "x2"), 
										new Pair(new Pattern.Bag(false, new Pair[]{
											new Pair(new Pattern.Leaf(type17), "vx1")}),null)}),
									null),null), 
								new Pair(new Pattern.Term("Mul",
									new Pattern.List(false, new Pair[]{
										new Pair(new Pattern.Leaf(type16), "x3"), 
										new Pair(new Pattern.Bag(false, new Pair[]{
											new Pair(new Pattern.Leaf(type17), "vx2")}),null)}),
									null),null)}),null)}),
						null), "s1")}),
				null), "ieq1"), 
			new Pair(new Pattern.Term("Inequality",
				new Pattern.List(false, new Pair[]{
					new Pair(new Pattern.Leaf(type24),null), 
					new Pair(new Pattern.Term("Sum",
						new Pattern.List(false, new Pair[]{
							new Pair(new Pattern.Leaf(type16), "y1"), 
							new Pair(new Pattern.Bag(false, new Pair[]{
								new Pair(new Pattern.Term("Mul",
									new Pattern.List(false, new Pair[]{
										new Pair(new Pattern.Leaf(type16), "y2"), 
										new Pair(new Pattern.Bag(false, new Pair[]{
											new Pair(new Pattern.Leaf(type17), "vy1")}),null)}),
									null),null), 
								new Pair(new Pattern.Term("Mul",
									new Pattern.List(false, new Pair[]{
										new Pair(new Pattern.Leaf(type16), "y3"), 
										new Pair(new Pattern.Bag(false, new Pair[]{
											new Pair(new Pattern.Leaf(type17), "vy2")}),null)}),
									null),null)}),null)}),
						null), "s2")}),
				null), "ieq2"), 
			new Pair(new Pattern.Leaf(type10), "rest")}),
		null);
	private final static Pattern.Term pattern85 = new Pattern.Term("And",
		new Pattern.Set(true, new Pair[]{
			new Pair(new Pattern.Term("Inequality",
				new Pattern.List(false, new Pair[]{
					new Pair(new Pattern.Leaf(type22), "t1"), 
					new Pair(new Pattern.Term("Sum",
						new Pattern.List(false, new Pair[]{
							new Pair(new Pattern.Leaf(type16), "x1"), 
							new Pair(new Pattern.Bag(true, new Pair[]{
								new Pair(new Pattern.Term("Mul",
									new Pattern.List(false, new Pair[]{
										new Pair(new Pattern.Leaf(type16), "x2"), 
										new Pair(new Pattern.Bag(false, new Pair[]{
											new Pair(new Pattern.Leaf(type17), "v1")}),null)}),
									null),null), 
								new Pair(new Pattern.Leaf(type23), "xs")}), "xxs")}),
						null), "s1")}),
				null), "eq1"), 
			new Pair(new Pattern.Term("Inequality",
				new Pattern.List(false, new Pair[]{
					new Pair(new Pattern.Leaf(type22), "t2"), 
					new Pair(new Pattern.Term("Sum",
						new Pattern.List(false, new Pair[]{
							new Pair(new Pattern.Leaf(type16), "y1"), 
							new Pair(new Pattern.Bag(true, new Pair[]{
								new Pair(new Pattern.Term("Mul",
									new Pattern.List(false, new Pair[]{
										new Pair(new Pattern.Leaf(type16), "y2"), 
										new Pair(new Pattern.Bag(false, new Pair[]{
											new Pair(new Pattern.Leaf(type17), "v2")}),null)}),
									null),null), 
								new Pair(new Pattern.Leaf(type23), "ys")}), "yys")}),
						null), "s2")}),
				null), "eq2"), 
			new Pair(new Pattern.Leaf(type10), "rest")}),
		null);
	private final static Pattern.Term pattern86 = new Pattern.Term("And",
		new Pattern.Set(true, new Pair[]{
			new Pair(new Pattern.Term("Inequality",
				new Pattern.List(false, new Pair[]{
					new Pair(new Pattern.Leaf(type22), "t1"), 
					new Pair(new Pattern.Term("Sum",
						new Pattern.List(false, new Pair[]{
							new Pair(new Pattern.Leaf(type16), "x1"), 
							new Pair(new Pattern.Bag(true, new Pair[]{
								new Pair(new Pattern.Term("Mul",
									new Pattern.List(false, new Pair[]{
										new Pair(new Pattern.Leaf(type16), "x2"), 
										new Pair(new Pattern.Bag(false, new Pair[]{
											new Pair(new Pattern.Leaf(type17), "v1")}),null)}),
									null),null), 
								new Pair(new Pattern.Leaf(type23), "xs")}), "xxs")}),
						null), "s1")}),
				null), "eq1"), 
			new Pair(new Pattern.Term("Inequality",
				new Pattern.List(false, new Pair[]{
					new Pair(new Pattern.Leaf(type22), "t2"), 
					new Pair(new Pattern.Leaf(type8), "v2")}),
				null), "eq2"), 
			new Pair(new Pattern.Leaf(type10), "rest")}),
		null);
	private final static Pattern.Term pattern87 = new Pattern.Term("And",
		new Pattern.Set(true, new Pair[]{
			new Pair(new Pattern.Term("Equals",
				new Pattern.List(false, new Pair[]{
					new Pair(new Pattern.Leaf(type2), "t"), 
					new Pair(new Pattern.Bag(false, new Pair[]{
						new Pair(new Pattern.Leaf(type8), "x"), 
						new Pair(new Pattern.Leaf(type26), "y")}),null)}),
				null), "eq"), 
			new Pair(new Pattern.Leaf(type10), "bs")}),
		null);
	private final static Pattern.Term pattern88 = new Pattern.Term("ArrayGen",
		new Pattern.List(false, new Pair[]{
			new Pair(new Pattern.Leaf(type6), "x"), 
			new Pair(new Pattern.Term("Num",
				new Pattern.Leaf(type16),
				"r"),null)}),
		null);
	private final static Pattern.Term pattern89 = new Pattern.Term("And",
		new Pattern.Set(true, new Pair[]{
			new Pair(new Pattern.Term("Equals",
				new Pattern.List(false, new Pair[]{
					new Pair(new Pattern.Leaf(type2), "t"), 
					new Pair(new Pattern.Bag(false, new Pair[]{
						new Pair(new Pattern.Leaf(type8), "x"), 
						new Pair(new Pattern.Leaf(type27), "y")}),null)}),
				null), "eq"), 
			new Pair(new Pattern.Leaf(type10), "bs")}),
		null);
	private final static Pattern.Term pattern90 = new Pattern.Term("LengthOf",
		new Pattern.Term("Array",
			new Pattern.List(true, new Pair[]{
				new Pair(new Pattern.Leaf(type6), "xs")}),
			null),
		null);
	private final static Pattern.Term pattern91 = new Pattern.Term("LengthOf",
		new Pattern.Term("ArrayGen",
			new Pattern.List(false, new Pair[]{
				new Pair(new Pattern.Leaf(type6), "v"), 
				new Pair(new Pattern.Leaf(type6), "n")}),
			null),
		null);
	private final static Pattern.Term pattern92 = new Pattern.Term("IndexOf",
		new Pattern.List(false, new Pair[]{
			new Pair(new Pattern.Term("Array",
				new Pattern.List(true, new Pair[]{
					new Pair(new Pattern.Leaf(type6), "xs")}),
				null),null), 
			new Pair(new Pattern.Term("Num",
				new Pattern.Leaf(type16),
				"i"),null)}),
		null);
	private final static Pattern.Term pattern93 = new Pattern.Term("IndexOf",
		new Pattern.List(false, new Pair[]{
			new Pair(new Pattern.Term("ArrayGen",
				new Pattern.List(false, new Pair[]{
					new Pair(new Pattern.Leaf(type6), "v"), 
					new Pair(new Pattern.Leaf(type6), "n")}),
				null),null), 
			new Pair(new Pattern.Leaf(type6),null)}),
		null);
	private final static Pattern.Term pattern94 = new Pattern.Term("ForAll",
		new Pattern.List(false, new Pair[]{
			new Pair(new Pattern.Set(true, new Pair[]{
				new Pair(new Pattern.List(false, new Pair[]{
					new Pair(new Pattern.Leaf(type28),null), 
					new Pair(new Pattern.Leaf(type2),null)}), "qs")}),null), 
			new Pair(new Pattern.Leaf(type10), "be")}),
		null);
	private final static Pattern.Term pattern95 = new Pattern.Term("Not",
		new Pattern.Term("ForAll",
			new Pattern.List(false, new Pair[]{
				new Pair(new Pattern.Set(true, new Pair[]{
					new Pair(new Pattern.List(false, new Pair[]{
						new Pair(new Pattern.Leaf(type28),null), 
						new Pair(new Pattern.Leaf(type2),null)}),null)}), "vars"), 
				new Pair(new Pattern.Leaf(type10), "be")}),
			null),
		null);
	private final static Pattern.Term pattern96 = new Pattern.Term("ForAll",
		new Pattern.List(false, new Pair[]{
			new Pair(new Pattern.Set(true, new Pair[]{
				new Pair(new Pattern.List(false, new Pair[]{
					new Pair(new Pattern.Leaf(type28),null), 
					new Pair(new Pattern.Leaf(type2),null)}),null)}), "xs"), 
			new Pair(new Pattern.Term("ForAll",
				new Pattern.List(false, new Pair[]{
					new Pair(new Pattern.Set(true, new Pair[]{
						new Pair(new Pattern.List(false, new Pair[]{
							new Pair(new Pattern.Leaf(type28),null), 
							new Pair(new Pattern.Leaf(type2),null)}),null)}), "ys"), 
					new Pair(new Pattern.Leaf(type10), "e")}),
				null),null)}),
		null);
	private final static Pattern.Term pattern97 = new Pattern.Term("ForAll",
		new Pattern.List(false, new Pair[]{
			new Pair(new Pattern.Set(true, new Pair[]{
				new Pair(new Pattern.List(false, new Pair[]{
					new Pair(new Pattern.Leaf(type28), "v"), 
					new Pair(new Pattern.Leaf(type2),null)}),null), 
				new Pair(new Pattern.List(false, new Pair[]{
					new Pair(new Pattern.Leaf(type28),null), 
					new Pair(new Pattern.Leaf(type2),null)}), "xs")}),null), 
			new Pair(new Pattern.Leaf(type10), "e")}),
		null);
	private final static Pattern.Term pattern98 = new Pattern.Term("And",
		new Pattern.Set(true, new Pair[]{
			new Pair(new Pattern.Leaf(type10), "e1"), 
			new Pair(new Pattern.Term("ForAll",
				new Pattern.List(false, new Pair[]{
					new Pair(new Pattern.Set(true, new Pair[]{
						new Pair(new Pattern.List(false, new Pair[]{
							new Pair(new Pattern.Leaf(type28),null), 
							new Pair(new Pattern.Leaf(type2),null)}),null), 
						new Pair(new Pattern.List(false, new Pair[]{
							new Pair(new Pattern.Leaf(type28),null), 
							new Pair(new Pattern.Leaf(type2),null)}),null)}), "vs"), 
					new Pair(new Pattern.Leaf(type10), "e2")}),
				null), "qf"), 
			new Pair(new Pattern.Leaf(type10), "es")}),
		null);
	private final static Pattern.Term pattern99 = new Pattern.Term("Exists",
		new Pattern.List(false, new Pair[]{
			new Pair(new Pattern.Set(true, new Pair[]{
				new Pair(new Pattern.List(false, new Pair[]{
					new Pair(new Pattern.Leaf(type28),null), 
					new Pair(new Pattern.Leaf(type2),null)}), "qs")}),null), 
			new Pair(new Pattern.Leaf(type10), "be")}),
		null);
	private final static Pattern.Term pattern100 = new Pattern.Term("Not",
		new Pattern.Term("Exists",
			new Pattern.List(false, new Pair[]{
				new Pair(new Pattern.Set(true, new Pair[]{
					new Pair(new Pattern.List(false, new Pair[]{
						new Pair(new Pattern.Leaf(type28),null), 
						new Pair(new Pattern.Leaf(type2),null)}),null)}), "vars"), 
				new Pair(new Pattern.Leaf(type10), "be")}),
			null),
		null);
	private final static Pattern.Term pattern101 = new Pattern.Term("Exists",
		new Pattern.List(false, new Pair[]{
			new Pair(new Pattern.Set(true, new Pair[]{
				new Pair(new Pattern.List(false, new Pair[]{
					new Pair(new Pattern.Leaf(type28),null), 
					new Pair(new Pattern.Leaf(type2),null)}),null)}), "xs"), 
			new Pair(new Pattern.Term("Exists",
				new Pattern.List(false, new Pair[]{
					new Pair(new Pattern.Set(true, new Pair[]{
						new Pair(new Pattern.List(false, new Pair[]{
							new Pair(new Pattern.Leaf(type28),null), 
							new Pair(new Pattern.Leaf(type2),null)}),null)}), "ys"), 
					new Pair(new Pattern.Leaf(type10), "e")}),
				null),null)}),
		null);
	private final static Pattern.Term pattern102 = new Pattern.Term("And",
		new Pattern.Set(true, new Pair[]{
			new Pair(new Pattern.Term("Exists",
				new Pattern.List(false, new Pair[]{
					new Pair(new Pattern.Set(true, new Pair[]{
						new Pair(new Pattern.List(false, new Pair[]{
							new Pair(new Pattern.Leaf(type28),null), 
							new Pair(new Pattern.Leaf(type2),null)}),null)}), "vs"), 
					new Pair(new Pattern.Leaf(type10), "e")}),
				null),null), 
			new Pair(new Pattern.Leaf(type10), "es")}),
		null);
	private final static Pattern.Term pattern103 = new Pattern.Term("Is",
		new Pattern.List(false, new Pair[]{
			new Pair(new Pattern.Leaf(type6), "e"), 
			new Pair(new Pattern.Leaf(type1),null)}),
		null);
	private final static Pattern.Term pattern104 = new Pattern.Term("Not",
		new Pattern.Term("Is",
			new Pattern.List(false, new Pair[]{
				new Pair(new Pattern.Leaf(type6), "e"), 
				new Pair(new Pattern.Leaf(type2), "t")}),
			null),
		null);
	private final static Pattern.Term pattern105 = new Pattern.Term("And",
		new Pattern.Set(true, new Pair[]{
			new Pair(new Pattern.Term("Is",
				new Pattern.List(false, new Pair[]{
					new Pair(new Pattern.Leaf(type6), "e1"), 
					new Pair(new Pattern.Leaf(type2), "t1")}),
				null),null), 
			new Pair(new Pattern.Term("Is",
				new Pattern.List(false, new Pair[]{
					new Pair(new Pattern.Leaf(type6), "e2"), 
					new Pair(new Pattern.Leaf(type2), "t2")}),
				null),null), 
			new Pair(new Pattern.Leaf(type10), "bs")}),
		null);
	// =========================================================================
	// rules
	// =========================================================================

	public static final InferenceRule[] inferences = new InferenceRule[]{
		new Inference_0(pattern53),
		new Inference_1(pattern77),
		new Inference_2(pattern85),
		new Inference_3(pattern86),
		new Inference_4(pattern98)
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
		new Reduction_30(pattern30),
		new Reduction_31(pattern31),
		new Reduction_32(pattern32),
		new Reduction_33(pattern33),
		new Reduction_34(pattern34),
		new Reduction_35(pattern35),
		new Reduction_36(pattern36),
		new Reduction_37(pattern37),
		new Reduction_38(pattern38),
		new Reduction_39(pattern39),
		new Reduction_40(pattern40),
		new Reduction_41(pattern41),
		new Reduction_42(pattern42),
		new Reduction_43(pattern43),
		new Reduction_44(pattern44),
		new Reduction_45(pattern45),
		new Reduction_46(pattern46),
		new Reduction_47(pattern47),
		new Reduction_48(pattern48),
		new Reduction_49(pattern49),
		new Reduction_50(pattern50),
		new Reduction_51(pattern51),
		new Reduction_52(pattern52),
		new Reduction_53(pattern54),
		new Reduction_54(pattern55),
		new Reduction_55(pattern56),
		new Reduction_56(pattern57),
		new Reduction_57(pattern58),
		new Reduction_58(pattern59),
		new Reduction_59(pattern60),
		new Reduction_60(pattern61),
		new Reduction_61(pattern62),
		new Reduction_62(pattern63),
		new Reduction_63(pattern64),
		new Reduction_64(pattern65),
		new Reduction_65(pattern66),
		new Reduction_66(pattern67),
		new Reduction_67(pattern68),
		new Reduction_68(pattern69),
		new Reduction_69(pattern70),
		new Reduction_70(pattern71),
		new Reduction_71(pattern72),
		new Reduction_72(pattern73),
		new Reduction_73(pattern74),
		new Reduction_74(pattern75),
		new Reduction_75(pattern76),
		new Reduction_76(pattern78),
		new Reduction_77(pattern79),
		new Reduction_78(pattern80),
		new Reduction_79(pattern81),
		new Reduction_80(pattern82),
		new Reduction_81(pattern83),
		new Reduction_82(pattern84),
		new Reduction_83(pattern87),
		new Reduction_84(pattern88),
		new Reduction_85(pattern89),
		new Reduction_86(pattern90),
		new Reduction_87(pattern91),
		new Reduction_88(pattern92),
		new Reduction_89(pattern93),
		new Reduction_90(pattern94),
		new Reduction_91(pattern95),
		new Reduction_92(pattern96),
		new Reduction_93(pattern97),
		new Reduction_94(pattern99),
		new Reduction_95(pattern100),
		new Reduction_96(pattern101),
		new Reduction_97(pattern102),
		new Reduction_98(pattern103),
		new Reduction_99(pattern104),
		new Reduction_100(pattern105)
	};


	// =========================================================================
	// Main Method
	// =========================================================================

	public static void main(String[] args) throws IOException {
		new wyrl.ConsoleRewriter(SCHEMA,inferences,reductions).readEvaluatePrintLoop();
	}
}
