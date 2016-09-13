package wyrw.util;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Comparator;

import wyautl.core.Automaton;
import wyautl.core.Schema;
import wyrw.core.Reduction;
import wyrw.core.ReductionRule;
import wyrw.core.Rewrite;

public class Reductions {
	
	
	public static void minimiseAndReduce(Automaton automaton, int maxSteps, Schema schema, ReductionRule... reductions) {
		minimiseAndReduce(automaton,maxSteps,schema,reductions,null);
	}
	
	public static void minimiseAndReduce(Automaton automaton, int maxSteps, Schema schema, ReductionRule[] reductions,
			Comparator<Rewrite.Activation> comparator) {
		automaton.minimise();
		automaton.compact(0);		
		reduceOver(automaton, 0, maxSteps,schema,reductions, comparator);
	}
	
	public static void reduceOver(Automaton automaton, int start, int maxSteps, Schema schema, ReductionRule... reductions) {
		reduceOver(automaton,start,maxSteps,schema,reductions,null);
	}
		
	public static void reduce(Automaton automaton, int maxSteps, Schema schema, ReductionRule... reductions) {
		reduceOver(automaton,0,maxSteps,schema,reductions,null);
	}
	
	/**
	 * Simple helper method for reducing an automaton.  
	 * 
	 * @param automaton
	 */
	public static void reduceOver(Automaton automaton, int start, int maxSteps, Schema schema, ReductionRule[] reductions,
			Comparator<Rewrite.Activation> comparator) {
		// Now, attempt to reduce as much as possible
		IncrementalAutomatonMinimiser inc = new IncrementalAutomatonMinimiser(automaton,schema);
		
		boolean changed = true;
		while (changed && maxSteps-- > 0) {
			changed = false;
			AbstractActivation[] activations = probe(automaton, start, reductions, comparator);
			int pivot = automaton.nStates();
			for (int i = 0; i != activations.length; ++i) {
				AbstractActivation activation = activations[i];
				int from = activation.target();
				int target = activation.apply(automaton);
				if (target != Automaton.K_VOID && from != target) {
					// Rewrite applied
					inc.rewrite(from, target, pivot);
					//
					changed = true;
					break;
				} 
			}
		}
		// At this point, the automaton may not be compacted but it should be
		// minimised (assuming it was on entry).
		automaton.compact(0);
	}
	
	private static AbstractActivation[] probe(Automaton automaton, int start, ReductionRule[] reductions,
			Comparator<Rewrite.Activation> comparator) {
		ArrayList<Reduction.Activation> activations = new ArrayList<Reduction.Activation>();
		for (int s = start; s != automaton.nStates(); ++s) {
			// State is reachable from the given root
			Automaton.State state = automaton.get(s);
			// Check whether this state is a term or not; that's because
			// only
			// terms can be roots for rewrite rule applications.
			if (state instanceof Automaton.Term) {
				for (int r = 0; r != reductions.length; ++r) {
					reductions[r].probe(automaton, s, activations);
				}
			}
		}
		AbstractActivation[] array = activations.toArray(new AbstractActivation[activations.size()]);
		if (comparator != null) {
			Arrays.sort(array, comparator);
		}
		return array;
	}
	
	/**
	 * Visit all states reachable from a given starting state in the given
	 * automaton. In doing this, states which are visited are marked and,
	 * furthermore, those which are "headers" are additionally identified. A
	 * header state is one which is the target of a back-edge in the directed
	 * graph reachable from the start state.
	 *
	 * @param automaton
	 *            --- automaton to traverse.
	 * @param reachable
	 *            --- states marked with false are those which have not been
	 *            visited.
	 * @param index
	 *            --- state to begin traversal from.
	 * @return
	 */
	public static void findReachable(Automaton automaton, boolean[] reachable,
			int index) {
		if (index < 0) {
			return;
		} else if (reachable[index]) {
			// Already visited, so terminate here
			return;
		} else {
			// Not previously visited, so mark now and traverse any children
			reachable[index] = true;
			Automaton.State state = automaton.get(index);
			if (state instanceof Automaton.Term) {
				Automaton.Term term = (Automaton.Term) state;
				if (term.contents != Automaton.K_VOID) {
					findReachable(automaton, reachable, term.contents);
				}
			} else if (state instanceof Automaton.Collection) {
				Automaton.Collection compound = (Automaton.Collection) state;
				for (int i = 0; i != compound.size(); ++i) {
					findReachable(automaton, reachable, compound.get(i));
				}
			}
		}
	}
}
