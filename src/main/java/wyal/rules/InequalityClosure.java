package wyal.rules;

import java.util.ArrayList;
import java.util.Arrays;

import wyal.lang.Formula;
import wyal.lang.Formula.Polynomial;
import wyal.lang.WyalFile.Pair;
import wyal.util.AutomatedTheoremProver;
import wyal.util.AutomatedTheoremProver.RewriteRule;

public class InequalityClosure implements RewriteRule {

	@Override
	public Formula rewrite(Formula item) {
		if (item instanceof Formula.Conjunct) {
			// We've found a conjunct of terms. Therefore, we want to look
			// through and pick out all inequalities and close over them.
			Formula.Conjunct conjunct = (Formula.Conjunct) item;
			ArrayList<Formula> inferred = new ArrayList<>();
			for (int i = 0; i != conjunct.size(); ++i) {
				Formula ith = conjunct.getOperand(i);
				if (ith instanceof Formula.Inequality) {
					for (int j = i + 1; j != conjunct.size(); ++j) {
						Formula jth = conjunct.getOperand(j);
						if (jth instanceof Formula.Inequality) {
							infer((Formula.Inequality) ith, (Formula.Inequality) jth, inferred);
						}
					}
				}
			}
			if (inferred.size() > 0) {
				// We have inferred some new inequalities. Therefore, update the
				// conjunct to reflect this.
				for(int i=0;i!=conjunct.size();++i) {
					inferred.add(conjunct.getOperand(i));
				}
				Formula[] items = inferred.toArray(new Formula[inferred.size()]);
				item = new Formula.Conjunct(items);
				if (item.equals(conjunct)) {
					return conjunct;
				} else {
					return item;
				}
			}
		}
		// For the moment, do nothing
		return item;
	}

	private static void infer(Formula.Inequality ith, Formula.Inequality jth, ArrayList<Formula> inferred) {
		//
		Formula op = closeOverInequalities(ith, jth);
		if (op != null) {
			System.out.print("FROM: ");
			AutomatedTheoremProver.print(ith);
			System.out.print(" AND: ");
			AutomatedTheoremProver.print(jth);
			System.out.print(" INFERRED: ");
			AutomatedTheoremProver.println(op);
			inferred.add(op);
		}
	}


}
