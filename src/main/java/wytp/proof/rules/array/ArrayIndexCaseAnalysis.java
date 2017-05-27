// Copyright 2017 David J. Pearce
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
package wytp.proof.rules.array;

import java.util.List;

import wyal.lang.NameResolver.ResolutionError;
import wyal.lang.SyntacticItem;
import wyal.lang.WyalFile;
import wyal.lang.WyalFile.Expr;
import wyal.lang.WyalFile.Opcode;
import wyal.lang.WyalFile.Tuple;
import wytp.proof.Formula;
import wytp.proof.Proof;
import wytp.proof.Proof.State;
import wytp.proof.rules.Simplification;
import wytp.proof.util.AbstractProofRule;
import wytp.proof.util.Formulae;
import wytp.types.TypeSystem;

public class ArrayIndexCaseAnalysis extends AbstractProofRule implements Proof.LinearRule {

	public ArrayIndexCaseAnalysis(Simplification simplify,TypeSystem types) {
		super(simplify,types);
	}

	@Override
	public String getName() {
		return "ArrInd-C";
	}

	@Override
	public State apply(State state, Formula truth) throws ResolutionError {
		List<Expr.Operator> matches = extractDefinedTerms(truth,Opcode.EXPR_arridx);
		if (matches.size() > 0) {
			for(int i=0;i!=matches.size();++i) {
				Expr.Operator match = matches.get(i);
				Formula[] cases = generateCaseAnalysis(match, truth, state);
				if(cases.length > 0) {
					Formula disjunct = new Formula.Disjunct(cases);
					state = state.subsume(this, truth, disjunct);
				}
			}
		}
		return state;
	}

	private Formula[] generateCaseAnalysis(Expr.Operator split, Formula truth, Proof.State state) {
		Formula[] result;
		switch (split.getOpcode()) {
		case EXPR_arridx: {
			Expr src = split.getOperand(0);
			Expr j = split.getOperand(1);
			if (src.getOpcode() == Opcode.EXPR_arrupdt) {
				// xs[i:=v][j]
				Expr xs = (Expr) src.getOperand(0);
				Expr i = (Expr) src.getOperand(1);
				Expr v = (Expr) src.getOperand(2);
				result = new Formula[2];
				Formula case1 = (Formula) substitute(split, v, truth);
				// NOTE: we must call construct here since we are creating a new
				// term from scratch.
				WyalFile.Expr arridx = (Expr) new Expr.ArrayAccess(xs, j);
				Formula case2 = (Formula) substitute(split, arridx, truth);
				result[0] = Formulae.and(new Formula.ArithmeticEquality(true, i, j), case1);
				result[1] = Formulae.and(new Formula.ArithmeticEquality(false, i, j), case2);
				break;
			} else if (src.getOpcode() == Opcode.EXPR_arrinit) {
				// [a,b,c][j] >= 0
				result = new Formula[src.size()];
				for (int i = 0; i != src.size(); ++i) {
					// a >= 0 && j == 0
					Expr ith = new Expr.Constant(new WyalFile.Value.Int(i));
					Formula lhs = (Formula) substitute(split, src.getOperand(i), truth);
					Formula rhs = new Formula.ArithmeticEquality(true, j, ith);
					result[i] = Formulae.and(lhs, rhs);
				}
				break;
			}
		}
		default:
			// NOTE: we can arrive here if we extracted a defined term that
			// didn't meet our criteria above.
			return new Formula[0];
		}
		return result;
	}
}
