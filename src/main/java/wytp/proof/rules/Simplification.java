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
package wytp.proof.rules;

import java.math.BigInteger;
import java.util.Arrays;

import wyal.lang.WyalFile.Expr;
import wyal.util.NameResolver.ResolutionError;

import static wyal.lang.WyalFile.*;
import wyfs.util.ArrayUtils;
import wytp.proof.Formula;
import wytp.proof.Formula.ArithmeticEquality;
import wytp.proof.Formula.Conjunct;
import wytp.proof.Formula.Disjunct;
import wytp.proof.Formula.Equality;
import wytp.proof.Formula.Inequality;
import wytp.proof.Formula.Invoke;
import wytp.proof.Formula.Quantifier;
import wytp.proof.Formula.Truth;
import wytp.proof.Proof;
import wytp.proof.Proof.State;
import wytp.proof.util.AbstractProofRule;
import wytp.proof.util.Arithmetic;
import wytp.proof.util.Formulae;
import wytp.proof.util.Arithmetic.Polynomial;
import wytp.types.TypeSystem;

public class Simplification extends AbstractProofRule implements Proof.LinearRule {

	private final static Formula TRUE = new Formula.Truth(true);
	private final static Formula FALSE = new Formula.Truth(false);

	public Simplification(TypeSystem types) {
		super(null,types);
	}

	@Override
	public String getName() {
		return "Simp";
	}


	@Override
	public State apply(State head, Formula truth) throws ResolutionError {
		Formula simplifiedTruth = simplify(truth);
		if(!simplifiedTruth.equals(truth)) {
			// FIXME: useful optimisation would be to support pointer equality
			// for the above test.
			head = head.subsume(this, truth, simplifiedTruth);
		}
		return head;
	}

	/**
	 * Recursively simplify a given formula by applying the "standard"
	 * simplifications for each kind. If no simplification is performed, this
	 * returns the original object in tact.
	 *
	 * @param f
	 * @return
	 * @throws AmbiguousNameError
	 * @throws NameNotFoundError
	 */
	public Formula simplify(Formula f) throws ResolutionError {
		switch (f.getOpcode()) {
		case EXPR_const:
			return f;
		case EXPR_and:
			return simplifyConjunct((Formula.Conjunct) f);
		case EXPR_or:
			return simplifyDisjunct((Formula.Disjunct) f);
		case EXPR_exists:
		case EXPR_forall: {
			return simplifyQuantifier((Formula.Quantifier) f);
		}
		case EXPR_eq:
		case EXPR_neq: {
			if (f instanceof ArithmeticEquality) {
				return simplifyArithmeticEquality((Formula.ArithmeticEquality) f);
			} else {
				return simplifyEquality((Formula.Equality) f);
			}
		}
		case EXPR_lt:
		case EXPR_gteq: {
			return simplifyInequality((Formula.Inequality) f);
		}
		case EXPR_invoke: {
			return simplifyInvoke((Formula.Invoke) f);
		}
		case EXPR_is: {
			return simplifyIs((Formula.Is) f);
		}
		default:
			throw new IllegalArgumentException("invalid formula opcode: " + f.getOpcode());
		}
	}

	public Formula simplifyConjunct(Conjunct conjunct) throws ResolutionError {
		Formula[] children = conjunct.getAll();
		Formula[] nChildren = simplify(children);
		// Check whether contains false
		if (ArrayUtils.firstIndexOf(nChildren, FALSE) >= 0) {
			// Any conjunct containing false equals false
			return new Formula.Truth(false);
		}
		// Expand any nested conjuncts
		nChildren = inlineNestedConjuncts(nChildren);
		// Remove any duplicate types
		nChildren = ArrayUtils.removeDuplicates(nChildren);
		// Remove all occurrences of true
		nChildren = ArrayUtils.removeAll(nChildren, TRUE);
		//
		if(nChildren.length == 0) {
			return new Formula.Truth(true);
		} else if(nChildren.length == 1) {
			return nChildren[0];
		} else if(children == nChildren) {
			return conjunct;
		} else {
			return new Formula.Conjunct(nChildren);
		}
	}

	public Formula simplifyDisjunct(Disjunct disjunct) throws ResolutionError {
		Formula[] children = disjunct.getAll();
		Formula[] nChildren = simplify(children);
		// Check whether contains true
		if (ArrayUtils.firstIndexOf(nChildren, TRUE) >= 0) {
			// Any disjunct containing true equals true
			return new Formula.Truth(true);
		}
		// Expand any nested disjuncts
		nChildren = inlineNestedDisjuncts(nChildren);
		// Remove any duplicate types
		nChildren = ArrayUtils.removeDuplicates(nChildren);
		// Remove all occurrences of false
		nChildren = ArrayUtils.removeAll(nChildren, FALSE);
		//
		if(nChildren.length == 0) {
			return new Formula.Truth(false);
		} else if(nChildren.length == 1) {
			return nChildren[0];
		} else if(children == nChildren) {
			return disjunct;
		} else {
			return new Formula.Disjunct(nChildren);
		}
	}

	public Formula[] simplify(Formula[] children) throws ResolutionError {
		Formula[] nChildren = children;
		for (int i = 0; i != nChildren.length; ++i) {
			Formula child = children[i];
			Formula nChild = simplify(child);
			if (child != nChild && children == nChildren) {
				nChildren = Arrays.copyOf(children, children.length);
			}
			nChildren[i] = nChild;
		}
		return nChildren;
	}

	/**
	 * Simplify a quantified formula. In essence, if the body is a truth value
	 * then that is returned. For example, <code>forall x.true</code> is simply
	 * <code>true</code>.
	 *
	 * @param quantifier
	 * @return
	 * @throws AmbiguousNameError
	 * @throws NameNotFoundError
	 */
	public Formula simplifyQuantifier(Quantifier quantifier) throws ResolutionError {
		Formula body = quantifier.getBody();
		Formula nBody = simplify(body);
		if (nBody instanceof Truth) {
			return nBody;
		} else if (nBody != body) {
			return new Quantifier(quantifier.getSign(), quantifier.getParameters(), nBody);
		} else {
			return quantifier;
		}
	}

	/**
	 * Simplify an inequality by canceling, evaluating and/or balancing:
	 * <ol>
	 * <li><b>Canceling</b> is the process of removing commons terms from both
	 * sides. For example, in <code>x+y < x</code> we can cancel <code>x</code>
	 * to give <code>y < 0</code>.</li>
	 * <li><b>Evaluating</b> is the process of reducing a constant inequality to
	 * either <code>true</code> or <code>false</code>. For example,
	 * <code>0 < 1</code> reduces to <code>true</code> whilst
	 * <code>1 >= 0</code> reduces to <code>false</code>.</li>
	 * <li><b>Balancing</b> is the process of eliminating negative terms and
	 * factorising. For example, <code>-x < 1</code> is balanced to
	 * <code>0 < 1 + x</code>. Likewise, <code>2*x < 6*y</code> is factorised to
	 * <code>x < 3*y</code>.</li>
	 * </ol>
	 *
	 * @param ieq
	 * @return
	 * @throws AmbiguousNameError
	 * @throws NameNotFoundError
	 */
	public Formula simplifyInequality(Inequality ieq) throws ResolutionError {
		Expr lhs = ieq.get(0);
		Expr rhs = ieq.get(1);
		Expr nLhs = simplifyExpression(lhs);
		Expr nRhs = simplifyExpression(rhs);
		Pair<Expr, Expr> bs = normaliseBounds(nLhs, nRhs);
		nLhs = bs.getFirst();
		nRhs = bs.getSecond();
		//
		if (nLhs instanceof Expr.Constant && nRhs instanceof Expr.Constant) {
			Value.Int lhs_v = (Value.Int) ((Expr.Constant) nLhs).getValue();
			Value.Int rhs_v = (Value.Int) ((Expr.Constant) nRhs).getValue();
			return evaluateInequality(ieq.getOpcode(), lhs_v, rhs_v);
		} else if (nLhs.equals(nRhs)) {
			return new Formula.Truth(true);
		} else if(lhs.equals(nLhs) && rhs.equals(nRhs)) {
			return ieq;
		} else {
			return new Inequality(bs.getFirst(), bs.getSecond());
		}
	}

	/**
	 * Simplify an arithmetic equality by canceling, evaluating and/or
	 * balancing:
	 * <ol>
	 * <li><b>Canceling</b> is the process of removing commons terms from both
	 * sides. For example, in <code>x+y == x</code> we can cancel <code>x</code>
	 * to give <code>y == 0</code>.</li>
	 * <li><b>Evaluating</b> is the process of reducing a constant inequality to
	 * either <code>true</code> or <code>false</code>. For example,
	 * <code>0 == 0</code> reduces to <code>true</code> whilst
	 * <code>1 == 0</code> reduces to <code>false</code>.</li>
	 * <li><b>Balancing</b> is the process of eliminating negative terms and
	 * factorising. For example, <code>-x == 1</code> is balanced to
	 * <code>0 == 1 + x</code>. Likewise, <code>2*x == 6*y</code> is factorised
	 * to <code>x == 3*y</code>.</li>
	 * </ol>
	 *
	 * @param ieq
	 * @return
	 * @throws AmbiguousNameError
	 * @throws NameNotFoundError
	 */
	public Formula simplifyArithmeticEquality(ArithmeticEquality eq) throws ResolutionError {
		Expr lhs = eq.get(0);
		Expr rhs = eq.get(1);
		Expr nLhs = simplifyExpression(lhs);
		Expr nRhs = simplifyExpression(rhs);
		Pair<Expr, Expr> bs = normaliseBounds(nLhs, nRhs);
		nLhs = bs.getFirst();
		nRhs = bs.getSecond();
		if (nLhs instanceof Expr.Constant && nRhs instanceof Expr.Constant) {
			Value lhs_v = ((Expr.Constant) nLhs).getValue();
			Value rhs_v = ((Expr.Constant) nRhs).getValue();
			return evaluateEquality(eq.getOpcode(), lhs_v, rhs_v);
		} else if (nLhs.equals(nRhs)) {
			return new Formula.Truth(eq.getSign());
		}
		Arithmetic.Polynomial difference = Arithmetic.asPolynomial(nLhs).subtract(Arithmetic.asPolynomial(nRhs));
		if(difference.isConstant()) {
			BigInteger constant = difference.toConstant();
			return new Formula.Truth(constant.equals(BigInteger.ZERO));
		}
		// Handle orientation
		if(nLhs.compareTo(nRhs) > 0) {
			Expr tmp = nLhs;
			nLhs = nRhs;
			nRhs = tmp;
		}
		if(nLhs.equals(lhs) && nRhs.equals(rhs)) {
			// FIXME: above could be more efficient
			return eq;
		} else {
			return new ArithmeticEquality(eq.getSign(), nLhs, nRhs);
		}
	}

	/**
	 * Simplify a non-arithmetic equality by attempting to evaluate it. For
	 * example, <code>true == false</code> reduces to <code>false</code>. In the
	 * case that neither side is a constant, then the original equality is
	 * returned.
	 *
	 * @param eq
	 * @return
	 * @throws AmbiguousNameError
	 * @throws NameNotFoundError
	 */
	public Formula simplifyEquality(Equality eq) throws ResolutionError {
		Expr lhs = eq.get(0);
		Expr rhs = eq.get(1);
		Expr nLhs = simplifyExpression(lhs);
		Expr nRhs = simplifyExpression(rhs);
		if (nLhs instanceof Expr.Constant && nRhs instanceof Expr.Constant) {
			Value lhs_v = ((Expr.Constant) nLhs).getValue();
			Value rhs_v = ((Expr.Constant) nRhs).getValue();
			return evaluateEquality(eq.getOpcode(), lhs_v, rhs_v);
		} else if (nLhs.equals(nRhs)) {
			return new Formula.Truth(eq.getSign());
		}
		// Handle orientation
		if(nLhs.compareTo(nRhs) > 0) {
			Expr tmp = nLhs;
			nLhs = nRhs;
			nRhs = tmp;
		}
		// Now decide whether need to create a new equality or not.
		if(nLhs == lhs && nRhs == rhs) {
			return eq;
		} else {
			return new Equality(eq.getSign(),nLhs,nRhs);
		}
	}

	public Formula simplifyInvoke(Invoke ivk) throws ResolutionError {
		Tuple<Expr> args = ivk.getArguments();
		Expr[] nChildren = new Expr[args.size()];
		boolean changed = false;
		for (int i = 0; i != args.size(); ++i) {
			Expr child = args.get(i);
			Expr nChild = simplifyExpression(child);
			//
			changed |= (child != nChild);
			nChildren[i] = nChild;
		}
		if(!changed) {
			return ivk;
		} else {
			Tuple<Expr> nArgs = new Tuple<>(nChildren);
			return new Invoke(ivk.getSign(),ivk.getSignatureType(),ivk.getName(),ivk.getSelector(),nArgs);
		}
	}

	public Formula simplifyIs(Formula.Is e) throws ResolutionError {
		Expr lhs = e.getTestExpr();
		Expr nLhs = simplifyExpression(lhs);
		if(lhs != nLhs) {
			return new Formula.Is(nLhs, e.getTestType());
		} else {
			return e;
		}
	}


	public Expr[] simplifyExpressions(Expr[] children) throws ResolutionError {
		Expr[] nChildren = children;
		for (int i = 0; i != children.length; ++i) {
			Expr child = children[i];
			Expr nChild = simplifyExpression(child);
			if (child != nChild && children == nChildren) {
				nChildren = Arrays.copyOf(children, children.length);
			}
			nChildren[i] = nChild;
		}
		return nChildren;
	}

	/**
	 * Convert an arbitrary expression to an atom.
	 *
	 * @param e
	 * @return
	 * @throws AmbiguousNameError
	 * @throws NameNotFoundError
	 */
	public Expr simplifyExpression(Expr e) throws ResolutionError {
		switch (e.getOpcode()) {
		case EXPR_varcopy:
			return e;
		case EXPR_const:
			return simplifyConstant((Expr.Constant) e);
		case EXPR_invoke:
			return simplifyInvoke((Expr.Invoke) e);
		case EXPR_arridx:
			return simplifyArrayIndex((Expr.Operator) e);
		case EXPR_arrupdt:
			return simplifyArrayUpdate((Expr.Operator) e);
		case EXPR_arrlen:
			return simplifyArrayLength((Expr.Operator)e);
		case EXPR_arrinit:
		case EXPR_arrgen:
		case EXPR_div: // temporary for now
		case EXPR_rem: // temporary for now
			return simplifyNonArithmetic((Expr.Operator) e);
		case EXPR_neg:
		case EXPR_add:
		case EXPR_mul:
		case EXPR_sub:
			return simplifyArithmetic((Expr.Operator) e);
		case EXPR_recinit:
			return simplifyRecordInitialiser((Expr.RecordInitialiser) e);
		case EXPR_recfield:
			return simplifyRecordAccess((Expr.RecordAccess) e);
		case EXPR_recupdt:
			return simplifyRecordUpdate((Expr.RecordUpdate) e);
		case EXPR_deref:
			return simplifyDereference((Expr.Dereference) e);
		case EXPR_not:
		case EXPR_and:
		case EXPR_or:
		case EXPR_exists:
		case EXPR_forall:
		case EXPR_eq:
		case EXPR_neq:
		case EXPR_lt:
		case EXPR_lteq:
		case EXPR_gt:
		case EXPR_gteq:
		case EXPR_is:
			if(e instanceof Formula) {
				return simplify((Formula) e);
			} else {
				// We need toFormula here because of the potential for arbitrarily
				// nested expressions to contain these constructs.
				return simplify(Formulae.toFormula(e,types));
			}
		default:
			throw new IllegalArgumentException("cannot convert expression to atom: " + e.getClass().getName());
		}
	}

	public Expr simplifyConstant(Expr.Constant e) {
		Value val = e.getValue();
		if (val instanceof Value.Bool) {
			Value.Bool b = (Value.Bool) val;
			return new Formula.Truth(b.get());
		} else {
			return e;
		}
	}

	public Expr simplifyRecordInitialiser(Expr.RecordInitialiser e) throws ResolutionError {
		Pair<Identifier,Expr>[] fields = e.getFields();
		Pair<Identifier,Expr>[] nFields = fields;
		for(int i=0;i!=fields.length;++i) {
			Expr ith = fields[i].getSecond();
			Expr nIth = simplifyExpression(ith);
			if(ith != nIth && fields == nFields) {
				nFields = Arrays.copyOf(fields, fields.length);
			}
			if(ith != nIth) {
				nFields[i] = new Pair<>(fields[i].getFirst(),nIth);
			}
		}
		if(fields == nFields) {
			return e;
		} else {
			return new Expr.RecordInitialiser(nFields);
		}
	}

	public Expr simplifyRecordAccess(Expr.RecordAccess e) throws ResolutionError {
		Expr source = e.getSource();
		Expr nSource = simplifyExpression(source);
		if(nSource instanceof Expr.RecordInitialiser) {
			Expr.RecordInitialiser ri = (Expr.RecordInitialiser) nSource;
			Pair<Identifier, Expr>[] fields = ri.getFields();
			for(int i=0;i!=fields.length;++i) {
				Pair<Identifier, Expr> field = fields[i];
				if(e.getField().equals(field.getFirst())) {
					return field.getSecond();
				}
			}
		} else if(nSource instanceof Expr.RecordUpdate) {
			Expr.RecordUpdate r = (Expr.RecordUpdate) nSource;
			if(e.getField().equals(r.getField())) {
				return r.getValue();
			} else {
				return new Expr.RecordAccess(r.getSource(), e.getField());
			}
		}
		//
		if(source == nSource) {
			return e;
		} else {
			return new Expr.RecordAccess(nSource, e.getField());
		}
	}

	public Expr simplifyRecordUpdate(Expr.RecordUpdate e) throws ResolutionError {
		Expr source = e.getSource();
		Expr value = e.getValue();
		Expr nSource = simplifyExpression(source);
		Expr nValue = simplifyExpression(value);
		//
		if(nSource instanceof Expr.RecordInitialiser) {
			Expr.RecordInitialiser ri = (Expr.RecordInitialiser) nSource;
			Pair<Identifier, Expr>[] oldFields = ri.getFields();
			Pair<Identifier, Expr>[] newFields = Arrays.copyOf(oldFields, oldFields.length);
			for(int i=0;i!=oldFields.length;++i) {
				Pair<Identifier, Expr> field = oldFields[i];
				if(e.getField().equals(field.getFirst())) {
					newFields[i] = new Pair<>(field.getFirst(),nValue);
				}
			}
			return new Expr.RecordInitialiser(newFields);
		}
		//
		if(source == nSource && value == nValue) {
			return e;
		} else {
			return new Expr.RecordUpdate(nSource, e.getField(), nValue);
		}
	}

	public Expr simplifyDereference(Expr.Dereference e) throws ResolutionError {
		Expr source = e.getOperand();
		Expr nSource = simplifyExpression(source);
		if (source == nSource) {
			return e;
		} else {
			return new Expr.Dereference(nSource);
		}
	}

	public Expr simplifyInvoke(Expr.Invoke ivk) throws ResolutionError {
		Tuple<Expr> args = ivk.getArguments();
		Expr[] nChildren = new Expr[args.size()];
		boolean changed = false;
		for (int i = 0; i != args.size(); ++i) {
			Expr child = args.get(i);
			Expr nChild = simplifyExpression(child);
			//
			changed |= (child != nChild);
			nChildren[i] = nChild;
		}
		if(!changed) {
			return ivk;
		} else {
			Tuple<Expr> nArgs = new Tuple<>(nChildren);
			return new Expr.Invoke(ivk.getSignatureType(),ivk.getName(),ivk.getSelector(),nArgs);
		}
	}

	public Expr simplifyArrayIndex(Expr.Operator e) throws ResolutionError {
		Expr source = e.get(0);
		Expr index = e.get(1);
		Expr nSource = simplifyExpression(source);
		Expr nIndex = simplifyExpression(index);
		//
		if (nSource instanceof Expr.Operator && nIndex instanceof Expr.Constant) {
			// We may have a constant index value into a constant array
			Expr.Operator arr = (Expr.Operator) nSource;
			if (arr.getOpcode() == EXPR_arrinit) {
				// We definitely have a constant index value into a constant
				// array
				BigInteger i = ((Value.Int) ((Expr.Constant) nIndex).getValue()).get();
				if (i.compareTo(BigInteger.ZERO) >= 0 && i.compareTo(BigInteger.valueOf(arr.size())) < 0) {
					// The constant index is within bounds
					return arr.get(i.intValue());
				}
			}
		}
		if(nSource.getOpcode() == EXPR_arrgen) {
			return (Expr) nSource.get(0);
		}
		// If we get here, then no simplification of the array access expression
		// was possible.
		if (source == nSource && index == nIndex) {
			return e;
		} else {
			return new Expr.ArrayAccess(nSource, nIndex);
		}
	}

	public Expr simplifyArrayUpdate(Expr.Operator e) throws ResolutionError {
		Expr source = e.get(0);
		Expr index = e.get(1);
		Expr value = e.get(2);
		Expr nSource = simplifyExpression(source);
		Expr nIndex = simplifyExpression(index);
		Expr nValue = simplifyExpression(value);
		//
		if(nIndex instanceof Expr.Constant && nSource.getOpcode() == EXPR_arrinit) {
			Expr.Operator src = (Expr.Operator) nSource;
			BigInteger b = ((Value.Int) ((Expr.Constant) nIndex).getValue()).get();
			if(b.compareTo(BigInteger.ZERO) >= 0 && b.compareTo(BigInteger.valueOf(nSource.size())) < 0) {
				int idx = b.intValue();
				Expr[] nChildren = Arrays.copyOf(src.getAll(),src.size());
				nChildren[idx] = nValue;
				return src.clone(nChildren);
			}
		}
		if (source == nSource && index == nIndex && value == nValue) {
			return e;
		} else {
			return new Expr.ArrayUpdate(nSource, nIndex, nValue);
		}
	}

	public Expr simplifyArrayLength(Expr.Operator e) throws ResolutionError {
		Expr r = simplifyNonArithmetic(e);
		if (r instanceof Expr.Operator) {
			Expr src = (Expr) r.get(0);
			if (src.getOpcode() == EXPR_arrinit) {
				return new Expr.Constant(new Value.Int(src.size()));
			} else if (src.getOpcode() == EXPR_arrgen) {
				return (Expr) src.get(1);
			} else if (src.getOpcode() == EXPR_arrupdt) {
				return simplifyArrayLength(new Expr.ArrayLength((Expr) src.get(0)));
			}
		}
		return r;
	}

	public Expr simplifyNonArithmetic(Expr.Operator e) throws ResolutionError {
		Expr[] children = e.getAll();
		Expr[] nChildren = simplifyExpressions(children);

		if (nChildren == children) {
			return e;
		} else {
			// FIXME: there are further simplifications that can be performed
			// here. For example, taking the field of a constant record;
			// likewise, taking a constant index into a constant array. Although
			// unlikely, they can arise through the use of e.g. configuration
			// constants, etc.
			return e.clone(nChildren);
		}
	}

	public Expr simplifyArithmetic(Expr.Operator e) throws ResolutionError {
		Expr[] children = e.getAll();
		Polynomial result = Arithmetic.asPolynomial(simplifyExpression(children[0]));
		switch (e.getOpcode()) {
		case EXPR_add: {
			for (int i = 1; i != children.length; ++i) {
				result = result.add(Arithmetic.asPolynomial(simplifyExpression(children[i])));
			}
			break;
		}
		case EXPR_sub: {
			for (int i = 1; i != children.length; ++i) {
				result = result.subtract(Arithmetic.asPolynomial(simplifyExpression(children[i])));
			}
			break;
		}
		case EXPR_mul: {
			for (int i = 1; i != children.length; ++i) {
				result = result.multiply(Arithmetic.asPolynomial(simplifyExpression(children[i])));
			}
			break;
		}
		case EXPR_neg: {
			result = result.negate();
			break;
		}
		default:
			throw new IllegalArgumentException("Unknown arithmetic opcode encountered");
		}
		return result.toExpression();
	}

	// ========================================================================
	// Equalities / Inequalities
	// ========================================================================

	/**
	 * Evaluate a given inequality whose bounds are known to be constant integer
	 * values. For example, <code>1 < 0</code> evaluates to <code>false</code>,
	 * etc.
	 *
	 * @param opcode
	 * @param lhs
	 * @param rhs
	 * @return
	 */
	public Formula.Truth evaluateInequality(int opcode, Value.Int lhs, Value.Int rhs) {
		boolean result;
		switch (opcode) {
		case EXPR_lt:
			result = lhs.compareTo(rhs) < 0;
			break;
		case EXPR_lteq:
			result = lhs.compareTo(rhs) <= 0;
			break;
		case EXPR_gt:
			result = lhs.compareTo(rhs) > 0;
			break;
		case EXPR_gteq:
			result = lhs.compareTo(rhs) >= 0;
			break;
		default:
			throw new IllegalArgumentException("Invalid inequality opcode: " + opcode);
		}
		return new Formula.Truth(result);
	}

	/**
	 * Evaluate a given equality whose bounds are known to be constant values of
	 * some sort. For example, <code>true == false</code> evaluates to
	 * <code>false</code>, etc.
	 *
	 * @param opcode
	 * @param lhs
	 * @param rhs
	 * @return
	 */
	public Formula.Truth evaluateEquality(int opcode, Value lhs, Value rhs) {
		boolean result;
		switch (opcode) {
		case EXPR_eq:
			result = lhs.equals(rhs);
			break;
		case EXPR_neq:
			result = !(lhs.equals(rhs));
			break;
		default:
			throw new IllegalArgumentException("Invalid equality opcode: " + opcode);
		}
		return new Formula.Truth(result);
	}

	/**
	 * Normalise bounds of an equation to be positive. For example, consider the
	 * inequality <code>x < y - z</code>. In this case, the right-hand side is
	 * not simplifyd because it contains a negative term. The simplifyd
	 * version of this inequality would be <code>x + z < y</code>.
	 *
	 * @param lhs
	 * @param rhs
	 * @return
	 */
	public Pair<Expr, Expr> normaliseBounds(Expr lhs, Expr rhs) {
		Polynomial left = Arithmetic.asPolynomial(lhs);
		Polynomial right = Arithmetic.asPolynomial(rhs);
		Polynomial bound = left.subtract(right).factorise();
		//
		Polynomial pos = filter(bound, true);
		Polynomial neg = filter(bound, false);
		return new Pair<>(pos.toExpression(), neg.toExpression());
	}

	public Polynomial filter(Polynomial p, boolean sign) {
		Polynomial result = Polynomial.ZERO;
		for (int i = 0; i != p.size(); ++i) {
			Polynomial.Term term = p.getTerm(i);
			BigInteger coefficient = term.getCoefficient();
			int c = coefficient.compareTo(BigInteger.ZERO);
			if (sign && c >= 0) {
				result = result.add(term);
			} else if (!sign && c < 0) {
				result = result.subtract(term);
			}
		}
		return result;
	}


	private Formula[] inlineNestedDisjuncts(Formula[] children) {
		Formula[] nChildren = children;
		for(int i=0;i!=nChildren.length;++i) {
			Formula child = nChildren[i];
			if(child instanceof Formula.Disjunct) {
				// We found a nested disjunct!
				Formula.Disjunct disjunct = (Formula.Disjunct) child;
				Formula[] nested = disjunct.getAll();
				// Inline the nested disjunct's operands
				nChildren = inlineNestedArray(nChildren,i,nested);
				// Can safely skip all elements in nested since disjunct already
				// in simplified form by construction.
				i += (nested.length - 1);
			}
		}
		return nChildren;
	}

	private Formula[] inlineNestedConjuncts(Formula[] children) {
		Formula[] nChildren = children;
		for (int i = 0; i != nChildren.length; ++i) {
			Formula child = nChildren[i];
			if (child instanceof Formula.Conjunct) {
				// We found a nested conjunct!
				Formula.Conjunct conjunct = (Formula.Conjunct) child;
				Formula[] nested = conjunct.getAll();
				// Inline the nested conjunct's operands
				nChildren = inlineNestedArray(nChildren, i, nested);
				// Can safely skip all elements in nested since conjunct already
				// in simplified form by construction.
				i += (nested.length - 1);
			}
		}
		return nChildren;
	}

	public <T> Formula[] inlineNestedArray(Formula[] parent, int index, Formula[] child) {
		Formula[] types = new Formula[parent.length + child.length - 1];
		System.arraycopy(parent, 0, types, 0, index);
		System.arraycopy(child, 0, types, index, child.length);
		System.arraycopy(parent, index + 1, types, index + child.length, parent.length - (index + 1));
		return types;
	}
}
