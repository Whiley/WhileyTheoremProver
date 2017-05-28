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
package wytp.types.util;

import wyal.lang.NameResolver.ResolutionError;
import wyal.lang.WyalFile.Expr;
import wyal.lang.WyalFile.FieldDeclaration;
import wyal.lang.WyalFile.Identifier;
import wyal.lang.WyalFile.Pair;
import wyal.lang.WyalFile.Tuple;
import wyal.lang.WyalFile.Type;
import wyal.lang.WyalFile.Value;
import wycc.util.ArrayUtils;
import wytp.types.TypeInferer;
import wytp.types.TypeSystem;

/**
 * A simple type inference for expressions found in WyalFiles.
 *
 * @author David J. Pearce
 *
 */
public class StdTypeInfererence implements TypeInferer {
	private final TypeSystem types;

	public StdTypeInfererence(TypeSystem types) {
		this.types = types;
	}

	@Override
	public Type getInferredType(Environment environment, Expr expression) throws ResolutionError {
		return inferExpression(environment, expression);
	}

	protected Type inferExpression(Environment environment, Expr expr) throws ResolutionError {
		switch (expr.getOpcode()) {
		case EXPR_const:
			return inferConstant(environment, (Expr.Constant) expr);
		case EXPR_cast:
			return inferCast(environment, (Expr.Cast) expr);
		case EXPR_invoke:
			return inferInvoke(environment, (Expr.Invoke) expr);
		case EXPR_var:
			return inferVariableAccess(environment, (Expr.VariableAccess) expr);
		case EXPR_not:
		case EXPR_and:
		case EXPR_or:
		case EXPR_implies:
		case EXPR_iff:
		case EXPR_eq:
		case EXPR_neq:
		case EXPR_lt:
		case EXPR_lteq:
		case EXPR_gt:
		case EXPR_gteq:
			return inferLogicalOperator(environment, (Expr.Operator) expr);
		case EXPR_forall:
		case EXPR_exists:
			return inferQuantifier(environment, (Expr.Quantifier) expr);
		case EXPR_neg:
		case EXPR_add:
		case EXPR_sub:
		case EXPR_mul:
		case EXPR_div:
		case EXPR_rem:
			return inferArithmeticOperator(environment, (Expr.Operator) expr);
		case EXPR_arrlen:
			return inferArrayLength(environment, (Expr.Operator) expr);
		case EXPR_arrinit:
			return inferArrayInitialiser(environment, (Expr.Operator) expr);
		case EXPR_arrgen:
			return inferArrayGenerator(environment, (Expr.Operator) expr);
		case EXPR_arridx:
			return inferArrayIndex(environment, (Expr.Operator) expr);
		case EXPR_arrupdt:
			return inferArrayUpdate(environment, (Expr.Operator) expr);
		case EXPR_recinit:
			return inferRecordInitialiser(environment, (Expr.RecordInitialiser) expr);
		case EXPR_recfield:
			return inferRecordAccess(environment, (Expr.RecordAccess) expr);
		case EXPR_recupdt:
			return inferRecordUpdate(environment, (Expr.RecordUpdate) expr);
		case EXPR_deref:
			return inferDereference(environment, (Expr.Dereference) expr);
		default:
			throw new IllegalArgumentException("invalid expression encountered: " + expr);
		}
	}

	protected Type inferCast(Environment environment, Expr.Cast expr) {
		return (Type) expr.getCastType();
	}

	protected Type inferLogicalOperator(Environment environment, Expr.Operator expr) throws ResolutionError {
		return new Type.Bool();
	}

	protected Type inferArithmeticOperator(Environment environment, Expr.Operator expr) throws ResolutionError {
		return new Type.Int();
	}

	protected Type inferVariableAccess(Environment environment, Expr.VariableAccess expr) {
		return environment.getType(expr.getVariableDeclaration());
	}

	protected Type inferConstant(Environment environment, Expr.Constant expr) {
		return expr.getValue().getType();
	}

	protected Type inferIs(Environment environment, Expr.Is expr) {
		return new Type.Bool();
	}

	protected Type inferInvoke(Environment environment, Expr.Invoke expr) {
		Type.FunctionOrMacroOrInvariant type = expr.getSignatureType();
		Tuple<Type> returns = type.getReturns();
		Value.Int selector = expr.getSelector();

		if (selector == null && returns.size() != 1) {
			throw new IllegalArgumentException("need support for multiple returns");
		} else if(selector == null) {
			return returns.getOperand(0);
		} else {
			return returns.getOperand(selector.get().intValue());
		}
	}

	protected Type inferQuantifier(Environment environment, Expr.Quantifier expr) {
		return new Type.Bool();
	}

	// ======================================================================
	// Arrays
	// ======================================================================

	protected Type inferArrayLength(Environment environment, Expr.Operator expr) {
		return new Type.Int();
	}

	protected Type inferArrayInitialiser(Environment environment, Expr.Operator expr) throws ResolutionError {
		if (expr.size() > 0) {
			Type[] ts = new Type[expr.size()];
			for (int i = 0; i != ts.length; ++i) {
				ts[i] = inferExpression(environment, expr.getOperand(i));
			}
			// Perform a little simplification here by collapsing
			// identical types together.
			ts = ArrayUtils.removeDuplicates(ts);
			Type element = ts.length == 1 ? ts[0] : new Type.Union(ts);
			return new Type.Array(element);
		} else {
			return new Type.Array(new Type.Void());
		}
	}

	protected Type inferArrayGenerator(Environment environment, Expr.Operator expr) throws ResolutionError {
		Type element = inferExpression(environment, expr.getOperand(0));
		return new Type.Array(element);
	}

	protected Type inferArrayIndex(Environment environment, Expr.Operator expr) throws ResolutionError {
		Type src = inferExpression(environment, expr.getOperand(0));
		if(src != null) {
			Type.Array effectiveArray = types.extractReadableArray(src);
			if(effectiveArray != null) {
				return effectiveArray.getElement();
			}
		}
		return null;
	}

	protected Type inferArrayUpdate(Environment environment, Expr.Operator expr) throws ResolutionError {
		return inferExpression(environment, expr.getOperand(0));
	}

	protected Type inferRecordAccess(Environment environment, Expr.RecordAccess expr) throws ResolutionError {
		Type src = inferExpression(environment, expr.getSource());
		if (src != null) {
			Type.Record effectiveRecord = types.extractReadableRecord(src);
			if (effectiveRecord != null) {
				FieldDeclaration[] fields = effectiveRecord.getFields();
				String actualFieldName = expr.getField().get();
				for (int i = 0; i != fields.length; ++i) {
					FieldDeclaration vd = fields[i];
					String declaredFieldName = vd.getVariableName().get();
					if (declaredFieldName.equals(actualFieldName)) {
						return vd.getType();
					}
				}
			}
		}
		//
		return null;
	}

	protected Type inferRecordUpdate(Environment environment, Expr.RecordUpdate expr) throws ResolutionError {
		return inferExpression(environment, expr.getSource());
	}

	protected Type inferRecordInitialiser(Environment environment, Expr.RecordInitialiser expr) throws ResolutionError {
		Pair<Identifier, Expr>[] fields = expr.getFields();
		FieldDeclaration[] decls = new FieldDeclaration[fields.length];
		for (int i = 0; i != fields.length; ++i) {
			Identifier fieldName = fields[i].getFirst();
			Type fieldType = inferExpression(environment, fields[i].getSecond());
			decls[i] = new FieldDeclaration(fieldType, fieldName);
		}
		// NOTE: a record initialiser never produces an open record
		// type. But definition, an initialiser always produces a closed
		// (i.e. concrete) type.
		return new Type.Record(false, decls);
	}

	// ======================================================================
	// References
	// ======================================================================

	protected Type inferDereference(Environment environment, Expr.Dereference expr) throws ResolutionError {
		Type src = inferExpression(environment, expr.getOperand());
		if(src != null) {
			Type.Reference effectiveReference = types.extractReadableReference(src);
			if(effectiveReference != null) {
				return effectiveReference.getElement();
			}
		}
		return null;
	}
}
