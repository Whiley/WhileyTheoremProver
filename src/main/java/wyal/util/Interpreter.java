package wyal.util;

import java.math.BigInteger;
import java.util.Arrays;
import java.util.Comparator;
import java.util.IdentityHashMap;
import java.util.List;
import java.util.Map;
import java.util.Objects;

import wyal.lang.Domain;

import static wyal.lang.WyalFile.*;
import wyal.lang.WyalFile;
import wyal.lang.WyalFile.Stmt.Block;
import wybs.lang.NameResolver;
import wybs.lang.NameResolver.NameNotFoundError;
import wybs.lang.NameResolver.ResolutionError;
import wytp.types.extractors.TypeInvariantExtractor;

public class Interpreter {
	private final Domain domain;
	private final NameResolver resolver;
	private final TypeInvariantExtractor extractor;

	public Interpreter(Domain domain, NameResolver resolver, TypeInvariantExtractor extractor) {
		this.domain = domain;
		this.resolver = resolver;
		this.extractor = extractor;
	}

	public Result evaluate(Declaration.Assert a) throws UndefinedException {
		return evaluateBlock(a.getBody(),new Environment(domain));
	}

	protected Result evaluateBlock(Block block, Environment environment) throws UndefinedException {
		for(int i=0;i!=block.size();++i) {
			Result r = evaluateStatement(block.get(i),environment);
			if(!r.holds()) {
				return r;
			}
		}
		return new Result(environment,true);
	}

	protected Result evaluateStatement(Stmt stmt, Environment environment) throws UndefinedException {
		switch(stmt.getOpcode()) {
		case WyalFile.STMT_block:
			return evaluateBlock((Stmt.Block)stmt,environment);
		case WyalFile.STMT_ifthen:
			return evaluateIfThen((Stmt.IfThen)stmt,environment);
		case WyalFile.STMT_caseof:
			return evaluateCaseOf((Stmt.CaseOf)stmt,environment);
		case WyalFile.STMT_exists:
			return evaluateExists((Stmt.ExistentialQuantifier)stmt,environment);
		case WyalFile.STMT_forall:
			return evaluateForAll((Stmt.UniversalQuantifier)stmt,environment);
		default:
			if (stmt instanceof Expr) {
				boolean b = (Boolean) evaluateExpression((Expr) stmt, environment);
				return new Result(environment,b);
			} else {
				throw new RuntimeException("unknown statement encountered " + stmt.getClass().getName());
			}
		}
	}

	protected Result evaluateIfThen(Stmt.IfThen stmt, Environment environment) throws UndefinedException {
		Result r = evaluateStatement(stmt.getIfBody(),environment);
		if(r.holds()) {
			return evaluateStatement(stmt.getThenBody(),environment);
		} else {
			return new Result(environment,true);
		}
	}

	protected Result evaluateCaseOf(Stmt.CaseOf stmt, Environment environment) throws UndefinedException {
		for(int i=0;i!=stmt.size();++i) {
			Block block = stmt.get(i);
			Result r = evaluateBlock(block,environment);
			if(r.holds()) {
				return r;
			}
		}
		return new Result(environment,false);
	}

	protected Result evaluateExists(Stmt.ExistentialQuantifier stmt, Environment environment) {
		Tuple<VariableDeclaration> vars = stmt.getParameters();
		for(Environment nEnv : environment.declare(vars)) {
			try {
				checkTypeInvariants(vars,nEnv);
				Result r = evaluateBlock(stmt.getBody(), nEnv);
				if (r.holds()) {
					return r;
				}
			} catch (UndefinedException e) {
				continue;
			}
		}
		return new Result(environment,false);
	}

	protected Result evaluateForAll(Stmt.UniversalQuantifier stmt, Environment environment) {
		Tuple<VariableDeclaration> vars = stmt.getParameters();
		for(Environment nEnv : environment.declare(vars)) {
			try {
				checkTypeInvariants(vars,nEnv);
				Result r = evaluateBlock(stmt.getBody(), nEnv);
				if (!r.holds()) {
					return r;
				}
			} catch (UndefinedException e) {
				continue;
			}
		}
		return new Result(environment,true);
	}

	protected Object evaluateExpression(Expr expr, Environment environment) throws UndefinedException {

		switch (expr.getOpcode()) {
		case WyalFile.EXPR_const:
			return evaluateConstant((Expr.Constant) expr, environment);
		case WyalFile.EXPR_varcopy:
			return evaluateVariable((Expr.VariableAccess) expr, environment);
		case WyalFile.EXPR_invoke:
			return evaluateInvoke((Expr.Invoke) expr, environment);
		case WyalFile.EXPR_and:
			return evaluateLogicalAnd((Expr.LogicalAnd) expr,environment);
		case WyalFile.EXPR_or:
			return evaluateLogicalOr((Expr.LogicalOr) expr,environment);
		case WyalFile.EXPR_not:
			return evaluateLogicalNot((Expr.LogicalNot) expr,environment);
		case WyalFile.EXPR_exists:
			return evaluateExistentialQuantifier((Expr.ExistentialQuantifier) expr,environment);
		case WyalFile.EXPR_forall:
			return evaluateUniversalQuantifier((Expr.UniversalQuantifier) expr,environment);
		case WyalFile.EXPR_implies:
			return evaluateLogicalImplication((Expr.LogicalImplication) expr,environment);
		case WyalFile.EXPR_iff:
			return evaluateLogicalIff((Expr.LogicalIff) expr,environment);
		case WyalFile.EXPR_eq:
			return evaluateEqual((Expr.Equal) expr,environment);
		case WyalFile.EXPR_neq:
			return evaluateNotEqual((Expr.NotEqual) expr,environment);
		case WyalFile.EXPR_neg:
			return evaluateNegation((Expr.Negation) expr,environment);
		case WyalFile.EXPR_lt:
			return evaluateLessThan((Expr.LessThan) expr,environment);
		case WyalFile.EXPR_lteq:
			return evaluateLessThanOrEqual((Expr.LessThanOrEqual) expr,environment);
		case WyalFile.EXPR_gt:
			return evaluateGreaterThan((Expr.GreaterThan) expr,environment);
		case WyalFile.EXPR_gteq:
			return evaluateGreaterThanOrEqual((Expr.GreaterThanOrEqual) expr,environment);
		case WyalFile.EXPR_add:
			return evaluateAddition((Expr.Addition) expr,environment);
		case WyalFile.EXPR_sub:
			return evaluateSubtraction((Expr.Subtraction) expr,environment);
		case WyalFile.EXPR_mul:
			return evaluateMultiplication((Expr.Multiplication) expr,environment);
		case WyalFile.EXPR_div:
			return evaluateDivision((Expr.Division) expr,environment);
		case WyalFile.EXPR_is:
			return evaluateIs((Expr.Is) expr,environment);
		case WyalFile.EXPR_arrlen:
			return evaluateArrayLength((Expr.ArrayLength) expr,environment);
		case WyalFile.EXPR_arridx:
			return evaluateArrayAccess((Expr.ArrayAccess) expr,environment);
		case WyalFile.EXPR_arrinit:
			return evaluateArrayInitialiser((Expr.ArrayInitialiser) expr,environment);
		case WyalFile.EXPR_arrupdt:
			return evaluateArrayUpdate((Expr.ArrayUpdate) expr,environment);
		case WyalFile.EXPR_arrgen:
			return evaluateArrayGenerator((Expr.ArrayGenerator) expr,environment);
		case WyalFile.EXPR_recinit:
			return evaluateRecordInitialiser((Expr.RecordInitialiser) expr,environment);
		case WyalFile.EXPR_recfield:
			return evaluateRecordAccess((Expr.RecordAccess) expr,environment);
		case WyalFile.EXPR_recupdt:
			return evaluateRecordUpdate((Expr.RecordUpdate) expr,environment);
		default:
			throw new RuntimeException("unknown expression encountered: " + expr.getClass().getName());
		}
	}

	protected Object evaluateConstant(Expr.Constant expr, Environment environment) {
		Value value = expr.getValue();
		if (value instanceof Value.Null) {
			return null;
		} else if (value instanceof Value.Bool) {
			Value.Bool b = (Value.Bool) value;
			return b.get();
		} else {
			Value.Int i = (Value.Int) value;
			return i.get();
		}
	}

	protected Object evaluateVariable(Expr.VariableAccess expr, Environment environment) {
		return environment.read(expr);
	}

	protected Object evaluateInvoke(Expr.Invoke expr, Environment environment) throws UndefinedException {
		Tuple<Expr> arguments = expr.getArguments();
		Object[] argumentValues = new Object[arguments.size()];
		for(int i=0;i!=argumentValues.length;++i) {
			argumentValues[i] = evaluateExpression(arguments.get(i),environment);
		}
		//
		Declaration.Named decl = resolve(expr);
		//
		Tuple<VariableDeclaration> parameters = decl.getParameters();
		Environment localEnvironment = new Environment(environment.domain);
		for(int i=0;i!=parameters.size();++i) {
			VariableDeclaration d = parameters.get(i);
			localEnvironment.values.put(d, argumentValues[i]);
		}
		//
		if(decl instanceof Declaration.Named.Macro) {
			Declaration.Named.Macro macro = (Declaration.Named.Macro) decl;
			return evaluateBlock(macro.getBody(),localEnvironment).value;
		} else {
			Declaration.Named.Type type = (Declaration.Named.Type) decl;
			Tuple<Block> invariant = type.getInvariant();
			for(int i=0;i!=invariant.size();++i) {
				if (!evaluateBlock(invariant.get(i), localEnvironment).value) {
					return false;
				}
			}
			return true;
		}
	}

	protected Declaration.Named resolve(Expr.Invoke ivk) {
		Type.FunctionOrMacroOrInvariant signature = ivk.getSignatureType();
		//
		try {
			if (signature instanceof Type.Property) {
				// We need to find the property in question so that we can
				// evaluate it and see what's going on.
				List<Declaration.Named.Macro> candidates = resolver.resolveAll(ivk.getName(),
						Declaration.Named.Macro.class);
				// Look for matching signature
				for (int i = 0; i != candidates.size(); ++i) {
					Declaration.Named.Macro macro = candidates.get(i);
					if (macro.getSignatureType().equals(signature)) {
						return macro;
					}
				}
				// Should really be impossible to get here
				throw new NameNotFoundError(ivk.getName());
			} else if (signature instanceof Type.Function) {
				// What we need to do here is look at the return type and return
				// something sensible. Or we could preiterate all function
				// invocations beforehand.
				throw new RuntimeException("UNKNOWN");
			} else {
				// Must be a type declaration
				return resolver.resolveExactly(ivk.getName(), Declaration.Named.Type.class);
			}
		} catch(NameResolver.ResolutionError e) {
			throw new RuntimeException(e);
		}
	}

	protected boolean evaluateLogicalAnd(Expr.LogicalAnd conjunct, Environment environment) throws UndefinedException {
		for(int i=0;i!=conjunct.size();++i) {
			Expr child = conjunct.get(i);
			boolean b = (Boolean) evaluateExpression(child,environment);
			if(!b) {
				return false;
			}
		}
		return true;
	}

	protected boolean evaluateLogicalOr(Expr.LogicalOr disjunct, Environment environment) throws UndefinedException {
		for (int i = 0; i != disjunct.size(); ++i) {
			Expr child = disjunct.get(i);
			boolean b = (Boolean) evaluateExpression(child, environment);
			if (b) {
				return true;
			}
		}
		return false;
	}

	protected boolean evaluateLogicalNot(Expr.LogicalNot expr, Environment environment) throws UndefinedException {
		boolean b = (Boolean) evaluateExpression(expr.getOperand(),environment);
		return !b;
	}

	protected boolean evaluateLogicalImplication(Expr.LogicalImplication expr, Environment environment) throws UndefinedException {
		boolean lhs = (Boolean) evaluateExpression(expr.get(0),environment);
		boolean rhs = (Boolean) evaluateExpression(expr.get(1),environment);
		return (!lhs) || rhs;
	}

	protected boolean evaluateLogicalIff(Expr.LogicalIff expr, Environment environment) throws UndefinedException {
		boolean lhs = (Boolean) evaluateExpression(expr.get(0),environment);
		boolean rhs = (Boolean) evaluateExpression(expr.get(1),environment);
		return lhs == rhs;
	}

	protected boolean evaluateExistentialQuantifier(Expr.ExistentialQuantifier stmt, Environment environment) {
		Tuple<VariableDeclaration> vars = stmt.getParameters();
		for(Environment nEnv : environment.declare(vars)) {
			try {
				checkTypeInvariants(vars,nEnv);
				boolean b = (Boolean) evaluateExpression(stmt.getBody(),nEnv);
				if(b) {
					return true;
				}
			} catch (UndefinedException e) {
				continue;
			}
		}
		return false;
	}

	protected boolean evaluateUniversalQuantifier(Expr.UniversalQuantifier stmt, Environment environment) {
		Tuple<VariableDeclaration> vars = stmt.getParameters();
		for(Environment nEnv : environment.declare(vars)) {
			try {
				checkTypeInvariants(vars,nEnv);
				boolean b = (Boolean) evaluateExpression(stmt.getBody(), nEnv);
				if (!b) {
					return false;
				}
			} catch (UndefinedException e) {
				continue;
			}
		}
		return true;
	}
	protected boolean evaluateEqual(Expr.Equal expr, Environment environment) throws UndefinedException {
		Object lhs = evaluateExpression(expr.get(0), environment);
		Object rhs = evaluateExpression(expr.get(1), environment);
		return equals(lhs,rhs);
	}

	protected boolean evaluateNotEqual(Expr.NotEqual expr, Environment environment) throws UndefinedException {
		Object lhs = evaluateExpression(expr.get(0), environment);
		Object rhs = evaluateExpression(expr.get(1), environment);
		return !equals(lhs,rhs);
	}

	protected boolean equals(Object lhs, Object rhs) {
		if(lhs instanceof Object[]) {
			if(rhs instanceof Object[]) {
				return equalsArray((Object[])lhs,(Object[])rhs);
			} else {
				return false;
			}
		} else if(lhs instanceof Record) {
			if(rhs instanceof Record) {
				return equalsRecord((Record)lhs,(Record)rhs);
			} else {
				return false;
			}
		} else if(lhs == null) {
			return rhs == null;
		} else {
			return lhs.equals(rhs);
		}
	}

	protected boolean equalsArray(Object[] lhs, Object[] rhs) {
		if (lhs.length != rhs.length) {
			return false;
		} else {
			for (int i = 0; i != lhs.length; ++i) {
				if (!equals(lhs[i], rhs[i])) {
					return false;
				}
			}
			return true;
		}
	}

	protected boolean equalsRecord(Record lhs, Record rhs) {
		if (Arrays.equals(lhs.fields, rhs.fields)) {
			Identifier[] fields = lhs.fields;
			for (int i = 0; i != fields.length; ++i) {
				if(!equals(lhs.values[i],rhs.values[i])) {
					return false;
				}
			}
			return true;
		}
		return false;
	}

	protected boolean evaluateLessThan(Expr.LessThan expr, Environment environment) throws UndefinedException {
		BigInteger lhs = (BigInteger) evaluateExpression(expr.get(0), environment);
		BigInteger rhs = (BigInteger) evaluateExpression(expr.get(1), environment);
		return lhs.compareTo(rhs) < 0;
	}

	protected boolean evaluateLessThanOrEqual(Expr.LessThanOrEqual expr, Environment environment) throws UndefinedException {
		BigInteger lhs = (BigInteger) evaluateExpression(expr.get(0), environment);
		BigInteger rhs = (BigInteger) evaluateExpression(expr.get(1), environment);
		return lhs.compareTo(rhs) <= 0;
	}

	protected boolean evaluateGreaterThan(Expr.GreaterThan expr, Environment environment) throws UndefinedException {
		BigInteger lhs = (BigInteger) evaluateExpression(expr.get(0), environment);
		BigInteger rhs = (BigInteger) evaluateExpression(expr.get(1), environment);
		return lhs.compareTo(rhs) > 0;
	}

	protected boolean evaluateGreaterThanOrEqual(Expr.GreaterThanOrEqual expr, Environment environment) throws UndefinedException {
		BigInteger lhs = (BigInteger) evaluateExpression(expr.get(0), environment);
		BigInteger rhs = (BigInteger) evaluateExpression(expr.get(1), environment);
		return lhs.compareTo(rhs) >= 0;
	}

	protected Object evaluateNegation(Expr.Negation expr, Environment environment) throws UndefinedException {
		BigInteger value = (BigInteger) evaluateExpression(expr.get(0), environment);
		return value.negate();
	}

	protected Object evaluateAddition(Expr.Addition expr, Environment environment) throws UndefinedException {
		BigInteger value = (BigInteger) evaluateExpression(expr.get(0), environment);
		for (int i = 1; i != expr.size(); ++i) {
			BigInteger next = (BigInteger) evaluateExpression(expr.get(1), environment);
			value = value.add(next);
		}
		return value;
	}

	protected Object evaluateSubtraction(Expr.Subtraction expr, Environment environment) throws UndefinedException {
		BigInteger value = (BigInteger) evaluateExpression(expr.get(0), environment);
		for (int i = 1; i != expr.size(); ++i) {
			BigInteger next = (BigInteger) evaluateExpression(expr.get(1), environment);
			value = value.subtract(next);
		}
		return value;
	}

	protected Object evaluateMultiplication(Expr.Multiplication expr, Environment environment) throws UndefinedException {
		BigInteger value = (BigInteger) evaluateExpression(expr.get(0), environment);
		for (int i = 1; i != expr.size(); ++i) {
			BigInteger next = (BigInteger) evaluateExpression(expr.get(1), environment);
			value = value.multiply(next);
		}
		return value;
	}

	protected Object evaluateDivision(Expr.Division expr, Environment environment) throws UndefinedException {
		BigInteger value = (BigInteger) evaluateExpression(expr.get(0), environment);
		for (int i = 1; i != expr.size(); ++i) {
			BigInteger next = (BigInteger) evaluateExpression(expr.get(1), environment);
			if (next == BigInteger.ZERO) {
				throw new UndefinedException("division by zero");
			}
			value = value.divide(next);
		}
		return value;
	}

	protected Object evaluateIs(Expr.Is expr, Environment environment) throws UndefinedException {
		try {
			Object value = evaluateExpression(expr.getTestExpr(), environment);
			Type type = expr.getTestType();
			return isInstance(value,type);
		} catch(NameResolver.ResolutionError e) {
			throw new RuntimeException(e);
		}
	}

	protected Object evaluateArrayAccess(Expr.ArrayAccess expr, Environment environment) throws UndefinedException {
		Object[] source = (Object[]) evaluateExpression(expr.getSource(), environment);
		BigInteger index = (BigInteger) evaluateExpression(expr.getSubscript(), environment);
		int idx = index.intValue();
		if(idx < 0 || idx >= source.length) {
			throw new UndefinedException("index out-of-bounds");
		}
		return source[index.intValue()];
	}

	protected Object evaluateArrayLength(Expr.ArrayLength expr, Environment environment) throws UndefinedException {
		Object[] source = (Object[]) evaluateExpression(expr.getSource(), environment);
		return BigInteger.valueOf(source.length);
	}

	protected Object evaluateArrayInitialiser(Expr.ArrayInitialiser expr, Environment environment)
			throws UndefinedException {
		Object[] arr = new Object[expr.size()];
		for (int i = 0; i != arr.length; ++i) {
			arr[i] = evaluateExpression(expr.get(i), environment);
		}
		return arr;
	}

	protected Object evaluateArrayGenerator(Expr.ArrayGenerator expr, Environment environment) throws UndefinedException {
		Object value = evaluateExpression(expr.getValue(), environment);
		int length = ((BigInteger) evaluateExpression(expr.getLength(), environment)).intValue();
		if(length < 0) {
			throw new UndefinedException("negative array length");
		} else {
			Object[] arr = new Object[length];
			for (int i = 0; i != length; ++i) {
				arr[i] = value;
			}
			return arr;
		}
	}

	protected Object evaluateArrayUpdate(Expr.ArrayUpdate expr, Environment environment) throws UndefinedException {
		Object[] source = (Object[]) evaluateExpression(expr.getSource(), environment);
		int index = ((BigInteger) evaluateExpression(expr.getSubscript(), environment)).intValue();
		Object value = evaluateExpression(expr.getValue(), environment);
		source = Arrays.copyOf(source, source.length);
		source[index] = value;
		return source;
	}

	protected Object evaluateRecordInitialiser(Expr.RecordInitialiser expr, Environment environment)
			throws UndefinedException {
		WyalFile.Pair<Identifier, Expr>[] fieldAssignments = expr.getFields();
		Arrays.sort(fieldAssignments, fieldComparator);
		Identifier[] fields = new Identifier[fieldAssignments.length];
		Object[] values = new Object[fieldAssignments.length];
		for (int i = 0; i != fieldAssignments.length; ++i) {
			WyalFile.Pair<Identifier, Expr> p = fieldAssignments[i];
			fields[i] = p.getFirst();
			values[i] = evaluateExpression(p.getSecond(), environment);
		}
		return new Record(fields, values);
	}
	protected Object evaluateRecordAccess(Expr.RecordAccess expr, Environment environment) throws UndefinedException {
		Record source = (Record) evaluateExpression(expr.getSource(), environment);
		return source.getField(expr.getField());
	}
	protected Object evaluateRecordUpdate(Expr.RecordUpdate expr, Environment environment)
			throws UndefinedException {
		Record source = (Record) evaluateExpression(expr.getSource(), environment);
		Object value = evaluateExpression(expr.getValue(),environment);
		return source.setField(expr.getField(), value);
	}

	private static final Comparator<Pair<Identifier,Expr>> fieldComparator = new Comparator<Pair<Identifier,Expr>>() {

		@Override
		public int compare(Pair<Identifier,Expr> o1, Pair<Identifier,Expr> o2) {
			return o1.getFirst().compareTo(o2.getFirst());
		}

	};

	private static final Comparator<FieldDeclaration> fieldDeclarationComparator = new Comparator<FieldDeclaration>() {

		@Override
		public int compare(FieldDeclaration o1, FieldDeclaration o2) {
			return o1.getVariableName().compareTo(o2.getVariableName());
		}

	};



	protected boolean isInstance(Object value, Type type) throws ResolutionError, UndefinedException {
		// Handle nominal types
		if(type instanceof Type.Nominal) {
			Type.Nominal nom = (Type.Nominal) type;
			Declaration.Named.Type decl = resolver.resolveExactly(nom.getName(), Declaration.Named.Type.class);
			if(isInstance(value,decl.getVariableDeclaration().getType())) {
				Tuple<Block> invariant = decl.getInvariant();
				Environment environment = new Environment(domain);
				environment.values.put(decl.getVariableDeclaration(), value);
				for (int i = 0; i != invariant.size(); ++i) {
					Result r = evaluateBlock(invariant.get(i), environment);
					if (!r.holds()) {
						return false;
					}
				}
				return true;
			} else {
				return false;
			}
		}
		// Handle type connectives
		if(type instanceof Type.Union) {
			Type.Union union = (Type.Union) type;
			for(int i=0;i!=union.size();++i) {
				if(isInstance(value,union.get(i))) {
					return true;
				}
			}
			return false;
		} else if(type instanceof Type.Intersection) {
			Type.Intersection intersection = (Type.Intersection) type;
			for(int i=0;i!=intersection.size();++i) {
				if(!isInstance(value,intersection.get(i))) {
					return false;
				}
			}
			return true;
		} else if(type instanceof Type.Negation) {
			Type.Negation negation = (Type.Negation) type;
			return !isInstance(value,negation.getElement());
		}
		// Handle atomic cases
		if(value == null) {
			return type instanceof Type.Null;
		} else if(value instanceof Boolean) {
			return type instanceof Type.Bool;
		} else if(value instanceof Byte) {
			return type instanceof Type.Byte;
		} else if(value instanceof BigInteger) {
			return type instanceof Type.Int;
		} else if(value instanceof Object[]) {
			if(type instanceof Type.Array) {
				Object[] elements = (Object[]) value;
				Type elementType = ((Type.Array) type).getElement();
				for(int i=0;i!=elements.length;++i) {
					if(!isInstance(elements[i],elementType)) {
						return false;
					}
				}
				return true;
			} else {
				return false;
			}
		} else if(value instanceof Record) {
			if(type instanceof Type.Record) {
				Record record = (Record) value;
				Type.Record recT = (Type.Record) type;
				FieldDeclaration[] fields = recT.getFields();
				Arrays.sort(fields,fieldDeclarationComparator);
				for(int i=0;i!=recT.size();++i) {
					FieldDeclaration field = fields[i];
					if(!isInstance(record.values[i],field.getType())) {
						return false;
					}
				}
				return true;
			} else {
				return false;
			}
		} else {
			throw new IllegalArgumentException("unknown value encountered: " + value);
		}
	}

	protected void checkTypeInvariants(Tuple<VariableDeclaration> vars, Environment environment)
			throws UndefinedException {
		try {
			for (int i = 0; i != vars.size(); ++i) {
				VariableDeclaration decl = vars.get(i);
				Expr invariant = extractor.extract(decl.getType(), new Expr.VariableAccess(decl));
				if (invariant != null) {
					boolean b = (Boolean) evaluateExpression(invariant, environment);
					if (!b) {
						throw new UndefinedException("invalid type invariant");
					}
				}
			}
		} catch (NameResolver.ResolutionError err) {
			// If original WyAL file well typed, then should be impossible to
			// get here.
			throw new RuntimeException(err);
		}
	}

	/**
	 * A result simply catches the result of a given boolean expression, and the
	 * environment which lead to that result.
	 *
	 * @author David J. Pearce
	 *
	 */
	public final class Result {
		private final Environment environment;
		private final boolean value;

		public Result(Environment environment, boolean value) {
			this.environment = environment;
			this.value = value;
		}

		public Environment getEnvironment() {
			return environment;
		}

		public boolean holds() {
			return value;
		}
	}

	public static class Environment {
		private final Environment parent;
		private final Domain domain;
		private final Map<VariableDeclaration,Object> values;

		public Environment(Domain domain) {
			this.parent = null;
			this.domain = domain;
			this.values = new IdentityHashMap<>();
		}

		private Environment(Environment parent) {
			this.parent = parent;
			this.domain = parent.domain;
			this.values = new IdentityHashMap<>();
		}

		public Object read(Expr.VariableAccess expr) {
			VariableDeclaration var = expr.getVariableDeclaration();
			if(values.containsKey(var)) {
				return values.get(var);
			} else if(parent != null) {
				return parent.read(expr);
			} else {
				throw new IllegalArgumentException("invalid variable access");
			}
		}

		public Iterable<Environment> declare(Tuple<VariableDeclaration> variables) {
			// Some Java switcheroo stuff
			return new Iterable<Environment>() {

				@Override
				public java.util.Iterator<Environment> iterator() {
					return new Environment.Iterator(variables);
				}

			};
		}

		@Override
		public String toString() {
			return "{" + toString(this) + "}";
		}

		private static String toString(Environment env) {
			String r;
			if(env == null) {
				return "";
			} else {
				r = toString(env.parent);
				boolean firstTime=true;
				for(Map.Entry<VariableDeclaration, Object> e : env.values.entrySet()) {
					if(!firstTime) {
						r += ", ";
					}
					firstTime=false;
					r += e.getKey().getVariableName() + "=" + toString(e.getValue());
				}
				return r;
			}
		}

		private static String toString(Object o) {
			if(o instanceof Object[]) {
				Object[] arr = (Object[]) o;
				String r = "[";
				for(int i=0;i!=arr.length;++i) {
					if(i != 0) {
						r += ",";
					}
					r += toString(arr[i]);
				}
				return r += "]";
			}
			// Default
			return o.toString();
		}

		private class Iterator implements java.util.Iterator<Environment> {
			private final VariableDeclaration[] variables;
			private final Domain.Generator[] generators;

			public Iterator(Tuple<VariableDeclaration> variables) {
				this.variables = variables.toArray(VariableDeclaration.class);
				this.generators = new Domain.Generator[this.variables.length];
				for(int i=0;i!=this.variables.length;++i) {
					VariableDeclaration var = this.variables[i];
					generators[i] = domain.generator(var.getType());
				}
			}

			@Override
			public boolean hasNext() {
				// Check whether secret signal has been made
				return generators[0] != null;
			}

			@Override
			public Environment next() {
				// Construct new environment based on current values.
				Environment next = new Environment(Environment.this);
				for(int i=0;i!=variables.length;++i) {
					VariableDeclaration var = variables[i];
					Object value = generators[i].get();
					next.values.put(var, value);
				}
				// Toggle next position
				for(int i=0;i!=generators.length;++i) {
					Domain.Generator gen = generators[i];
					if(gen.hasNext()) {
						gen.next();
						return next;
					} else {
						gen.reset();
					}
				}
				// If we get here, then we are properly finished. Therefore, we
				// make the secret signal.
				generators[0] = null;
				return next;
			}
		}
	}

	public static class UndefinedException extends Exception {
		public UndefinedException(String msg) {
			super(msg);
		}
	}

	public static class Record {
		private Identifier[] fields;
		private Object[] values;

		public Record(Identifier[] fields, Object[] values) {
			this.fields = fields;
			this.values = values;
		}

		public Object getField(Identifier field) throws UndefinedException {
			for(int i=0;i!=fields.length;++i) {
				if(fields[i].equals(field)) {
					return values[i];
				}
			}
			throw new UndefinedException("invalid record access");
		}

		public Record setField(Identifier field, Object value) throws UndefinedException {
			for(int i=0;i!=fields.length;++i) {
				if(fields[i].equals(field)) {
					Object[] nValues = Arrays.copyOf(values, fields.length);
					nValues[i] = value;
					return new Record(fields,nValues);
				}
			}
			throw new UndefinedException("invalid record access");
		}

		@Override
		public boolean equals(Object o) {
			if(o instanceof Record) {
				Record r = (Record) o;
				return Arrays.equals(fields, r.fields) && Arrays.equals(values, r.values);
			}
			return false;
		}

		@Override
		public int hashCode() {
			return Arrays.hashCode(values);
		}

		@Override
		public String toString() {
			String r = "";
			for(int i=0;i!=fields.length;++i) {
				if(i!=0) {
					r += ",";
				}
				r += fields[i] + ":" + Objects.toString(values[i]);
			}
			return "{" + r + "}";
		}
	}
}
