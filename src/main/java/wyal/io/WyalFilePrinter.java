package wyal.io;

import java.io.OutputStream;
import java.io.OutputStreamWriter;
import java.io.PrintWriter;
import java.io.UnsupportedEncodingException;
import java.io.Writer;
import java.util.HashMap;
import java.util.List;

import static wyal.lang.WyalFile.*;
import wyal.lang.SemanticType;
import wyal.lang.SyntacticItem;
import wyal.lang.WyalFile;
import wybs.lang.SyntaxError.*;
import wyfs.lang.Path;
import wyfs.util.Trie;

public class WyalFilePrinter {
	private final PrintWriter out;
	private boolean raw=true;

	public WyalFilePrinter(OutputStream writer) throws UnsupportedEncodingException {
		this(new OutputStreamWriter(writer,"UTF-8"));
	}

	public WyalFilePrinter(Writer writer) {
		this.out = new PrintWriter(writer);
	}

	public WyalFilePrinter(PrintWriter writer) {
		this.out = writer;
	}

	public void write(WyalFile wf) {
		writeConstantPool(wf);
		// First, write package information
		Path.ID pkg = wf.getEntry().id().parent();
		if(pkg != Trie.ROOT) {
			out.println("package " + pkg.toString());
			out.println();
		}
		// Second, write all declarations
		for(WyalFile.Declaration d : wf.getSyntacticItems(WyalFile.Declaration.class)) {
			write(wf, d);
			out.println();
		}
		out.flush();
	}

	public void writeConstantPool(WyalFile wf) {
		if(raw) {
			List<SyntacticItem> items = wf.getSyntacticItems();
			for(int i=0;i!=items.size();++i) {
				out.println("// #" + i + " " + items.get(i));
			}
		}
	}


	private void write(WyalFile wf, Declaration s) {
		if(s instanceof Declaration.Named.Function) {
			write(wf,(Declaration.Named.Function) s);
		} else if(s instanceof Declaration.Named.Macro) {
			write(wf,(Declaration.Named.Macro) s);
		} else if(s instanceof Declaration.Named.Type) {
			write(wf,(Declaration.Named.Type) s);
		} else if(s instanceof Declaration.Assert) {
			write(wf,(Declaration.Assert) s);
		} else {
			throw new InternalFailure("unknown statement encountered " + s,
					wf.getEntry(), s);
		}
		out.println();
	}

	public void write(WyalFile wf, Declaration.Named.Function s) {
		out.print("function ");
		out.print(s.getName());
		//out.print("(" + s.getType().element(0) + ") => " + s.getType().element(1));
	}

	public void write(WyalFile wf, Declaration.Named.Macro s) {
		out.print("define ");

		out.print(s.getName());
		//out.print("(" + s.getType().from() + ") => " + s.getType().to());
		if(s.getBody() != null) {
			out.println(" as:");
			writeBlock(s.getBody(),1);
		}
	}

	public void write(WyalFile wf, Declaration.Named.Type s) {
		out.print("type ");

		out.print(s.getName());
//		out.print(" is " + s.getType());
//		if(s.getInvariant().length > 0) {
//			for(WyalFile.Term stmt : s.getInvariant()) {
//				out.println(" where");
//				writeStatement(stmt,1);
//			}
//		}
	}

	public void write(WyalFile wf, Declaration.Assert s) {
		out.print("assertion ");
		out.println(":");
		writeBlock(s.getBody(),1);
		out.println();
	}

	private void writeParameters(List<VariableDeclaration> parameters) {
		out.print("(");
		for (int i = 0; i != parameters.size(); ++i) {
			if (i != 0) {
				out.print(", ");
			}
			VariableDeclaration parameter = parameters.get(i);
			writeType(parameter.getType());
			out.print(" ");
			out.print(parameter.getVariableName());
		}
		out.print(")");
	}

	public void writeBlock(Block block, int indent) {
		System.out.println("WRITING BLOCK");
		for(int i=0;i!=block.numberOfOperands();i=i+1) {
			System.out.println("WRITING STATEMENT: " + block.getOperand(i));
			writeStatement(block.getOperand(i),indent);
		}
	}

	public void writeStatement(WyalFile.Stmt loc, int indent) {
		switch(loc.getOpcode()) {
		case STMT_ifthen:
			writeIfThen((Stmt.IfThen) loc,indent);
			break;
		case STMT_forall:
		case STMT_exists:
			writeQuantifier((Stmt.Quantifier) loc,indent);
			break;
		default:
			writeExpressionAsStatement((Expr) loc,indent);
		}
	}

	private void writeExpressionAsStatement(WyalFile.Expr expr, int indent) {
		indent(indent);
		writeExpression(expr);
		out.println();
	}

	private void writeIfThen(Stmt.IfThen stmt, int indent) {
		indent(indent);
		out.println("if:");
		writeBlock(stmt.getIfBody(),indent+1);
		indent(indent);
		out.println("then:");
		writeBlock(stmt.getThenBody(),indent+1);
	}

	private void writeQuantifier(Stmt.Quantifier stmt, int indent) {
		indent(indent);
		if(stmt.getOpcode() == Opcode.STMT_forall) {
			out.print("forall");
		} else {
			out.print("exists");
		}
		out.println("( ... ):");
		writeBlock(stmt.getBody(),indent+1);
	}

	/**
	 * Write an expression with brackets (if necessary). For some expressiones,
	 * brackets are never required.
	 *
	 * @param expr
	 */
	public void writeExpressionWithBrackets(WyalFile.Expr expr) {
		switch(expr.getOpcode()) {
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
		case EXPR_is:
		case EXPR_add:
		case EXPR_sub:
		case EXPR_mul:
		case EXPR_div:
		case EXPR_rem:
			// Brackets always required
			out.print("(");
			writeExpression(expr);
			out.print(")");
			break;
		default:
			// Brackets never required
			writeExpression(expr);
		}
	}

	public void writeExpression(WyalFile.Expr expr) {
		switch (expr.getOpcode()) {
		case EXPR_cast:
			writeCast((Expr.Cast) expr);
			break;
		case EXPR_const:
			writeConstant((Expr.Constant)expr);
			break;
		case EXPR_not:
		case EXPR_neg:
		case EXPR_arrlen:
			writeUnaryOperator((Expr.Operator)expr);
			break;
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
		case EXPR_is:
		case EXPR_add:
		case EXPR_sub:
		case EXPR_mul:
		case EXPR_div:
		case EXPR_rem:
			writeInfixOperator((Expr.Operator)expr);
			break;
		case EXPR_var:
			writeVariableAccess((Expr.VariableAccess)expr);
			break;
		default:
			throw new RuntimeException("unknown bytecode encountered:" + expr.getOpcode());
		}
	}

	public void writeVariableAccess(Expr.VariableAccess expr) {
		// Determine variable declaration to which this access refers
		Identifier ident = expr.getVariableDeclaration().getVariableName();
		// Print out the declared variable name
		out.print(ident.get());
	}

	public void writeCast(Expr.Cast expr) {
		out.print("(");
		writeType(expr.getCastType());
		out.print(")");
		writeExpression(expr.getExpr());
	}

	public void writeConstant(Expr.Constant expr) {
		Item value = expr.getValue();
		switch (value.getOpcode()) {
		case CONST_null:
			out.print("null");
			break;
		case CONST_bool: {
			Bool item = (Bool) expr.getValue();
			out.print(item.get());
			break;
		}
		case CONST_int: {
			Int item = (Int) expr.getValue();
			out.print(item.get());
			break;
		}
		default:
			throw new RuntimeException("unknown bytecode encountered:" + expr.getOpcode());
		}
	}

	public void writeUnaryOperator(Expr.Operator expr) {

	}

	public void writeInfixOperator(Expr.Operator expr) {
		for(int i=1;i!=expr.numberOfOperands();++i) {
			if(i != 1) {
				out.print(" ");
				out.print(OPERATOR_MAP.get(expr.getOpcode()));
				out.print(" ");
			}
			writeExpressionWithBrackets(expr.getOperand(i));
		}
	}

	private void writeType(Type loc) {
		switch(loc.getOpcode()) {
		case TYPE_any:
			out.print("any");
			break;
		case TYPE_void:
			out.print("void");
			break;
		case TYPE_null:
			out.print("null");
			break;
		case TYPE_bool:
			out.print("bool");
			break;
		case TYPE_int:
			out.print("int");
			break;
		case TYPE_nom: {
			Type.Nominal t = (Type.Nominal) loc;
			Name name = t.getName();
			out.print(name);
			break;
		}
		case TYPE_arr: {
			Type.Array t = (Type.Array) loc;
			writeTypeWithBraces(t.getElement());
			out.print("[]");
			break;
		}
		case TYPE_ref: {
			out.print("&");
			Type.Reference t = (Type.Reference) loc;
			writeTypeWithBraces(t.getElement());
			break;
		}
		case TYPE_not: {
			out.print("!");
			Type.Negation t = (Type.Negation) loc;
			writeTypeWithBraces(t.getElement());
			break;
		}
		case TYPE_or: {
			Type.Union t = (Type.Union) loc;
			for(int i=0;i!=loc.numberOfOperands();++i) {
				if(i != 0) {
					out.print(" | ");
				}
				writeTypeWithBraces(t.getOperand(i));
			}
			break;
		}
		case TYPE_and: {
			Type.Intersection t = (Type.Intersection) loc;
			for(int i=0;i!=loc.numberOfOperands();++i) {
				if(i != 0) {
					out.print(" & ");
				}
				writeTypeWithBraces(t.getOperand(i));
			}
			break;
		}
		}
	}

	private void writeTypeWithBraces(Type type) {
		switch(type.getOpcode()) {
		case TYPE_or:
		case TYPE_and:
			out.print("(");
			writeType(type);
			out.print(")");
			break;
		default:
			writeType(type);
		}

	}

	private void indent(int indent) {
		indent = indent * 4;
		for(int i=0;i<indent;++i) {
			out.print(" ");
		}
	}

	/**
	 * A fixed map from token kinds to their correspond bytecode opcodes.
	 */
	private static final HashMap<Opcode,String> OPERATOR_MAP = new HashMap<>();

	static {
		OPERATOR_MAP.put(Opcode.EXPR_and,"&&");
		OPERATOR_MAP.put(Opcode.EXPR_or,"||");
		OPERATOR_MAP.put(Opcode.EXPR_implies,"==>");
		OPERATOR_MAP.put(Opcode.EXPR_iff,"<==>");
		OPERATOR_MAP.put(Opcode.EXPR_lteq,"<=");
		OPERATOR_MAP.put(Opcode.EXPR_lt,"<");
		OPERATOR_MAP.put(Opcode.EXPR_gteq,">=");
		OPERATOR_MAP.put(Opcode.EXPR_gt,">");
		OPERATOR_MAP.put(Opcode.EXPR_eq,"==");
		OPERATOR_MAP.put(Opcode.EXPR_neq,"!=");
		OPERATOR_MAP.put(Opcode.EXPR_is,"is");
		OPERATOR_MAP.put(Opcode.EXPR_add,"+");
		OPERATOR_MAP.put(Opcode.EXPR_sub,"-");
		OPERATOR_MAP.put(Opcode.EXPR_mul,"*");
		OPERATOR_MAP.put(Opcode.EXPR_div,"/");
	}
}