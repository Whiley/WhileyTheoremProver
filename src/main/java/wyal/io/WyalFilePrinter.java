package wyal.io;

import java.io.OutputStream;
import java.io.OutputStreamWriter;
import java.io.PrintWriter;
import java.io.UnsupportedEncodingException;
import java.io.Writer;
import java.util.HashMap;
import java.util.List;

import wyal.lang.Bytecode;
import wyal.lang.SemanticType;
import wyal.lang.WyalFile;
import wyal.lang.Bytecode.*;
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
			List<WyalFile.ConstantPoolItem> items = wf.getSyntacticItems();
			for(int i=0;i!=items.size();++i) {
				out.println("// #" + i + " " + wf.getConstantPoolItem(i));
			}
		}
	}


	private void write(WyalFile wf, WyalFile.Declaration s) {
		if(s instanceof WyalFile.Function) {
			write(wf,(WyalFile.Function) s);
		} else if(s instanceof WyalFile.Macro) {
			write(wf,(WyalFile.Macro) s);
		} else if(s instanceof WyalFile.Type) {
			write(wf,(WyalFile.Type) s);
		} else if(s instanceof WyalFile.Assert) {
			write(wf,(WyalFile.Assert) s);
		} else {
			throw new InternalFailure("unknown statement encountered " + s,
					wf.getEntry(), s);
		}
		out.println();
	}

	public void write(WyalFile wf, WyalFile.Function s) {
		out.print("function ");
		out.print(s.getName());
		out.print("(" + s.getType().element(0) + ") => " + s.getType().element(1));
	}

	public void write(WyalFile wf, WyalFile.Macro s) {
		out.print("define ");

		out.print(s.getName());
		out.print("(" + s.getType().from() + ") => " + s.getType().to());
		if(s.getBody() != null) {
			out.println(" as:");
			writeStatement(s.getBody(),1);
		}
	}

	public void write(WyalFile wf, WyalFile.Type s) {
		out.print("type ");

		out.print(s.getName());
		out.print(" is " + s.getType());
		if(s.getInvariant().length > 0) {
			for(WyalFile.Location stmt : s.getInvariant()) {
				out.println(" where");
				writeStatement(stmt,1);
			}
		}
	}

	public void write(WyalFile wf, WyalFile.Assert s) {
		out.print("assertion ");
		out.println(":");
		writeStatement(s.getBody(),1);
		out.println();
	}

	private void writeParameters(List<WyalFile.Location> parameters) {
		out.print("(");
		for (int i = 0; i != parameters.size(); ++i) {
			if (i != 0) {
				out.print(", ");
			}
			WyalFile.Location parameter = parameters.get(i);
			writeType(parameter.getOperand(0));
			out.print(" ");
			out.print(parameter.getCode().getName());
		}
		out.print(")");
	}

	public void writeStatement(WyalFile.Location loc, int indent) {
		switch(loc.getOpcode()) {
		case STMT_block:
			writeBlock(loc, indent);
			break;
		case STMT_ifthen:
			writeIfThen(loc,indent);
			break;
		case STMT_forall:
		case STMT_exists:
			writeQuantifier(loc,indent);
			break;
		default:
			writeExpressionAsStatement(loc,indent);
		}
	}

	private void writeExpressionAsStatement(WyalFile.Location loc, int indent) {
		indent(indent);
		writeExpression(loc);
		out.println();
	}

	private void writeBlock(WyalFile.Location block, int indent) {
		for (int i = 0; i != block.numberOfOperands(); ++i) {
			writeStatement(block.getOperand(i), indent);
		}
	}

	private void writeIfThen(WyalFile.Location block, int indent) {
		indent(indent);
		out.println("if:");
		writeStatement(block.getOperand(0),indent+1);
		indent(indent);
		out.println("then:");
		writeStatement(block.getOperand(1),indent+1);
	}

	private void writeQuantifier(WyalFile.Location block, int indent) {
		indent(indent);
		if(block.getOpcode() == Opcode.STMT_forall) {
			out.print("forall");
		} else {
			out.print("exists");
		}
		out.println("( ... ):");
		writeStatement(block.getOperand(0),indent+1);
	}

	/**
	 * Write an expression with brackets (if necessary). For some expressiones,
	 * brackets are never required.
	 *
	 * @param loc
	 */
	public void writeExpressionWithBrackets(WyalFile.Location loc) {
		switch(loc.getOpcode()) {
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
			writeExpression(loc);
			out.print(")");
			break;
		default:
			// Brackets never required
			writeExpression(loc);
		}
	}

	public void writeExpression(WyalFile.Location loc) {
		switch (loc.getOpcode()) {
		case EXPR_cast:
			writeCast(loc);
			break;
		case CONST_null:
		case CONST_bool:
		case CONST_int:
			writeConstant(loc);
			break;
		case EXPR_not:
		case EXPR_neg:
		case EXPR_arrlen:
			writeUnaryOperator(loc);
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
			writeInfixOperator(loc);
			break;
		case EXPR_var:
			writeVariableAccess(loc);
			break;
		default:
			throw new RuntimeException("unknown bytecode encountered:" + loc.getOpcode());
		}
	}

	public void writeVariableAccess(WyalFile.Location loc) {
		// Determine variable declaration to which this access refers
		WyalFile.Location decl = loc.getOperand(0);
		Bytecode.Identifier ident = (Bytecode.Identifier) decl.getOperand(1).getCode();
		// Print out the declared variable name
		out.print(ident.get());
	}

	public void writeCast(WyalFile.Location loc) {
		out.print("(");
		writeType(loc.getOperand(0));
		out.print(")");
		writeExpression(loc.getOperand(0));
	}

	public void writeConstant(WyalFile.Location loc) {
		switch (loc.getOpcode()) {
		case CONST_null:
			out.print("null");
			break;
		case CONST_bool: {
			Bytecode.Bool bytecode = (Bytecode.Bool) loc.getCode();
			out.print(bytecode.get());
			break;
		}
		case CONST_int: {
			Bytecode.Int bytecode = (Bytecode.Int) loc.getCode();
			out.print(bytecode.get());
			break;
		}
		default:
			throw new RuntimeException("unknown bytecode encountered:" + loc.getOpcode());
		}
	}

	public void writeUnaryOperator(WyalFile.Location loc) {

	}

	public void writeInfixOperator(WyalFile.Location loc) {
		for(int i=0;i!=loc.numberOfOperands();++i) {
			if(i != 0) {
				out.print(" ");
				out.print(OPERATOR_MAP.get(loc.getOpcode()));
				out.print(" ");
			}
			writeExpressionWithBrackets(loc.getOperand(i));
		}
	}

	private void writeType(WyalFile.Location loc) {
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
			NominalType t = (NominalType) loc.getCode();
			String[] elements = t.getElements();
			for(int i=0;i!=elements.length;++i) {
				if(i != 0) {
					out.print(".");
				}
				out.print(elements[i]);
			}
			break;
		}
		case TYPE_arr: {
			writeTypeWithBraces(loc.getOperand(0));
			out.print("[]");
			break;
		}
		case TYPE_ref: {
			out.print("&");
			writeTypeWithBraces(loc.getOperand(0));
			break;
		}
		case TYPE_not: {
			out.print("!");
			writeTypeWithBraces(loc.getOperand(0));
			break;
		}
		case TYPE_or: {
			for(int i=0;i!=loc.numberOfOperands();++i) {
				if(i != 0) {
					out.print(" | ");
				}
				writeTypeWithBraces(loc.getOperand(i));
			}
			break;
		}
		case TYPE_and: {
			for(int i=0;i!=loc.numberOfOperands();++i) {
				if(i != 0) {
					out.print(" & ");
				}
				writeTypeWithBraces(loc.getOperand(i));
			}
			break;
		}
		}
	}

	private void writeTypeWithBraces(WyalFile.Location loc) {
		switch(loc.getOpcode()) {
		case TYPE_or:
		case TYPE_and:
			out.print("(");
			writeType(loc);
			out.print(")");
			break;
		default:
			writeType(loc);
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
	private static final HashMap<Bytecode.Opcode,String> OPERATOR_MAP = new HashMap<>();

	static {
		OPERATOR_MAP.put(Bytecode.Opcode.EXPR_and,"&&");
		OPERATOR_MAP.put(Bytecode.Opcode.EXPR_or,"||");
		OPERATOR_MAP.put(Bytecode.Opcode.EXPR_implies,"==>");
		OPERATOR_MAP.put(Bytecode.Opcode.EXPR_iff,"<==>");
		OPERATOR_MAP.put(Bytecode.Opcode.EXPR_lteq,"<=");
		OPERATOR_MAP.put(Bytecode.Opcode.EXPR_lt,"<");
		OPERATOR_MAP.put(Bytecode.Opcode.EXPR_gteq,">=");
		OPERATOR_MAP.put(Bytecode.Opcode.EXPR_gt,">");
		OPERATOR_MAP.put(Bytecode.Opcode.EXPR_eq,"==");
		OPERATOR_MAP.put(Bytecode.Opcode.EXPR_neq,"!=");
		OPERATOR_MAP.put(Bytecode.Opcode.EXPR_is,"is");
		OPERATOR_MAP.put(Bytecode.Opcode.EXPR_add,"+");
		OPERATOR_MAP.put(Bytecode.Opcode.EXPR_sub,"-");
		OPERATOR_MAP.put(Bytecode.Opcode.EXPR_mul,"*");
		OPERATOR_MAP.put(Bytecode.Opcode.EXPR_div,"/");
	}
}