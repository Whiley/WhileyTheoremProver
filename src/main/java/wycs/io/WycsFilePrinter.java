package wycs.io;

import static wycs.io.WyalFileLexer.Token.Kind.EqualsEquals;
import static wycs.io.WyalFileLexer.Token.Kind.GreaterEquals;
import static wycs.io.WyalFileLexer.Token.Kind.Is;
import static wycs.io.WyalFileLexer.Token.Kind.LeftAngle;
import static wycs.io.WyalFileLexer.Token.Kind.LessEquals;
import static wycs.io.WyalFileLexer.Token.Kind.LogicalAnd;
import static wycs.io.WyalFileLexer.Token.Kind.LogicalIff;
import static wycs.io.WyalFileLexer.Token.Kind.LogicalImplication;
import static wycs.io.WyalFileLexer.Token.Kind.LogicalOr;
import static wycs.io.WyalFileLexer.Token.Kind.Minus;
import static wycs.io.WyalFileLexer.Token.Kind.NotEquals;
import static wycs.io.WyalFileLexer.Token.Kind.Plus;
import static wycs.io.WyalFileLexer.Token.Kind.RightAngle;
import static wycs.io.WyalFileLexer.Token.Kind.RightSlash;
import static wycs.io.WyalFileLexer.Token.Kind.Star;

import java.io.OutputStream;
import java.io.OutputStreamWriter;
import java.io.PrintWriter;
import java.io.UnsupportedEncodingException;
import java.io.Writer;
import java.util.HashMap;
import java.util.List;

import wycc.util.Pair;
import wybs.lang.SyntacticElement;
import wybs.lang.SyntaxError.*;
import wycs.io.WyalFileLexer.Token;
import wycs.lang.Bytecode;
import wycs.lang.SemanticType;
import wycs.lang.SyntaxTree;
import wycs.lang.WycsFile;
import wycs.lang.Bytecode.*;
import wycs.lang.SyntaxTree.Location;
import wyfs.lang.Path;
import wyfs.util.Trie;

public class WycsFilePrinter {
	private final PrintWriter out;
	private boolean raw=true;

	public WycsFilePrinter(OutputStream writer) throws UnsupportedEncodingException {
		this(new OutputStreamWriter(writer,"UTF-8"));
	}

	public WycsFilePrinter(Writer writer) {
		this.out = new PrintWriter(writer);
	}

	public WycsFilePrinter(PrintWriter writer) {
		this.out = writer;
	}

	public void write(WycsFile wf) {
		// First, write package information
		Path.ID pkg = wf.getEntry().id().parent();
		if(pkg != Trie.ROOT) {
			out.println("package " + pkg.toString());
			out.println();
		}
		// Second, write all declarations
		for(WycsFile.Declaration d : wf.getDeclarations()) {
			write(wf, d);
			out.println();
		}
		out.flush();
	}

	private void write(WycsFile wf, WycsFile.Declaration s) {
		writeRawBytecodes(s);
		if(s instanceof WycsFile.Function) {
			write(wf,(WycsFile.Function) s);
		} else if(s instanceof WycsFile.Macro) {
			write(wf,(WycsFile.Macro) s);
		} else if(s instanceof WycsFile.Type) {
			write(wf,(WycsFile.Type) s);
		} else if(s instanceof WycsFile.Assert) {
			write(wf,(WycsFile.Assert) s);
		} else {
			throw new InternalFailure("unknown statement encountered " + s,
					wf.getEntry(), s);
		}
		out.println();
	}

	public void writeRawBytecodes(WycsFile.Declaration d) {
		if(raw) {
			SyntaxTree tree = d.getTree();
			for(int i=0;i!=tree.size();++i) {
				out.println("// #" + i + " " + tree.getLocation(i).getCode());
			}
		}
	}

	public void write(WycsFile wf, WycsFile.Function s) {
		out.print("function ");
		out.print(s.getName());
		SemanticType[] generics = s.getType().generics();
		if(generics.length > 0) {
			out.print("<");
			boolean firstTime=true;
			for(SemanticType g : generics) {
				if(!firstTime) {
					out.print(", ");
				}
				firstTime=false;
				out.print(((SemanticType.Var)g).name());
			}
			out.print(">");
		}
		out.print("(" + s.getType().element(0) + ") => " + s.getType().element(1));
	}

	public void write(WycsFile wf, WycsFile.Macro s) {
		out.print("define ");

		out.print(s.getName());
		SemanticType[] generics = s.getType().generics();
		if(generics.length > 0) {
			out.print("<");
			boolean firstTime=true;
			for(SemanticType g : generics) {
				if(!firstTime) {
					out.print(", ");
				}
				firstTime=false;
				out.print(((SemanticType.Var)g).name());
			}
			out.print(">");
		}
		out.print("(" + s.getType().from() + ") => " + s.getType().to());
		if(s.getBody() != null) {
			out.println(" as:");
			writeStatement(s.getBody(),1);
		}
	}

	public void write(WycsFile wf, WycsFile.Type s) {
		out.print("type ");

		out.print(s.getName());
		out.print(" is " + s.getType());
		if(s.getInvariant().size() > 0) {
			for(Location<?> stmt : s.getInvariant()) {
				out.println(" where");
				writeStatement(stmt,1);
			}
		}
	}

	public void write(WycsFile wf, WycsFile.Assert s) {
		out.print("assertion ");
		out.print(s.getName());
		writeParameters(s.getParameters());
		out.println(":");
		writeStatement(s.getBody(),1);
		out.println();
	}

	private void writeParameters(List<Location<VariableDeclaration>> parameters) {
		out.print("(");
		for (int i = 0; i != parameters.size(); ++i) {
			if (i != 0) {
				out.print(", ");
			}
			Location<VariableDeclaration> parameter = parameters.get(i);
			writeType(parameter.getOperand(0));
			out.print(" ");
			out.print(parameter.getCode().getName());
		}
		out.print(")");
	}

	public void writeStatement(Location<?> loc, int indent) {
		switch(loc.getOpcode()) {
		case BLOCK:
			writeBlock((Location<Block>) loc, indent);
			break;
		case IFTHEN:
			writeIfThen((Location<IfThen>)loc,indent);
			break;
		default:
			writeExpressionAsStatement(loc,indent);
		}
	}

	private void writeExpressionAsStatement(Location<?> loc, int indent) {
		indent(indent);
		writeExpression(loc);
		out.println();
	}

	private void writeBlock(Location<Block> block, int indent) {
		for (int i = 0; i != block.numberOfOperands(); ++i) {
			writeStatement(block.getOperand(i), indent);
		}
	}

	private void writeIfThen(Location<IfThen> block, int indent) {
		indent(indent);
		out.println("if:");
		writeStatement(block.getOperand(0),indent+1);
		indent(indent);
		out.println("then:");
		writeStatement(block.getOperand(1),indent+1);
	}

	/**
	 * Write an expression with brackets (if necessary). For some expressiones,
	 * brackets are never required.
	 *
	 * @param loc
	 */
	public void writeExpressionWithBrackets(Location<?> loc) {
		switch(loc.getOpcode()) {
		case AND:
		case OR:
		case IMPLIES:
		case IFF:
		case EQ:
		case NEQ:
		case LT:
		case LTEQ:
		case GT:
		case GTEQ:
		case IS:
		case ADD:
		case SUB:
		case MUL:
		case DIV:
		case REM:
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

	public void writeExpression(Location<?> loc) {
		switch (loc.getOpcode()) {
		case CAST:
			writeCast((Location<Cast>) loc);
			break;
		case CONST:
			writeConstant((Location<Constant>) loc);
			break;
		case NOT:
		case NEG:
		case ARRAYLENGTH:
			writeUnaryOperator((Location<Operator>) loc);
			break;
		case AND:
		case OR:
		case IMPLIES:
		case IFF:
		case EQ:
		case NEQ:
		case LT:
		case LTEQ:
		case GT:
		case GTEQ:
		case IS:
		case ADD:
		case SUB:
		case MUL:
		case DIV:
		case REM:
			writeInfixOperator((Location<Operator>) loc);
			break;
		case VARACCESS:
			writeVariableAccess((Location<VariableAccess>) loc);
			break;
		default:
			throw new RuntimeException("unknown bytecode encountered:" + loc.getOpcode());
		}
	}

	public void writeVariableAccess(Location<VariableAccess> loc) {
		// Determine variable declaration to which this access refers
		Location<VariableDeclaration> decl = (Location<VariableDeclaration>) loc.getOperand(0);
		// Print out the declared variable name
		out.print(decl.getCode().getName());
	}

	public void writeCast(Location<Cast> loc) {
		out.print("(");
		writeType(loc.getOperand(0));
		out.print(")");
		writeExpression(loc.getOperand(0));
	}

	public void writeConstant(Location<Constant> loc) {
		Bytecode.Constant bytecode = loc.getCode();
		out.print(bytecode.getValue());
	}

	public void writeUnaryOperator(Location<Operator> loc) {

	}

	public void writeInfixOperator(Location<Operator> loc) {
		for(int i=0;i!=loc.numberOfOperands();++i) {
			if(i != 0) {
				out.print(" ");
				out.print(OPERATOR_MAP.get(loc.getOpcode()));
				out.print(" ");
			}
			writeExpressionWithBrackets(loc.getOperand(i));
		}
	}

	private void writeType(Location<?> loc) {
		switch(loc.getOpcode()) {
		case T_ANY:
			out.print("any");
			break;
		case T_VOID:
			out.print("void");
			break;
		case T_NULL:
			out.print("null");
			break;
		case T_BOOL:
			out.print("bool");
			break;
		case T_INT:
			out.print("int");
			break;
		case T_NOMINAL: {
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
		case T_ARRAY: {
			writeTypeWithBraces(loc.getOperand(0));
			out.print("[]");
			break;
		}
		case T_REF: {
			out.print("&");
			writeTypeWithBraces(loc.getOperand(0));
			break;
		}
		case T_NEGATION: {
			out.print("!");
			writeTypeWithBraces(loc.getOperand(0));
			break;
		}
		case T_UNION: {
			for(int i=0;i!=loc.numberOfOperands();++i) {
				if(i != 0) {
					out.print(" | ");
				}
				writeTypeWithBraces(loc.getOperand(i));
			}
			break;
		}
		case T_INTERSECTION: {
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

	private void writeTypeWithBraces(Location<?> loc) {
		switch(loc.getOpcode()) {
		case T_UNION:
		case T_INTERSECTION:
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
		OPERATOR_MAP.put(Bytecode.Opcode.AND,"&&");
		OPERATOR_MAP.put(Bytecode.Opcode.OR,"||");
		OPERATOR_MAP.put(Bytecode.Opcode.IMPLIES,"==>");
		OPERATOR_MAP.put(Bytecode.Opcode.IFF,"<==>");
		OPERATOR_MAP.put(Bytecode.Opcode.LTEQ,"<=");
		OPERATOR_MAP.put(Bytecode.Opcode.LT,"<");
		OPERATOR_MAP.put(Bytecode.Opcode.GTEQ,">=");
		OPERATOR_MAP.put(Bytecode.Opcode.GT,">");
		OPERATOR_MAP.put(Bytecode.Opcode.EQ,"==");
		OPERATOR_MAP.put(Bytecode.Opcode.NEQ,"!=");
		OPERATOR_MAP.put(Bytecode.Opcode.IS,"is");
		OPERATOR_MAP.put(Bytecode.Opcode.ADD,"+");
		OPERATOR_MAP.put(Bytecode.Opcode.SUB,"-");
		OPERATOR_MAP.put(Bytecode.Opcode.MUL,"*");
		OPERATOR_MAP.put(Bytecode.Opcode.DIV,"/");
	}
}
