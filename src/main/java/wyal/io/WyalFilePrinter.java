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

package wyal.io;

import java.io.OutputStream;
import java.io.OutputStreamWriter;
import java.io.PrintWriter;
import java.io.Writer;
import java.util.HashMap;
import java.util.List;

import static wyal.lang.WyalFile.*;

import wyal.lang.WyalFile;
import wybs.lang.Attribute;
import wybs.lang.SyntacticItem;
import wybs.lang.SyntaxError.*;
import wyfs.lang.Path;
import wyfs.util.Trie;
import wytp.proof.Formula;

public class WyalFilePrinter {
	private final PrintWriter out;
	private boolean raw = true;
	private boolean nonces = false;
	private boolean functionSignatures = false;

	public WyalFilePrinter(OutputStream writer) {
		this(new OutputStreamWriter(writer));
	}

	public WyalFilePrinter(Writer writer) {
		this.out = new PrintWriter(writer);
	}

	public WyalFilePrinter(PrintWriter writer) {
		this.out = writer;
	}

	public void flush() {
		out.flush();
	}

	public void write(WyalFile wf) {
		// First, write package information
		Path.ID pkg = wf.getEntry().id().parent();
		if (pkg != Trie.ROOT) {
			out.println("package " + pkg.toString().replace("/","."));
			out.println();
		}
		// Second, write all declarations
		for (WyalFile.Declaration d : wf.getSyntacticItems(WyalFile.Declaration.class)) {
			write(wf, d);
			out.println();
		}
		out.flush();
	}

	public void writeSyntacticItems(WyalFile wf) {
		if (raw) {
			String lenStr = Integer.toString(wf.size());
			for (int i = 0; i != wf.size(); ++i) {
				SyntacticItem item = wf.getSyntacticItem(i);
				out.print("// ");
				// Right align the string to ensure that all bytecodes are
				// displayed on the same column. This just helps reading them.
				String iStr = Integer.toString(i);
				for (int j = iStr.length(); j < lenStr.length(); ++j) {
					out.print(" ");
				}
				out.print("#" + i + " " + item);
				//
				List<Attribute> attributes = item.attributes();
				if(attributes.size() > 0) {
					out.print(" [");
					for(int j=0;j!=attributes.size();++j) {
						if(j != 0) {
							out.print(", ");
						}
						out.print(attributes.get(j));
					}
					out.print("]");
				}

				out.println();
			}
		}
	}

	private void write(WyalFile wf, Declaration s) {
		if (s instanceof Declaration.Named.Function) {
			write(wf, (Declaration.Named.Function) s);
		} else if (s instanceof Declaration.Named.Macro) {
			write(wf, (Declaration.Named.Macro) s);
		} else if (s instanceof Declaration.Named.Type) {
			write(wf, (Declaration.Named.Type) s);
		} else if (s instanceof Declaration.Assert) {
			write(wf, (Declaration.Assert) s);
		} else {
			throw new InternalFailure("unknown statement encountered " + s, wf.getEntry(), s);
		}
		out.println();
	}

	public void write(WyalFile wf, Declaration.Named.Function s) {
		out.print("function ");
		out.print(s.getName().get());
		writeVariableDeclarations(s.getParameters());
		out.print(" -> ");
		writeVariableDeclarations(s.getReturns());
	}

	public void write(WyalFile wf, Declaration.Named.Macro s) {
		out.print("define ");

		out.print(s.getName().get());
		writeVariableDeclarations(s.getParameters());
		if (s.getBody() != null) {
			out.println(" is:");
			writeBlock(s.getBody(), 1);
		}
	}

	public void write(WyalFile wf, Declaration.Named.Type s) {
		Identifier name = s.getName();
		VariableDeclaration vardecl = s.getVariableDeclaration();
		Tuple<Stmt.Block> invariant = s.getInvariant();
		out.print("type ");
		out.print(name.get());
		out.print(" is (");
		writeVariableDeclaration(vardecl);
		out.println(")");
		for(int i=0;i!=invariant.size();++i) {
			out.println("where:");
			writeBlock(invariant.get(i),1);
		}
	}

	public void write(WyalFile wf, Declaration.Assert s) {
		out.print("assert");
		String message = s.getMessage();
		if(message != null) {
			out.print(" \"");
			out.print(message);
			out.print("\"");
		}
		out.println(":");
		writeBlock(s.getBody(), 1);
	}

	private void writeVariableDeclarations(Tuple<VariableDeclaration> parameters) {
		out.print("(");
		for (int i = 0; i != parameters.size(); ++i) {
			if (i != 0) {
				out.print(", ");
			}
			writeVariableDeclaration(parameters.get(i));
		}
		out.print(")");
	}

	public void writeVariableDeclaration(VariableDeclaration decl) {
		writeType(decl.getType());
		out.print(" ");
		out.print(decl.getVariableName().get());
		// print nonces
		if(nonces && decl.getHeap() != null) {
			out.print("'" + decl.getIndex());
		} else if(nonces) {
			out.print("'?");
		}
	}

	public void writeFieldDeclaration(FieldDeclaration decl) {
		writeType(decl.getType());
		out.print(" ");
		out.print(decl.getVariableName().get());
	}

	public void writeBlock(Stmt.Block block, int indent) {
		for (int i = 0; i != block.size(); i = i + 1) {
			writeStatement(block.get(i), indent);
		}
	}

	public void writeStatement(WyalFile.Stmt loc, int indent) {
		switch (loc.getOpcode()) {
		case STMT_block:
			writeBlock((Stmt.Block) loc, indent);
			break;
		case STMT_ifthen:
			writeIfThen((Stmt.IfThen) loc, indent);
			break;
		case STMT_caseof:
			writeCaseOf((Stmt.CaseOf) loc, indent);
			break;
		case STMT_forall:
		case STMT_exists:
			writeQuantifier((Stmt.Quantifier) loc, indent);
			break;
		default:
			writeExpressionAsStatement((Expr) loc, indent);
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
		writeBlock(stmt.getIfBody(), indent + 1);
		indent(indent);
		out.println("then:");
		writeBlock(stmt.getThenBody(), indent + 1);
	}

	private void writeCaseOf(Stmt.CaseOf stmt, int indent) {
		for(int i=0;i!=stmt.size();++i) {
			indent(indent);
			if(i == 0) {
				out.println("either:");
			} else {
				out.println("or:");
			}
			writeBlock(stmt.get(i), indent + 1);
		}
	}

	private void writeQuantifier(Stmt.Quantifier stmt, int indent) {
		indent(indent);
		if (stmt.getOpcode() == WyalFile.STMT_forall) {
			out.print("forall");
		} else {
			out.print("exists");
		}
		writeVariableDeclarations(stmt.getParameters());
		out.println(":");
		writeBlock(stmt.getBody(), indent + 1);
	}

	/**
	 * Write an expression with brackets (if necessary). For some expressiones,
	 * brackets are never required.
	 *
	 * @param expr
	 */
	public void writeExpressionWithBrackets(WyalFile.Expr expr) {
		switch (expr.getOpcode()) {
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
		case EXPR_deref:
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
			writeConstant((Expr.Constant) expr);
			break;
		case EXPR_not:
		case EXPR_neg:
		case EXPR_arrlen:
		case EXPR_deref:
			writeUnaryOperator((Expr.Operator) expr);
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
		case EXPR_add:
		case EXPR_sub:
		case EXPR_mul:
		case EXPR_div:
		case EXPR_rem:
			writeInfixOperator((Expr.Operator) expr);
			break;
		case EXPR_is:
			writeIsOperator((Expr.Is) expr);
			break;
		case EXPR_varcopy:
			writeVariableAccess((Expr.VariableAccess) expr);
			break;
		case EXPR_invoke:
			writeInvoke((Expr.Invoke)expr);
			break;
		case EXPR_arrgen:
			writeArrayGenerator((Expr.Operator)expr);
			break;
		case EXPR_arridx:
			writeArrayAccess((Expr.Operator)expr);
			break;
		case EXPR_arrinit:
			writeArrayInitialiser((Expr.Operator)expr);
			break;
		case EXPR_arrupdt:
			writeArrayUpdate((Expr.Operator)expr);
			break;
		case EXPR_recfield:
			writeRecordAccess((Expr.RecordAccess)expr);
			break;
		case EXPR_recupdt:
			writeRecordUpdate((Expr.RecordUpdate)expr);
			break;
		case EXPR_recinit:
			writeRecordInitialiser((Expr.RecordInitialiser)expr);
			break;
		case EXPR_exists:
		case EXPR_forall:
			writeQuantifier((Expr.Quantifier)expr);
			break;
		default:
			throw new RuntimeException("unknown bytecode encountered:" + expr.getOpcode());
		}
	}

	public void writeVariableAccess(Expr.VariableAccess expr) {
		// Determine variable declaration to which this access refers
		VariableDeclaration decl = expr.getVariableDeclaration();
		Identifier ident = decl.getVariableName();
		// Print out the declared variable name
		out.print(ident.get());
		//
		if(nonces && decl.getHeap() != null) {
			out.print("'" + decl.getIndex());
		} else if(nonces) {
			out.print("'?");
		}
	}

	public void writeCast(Expr.Cast expr) {
		out.print("(");
		writeType(expr.getCastType());
		out.print(")");
		writeExpression(expr.getCastedExpr());
	}

	public void writeConstant(Expr.Constant expr) {
		Value value = expr.getValue();
		switch (value.getOpcode()) {
		case ITEM_null:
			out.print("null");
			break;
		case ITEM_bool: {
			Value.Bool item = (Value.Bool) expr.getValue();
			out.print(item.get());
			break;
		}
		case ITEM_byte: {
			Value.Byte item = (Value.Byte) expr.getValue();
			out.print(item.get());
			break;
		}
		case ITEM_int: {
			Value.Int item = (Value.Int) expr.getValue();
			out.print(item.get());
			break;
		}
		case ITEM_utf8: {
			Value.UTF8 item = (Value.UTF8) expr.getValue();
			out.print("\"");
			out.print(new String(item.get()));
			out.print("\"");
			break;
		}
		default:
			throw new RuntimeException("unknown bytecode encountered:" + expr.getOpcode());
		}
	}

	public void writeUnaryOperator(Expr.Operator expr) {
		switch(expr.getOpcode()) {
		case EXPR_not:
			out.print("!");
			writeExpressionWithBrackets(expr.get(0));
			break;
		case EXPR_neg:
			out.print("-");
			writeExpressionWithBrackets(expr.get(0));
			break;
		case EXPR_arrlen:
			out.print("|");
			writeExpression(expr.get(0));
			out.print("|");
			break;
		case EXPR_deref:
			out.print("*");
			writeExpressionWithBrackets(expr.get(0));
			break;
		default:
			throw new RuntimeException("unknown bytecode encountered:" + expr.getOpcode());
		}

	}

	public void writeInfixOperator(Expr.Operator expr) {
		for (int i = 0; i != expr.size(); ++i) {
			if (i != 0) {
				out.print(" ");
				out.print(OPERATOR_MAP.get(expr.getOpcode()));
				out.print(" ");
			}
			writeExpressionWithBrackets(expr.get(i));
		}
	}

	public void writeIsOperator(Expr.Is expr) {
		writeExpressionWithBrackets(expr.getTestExpr());
		out.print(" is ");
		writeType(expr.getTestType());
	}

	public void writeInvoke(Expr.Invoke expr) {
		if(expr instanceof Formula.Invoke){
			// FIXME: this is an ugly hack
			Formula.Invoke ivk = (Formula.Invoke) expr;
			if(!ivk.getSign()) {
				out.print("!");
			}
		}
		writeName(expr.getName());
		Type.FunctionOrMacroOrInvariant sig = expr.getSignatureType();
		if(sig != null && functionSignatures) {
			out.print("[");
			writeType(sig);
			out.print("]");
		}
		out.print("(");
		writeArguments(expr.getArguments().toArray(Expr.class));
		out.print(")");
		Value.Int selector = expr.getSelector();
		if(selector != null) {
			out.print("#");
			out.print(selector.get());
		}
	}

	public void writeArrayGenerator(Expr.Operator expr) {
		out.print("[");
		writeExpression(expr.get(0));
		out.print(";");
		writeExpression(expr.get(1));
		out.print("]");
	}

	public void writeArrayAccess(Expr.Operator expr) {
		writeExpressionWithBrackets(expr.get(0));
		out.print("[");
		writeExpression(expr.get(1));
		out.print("]");
	}

	public void writeArrayInitialiser(Expr.Operator expr) {
		out.print("[");
		writeArguments(expr.getAll());
		out.print("]");
	}

	public void writeArrayUpdate(Expr.Operator expr) {
		writeExpressionWithBrackets(expr.get(0));
		out.print("[");
		writeExpression(expr.get(1));
		out.print(":=");
		writeExpression(expr.get(2));
		out.print("]");
	}

	public void writeRecordUpdate(Expr.RecordUpdate expr) {
		writeExpressionWithBrackets(expr.getSource());
		out.print("{");
		out.print(expr.getField().get());
		out.print(":=");
		writeExpression(expr.getValue());
		out.print("}");
	}

	public void writeRecordAccess(Expr.RecordAccess expr) {
		writeExpressionWithBrackets(expr.getSource());
		out.print(".");
		out.print(expr.getField().get());
	}

	public void writeRecordInitialiser(Expr.RecordInitialiser expr) {
		out.print("{");
		Pair[] fields = expr.getFields();
		for(int i=0;i!=fields.length;++i) {
			if(i != 0) {
				out.print(", ");
			}
			Pair p = fields[i];
			Identifier f = (Identifier) p.get(0);
			Expr e = (Expr) p.get(1);
			out.print(f.get());
			out.print(": ");
			writeExpression(e);
		}
		out.print("}");
	}

	private void writeQuantifier(Expr.Quantifier stmt) {
		if (stmt.getOpcode() == WyalFile.EXPR_forall) {
			out.print("forall");
		} else {
			out.print("exists");
		}
		writeVariableDeclarations(stmt.getParameters());
		out.print(".");
		writeExpressionWithBrackets(stmt.getBody());
	}

	public void writeArguments(Expr[] exprs) {
		for(int i=0;i!=exprs.length;++i) {
			if(i!=0) {
				out.print(", ");
			}
			writeExpression(exprs[i]);
		}
	}

	public void writeType(Type type) {
		switch (type.getOpcode()) {
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
			Type.Nominal t = (Type.Nominal) type;
			writeName(t.getName());
			break;
		}
		case TYPE_arr: {
			Type.Array t = (Type.Array) type;
			writeTypeWithBraces(t.getElement());
			out.print("[]");
			break;
		}
		case TYPE_ref: {
			out.print("&");
			Type.Reference t = (Type.Reference) type;
			if(t.getLifetime() != null) {
				out.print(t.getLifetime());
				out.print(":");
			}
			writeTypeWithBraces(t.getElement());
			break;
		}
		case TYPE_rec: {
			Type.Record t = (Type.Record) type;
			FieldDeclaration[] fields = t.getFields();
			out.print("{");
			for (int i = 0; i != fields.length; ++i) {
				if (i != 0) {
					out.print(", ");
				}
				writeFieldDeclaration(fields[i]);
			}
			if(t.isOpen()) {
				if (fields.length > 0) {
					out.print(", ");
				}
				out.print("...");
			}
			out.print("}");
			break;
		}
		case TYPE_not: {
			out.print("!");
			Type.Negation t = (Type.Negation) type;
			writeTypeWithBraces(t.getElement());
			break;
		}
		case TYPE_or: {
			Type.Union t = (Type.Union) type;
			for (int i = 0; i != type.size(); ++i) {
				if (i != 0) {
					out.print("|");
				}
				writeTypeWithBraces(t.get(i));
			}
			break;
		}
		case TYPE_and: {
			Type.Intersection t = (Type.Intersection) type;
			for (int i = 0; i != type.size(); ++i) {
				if (i != 0) {
					out.print("&");
				}
				writeTypeWithBraces(t.get(i));
			}
			break;
		}
		case TYPE_fun: {
			Type.Function t = (Type.Function) type;
			out.print("function");
			writeTypeArray(t.getParameters());
			out.print("->");
			writeTypeArray(t.getReturns());
			break;
		}
		case TYPE_property: {
			Type.Property t = (Type.Property) type;
			out.print("macro");
			writeTypeArray(t.getParameters());
			break;
		}
		case TYPE_inv: {
			Type.Invariant t = (Type.Invariant) type;
			out.print("invariant");
			writeTypeArray(t.getParameters());
			break;
		}
		default:
			throw new RuntimeException("Unknown type encountered: " + type);
		}
	}

	private void writeTypeArray(Tuple<Type> types) {
		out.print("(");
		for(int i=0;i!=types.size();++i) {
			if(i != 0) {
				out.print(",");
			}
			writeType(types.get(i));
		}
		out.print(")");
	}

	private void writeTypeWithBraces(Type type) {
		switch (type.getOpcode()) {
		case TYPE_or:
		case TYPE_and:
		case TYPE_arr:
			out.print("(");
			writeType(type);
			out.print(")");
			break;
		default:
			writeType(type);
		}

	}

	private void writeName(Name n) {
		for(int i=0;i!=n.size();++i) {
			if(i!=0) {
				out.print(".");
			}
			out.print(n.get(i).get());
		}
	}

	private void indent(int indent) {
		indent = indent * 4;
		for (int i = 0; i < indent; ++i) {
			out.print(" ");
		}
	}

	/**
	 * A fixed map from token kinds to their correspond bytecode opcodes.
	 */
	private static final HashMap<Integer, String> OPERATOR_MAP = new HashMap<>();

	static {
		OPERATOR_MAP.put(WyalFile.EXPR_and, "&&");
		OPERATOR_MAP.put(WyalFile.EXPR_or, "||");
		OPERATOR_MAP.put(WyalFile.EXPR_implies, "==>");
		OPERATOR_MAP.put(WyalFile.EXPR_iff, "<==>");
		OPERATOR_MAP.put(WyalFile.EXPR_lteq, "<=");
		OPERATOR_MAP.put(WyalFile.EXPR_lt, "<");
		OPERATOR_MAP.put(WyalFile.EXPR_gteq, ">=");
		OPERATOR_MAP.put(WyalFile.EXPR_gt, ">");
		OPERATOR_MAP.put(WyalFile.EXPR_eq, "==");
		OPERATOR_MAP.put(WyalFile.EXPR_neq, "!=");
		OPERATOR_MAP.put(WyalFile.EXPR_is, "is");
		OPERATOR_MAP.put(WyalFile.EXPR_add, "+");
		OPERATOR_MAP.put(WyalFile.EXPR_sub, "-");
		OPERATOR_MAP.put(WyalFile.EXPR_mul, "*");
		OPERATOR_MAP.put(WyalFile.EXPR_div, "/");
		OPERATOR_MAP.put(WyalFile.EXPR_rem, "%");
	}
}