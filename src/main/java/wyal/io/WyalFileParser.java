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

import static wyal.io.WyalFileLexer.Token.Kind.*;
import java.math.BigInteger;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;

import wyal.io.WyalFileLexer.Token;
import static wyal.lang.WyalFile.*;

import wyal.lang.WyalFile;
import wyal.lang.WyalFile.Opcode;
import wybs.lang.Attribute;
import wybs.lang.SyntacticElement;
import wybs.lang.SyntaxError;
import wyfs.lang.Path;
import wyfs.util.Trie;

public class WyalFileParser {
	private final Path.Entry<WyalFile> entry;
	private ArrayList<Token> tokens;
	private int index;

	public WyalFileParser(Path.Entry<WyalFile> entry, List<Token> tokens) {
		this.entry = entry;
		this.tokens = new ArrayList<>(tokens);
	}

	/**
	 * Read a <code>WyalFile</code> from the token stream. If the stream is
	 * invalid in some way (e.g. contains a syntax error, etc) then a
	 * <code>SyntaxError</code> is thrown.
	 *
	 * @return
	 */
	public WyalFile read() {
		Path.ID pkg = parsePackage();

		// Construct object representing this WyalFile.
		WyalFile wf = new WyalFile(entry);

		skipWhiteSpace();
		while (index < tokens.size()) {
			Token lookahead = tokens.get(index);
			Declaration declaration;
			if (lookahead.kind == Import) {
				declaration = parseImportDeclaration(wf);
			} else {
				checkNotEof();
				lookahead = tokens.get(index);
				if (lookahead.kind == Assert) {
					declaration = parseAssertDeclaration(wf);
				} else if (lookahead.text.equals("type")) {
					declaration = parseTypeDeclaration(wf);
				} else if (lookahead.text.equals("define")) {
					declaration = parseMacroDeclaration(wf);
				} else if (lookahead.kind == Function) {
					declaration = parseFunctionDeclaration(wf);
				} else {
					syntaxError("unrecognised declaration", lookahead);
					return null; // dead-code
				}
			}
			wf.allocate(declaration);
			skipWhiteSpace();
		}

		return wf;
	}

	private Trie parsePackage() {
		Trie pkg = Trie.ROOT;

		if (tryAndMatch(true, Package) != null) {
			// found a package keyword
			pkg = pkg.append(match(Identifier).text);

			while (tryAndMatch(true, Dot) != null) {
				pkg = pkg.append(match(Identifier).text);
			}

			matchEndLine();
			return pkg;
		} else {
			return pkg; // no package
		}
	}

	/**
	 * Parse an import declaration, which is of the form:
	 *
	 * <pre>
	 * ImportDecl ::= Identifier ["from" ('*' | Identifier)] ( ('.' | '..') ('*' | Identifier) )*
	 * </pre>
	 *
	 * @param parent
	 *            WyalFile being constructed
	 */
	private Declaration parseImportDeclaration(WyalFile parent) {
		int start = index;
		EnclosingScope scope = new EnclosingScope(parent);

		match(Import);
		Identifier[] filterPath = parseFilterPath(scope);

		int end = index;
		matchEndLine();

		Declaration.Import imprt = new Declaration.Import(filterPath);
		imprt.attributes().add(sourceAttr(start, end - 1));
		return imprt;
	}

	private Identifier[] parseFilterPath(EnclosingScope scope) {
		// Parse package filter string
		ArrayList<Identifier> components = new ArrayList<>();
		components.add(parseIdentifier(scope));
		while (tryAndMatch(true, Dot) != null) {
			Identifier component = parseStarOrIdentifier(scope);
			components.add(component);
		}
		//
		return components.toArray(new Identifier[components.size()]);
	}

	private Identifier parseStarOrIdentifier(EnclosingScope scope) {
		if (tryAndMatch(true, Star) != null) {
			// TODO: implement something sensible here
			return null;
		} else {
			return parseIdentifier(scope);
		}
	}

	/**
	 * Parse an <code>assert</code> declaration in a WyAL source file.
	 *
	 * @param wf
	 *            The WyAL file in which this declaration is defined.
	 */
	protected Declaration parseAssertDeclaration(WyalFile parent) {
		EnclosingScope scope = new EnclosingScope(parent);
		int start = index;
		String message = null;
		//
		match(Assert);
		if(tryAndMatch(false,Colon) == null) {
			Token token = match(StringValue);
			message = parseString(token.text);
			match(Colon);
		}

		matchEndLine();
		Stmt.Block body = parseStatementBlock(scope, ROOT_INDENT);
		Declaration.Assert declaration = new Declaration.Assert(body,message);
		declaration.attributes().add(sourceAttr(start, index - 1));
		return declaration;
	}

	/**
	 * Parse a <code>type</code> declaration in a WyAL source file.
	 *
	 * @param wf
	 *            The WyAL file in which this declaration is defined.
	 */
	protected Declaration parseTypeDeclaration(WyalFile parent) {
		EnclosingScope scope = new EnclosingScope(parent);
		int start = index;
		//
		// Match identifier rather than kind e.g. keyword type to avoid "type"
		// being a keyword. We already know that the identifier in question must
		// be "type" as, otherwise, this method would not have been called.
		match(Identifier);
		//
		Identifier name = parseIdentifier(scope);
		match(Is);
		// Parse parameter declaration and invariant (if applicable)
		match(LeftBrace);
		VariableDeclaration parameter = parseParameterDeclaration(scope);
		match(RightBrace);
		//
		Stmt.Block[] invariant = parseInvariantClauses(scope);
		//
		Declaration.Named.Type declaration = new Declaration.Named.Type(name, parameter, invariant);
		declaration.attributes().add(sourceAttr(start, index - 1));
		return declaration;
	}

	private Stmt.Block[] parseInvariantClauses(EnclosingScope scope) {
		List<Stmt.Block> invariant = new ArrayList<>();
		while ((tryAndMatch(true, Where)) != null) {
			Stmt.Block block;
			if (tryAndMatch(true, Colon) != null) {
				block = parseStatementBlock(scope, ROOT_INDENT);
			} else {
				Stmt stmt = parseUnitExpression(scope, false);
				block = new Stmt.Block(stmt);
				matchEndLine();
			}
			invariant.add(block);
		}
		return invariant.toArray(new Stmt.Block[invariant.size()]);
	}

	protected Declaration parseFunctionDeclaration(WyalFile parent) {
		EnclosingScope scope = new EnclosingScope(parent);
		int start = index;
		//
		match(Function);
		Identifier name = parseIdentifier(scope);
		//
		VariableDeclaration[] parameters = parseParameterDeclarations(scope);
		match(MinusGreater);
		VariableDeclaration[] returns = parseParameterDeclarations(scope);
		matchEndLine();
		//
		Declaration.Named.Function declaration = new Declaration.Named.Function(name, parameters, returns);
		declaration.attributes().add(sourceAttr(start, index - 1));
		return declaration;
	}

	protected Declaration parseMacroDeclaration(WyalFile parent) {
		EnclosingScope scope = new EnclosingScope(parent);
		int start = index;
		//
		match(Define);
		Identifier name = parseIdentifier(scope);
		//
		VariableDeclaration[] parameters = parseParameterDeclarations(scope);
		match(Is);
		match(Colon);
		Stmt.Block body = parseStatementBlock(scope, ROOT_INDENT);
		// Create empty declaration
		Declaration.Named.Macro declaration = new Declaration.Named.Macro(name, parameters, body);
		declaration.attributes().add(sourceAttr(start, index - 1));
		return declaration;
	}

	/**
	 * Parse a block of zero or more "statements" which share the same
	 * indentation level. Their indentation level must be strictly greater than
	 * that of their parent, otherwise the end of block is signaled. The
	 * <i>indentation level</i> for the block is set by the first statement
	 * encountered (assuming their is one). An error occurs if a subsequent
	 * statement is reached with an indentation level <i>greater</i> than the
	 * block's indentation level.
	 *
	 * @param wf
	 *            The enclosing WyalFile being constructed.
	 * @param parentIndent
	 *            The indentation level of the parent, for which all statements
	 *            in this block must have a greater indent. May not be
	 *            <code>null</code>.
	 * @return
	 */
	private Stmt.Block parseStatementBlock(EnclosingScope scope, Indent parentIndent) {
		// First, determine the initial indentation of this block based on the
		// first statement (or null if there is no statement).
		Indent indent = getIndent();

		// Second, check that this is indeed the initial indentation for this
		// block (i.e. that it is strictly greater than parent indent).
		if (indent == null || indent.lessThanEq(parentIndent)) {
			// Initial indent either doesn't exist or is not strictly greater
			// than parent indent and,therefore, signals an empty block.
			//
			Expr bool = new Expr.Constant(new Value.Bool(true));
			return new Stmt.Block(bool);
		} else {
			// Initial indent is valid, so we proceed parsing statements with
			// the appropriate level of indent.
			//
			ArrayList<Stmt> statements = new ArrayList<>();
			Indent nextIndent;
			while ((nextIndent = getIndent()) != null && indent.lessThanEq(nextIndent)) {
				// At this point, nextIndent contains the indent of the current
				// statement. However, this still may not be equivalent to this
				// block's indentation level.
				//
				// First, check the indentation matches that for this block.
				if (!indent.equivalent(nextIndent)) {
					// No, it's not equivalent so signal an error.
					syntaxError("unexpected end-of-block", indent);
				}
				// Second, parse the actual statement at this point!
				statements.add(parseStatement(scope, indent));
			}
			return new Stmt.Block(toStmtArray(statements));
		}
	}

	/**
	 * Determine the indentation as given by the Indent token at this point (if
	 * any). If none, then <code>null</code> is returned.
	 *
	 * @return
	 */
	private Indent getIndent() {
		skipEmptyLines();
		if (index < tokens.size()) {
			Token token = tokens.get(index);
			if (token.kind == Indent) {
				return new Indent(token.text, token.start);
			}
			return null;
		}
		return null;
	}

	/**
	 * Parse a statement expression.
	 *
	 * @param scope
	 *            The enclosing scope for this expression. This identifies any
	 *            generic arguments which are in scope, and also allocated each
	 *            variable in scope to its location index.
	 * @param environment
	 *            The set of declared variables visible in the enclosing scope.
	 *            This is necessary to identify local variables within this
	 *            expression.
	 * @return
	 */
	private Stmt parseStatement(EnclosingScope scope, Indent indent) {
		checkNotEof();

		Token lookahead = tryAndMatch(false, If, Either, Exists, Forall);

		if (lookahead != null && lookahead.kind == If) {
			return parseIfThenStatement(scope, indent);
		} else if (lookahead != null && lookahead.kind == Either) {
			return parseEitherOrStatement(scope, indent);
		} else if (lookahead != null && lookahead.kind == Forall) {
			return parseExistsForallStatement(lookahead, scope, indent);
		} else if (lookahead != null && lookahead.kind == Exists) {
			return parseExistsForallStatement(lookahead, scope, indent);
		} else {
			Expr stmt = parseUnitExpression(scope, false);
			matchEndLine();
			return stmt;
		}
	}

	/**
	 * Parse an if-then expression.
	 *
	 * @param scope
	 *            The enclosing scope for this expression. This identifies any
	 *            generic arguments which are in scope, and also allocated each
	 *            variable in scope to its location index.
	 * @param environment
	 *            The set of declared variables visible in the enclosing scope.
	 *            This is necessary to identify local variables within this
	 *            expression.
	 * @return
	 */
	private Stmt parseIfThenStatement(EnclosingScope scope, Indent indent) {
		int start = index;
		match(Colon);
		matchEndLine();
		Stmt.Block ifBlock = parseStatementBlock(scope, indent);
		match(Then);
		match(Colon);
		matchEndLine();
		Stmt.Block thenBlock = parseStatementBlock(scope, indent);
		Stmt stmt = new Stmt.IfThen(ifBlock, thenBlock);
		stmt.attributes().add(sourceAttr(start, index - 1));
		return stmt;
	}

	private Stmt parseEitherOrStatement(EnclosingScope scope, Indent indent) {
		int start = index;

		ArrayList<Stmt.Block> blocks = new ArrayList<>();
		Indent nextIndent;
		Token lookahead;

		do {
			match(Colon);
			matchEndLine();
			blocks.add(parseStatementBlock(scope, indent));
			nextIndent = getIndent();
			if (nextIndent != null && nextIndent.equivalent(indent)) {
				lookahead = tryAndMatch(false, Or);
			} else {
				lookahead = null;
			}
		} while (lookahead != null && lookahead.kind == Or);

		Stmt.Block[] arr = blocks.toArray(new Stmt.Block[blocks.size()]);
		Stmt stmt = new Stmt.CaseOf(arr);
		stmt.attributes().add(sourceAttr(start, index - 1));
		return stmt;
	}

	/**
	 * Parse a quantifier expression.
	 *
	 * @param scope
	 *            The enclosing scope for this expression. This identifies any
	 *            generic arguments which are in scope, and also allocated each
	 *            variable in scope to its location index.
	 * @param environment
	 *            The set of declared variables visible in the enclosing scope.
	 *            This is necessary to identify local variables within this
	 *            expression.
	 * @return
	 */
	private Stmt parseExistsForallStatement(Token lookahead, EnclosingScope scope, Indent indent) {
		int start = index - 1;
		// Clone the environment here, since the following type pattern may
		// updated this and such updates should only be visible to the
		// conditions contained within the quantified statement.
		scope = scope.clone();
		// Parse the parameter declarations for this block
		VariableDeclaration[] parameters = parseParameterDeclarations(scope);
		// Parser the body
		Stmt.Block body;
		if (tryAndMatch(true, Colon) != null) {
			matchEndLine();
			body = parseStatementBlock(scope, indent);
		} else {
			match(Dot);
			Stmt unit = parseUnitExpression(scope, false);
			body = new Stmt.Block(unit);
		}
		//
		Stmt stmt;
		if(lookahead.kind == Forall) {
			stmt = new Stmt.UniversalQuantifier(parameters, body);
		} else {
			stmt = new Stmt.ExistentialQuantifier(parameters, body);
		}
		stmt.attributes().add(sourceAttr(start, index - 1));
		return stmt;
	}

	private VariableDeclaration[] parseParameterDeclarations(EnclosingScope scope) {
		ArrayList<VariableDeclaration> parameters = new ArrayList<>();
		match(LeftBrace);
		boolean firstTime = true;
		while (eventuallyMatch(RightBrace) == null) {
			if (!firstTime) {
				match(Comma);
			} else {
				firstTime = false;
			}
			parameters.add(parseParameterDeclaration(scope));
		}
		return parameters.toArray(new VariableDeclaration[parameters.size()]);
	}

	private VariableDeclaration parseParameterDeclaration(EnclosingScope scope) {
		int start = index;
		Type type = parseType(scope);
		Identifier name = parseIdentifier(scope);
		VariableDeclaration stmt = new VariableDeclaration(type,name);
		stmt.attributes().add(sourceAttr(start,index-1));
		scope.declareInScope(stmt);
		return stmt;
	}

	/**
	 * Parse a tuple expression, which has the form:
	 *
	 * <pre>
	 * TupleExpr::= Expr (',' Expr)*
	 * </pre>
	 *
	 * Tuple expressions are expressions which can return multiple values (i.e.
	 * tuples). In many situations, tuple expressions are not permitted since
	 * tuples cannot be used in that context.
	 *
	 * @param scope
	 *            The enclosing scope for this expression. This identifies any
	 *            generic arguments which are in scope, and also allocated each
	 *            variable in scope to its location index.
	 * @param terminated
	 *            This indicates that the expression is known to be terminated
	 *            (or not). An expression that's known to be terminated is one
	 *            which is guaranteed to be followed by something. This is
	 *            important because it means that we can ignore any newline
	 *            characters encountered in parsing this expression, and that
	 *            we'll never overrun the end of the expression (i.e. because
	 *            there's guaranteed to be something which terminates this
	 *            expression). A classic situation where terminated is true is
	 *            when parsing an expression surrounded in braces. In such case,
	 *            we know the right-brace will always terminate this expression.
	 *
	 * @return
	 */
	private Expr parseMultiExpression(EnclosingScope scope, boolean terminated) {
//		int start = index;
//		Expr lhs = parseUnitExpression(wf, generics, environment, terminated);
//
//		if (tryAndMatch(terminated, Comma) != null) {
//			// Indicates this is a tuple expression.
//			ArrayList<Expr> elements = new ArrayList<Expr>();
//			elements.add(lhs);
//			// Add all expressions separated by a comma
//			do {
//				elements.add(parseUnitExpression(wf, generics, environment,
//						terminated));
//			} while (tryAndMatch(terminated, Comma) != null);
//			// Done
//			return new Expr.Nary(Expr.Nary.Op.TUPLE, elements, sourceAttr(
//					start, index - 1));
//		}
//
//		return lhs;
		throw new IllegalArgumentException("IMPLEMENT ME!");
	}

	private Expr parseUnitExpression(EnclosingScope scope, boolean terminated) {
		checkNotEof();
		int start = index;
		Expr lhs = parseInfixExpression(scope, terminated);
		if (tryAndMatch(terminated, Is) == null) {
			return lhs;
		} else {
			Type rhs = parseType(scope);
			WyalFile.Expr expr = new Expr.Is(lhs, rhs);
			expr.attributes().add(sourceAttr(start, index - 1));
			return expr;
		}
	}

	/**
	 * Parse an infix expression of the form.
	 *
	 * @param scope
	 *            The enclosing scope for this expression. This identifies any
	 *            generic arguments which are in scope, and also allocated each
	 *            variable in scope to its location index.
	 * @param terminated
	 *            This indicates that the expression is known to be terminated
	 *            (or not). An expression that's known to be terminated is one
	 *            which is guaranteed to be followed by something. This is
	 *            important because it means that we can ignore any newline
	 *            characters encountered in parsing this expression, and that
	 *            we'll never overrun the end of the expression (i.e. because
	 *            there's guaranteed to be something which terminates this
	 *            expression). A classic situation where terminated is true is
	 *            when parsing an expression surrounded in braces. In such case,
	 *            we know the right-brace will always terminate this expression.
	 *
	 * @return
	 */
	private Expr parseInfixExpression(EnclosingScope scope, boolean terminated) {
		checkNotEof();
		int start = index;
		// Parse term
		Expr first = parseAccessExpression(scope, terminated);
		// See whether there is an infix operator trailing after term
		Token lookahead = tryAndMatch(terminated, INFIX_OPERATORS);
		if (lookahead != null) {
			// Yes, there is so try and parse operator sequence.
			ArrayList<Expr> operands = new ArrayList<>();
			operands.add(first);
			do {
				operands.add(parseAccessExpression(scope, terminated));
			} while (tryAndMatch(terminated, lookahead.kind) != null);
			//
			Expr expr = constructInfixExpression(lookahead, toExprArray(operands));
			expr.attributes().add(sourceAttr(start, index - 1));
			// Check for ambiguous operator expression
			if ((lookahead = tryAndMatch(terminated, INFIX_OPERATORS)) != null) {
				// If we get here, then it means we parsed a sequence of 1 or
				// more operators of the same kind. But, now, we find another
				// operator of a different kind.
				syntaxError("ambiguous expression encountered (braces required)", lookahead);
			}
			//
			return expr;
		} else {
			return first;
		}
	}

	/**
	 * Parse an <i>access expression</i>, which has the form:
	 *
	 * <pre>
	 * AccessExpr::= PathExpr
	 *            | AccessExpr '[' AdditiveExpr ']'
	 *            | AccessExpr '.' Identifier
	 *            | AccessExpr '.' Identifier '(' [ Expr (',' Expr)* ] ')'
	 *            | AccessExpr "->" Identifier
	 * </pre>
	 *
	 * <p>
	 * Access expressions are challenging for several reasons. First, they are
	 * <i>left-recursive</i>, making them more difficult to parse correctly.
	 * Secondly, there are several different forms above and, of these, some
	 * generate multiple AST nodes as well (see below).
	 * </p>
	 *
	 * <p>
	 * This parser attempts to construct the most accurate AST possible and this
	 * requires disambiguating otherwise identical forms. For example, an
	 * expression of the form "aaa.bbb.ccc" can correspond to either a field
	 * access, or a constant expression (e.g. with a package/module specifier).
	 * Likewise, an expression of the form "aaa.bbb.ccc()" can correspond to an
	 * indirect function/method call, or a direct function/method call with a
	 * package/module specifier. To disambiguate these forms, the parser relies
	 * on the fact any sequence of field-accesses must begin with a local
	 * variable.
	 * </p>
	 *
	 * @param scope
	 *            The enclosing scope for this statement, which determines the
	 *            set of visible (i.e. declared) variables and also the current
	 *            indentation level.
	 * @param terminated
	 *            This indicates that the expression is known to be terminated
	 *            (or not). An expression that's known to be terminated is one
	 *            which is guaranteed to be followed by something. This is
	 *            important because it means that we can ignore any newline
	 *            characters encountered in parsing this expression, and that
	 *            we'll never overrun the end of the expression (i.e. because
	 *            there's guaranteed to be something which terminates this
	 *            expression). A classic situation where terminated is true is
	 *            when parsing an expression surrounded in braces. In such case,
	 *            we know the right-brace will always terminate this expression.
	 *
	 * @return
	 */
	private Expr parseAccessExpression(EnclosingScope scope, boolean terminated) {
		int start = index;
		Expr lhs = parsePathExpression(scope, terminated);
		Token token;

		while ((token = tryAndMatch(terminated, LeftSquare,LeftCurly, Dot, MinusGreater)) != null) {
			switch (token.kind) {
			case LeftSquare: {
				// NOTE: expression guaranteed to be terminated by ']'.
				Expr rhs = parseUnitExpression(scope, true);
				if(tryAndMatchOnLine(ColonEquals) != null) {
					// This is an array update expression
					Expr mhs = parseUnitExpression(scope, true);
					match(RightSquare);
					lhs = new Expr.ArrayUpdate(lhs, rhs, mhs);
					lhs.attributes().add(sourceAttr(start, index - 1));
				} else {
					// This is a plain old array access expression
					match(RightSquare);
					lhs = new Expr.ArrayAccess(lhs, rhs);
					lhs.attributes().add(sourceAttr(start, index - 1));
				}
				break;
			}
			case LeftCurly: {
				// This is a record update update expression
				Identifier mhs = parseIdentifier(scope);
				match(ColonEquals);
				Expr rhs = parseUnitExpression(scope, true);
				match(RightCurly);
				lhs = new Expr.RecordUpdate(lhs, mhs, rhs);
				lhs.attributes().add(sourceAttr(start, index - 1));
				break;
			}
			case Dot: {
				Identifier rhs = parseIdentifier(scope);
				lhs = new Expr.RecordAccess(lhs, rhs);
				lhs.attributes().add(sourceAttr(start, index - 1));
				break;
			}
			}
		}

		return lhs;
	}

	/**
	 * Parse a <i>path expression</i> which has the form:
	 *
	 * <pre>
	 * PathExpr::= | PrimaryExpr
	 *             | Identifier '.' PathExpr
	 *             | PathExpr '(' [ Expr (',' Expr)* ] ')'
	 * </pre>
	 *
	 * The key distinction from an access expression is that the root identifier
	 * is <i>non-local</i>. That is, it is not declared within the enclosing
	 * declaration.
	 *
	 * @param scope
	 * @param terminated
	 * @return
	 */
	private Expr parsePathExpression(EnclosingScope scope, boolean terminated) {
		int start = index;
		int next = skipLineSpace(index);
		Token lookahead = tokens.get(next);
		if (lookahead.kind != Identifier || scope.isDeclaredVariable(lookahead.text)) {
			// This is not a path expression because either the next token is
			// not an identifier, or the identifier is a local variable.
			return parseTermExpression(scope, terminated);
		} else {
			Name nid = parseNameID(scope);
			// At this point, either we have a function invocation, or we have a
			// constant access.
			lookahead = tokens.get(skipLineSpace(index));
			if (lookahead.kind == LeftBrace) {
				// This is a function invocation.
				return parseInvokeExpression(nid, scope, start, terminated);
			} else {
				// This is a constant access
				syntaxError("constant expression not supported", lookahead);
				return null;
			}
		}
	}

	/**
	 * Parse an invocation expression, which has the form:
	 *
	 * <pre>
	 * InvokeExpr::= PathExpr '(' [ Expr (',' Expr)* ] ')'
	 * </pre>
	 *
	 * Observe that this when this function is called, we're assuming that the
	 * identifier and opening brace has already been matched.
	 *
	 * @param scope
	 *            The enclosing scope for this expression. This identifies any
	 *            generic arguments which are in scope, and also allocated each
	 *            variable in scope to its location index.
	 * @param terminated
	 *            This indicates that the expression is known to be terminated
	 *            (or not). An expression that's known to be terminated is one
	 *            which is guaranteed to be followed by something. This is
	 *            important because it means that we can ignore any newline
	 *            characters encountered in parsing this expression, and that
	 *            we'll never overrun the end of the expression (i.e. because
	 *            there's guaranteed to be something which terminates this
	 *            expression). A classic situation where terminated is true is
	 *            when parsing an expression surrounded in braces. In such case,
	 *            we know the right-brace will always terminate this expression.
	 *
	 * @return
	 */
	private Expr parseInvokeExpression(Name nid, EnclosingScope scope, int start, boolean terminated) {
		// Create a dummy nameid which will be resolved later on
		// Parse arguments
		Expr[] args = parseInvocationArguments(scope);
		// Parse selector (if present)
		Integer selector = null;
		if (tryAndMatch(terminated, Hash) != null) {
			Token t = match(IntValue);
			selector = new Integer(t.text);
		}
		// Construct relevant bytecode. The type signature is left as null at
		// this stage, since we cannot determined at this point.
		Expr ivk = new Expr.Invoke(null, nid, selector, args);
		ivk.attributes().add(sourceAttr(start, index - 1));
		return ivk;
	}

	/**
	 *
	 * @param scope
	 *            The enclosing scope for this expression. This identifies any
	 *            generic arguments which are in scope, and also allocated each
	 *            variable in scope to its location index.
	 * @param terminated
	 *            This indicates that the expression is known to be terminated
	 *            (or not). An expression that's known to be terminated is one
	 *            which is guaranteed to be followed by something. This is
	 *            important because it means that we can ignore any newline
	 *            characters encountered in parsing this expression, and that
	 *            we'll never overrun the end of the expression (i.e. because
	 *            there's guaranteed to be something which terminates this
	 *            expression). A classic situation where terminated is true is
	 *            when parsing an expression surrounded in braces. In such case,
	 *            we know the right-brace will always terminate this expression.
	 *
	 * @return
	 */
	private Expr parseTermExpression(EnclosingScope scope, boolean terminated) {
		checkNotEof();

		int start = index;
		Token token = tokens.get(index);

		switch (token.kind) {
		case LeftBrace:
			return parseBracketedExpression(scope, terminated);
		case Identifier:
			if (scope.isDeclaredVariable(token.text)) {
				// Signals a local variable access
				match(Identifier);
				VariableDeclaration decl = scope.getVariableDeclaration(token.text);
				Expr expr = new Expr.VariableAccess(decl);
				expr.attributes().add(sourceAttr(start, index - 1));
				return expr;
			} else {
				// Otherwise, we have an error since this should have already
				// been parsed as a path expression.
			}
			break;
		case Null:
		case True:
		case False:
		case CharValue:
		case IntValue:
		case RealValue:
		case StringValue:
			return parseConstantExpression(token, scope);
		case Minus:
			return parseNegationExpression(scope, terminated);
		case VerticalBar:
			return parseLengthOfExpression(scope, terminated);
		case LeftSquare:
			return parseArrayInitialiserExpression(scope, terminated);
		case LeftCurly:
			return parseRecordExpression(scope, terminated);
		case Star:
			return parseDereferenceExpression(scope, terminated);
		case Shreak:
			return parseLogicalNotExpression(scope, terminated);
		case Forall:
		case Exists:
			return parseQuantifiedExpression(token,scope,terminated);
		}

		syntaxError("unrecognised term", token);
		return null; //deadcode
	}

	private Expr parseConstantExpression(Token token, EnclosingScope scope) {
		match(token.kind);
		Value item;
		switch (token.kind) {
		case Null:
			item = new Value.Null();
			break;
		case True:
			item = new Value.Bool(true);
			break;
		case False:
			item = new Value.Bool(false);
			break;
		case IntValue: {
			BigInteger val = new BigInteger(token.text);
			item = new Value.Int(val);
			break;
		}
		case StringValue: {
			String str = parseString(token.text);
			// FIXME: following may be broken because of conversion between
			// UTF16 from java.lang.String.
			item = new Value.UTF8(str.getBytes());
			break;
		}
		default:
			syntaxError("unrecognised constant", token);
			return null; // deadcode
		}

		Expr expr = new Expr.Constant(item);
		expr.attributes().add(new Attribute.Source(token.start, token.end(), 0));
		return expr;
	}

	/**
	 * Parse an expression beginning with a left brace. This is either a cast or
	 * bracketed expression:
	 *
	 * <pre>
	 * BracketedExpr ::= '(' Type ')' Expr
	 *                      | '(' Expr ')'
	 * </pre>
	 *
	 * <p>
	 * The challenge here is to disambiguate the two forms (which is similar to
	 * the problem of disambiguating a variable declaration from e.g. an
	 * assignment). Getting this right is actually quite tricky, and we need to
	 * consider what permissible things can follow a cast and/or a bracketed
	 * expression. To simplify things, we only consider up to the end of the
	 * current line in determining whether this is a cast or not. That means
	 * that the expression following a cast *must* reside on the same line as
	 * the cast.
	 * </p>
	 *
	 * <p>
	 * A cast can be followed by the start of any valid expression. This
	 * includes: identifiers (e.g. "(T) x"), braces of various kinds (e.g.
	 * "(T) [1,2]" or "(T) (1,2)"), unary operators (e.g. "(T) !x", "(T) |xs|",
	 * etc). A bracketed expression, on the other hand, can be followed by a
	 * binary operator (e.g. "(e) + 1"), a left- or right-brace (e.g.
	 * "(1 + (x+1))" or "(*f)(1)") or a newline.
	 * </p>
	 * <p>
	 * Most of these are easy to disambiguate by the following rules:
	 * </p>
	 * <ul>
	 * <li>If what follows is a binary operator (e.g. +, -, etc) then this is an
	 * bracketed expression, not a cast.</li>
	 * <li>If what follows is a right-brace then this is a bracketed expression,
	 * not a cast.</li>
	 * <li>Otherwise, this is a cast.</li>
	 * </ul>
	 * <p>
	 * Unfortunately, there are two problematic casts: '-' and '('. In Java, the
	 * problem of '-' is resolved carefully as follows:
	 * </p>
	 *
	 * <pre>
	 * CastExpr::= ( PrimitiveType Dimsopt ) UnaryExpression
	 *                 | ( ReferenceType ) UnaryExpressionNotPlusMinus
	 * </pre>
	 *
	 * See JLS 15.16 (Cast Expressions). This means that, in cases where we can
	 * be certain we have a type, then a general expression may follow;
	 * otherwise, only a restricted expression may follow.
	 *
	 * @param scope
	 *            The enclosing scope for this expression. This identifies any
	 *            generic arguments which are in scope, and also allocated each
	 *            variable in scope to its location index.
	 * @param terminated
	 *            This indicates that the expression is known to be terminated
	 *            (or not). An expression that's known to be terminated is one
	 *            which is guaranteed to be followed by something. This is
	 *            important because it means that we can ignore any newline
	 *            characters encountered in parsing this expression, and that
	 *            we'll never overrun the end of the expression (i.e. because
	 *            there's guaranteed to be something which terminates this
	 *            expression). A classic situation where terminated is true is
	 *            when parsing an expression surrounded in braces. In such case,
	 *            we know the right-brace will always terminate this expression.
	 *
	 * @return
	 */
	private Expr parseBracketedExpression(EnclosingScope scope, boolean terminated) {
		int start = index;
		match(LeftBrace);

		// At this point, we must begin to disambiguate casts from general
		// bracketed expressions. In the case that what follows the left brace
		// is something which can only be a type, then clearly we have a cast.
		// However, in the other case, we may still have a cast since many types
		// cannot be clearly distinguished from expressions at this stage (e.g.
		// "(nat,nat)" could either be a tuple type (if "nat" is a type) or a
		// tuple expression (if "nat" is a variable or constant).

		Type t = parseDefiniteType(scope);

		if (t != null) {
			// At this point, it's looking likely that we have a cast. However,
			// it's not certain because of the potential for nested braces. For
			// example, consider "((char) x + y)". We'll parse the outermost
			// brace and what follows *must* be parsed as either a type, or
			// bracketed type.
			if (tryAndMatch(true, RightBrace) != null) {
				// Ok, finally, we are sure that it is definitely a cast.
				Expr e = parseMultiExpression(scope, terminated);
				Expr expr = new Expr.Cast(t, e);
				expr.attributes().add(sourceAttr(start, index - 1));
				return expr;
			}
		}
		// We still may have either a cast or a bracketed expression, and we
		// cannot tell which yet.
		index = start;
		match(LeftBrace);
		Expr e = parseUnitExpression(scope, true);
		match(RightBrace);

		// At this point, we now need to examine what follows to see whether
		// this is a cast or bracketed expression. See JavaDoc comments
		// above for more on this. What we do is first skip any whitespace,
		// and then see what we've got.
		int next = skipLineSpace(index);
		if (next < tokens.size()) {
			Token lookahead = tokens.get(next);

			switch (lookahead.kind) {
			case Null:
			case True:
			case False:
			case CharValue:
			case IntValue:
			case RealValue:
			case StringValue:
			case LeftCurly:

				// FIXME: there is a bug here when parsing a quantified
				// expression such as
				//
				// "all { i in 0 .. (|items| - 1) | items[i] < items[i + 1] }"
				//
				// This is because the trailing vertical bar makes it look
				// like this is a cast.

			case LeftBrace:
			case VerticalBar:
			case Shreak:
			case Identifier: {
				// Ok, this must be cast so back track and reparse
				// expression as a type.
				index = start; // backtrack
				Type type = parseType(scope);
				// Now, parse cast expression
				e = parseUnitExpression(scope, terminated);
				e = new Expr.Cast(type, e);
				e.attributes().add(sourceAttr(start, index - 1));
				return e;
			}
			default:
				// default case, fall through and assume bracketed
				// expression
			}
		}
		// Assume bracketed
		return e;
	}

	/**
	 * Parse an array initialiser expression, which is of the form:
	 *
	 * <pre>
	 * ListExpr ::= '[' [ Expr (',' Expr)* ] ']'
	 * </pre>
	 *
	 * @param scope
	 *            The enclosing scope for this expression. This identifies any
	 *            generic arguments which are in scope, and also allocated each
	 *            variable in scope to its location index.
	 * @param terminated
	 *            This indicates that the expression is known to be terminated
	 *            (or not). An expression that's known to be terminated is one
	 *            which is guaranteed to be followed by something. This is
	 *            important because it means that we can ignore any newline
	 *            characters encountered in parsing this expression, and that
	 *            we'll never overrun the end of the expression (i.e. because
	 *            there's guaranteed to be something which terminates this
	 *            expression). A classic situation where terminated is true is
	 *            when parsing an expression surrounded in braces. In such case,
	 *            we know the right-brace will always terminate this expression.
	 *
	 * @return
	 */
	private Expr parseArrayInitialiserExpression(EnclosingScope scope, boolean terminated) {
		int start = index;
		match(LeftSquare);
		ArrayList<Expr> operands = new ArrayList<>();
		//
		operands.add(parseUnitExpression(scope, true));
		//
		boolean isArrayInitialiser = true;
		while (eventuallyMatch(RightSquare) == null) {
			if (!isArrayInitialiser) {
				// Force failure
				match(RightSquare);
			} else if (tryAndMatch(true, SemiColon) == null) {
				match(Comma);
			} else {
				// This indicates an array generator
				isArrayInitialiser = false;
			}
			// NOTE: we require the following expression be a "non-tuple"
			// expression. That is, it cannot be composed using ',' unless
			// braces enclose the entire expression. This is because the outer
			// list constructor expression is used ',' to distinguish elements.
			// Also, expression is guaranteed to be terminated, either by ']' or
			// ','.
			operands.add(parseUnitExpression(scope, true));
		}
		Expr expr;
		if (isArrayInitialiser) {
			expr = new Expr.ArrayInitialiser(toExprArray(operands));
		} else {
			expr = new Expr.ArrayGenerator(operands.get(0), operands.get(1));
		}
		expr.attributes().add(sourceAttr(start, index - 1));
		return expr;
	}

	/**
	 * Parse a record constructor, which is of the form:
	 *
	 * <pre>
	 * RecordExpr ::= '{' Identifier ':' Expr (',' Identifier ':' Expr)* '}'
	 * </pre>
	 *
	 * During parsing, we additionally check that each identifier is unique;
	 * otherwise, an error is reported.
	 *
	 * @param scope
	 *            The enclosing scope for this expression. This identifies any
	 *            generic arguments which are in scope, and also allocated each
	 *            variable in scope to its location index.
	 * @param terminated
	 *            This indicates that the expression is known to be terminated
	 *            (or not). An expression that's known to be terminated is one
	 *            which is guaranteed to be followed by something. This is
	 *            important because it means that we can ignore any newline
	 *            characters encountered in parsing this expression, and that
	 *            we'll never overrun the end of the expression (i.e. because
	 *            there's guaranteed to be something which terminates this
	 *            expression). A classic situation where terminated is true is
	 *            when parsing an expression surrounded in braces. In such case,
	 *            we know the right-brace will always terminate this expression.
	 *
	 * @return
	 */
	private Expr parseRecordExpression(EnclosingScope scope, boolean terminated) {
		int start = index;
		match(LeftCurly);
		HashSet<String> keys = new HashSet<>();
		ArrayList<WyalFile.Pair> exprs = new ArrayList<>();

		boolean firstTime = true;
		while (eventuallyMatch(RightCurly) == null) {
			if (!firstTime) {
				match(Comma);
			}
			firstTime = false;
			// Parse field name being constructed
			int fieldStart = index;
			Identifier fieldName = parseIdentifier(scope);
			// FIXME: Check field name is unique
			if (keys.contains(fieldName.get())) {
				syntaxError("duplicate tuple key", fieldName);
			}
			match(Colon);
			// Parse expression being assigned to field
			// NOTE: we require the following expression be a "non-tuple"
			// expression. That is, it cannot be composed using ',' unless
			// braces enclose the entire expression. This is because the outer
			// record constructor expression is used ',' to distinguish fields.
			// Also, expression is guaranteed to be terminated, either by '}' or
			// ','.
			Expr fieldValue = parseUnitExpression(scope, true);
			WyalFile.Pair pair = new WyalFile.Pair(fieldName,fieldValue);
			pair.attributes().add(sourceAttr(fieldStart,index-1));
			exprs.add(pair);
		}

		Expr expr = new Expr.RecordInitialiser(toPairArray(exprs));
		expr.attributes().add(sourceAttr(start, index - 1));
		return expr;
	}

	/**
	 * Parse an array length expression, which is of the form:
	 *
	 * <pre>
	 * TermExpr::= ...
	 *                 |  '|' Expr '|'
	 * </pre>
	 *
	 * @param scope
	 *            The enclosing scope for this expression. This identifies any
	 *            generic arguments which are in scope, and also allocated each
	 *            variable in scope to its location index.
	 * @param terminated
	 *            This indicates that the expression is known to be terminated
	 *            (or not). An expression that's known to be terminated is one
	 *            which is guaranteed to be followed by something. This is
	 *            important because it means that we can ignore any newline
	 *            characters encountered in parsing this expression, and that
	 *            we'll never overrun the end of the expression (i.e. because
	 *            there's guaranteed to be something which terminates this
	 *            expression). A classic situation where terminated is true is
	 *            when parsing an expression surrounded in braces. In such case,
	 *            we know the right-brace will always terminate this expression.
	 *
	 * @return
	 */
	private Expr parseLengthOfExpression(EnclosingScope scope, boolean terminated) {
		int start = index;
		match(VerticalBar);
		Expr e = parseUnitExpression(scope, true);
		match(VerticalBar);
		e = new Expr.ArrayLength(e);
		e.attributes().add(sourceAttr(start, index - 1));
		return e;
	}

	/**
	 * Parse a negation expression, which is of the form:
	 *
	 * <pre>
	 * TermExpr::= ...
	 *                 |  '-' Expr
	 * </pre>
	 *
	 * @param scope
	 *            The enclosing scope for this expression. This identifies any
	 *            generic arguments which are in scope, and also allocated each
	 *            variable in scope to its location index.
	 * @param terminated
	 *            This indicates that the expression is known to be terminated
	 *            (or not). An expression that's known to be terminated is one
	 *            which is guaranteed to be followed by something. This is
	 *            important because it means that we can ignore any newline
	 *            characters encountered in parsing this expression, and that
	 *            we'll never overrun the end of the expression (i.e. because
	 *            there's guaranteed to be something which terminates this
	 *            expression). A classic situation where terminated is true is
	 *            when parsing an expression surrounded in braces. In such case,
	 *            we know the right-brace will always terminate this expression.
	 *
	 * @return
	 */
	private Expr  parseNegationExpression(EnclosingScope scope, boolean terminated) {
		int start = index;
		match(Minus);
		Expr expr = parseTermExpression(scope, terminated);
		//
		expr = new Expr.Negation(expr);
		expr.attributes().add(sourceAttr(start, index - 1));
		return expr;
	}


	/**
	 * Parse a deference expression, which is of the form:
	 *
	 * <pre>
	 * RecordExpr ::= '*' Expr
	 * </pre>
	 *
	 * @param scope
	 *            The enclosing scope for this expression. This identifies any
	 *            generic arguments which are in scope, and also allocated each
	 *            variable in scope to its location index.
	 * @param terminated
	 *            This indicates that the expression is known to be terminated
	 *            (or not). An expression that's known to be terminated is one
	 *            which is guaranteed to be followed by something. This is
	 *            important because it means that we can ignore any newline
	 *            characters encountered in parsing this expression, and that
	 *            we'll never overrun the end of the expression (i.e. because
	 *            there's guaranteed to be something which terminates this
	 *            expression). A classic situation where terminated is true is
	 *            when parsing an expression surrounded in braces. In such case,
	 *            we know the right-brace will always terminate this expression.
	 *
	 * @return
	 */
	private Expr parseDereferenceExpression(EnclosingScope scope, boolean terminated) {
		int start = index;
		match(Star);
		Expr e = parseUnitExpression(scope, true);
		e = new Expr.Dereference(e);
		e.attributes().add(sourceAttr(start, index - 1));
		return e;
	}


	/**
	 * Parse a sequence of arguments separated by commas that ends in a
	 * right-brace:
	 *
	 * <pre>
	 * ArgumentList ::= [ Expr (',' Expr)* ] ')'
	 * </pre>
	 *
	 * Note, when this function is called we're assuming the left brace was
	 * already parsed.
	 *
	 * @param scope
	 *            The enclosing scope for this expression. This identifies any
	 *            generic arguments which are in scope, and also allocated each
	 *            variable in scope to its location index.
	 * @param terminated
	 *            This indicates that the expression is known to be terminated
	 *            (or not). An expression that's known to be terminated is one
	 *            which is guaranteed to be followed by something. This is
	 *            important because it means that we can ignore any newline
	 *            characters encountered in parsing this expression, and that
	 *            we'll never overrun the end of the expression (i.e. because
	 *            there's guaranteed to be something which terminates this
	 *            expression). A classic situation where terminated is true is
	 *            when parsing an expression surrounded in braces. In such case,
	 *            we know the right-brace will always terminate this expression.
	 *
	 * @return
	 */
	private Expr[] parseInvocationArguments(EnclosingScope scope) {
		ArrayList<Expr> arguments = new ArrayList<>();
		match(LeftBrace);
		// generic arguments...
		boolean firstTime = true;
		while (eventuallyMatch(RightBrace) == null) {
			if (!firstTime) {
				match(Comma);
			}
			firstTime = false;
			// Note, we have to parse a unit expression here since comma's are
			// already being used to separate the argument list.
			arguments.add(parseUnitExpression(scope,true));
		}

		return toExprArray(arguments);
	}

	/**
	 * Parse a logical not expression, which has the form:
	 *
	 * <pre>
	 * TermExpr::= ...
	 *       | '!' Expr
	 * </pre>
	 *
	 * @param scope
	 *            The enclosing scope for this expression. This identifies any
	 *            generic arguments which are in scope, and also allocated each
	 *            variable in scope to its location index.
	 * @param terminated
	 *            This indicates that the expression is known to be terminated
	 *            (or not). An expression that's known to be terminated is one
	 *            which is guaranteed to be followed by something. This is
	 *            important because it means that we can ignore any newline
	 *            characters encountered in parsing this expression, and that
	 *            we'll never overrun the end of the expression (i.e. because
	 *            there's guaranteed to be something which terminates this
	 *            expression). A classic situation where terminated is true is
	 *            when parsing an expression surrounded in braces. In such case,
	 *            we know the right-brace will always terminate this expression.
	 *
	 * @return
	 */
	private Expr parseLogicalNotExpression(EnclosingScope scope, boolean terminated) {
		int start = index;
		match(Shreak);
		Expr expr = parseAccessExpression(scope, terminated);
		//
		expr = new Expr.LogicalNot(expr);
		expr.attributes().add(sourceAttr(start, index - 1));
		return expr;
	}

	private Expr parseQuantifiedExpression(Token lookahead,EnclosingScope scope, boolean terminated) {
		int start = index - 1;
		match(lookahead.kind);
		// Clone the environment here, since the following type pattern may
		// updated this and such updates should only be visible to the
		// conditions contained within the quantified statement.
		scope = scope.clone();
		// Parse the parameter declarations for this block
		VariableDeclaration[] parameters = parseParameterDeclarations(scope);
		// Parser the body
		match(Dot);
		Expr body = parseUnitExpression(scope, false);
		//
		Expr expr;
		if(lookahead.kind == Forall) {
			expr = new Expr.UniversalQuantifier(parameters, body);
		} else {
			expr = new Expr.ExistentialQuantifier(parameters, body);
		}
		expr.attributes().add(sourceAttr(start, index - 1));
		return expr;
	}


	/**
	 * Attempt to parse something which maybe a type, or an expression. The
	 * semantics of this function dictate that it returns an instanceof
	 * SyntacticType *only* if what it finds *cannot* be parsed as an
	 * expression, but can be parsed as a type. Otherwise, the state is left
	 * unchanged.
	 *
	 * @param scope
	 *            The enclosing scope for this expression. This identifies any
	 *            generic arguments which are in scope, and also allocated each
	 *            variable in scope to its location index.
	 *
	 * @return An instance of SyntacticType or null.
	 */
	public Type parseDefiniteType(EnclosingScope scope) {
		int start = index; // backtrack point
		try {
			Type type = parseType(scope);
			if (mustParseAsType(type,scope)) {
				return type;
			}
		} catch (SyntaxError e) {

		}
		index = start; // backtrack
		return null;
	}

	/**
	 * <p>
	 * Determine whether or not the given type can be parsed as an expression.
	 * In many cases, a type can (e.g. <code>{x}</code> is both a valid type and
	 * expression). However, some types are not also expressions (e.g.
	 * <code>int</code>, <code>{int f}</code>, <code>&int</code>, etc).
	 * </p>
	 *
	 * <p>
	 * This function *must* return false if what the given type could not be
	 * parsed as an expression. However, if what it can be parsed as an
	 * expression, then this function must return false (even if we will
	 * eventually treat this as a type). This function is called from either the
	 * beginning of a statement (i.e. to disambiguate variable declarations), or
	 * after matching a left brace (i.e. to disambiguate casts).
	 * </p>
	 *
	 * @param index
	 *            Position in the token stream to begin looking from.
	 * @return
	 */
	private boolean mustParseAsType(Type type, EnclosingScope scope) {
		switch (type.getOpcode()) {
		case TYPE_arr:
		case TYPE_rec:
		case TYPE_fun:
			return true;
		}
		return false;
	}

	/**
	 * Parse a top-level type, which is of the form:
	 *
	 * <pre>
	 * TupleType ::= Type (',' Type)*
	 * </pre>
	 *
	 * @param scope The enclosing scope for this expression. This identifies
	 * any generic arguments which are in scope, and also allocated each
	 * variable in scope to its location index.
	 *
	 * @see wyc.lang.SyntacticType.Tuple
	 * @return
	 */
	public Type parseType(EnclosingScope scope) {
		int start = index;
		Type first = parseUnaryType(scope);
		Token lookahead = tryAndMatch(false,Ampersand,VerticalBar);
		if(lookahead == null) {
			return first;
		} else {
			ArrayList<Type> operands = new ArrayList<>();
			operands.add(first);
			do  {
				operands.add(parseUnaryType(scope));
			} while(tryAndMatch(false,lookahead.kind) != null);
			Type rt;
			Type[] types = operands.toArray(new Type[operands.size()]);
			if(lookahead.kind == Ampersand) {
				rt = new Type.Intersection(types);
			} else {
				rt = new Type.Union(types);
			}
			rt.attributes().add(sourceAttr(start, index - 1));
			return rt;
		}
	}

	private Type parseUnaryType(EnclosingScope scope) {
		// Should match negation and reference types here!
		int start = index;
		Type type = parseBaseType(scope);
		while(tryAndMatch(false,LeftSquare) != null) {
			match(RightSquare);
			type = new Type.Array(type);
			type.attributes().add(sourceAttr(start, index - 1));
		}
		return type;
	}

	private Type parseBaseType(EnclosingScope scope) {
		checkNotEof();
		int start = index;
		Token token = tokens.get(index);

		switch (token.kind) {
		case Void:
		case Any:
		case Null:
		case Bool:
		case Int:
			return parsePrimitiveType(scope);
		case LeftBrace:
			return parseBracketedType(scope);
		case LeftCurly:
			return parseRecordType(scope);
		case Shreak:
			return parseNegationType(scope);
		case Ampersand:
			return parseReferenceType(scope);
		case Identifier:
			return parseNominalType(scope);
		case Function:
			return parseFunctionType(scope);
		default:
			syntaxError("unknown type encountered", token);
			return null; // deadcode
		}
	}

	private Type parsePrimitiveType(EnclosingScope scope) {
		int start = index;
		Token token = tokens.get(index);
		Type t;

		switch (token.kind) {
		case Any:
			t = new Type.Any();
			break;
		case Null:
			t = new Type.Null();
			break;
		case Bool:
			t = new Type.Bool();
			break;
		case Int:
			t = new Type.Int();
			break;
		default:
			syntaxError("unknown primitive type encountered", token);
			return null; // deadcode
		}
		match(token.kind);
		t.attributes().add(sourceAttr(start,index-1));
		return t;
	}

	/**
	 * Parse a negation type, which is of the form:
	 *
	 * <pre>
	 * NegationType ::= '!' Type
	 * </pre>
	 *
	 * @param scope
	 *            The enclosing scope for this expression. This identifies any
	 *            generic arguments which are in scope, and also allocated each
	 *            variable in scope to its location index.
	 *
	 * @return
	 */
	private Type parseNegationType(EnclosingScope scope) {
		int start = index;
		match(Shreak);
		Type element = parseBaseType(scope);
		Type type = new Type.Negation(element);
		type.attributes().add(sourceAttr(start, index - 1));
		return type;
	}

	/**
	 * Parse a reference type, which is of the form:
	 *
	 * <pre>
	 * ReferenceType ::= '&' Type
	 * </pre>
	 *
	 * @param scope
	 *            The enclosing scope for this expression. This identifies any
	 *            generic arguments which are in scope, and also allocated each
	 *            variable in scope to its location index.
	 * @return
	 */
	private Type parseReferenceType(EnclosingScope scope) {
		int start = index;
		match(Ampersand);
		Type element = parseBaseType(scope);
		Type type = new Type.Reference(element);
		type.attributes().add(sourceAttr(start, index - 1));
		return type;
	}

	/**
	 * Parse a bracketed type, which is of the form:
	 * @param scope
	 *            The enclosing scope for this expression. This identifies any
	 *            generic arguments which are in scope, and also allocated each
	 *            variable in scope to its location index.
	 * <pre>
	 * BracketedType ::= '(' Type ')'
	 * </pre>
	 *
	 * @return
	 */
	private Type parseBracketedType(EnclosingScope scope) {
		int start = index;
		match(LeftBrace);
		Type type = parseType(scope);
		match(RightBrace);
		return type;
	}

	/**
	 * Parse a record type, which are of the form:
	 *
	 * <pre>
	 * RecordType ::= '{' Type Identifier (',' Type Identifier)* [ ',' "..." ] '}'
	 * </pre>
	 *
	 * @param scope
	 *            The enclosing scope for this expression. This identifies any
	 *            generic arguments which are in scope, and also allocated each
	 *            variable in scope to its location index.
	 *
	 * Disambiguating these three forms is relatively straightforward as all
	 * three must be terminated by a right curly brace. Therefore, after parsing
	 * the first Type, we simply check what follows. One complication is the
	 * potential for "mixed types" where the field name and type and intertwined
	 * (e.g. function read()->[byte]).
	 *
	 * @return
	 */
	private Type parseRecordType(EnclosingScope scope) {
		int start = index;
		match(LeftCurly);
		List<FieldDeclaration> fields = new ArrayList<>();
		boolean isOpenRecord = false;
		boolean firstTime = true;
		while (eventuallyMatch(RightCurly) == null) {
			if (!firstTime) {
				match(Comma);
			} else {
				firstTime = false;
			}
			int fieldStart = index;
			// Check whether this is the end of an open record, or not.
			if(tryAndMatch(true, DotDotDot) == null) {
				// No, this is not an open record
				Type fieldType = parseType(scope);
				Identifier fieldName = parseIdentifier(scope);
				FieldDeclaration var = new FieldDeclaration(fieldType, fieldName);
				var.attributes().add(sourceAttr(fieldStart, index - 1));
				fields.add(var);
			} else {
				isOpenRecord = true;
				// The "..." of an open record can only come at the end.
				match(RightCurly);
				break;
			}
		}
		FieldDeclaration[] arr = fields.toArray(new FieldDeclaration[fields.size()]);
		Type type = new Type.Record(isOpenRecord,arr);
		type.attributes().add(sourceAttr(start, index - 1));
		return type;
	}

	/**
	 * Parse a nominal type, which is of the form:
	 *
	 * <pre>
	 * NominalType ::= Identifier ('.' Identifier)*
	 * </pre>
	 *
	 * @param scope
	 *            The enclosing scope for this expression. This identifies any
	 *            generic arguments which are in scope, and also allocated each
	 *            variable in scope to its location index.
	 *
	 * @see NominalType.lang.SyntacticType.Nominal
	 * @return
	 */
	private Type parseNominalType(EnclosingScope scope) {
		int start = index;
		//
		Name nameID = parseNameID(scope);
		// this is a nominal type constructor
		Type type = new Type.Nominal(nameID);
		type.attributes().add(sourceAttr(start, index - 1));
		return type;
	}

	/**
	 * Parse a function type of the form:
	 *
	 * <pre>
	 * FunctionType ::= "function" [Type (',' Type)* ] "->" Type
	 * </pre>
	 *
	 * Observer, it is required that parameters and returns for a function type
	 * are enclosed in braces.
	 *
	 * @param scope
	 * @return
	 */
	private Type parseFunctionType(EnclosingScope scope) {
		int start = index;
		match(Function);
		Tuple<Type> parameters = parseTypeParameters(scope);
		match(MinusGreater);
		Tuple<Type> returns = parseTypeParameters(scope);
		Type.Function type = new Type.Function(parameters, returns);
		type.attributes().add(sourceAttr(start, index - 1));
		return type;
	}

	private Tuple<Type> parseTypeParameters(EnclosingScope scope) {
		match(LeftBrace);
		ArrayList<Type> types = new ArrayList<>();
		boolean firstTime = true;
		while(eventuallyMatch(RightBrace) == null) {
			if(!firstTime) {
				match(Comma);
			}
			types.add(parseType(scope));
		}
		return new Tuple<>(types.toArray(new Type[types.size()]));
	}

	private Identifier parseIdentifier(EnclosingScope scope) {
		int start = index;
		String txt = match(Identifier).text;
		Identifier id = new Identifier(txt);
		id.attributes().add(sourceAttr(start, index - 1));
		return id;
	}

	private Name parseNameID(EnclosingScope scope) {
		int start = index;
		List<Identifier> components = new ArrayList<>();
		components.add(parseIdentifier(scope));
		while (tryAndMatch(false, Dot) != null) {
			components.add(parseIdentifier(scope));
		}
		Identifier[] ids = components.toArray(new Identifier[components.size()]);
		Name nid = new Name(ids);
		nid.attributes().add(sourceAttr(start, index - 1));
		return nid;
	}

	/**
	 * Match a given token kind, whilst moving passed any whitespace encountered
	 * inbetween. In the case that meet the end of the stream, or we don't match
	 * the expected token, then an error is thrown.
	 *
	 * @param kind
	 * @return
	 */
	private Token match(Token.Kind kind) {
		checkNotEof();
		Token token = tokens.get(index++);
		if (token.kind != kind) {
			syntaxError("expecting \"" + kind + "\" here", token);
		}
		return token;
	}

	/**
	 * Match a given sequence of tokens, whilst moving passed any whitespace
	 * encountered inbetween. In the case that meet the end of the stream, or we
	 * don't match the expected tokens in the expected order, then an error is
	 * thrown.
	 *
	 * @param operator
	 * @return
	 */
	private Token[] match(Token.Kind... kinds) {
		Token[] result = new Token[kinds.length];
		for (int i = 0; i != result.length; ++i) {
			checkNotEof();
			Token token = tokens.get(index++);
			if (token.kind == kinds[i]) {
				result[i] = token;
			} else {
				syntaxError("Expected \"" + kinds[i] + "\" here", token);
			}
		}
		return result;
	}

	/**
	 * Attempt to match a given kind of token with the view that it must
	 * *eventually* be matched. This differs from <code>tryAndMatch()</code>
	 * because it calls <code>checkNotEof()</code>. Thus, it is guaranteed to
	 * skip any whitespace encountered in between. This is safe because we know
	 * there is a terminating token still to come.
	 *
	 * @param kind
	 * @return
	 */
	private Token eventuallyMatch(Token.Kind kind) {
		checkNotEof();
		Token token = tokens.get(index);
		if (token.kind != kind) {
			return null;
		} else {
			index = index + 1;
			return token;
		}
	}

	/**
	 * Attempt to match a given token(s), whilst ignoring any whitespace in
	 * between. Note that, in the case it fails to match, then the index will be
	 * unchanged. This latter point is important, otherwise we could
	 * accidentally gobble up some important indentation. If more than one kind
	 * is provided then this will try to match any of them.
	 *
	 * @param terminated
	 *            Indicates whether or not this function should be concerned
	 *            with new lines. The terminated flag indicates whether or not
	 *            the current construct being parsed is known to be terminated.
	 *            If so, then we don't need to worry about newlines and can
	 *            greedily consume them (i.e. since we'll eventually run into
	 *            the terminating symbol).
	 * @param kinds
	 *
	 * @return
	 */
	private Token tryAndMatch(boolean terminated, Token.Kind... kinds) {
		// If the construct being parsed is know to be terminated, then we can
		// skip all whitespace. Otherwise, we can't skip newlines as these are
		// significant.
		int next = terminated ? skipWhiteSpace(index) : skipLineSpace(index);

		if (next < tokens.size()) {
			Token t = tokens.get(next);
			for (int i = 0; i != kinds.length; ++i) {
				if (t.kind == kinds[i]) {
					index = next + 1;
					return t;
				}
			}
		}
		return null;
	}

	/**
	 * Check whether a given token(s) could be matched, whilst ignoring any
	 * whitespace in between. Note that, in either case, the index will be
	 * unchanged. If more than one kind is provided then this will check for
	 * matching any of them.
	 *
	 * @param terminated
	 *            Indicates whether or not this function should be concerned
	 *            with new lines. The terminated flag indicates whether or not
	 *            the current construct being parsed is known to be terminated.
	 *            If so, then we don't need to worry about newlines and can
	 *            greedily consume them (i.e. since we'll eventually run into
	 *            the terminating symbol).
	 * @param kinds
	 *
	 * @return
	 */
	private Token canMatch(boolean terminated, Token.Kind... kinds) {
		// If the construct being parsed is know to be terminated, then we can
		// skip all whitespace. Otherwise, we can't skip newlines as these are
		// significant.
		int next = terminated ? skipWhiteSpace(index) : skipLineSpace(index);

		if (next < tokens.size()) {
			Token t = tokens.get(next);
			for (int i = 0; i != kinds.length; ++i) {
				if (t.kind == kinds[i]) {
					return t;
				}
			}
		}
		return null;
	}

	/**
	 * Attempt to match a given token on the *same* line, whilst ignoring any
	 * whitespace in between. Note that, in the case it fails to match, then the
	 * index will be unchanged. This latter point is important, otherwise we
	 * could accidentally gobble up some important indentation.
	 *
	 * @param kind
	 * @return
	 */
	private Token tryAndMatchOnLine(Token.Kind kind) {
		int next = skipLineSpace(index);
		if (next < tokens.size()) {
			Token t = tokens.get(next);
			if (t.kind == kind) {
				index = next + 1;
				return t;
			}
		}
		return null;
	}

	/**
	 * Match a the end of a line. This is required to signal, for example, the
	 * end of the current statement.
	 */
	private void matchEndLine() {
		// First, parse all whitespace characters except for new lines
		index = skipLineSpace(index);

		// Second, check whether we've reached the end-of-file (as signaled by
		// running out of tokens), or we've encountered some token which not a
		// newline.
		if (index >= tokens.size()) {
			return; // EOF
		} else if (tokens.get(index).kind != NewLine) {
			syntaxError("expected end-of-line", tokens.get(index));
		} else {
			index = index + 1;
		}
	}

	/**
	 * Check that the End-Of-File has not been reached. This method should be
	 * called from contexts where we are expecting something to follow.
	 */
	private void checkNotEof() {
		skipWhiteSpace();
		if (index >= tokens.size()) {
			// FIXME: this is clearly not a sensible approach
			SyntacticElement unknown = new SyntacticElement.Impl() {
			};
			unknown.attributes().add(new Attribute.Source(index - 1, index - 1, -1));
			throw new SyntaxError("unexpected end-of-file", entry, unknown);
		}
	}

	/**
	 * Skip over any whitespace characters.
	 */
	private void skipWhiteSpace() {
		index = skipWhiteSpace(index);
	}

	/**
	 * Skip over any whitespace characters, starting from a given index and
	 * returning the first index passed any whitespace encountered.
	 */
	private int skipWhiteSpace(int index) {
		while (index < tokens.size() && isWhiteSpace(tokens.get(index))) {
			index++;
		}
		return index;
	}

	/**
	 * Skip over any whitespace characters that are permitted on a given line
	 * (i.e. all except newlines), starting from a given index and returning the
	 * first index passed any whitespace encountered.
	 */
	private int skipLineSpace(int index) {
		while (index < tokens.size() && isLineSpace(tokens.get(index))) {
			index++;
		}
		return index;
	}

	/**
	 * Skip over any empty lines. That is lines which contain only whitespace
	 * and comments.
	 */
	private void skipEmptyLines() {
		int tmp = index;
		do {
			tmp = skipLineSpace(tmp);
			if (tmp < tokens.size() && tokens.get(tmp).kind != NewLine) {
				return; // done
			} else if (tmp >= tokens.size()) {
				index = tmp;
				return; // end-of-file reached
			}
			// otherwise, skip newline and continue
			tmp = tmp + 1;
			index = tmp;
		} while (true);
		// deadcode
	}

	/**
	 * Define what is considered to be whitespace.
	 *
	 * @param token
	 * @return
	 */
	private boolean isWhiteSpace(Token token) {
		return token.kind == NewLine || isLineSpace(token);
	}

	/**
	 * Define what is considered to be linespace.
	 *
	 * @param token
	 * @return
	 */
	private boolean isLineSpace(Token token) {
		return token.kind == Token.Kind.Indent
				|| token.kind == Token.Kind.LineComment
				|| token.kind == Token.Kind.BlockComment;
	}

	/**
	 * Parse a character from a string of the form 'c' or '\c'.
	 *
	 * @param input
	 * @return
	 */
	private char parseCharacter(String input) {
		int pos = 1;
		char c = input.charAt(pos++);
		if (c == '\\') {
			// escape code
			switch (input.charAt(pos++)) {
			case 'b':
				c = '\b';
				break;
			case 't':
				c = '\t';
				break;
			case 'n':
				c = '\n';
				break;
			case 'f':
				c = '\f';
				break;
			case 'r':
				c = '\r';
				break;
			case '"':
				c = '\"';
				break;
			case '\'':
				c = '\'';
				break;
			case '\\':
				c = '\\';
				break;
			default:
				throw new RuntimeException("unrecognised escape character");
			}
		}
		return c;
	}

	/**
	 * Parse a string whilst interpreting all escape characters.
	 *
	 * @param v
	 * @return
	 */
	protected String parseString(String v) {
		/*
		 * Parsing a string requires several steps to be taken. First, we need
		 * to strip quotes from the ends of the string.
		 */
		v = v.substring(1, v.length() - 1);
		// Second, step through the string and replace escaped characters
		for (int i = 0; i < v.length(); i++) {
			if (v.charAt(i) == '\\') {
				if (v.length() <= i + 1) {
					throw new RuntimeException("unexpected end-of-string");
				} else {
					char replace = 0;
					int len = 2;
					switch (v.charAt(i + 1)) {
					case 'b':
						replace = '\b';
						break;
					case 't':
						replace = '\t';
						break;
					case 'n':
						replace = '\n';
						break;
					case 'f':
						replace = '\f';
						break;
					case 'r':
						replace = '\r';
						break;
					case '"':
						replace = '\"';
						break;
					case '\'':
						replace = '\'';
						break;
					case '\\':
						replace = '\\';
						break;
					case 'u':
						len = 6; // unicode escapes are six digits long,
						// including "slash u"
						String unicode = v.substring(i + 2, i + 6);
						replace = (char) Integer.parseInt(unicode, 16); // unicode
						break;
					default:
						throw new RuntimeException("unknown escape character");
					}
					v = v.substring(0, i) + replace + v.substring(i + len);
				}
			}
		}
		return v;
	}

	/**
	 * Parse a token representing a byte value. Every such token is a sequence
	 * of one or more binary digits ('0' or '1') followed by 'b'. For example,
	 * "00110b" is parsed as the byte value 6.
	 *
	 * @param input
	 *            The token representing the byte value.
	 * @return
	 */
	private byte parseByte(Token input) {
		String text = input.text;
		if (text.length() > 9) {
			syntaxError("invalid binary literal (too long)", input);
		}
		int val = 0;
		for (int i = 0; i != text.length() - 1; ++i) {
			val = val << 1;
			char c = text.charAt(i);
			if (c == '1') {
				val = val | 1;
			} else if (c == '0') {

			} else {
				syntaxError("invalid binary literal (invalid characters)",
						input);
			}
		}
		return (byte) val;
	}

	private Attribute.Source sourceAttr(int start, int end) {
		Token t1 = tokens.get(start);
		Token t2 = tokens.get(end);
		// FIXME: problem here with the line numbering ?
		return new Attribute.Source(t1.start, t2.end(), 0);
	}

	private void syntaxError(String msg, SyntacticElement elem) {
		throw new SyntaxError(msg, entry, elem);
	}

	private void syntaxError(String msg, Token t) {
		// FIXME: this is clearly not a sensible approach
		SyntacticElement unknown = new SyntacticElement.Impl() {
		};
		unknown.attributes().add(new Attribute.Source(t.start, t.start + t.text.length() - 1, -1));
		throw new SyntaxError(msg, entry, unknown);
	}

	private Expr[] toExprArray(List<Expr> exprs) {
		Expr[] es = new Expr[exprs.size()];
		for(int i=0;i!=es.length;++i) {
			es[i] = exprs.get(i);
		}
		return es;
	}

	private Stmt[] toStmtArray(List<Stmt> exprs) {
		Stmt[] ss = new Stmt[exprs.size()];
		for(int i=0;i!=ss.length;++i) {
			ss[i] = exprs.get(i);
		}
		return ss;
	}

	private WyalFile.Pair[] toPairArray(List<WyalFile.Pair> exprs) {
		WyalFile.Pair[] ss = new WyalFile.Pair[exprs.size()];
		for(int i=0;i!=ss.length;++i) {
			ss[i] = exprs.get(i);
		}
		return ss;
	}

	// =======================================================================

	private Expr.Operator constructInfixExpression(Token token, Expr... arguments) {
		Token.Kind kind = token.kind;
		switch (kind) {
		case LogicalAnd:
			return new Expr.LogicalAnd(arguments);
		case LogicalOr:
			return new Expr.LogicalOr(arguments);
		case LogicalImplication:
			return new Expr.LogicalImplication(arguments);
		case LogicalIff:
			return new Expr.LogicalIff(arguments);
		case LessEquals:
			return new Expr.LessThanOrEqual(arguments);
		case LeftAngle:
			return new Expr.LessThan(arguments);
		case GreaterEquals:
			return new Expr.GreaterThanOrEqual(arguments);
		case RightAngle:
			return new Expr.GreaterThan(arguments);
		case EqualsEquals:
			return new Expr.Equal(arguments);
		case NotEquals:
			return new Expr.NotEqual(arguments);
		case Plus:
			return new Expr.Addition(arguments);
		case Minus:
			return new Expr.Subtraction(arguments);
		case Star:
			return new Expr.Multiplication(arguments);
		case RightSlash:
			return new Expr.Division(arguments);
		case Percent:
			return new Expr.Remainder(arguments);
		default:
			syntaxError("unknown operator \"" + token.text + "\" encountered", token);
			return null;
		}
	}

	/**
	 * The set of token kinds which correspond to binary or n-ary infix
	 * operators.
	 */
	private static Token.Kind[] INFIX_OPERATORS = {
			// Logical Operators
			LogicalAnd,
			LogicalOr,
			LogicalImplication,
			LogicalIff,
			// Comparators
			LessEquals,
			LeftAngle,
			GreaterEquals,
			RightAngle,
			EqualsEquals,
			NotEquals,
			// Arithmetic Operators
			Plus,
			Minus,
			Star,
			RightSlash,
			Percent
	};

	// =======================================================================

	/**
	 * Represents a given amount of indentation. Specifically, a count of tabs
	 * and spaces. Observe that the order in which tabs / spaces occurred is not
	 * retained.
	 *
	 * @author David J. Pearce
	 *
	 */
	private static class Indent extends Token {
		private final int countOfSpaces;
		private final int countOfTabs;

		public Indent(String text, int pos) {
			super(Token.Kind.Indent, text, pos);
			// Count the number of spaces and tabs
			int nSpaces = 0;
			int nTabs = 0;
			for (int i = 0; i != text.length(); ++i) {
				char c = text.charAt(i);
				switch (c) {
				case ' ':
					nSpaces++;
					break;
				case '\t':
					nTabs++;
					break;
				default:
					throw new IllegalArgumentException(
							"Space or tab character expected");
				}
			}
			countOfSpaces = nSpaces;
			countOfTabs = nTabs;
		}

		/**
		 * Test whether this indentation is considered "less than or equivalent"
		 * to another indentation. For example, an indentation of 2 spaces is
		 * considered less than an indentation of 3 spaces, etc.
		 *
		 * @param other
		 *            The indent to compare against.
		 * @return
		 */
		public boolean lessThanEq(Indent other) {
			return countOfSpaces <= other.countOfSpaces
					&& countOfTabs <= other.countOfTabs;
		}

		/**
		 * Test whether this indentation is considered "equivalent" to another
		 * indentation. For example, an indentation of 3 spaces followed by 1
		 * tab is considered equivalent to an indentation of 1 tab followed by 3
		 * spaces, etc.
		 *
		 * @param other
		 *            The indent to compare against.
		 * @return
		 */
		public boolean equivalent(Indent other) {
			return countOfSpaces == other.countOfSpaces
					&& countOfTabs == other.countOfTabs;
		}
	}

	/**
	 * An abstract indentation which represents the indentation of top-level
	 * declarations, such as function declarations. This is used to simplify the
	 * code for parsing indentation.
	 */
	private static final Indent ROOT_INDENT = new Indent("", 0);

	/**
	 * Captures all useful information about the scope in which a statement or
	 * expression is being translated. For example, it determines which WyIL
	 * register all visible variables and parameters map to. Furthermore, it
	 * determines where break and continue statements will jump to.
	 *
	 * @author David J. Pearce
	 *
	 */
	public static final class EnclosingScope {
		/**
		 * Maps variables to their WyIL location.
		 */
		private final HashMap<String, VariableDeclaration> environment;

		/**
		 * The enclosing source file scope
		 */
		private final WyalFile parent;

		public EnclosingScope(WyalFile parent) {
			this(new HashMap<String, VariableDeclaration>(), parent);
		}

		private EnclosingScope(Map<String, VariableDeclaration> environment, WyalFile parent) {
			this.environment = new HashMap<>(environment);
			this.parent = parent;
		}

		/**
		 * Check whether a given name corresponds to a declared local variable
		 * or not.
		 *
		 * @param name
		 * @return
		 */
		public boolean isDeclaredVariable(String name) {
			return environment.containsKey(name);
		}

		/**
		 * Get the declaration index corresponding to a given local variable
		 *
		 * @param name
		 * @return
		 */
		public VariableDeclaration getVariableDeclaration(String name) {
			return environment.get(name);
		}

		/**
		 * Declare a new variable in the enclosing scope.
		 *
		 * @param declartion
		 *            Index of declaration "Location"
		 * @return
		 */
		public void declareInScope(VariableDeclaration decl) {
			Identifier var = decl.getVariableName();
			environment.put(var.get(), decl);
		}

		/**
		 * Create a new clone scope. This is a subscope where new variables
		 * can be declared and, furthermore, it corresponds to a new block in
		 * the underlying forest.
		 *
		 * @return
		 */
		@Override
		public EnclosingScope clone() {
			return new EnclosingScope(environment, parent);
		}
	}
}
