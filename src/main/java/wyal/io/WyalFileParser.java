package wyal.io;

import static wyal.io.WyalFileLexer.Token.Kind.*;
import java.math.BigDecimal;
import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;

import wyal.io.WyalFileLexer.Token;
import wyal.lang.Bytecode;
import wyal.lang.SemanticType;
import wyal.lang.WyalFile;
import wyal.lang.WyalFile;
import wyal.lang.Bytecode.Opcode;
import wycc.util.ArrayUtils;
import wycc.util.Pair;
import wybs.lang.Attribute;
import wybs.lang.NameID;
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
		this.tokens = new ArrayList<Token>(tokens);
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
			if (lookahead.kind == Import) {
				parseImportDeclaration(wf);
			} else {
				checkNotEof();
				lookahead = tokens.get(index);
				if (lookahead.kind == Assert) {
					parseAssertDeclaration(wf);
				} else if (lookahead.text.equals("type")) {
					parseTypeDeclaration(wf);
				} else if (lookahead.text.equals("define")) {
					parseMacroDeclaration(wf);
				} else if (lookahead.kind == Function) {
					parseFunctionDeclaration(wf);
				} else {
					syntaxError("unrecognised declaration", lookahead);
				}
			}
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
	private void parseImportDeclaration(WyalFile parent) {
		int start = index;
		EnclosingScope scope = new EnclosingScope(parent);

		match(Import);
		int[] filterPath = parseFilterPath(scope);

		int end = index;
		matchEndLine();

		parent.getConstantPool().add(new WyalFile.Import(parent,filterPath, sourceAttr(start, end - 1)));
	}

	private int[] parseFilterPath(EnclosingScope scope) {
		// Parse package filter string
		ArrayList<Integer> components = new ArrayList<Integer>();
		components.add(parseIdentifier(scope));
		while (tryAndMatch(true, Dot) != null) {
			int component = parseStarOrIdentifier(scope);
			components.add(component);
		}
		//
		return ArrayUtils.toIntArray(components);
	}

	private int parseStarOrIdentifier(EnclosingScope scope) {
		if (tryAndMatch(true, Star) != null) {
			return WyalFile.STAR;
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
	protected void parseAssertDeclaration(WyalFile parent) {
		EnclosingScope scope = new EnclosingScope(parent);
		int start = index;
		//
		match(Assert);
		match(Colon);
		matchEndLine();
		int body = parseBlock(scope, ROOT_INDENT);
		WyalFile.Assert declaration = new WyalFile.Assert(parent, body, sourceAttr(start, index - 1));
		parent.getConstantPool().add(declaration);
	}

	/**
	 * Parse a <code>type</code> declaration in a WyAL source file.
	 *
	 * @param wf
	 *            The WyAL file in which this declaration is defined.
	 */
	protected void parseTypeDeclaration(WyalFile parent) {
		EnclosingScope scope = new EnclosingScope(parent);
		int start = index;
		//
		match(Type);
		int nameIndex = parseIdentifier(scope);
		match(Is);
		// Parse parameter declaration and invariant (if applicable)
		match(LeftBrace);
		parseParameterDeclaration(scope);
		match(RightBrace);
		//
		int[] invariant = parseInvariantClauses(scope);
		//
		WyalFile.Type declaration = new WyalFile.Type(parent, nameIndex, invariant, sourceAttr(start, index - 1));
		//
		parent.getConstantPool().add(declaration);
	}

	private int[] parseInvariantClauses(EnclosingScope scope) {
		List<Integer> invariant = new ArrayList<Integer>();
		while ((tryAndMatch(false, Where)) != null) {
			if (tryAndMatch(true, Colon) != null) {
				invariant.add(parseBlock(scope, ROOT_INDENT));
			} else {
				invariant.add(parseUnitExpression(scope, false));
				matchEndLine();
			}
		}
		return ArrayUtils.toIntArray(invariant);
	}

	protected void parseFunctionDeclaration(WyalFile parent) {
		EnclosingScope scope = new EnclosingScope(parent);
		int start = index;
		//
		match(Function);
		int nameIndex = parseIdentifier(scope);
		//
		int[] parameters = parseParameterDeclarations(scope);
		match(MinusGreater);
		int[] returns = parseParameterDeclarations(scope);
		matchEndLine();
		//
		WyalFile.Function declaration = new WyalFile.Function(parent, nameIndex, parameters, returns,
				sourceAttr(start, index - 1));
		parent.getConstantPool().add(declaration);
	}

	protected void parseMacroDeclaration(WyalFile parent) {
		EnclosingScope scope = new EnclosingScope(parent);
		int start = index;
		//
		match(Define);
		int nameIndex = parseIdentifier(scope);
		//
		int[] parameters = parseParameterDeclarations(scope);
		match(Is);
		match(Colon);
		int body = parseBlock(scope, ROOT_INDENT);
		// Create empty declaration
		WyalFile.Macro declaration = new WyalFile.Macro(parent, nameIndex, parameters, body,
				sourceAttr(start, index - 1));
		parent.getConstantPool().add(declaration);
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
	private int parseBlock(EnclosingScope scope, Indent parentIndent) {
		int start = index;
		// First, determine the initial indentation of this block based on the
		// first statement (or null if there is no statement).
		Indent indent = getIndent();

		// Second, check that this is indeed the initial indentation for this
		// block (i.e. that it is strictly greater than parent indent).
		if (indent == null || indent.lessThanEq(parentIndent)) {
			// Initial indent either doesn't exist or is not strictly greater
			// than parent indent and,therefore, signals an empty block.
			//
			return scope.add(new Bytecode.Bool(true));
		} else {
			// Initial indent is valid, so we proceed parsing statements with
			// the appropriate level of indent.
			//
			ArrayList<Integer> statements = new ArrayList<Integer>();
			Indent nextIndent;
			while ((nextIndent = getIndent()) != null
					&& indent.lessThanEq(nextIndent)) {
				// At this point, nextIndent contains the indent of the current
				// statement. However, this still may not be equivalent to this
				// block's indentation level.

				// First, check the indentation matches that for this block.
				if (!indent.equivalent(nextIndent)) {
					// No, it's not equivalent so signal an error.
					syntaxError("unexpected end-of-block", indent);
				}

				// Second, parse the actual statement at this point!
				statements.add(parseStatement(scope, indent));
			}
			return scope.add(new Bytecode(Opcode.BLOCK,statements), sourceAttr(start, index - 1));
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
	private int parseStatement(EnclosingScope scope, Indent indent) {
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
			int stmt = parseUnitExpression(scope, false);
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
	private int parseIfThenStatement(EnclosingScope scope, Indent indent) {
		int start = index;
		match(Colon);
		matchEndLine();
		int ifBlock = parseBlock(scope, indent);
		match(Then);
		match(Colon);
		matchEndLine();
		int thenBlock = parseBlock(scope, indent);
		return scope.add(new Bytecode(Opcode.IFTHEN,ifBlock, thenBlock), sourceAttr(start, index - 1));
	}

	private int parseEitherOrStatement(EnclosingScope scope, Indent indent) {
		int start = index;

		ArrayList<Integer> blocks = new ArrayList<Integer>();
		Indent nextIndent;
		Token lookahead;

		do {
			match(Colon);
			matchEndLine();
			blocks.add(parseBlock(scope, indent));
			nextIndent = getIndent();
			if(nextIndent != null && nextIndent.equivalent(indent)) {
				lookahead = tryAndMatch(false, Or);
			} else {
				lookahead = null;
			}
		} while (lookahead != null && lookahead.kind == Or);

		return scope.add(new Bytecode(Opcode.CASEOF,blocks), sourceAttr(start, index - 1));
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
	private int parseExistsForallStatement(Token lookahead, EnclosingScope scope, Indent indent) {
		boolean isUniversal = lookahead.kind == Forall;
		int start = index - 1;
		// Clone the environment here, since the following type pattern may
		// updated this and such updates should only be visible to the
		// conditions contained within the quantified statement.
		scope = scope.clone();
		// Parse the parameter declarations for this block
		int[] parameters = parseParameterDeclarations(scope);
		// Parser the body
		int body;
		if (tryAndMatch(true, Colon) != null) {
			matchEndLine();
			body = parseBlock(scope, indent);
		} else {
			match(SemiColon);
			body = parseUnitExpression(scope, false);
		}
		Bytecode bytecode = new Bytecode(isUniversal ? Opcode.FORALL : Opcode.EXISTS, body, parameters);
		return scope.add(bytecode, sourceAttr(start, index - 1));
	}

	private int[] parseParameterDeclarations(EnclosingScope scope) {
		ArrayList<Integer> parameters = new ArrayList<Integer>();
		match(LeftBrace);
		boolean firstTime=true;
		while(eventuallyMatch(RightBrace) == null) {
			if(!firstTime) {
				match(Comma);
			} else {
				firstTime=false;
			}
			parameters.add(parseParameterDeclaration(scope));
		}
		return ArrayUtils.toIntArray(parameters);
	}

	private int parseParameterDeclaration(EnclosingScope scope) {
		int start = index;
		int typeIndex = parseType(scope);
		int nameIndex = parseIdentifier(scope);
		int decl = scope.add(new Bytecode(Opcode.VARDECL,typeIndex,nameIndex), sourceAttr(start,index-1));
		scope.declareInScope(decl);
		return decl;
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
	private int parseMultiExpression(EnclosingScope scope, boolean terminated) {
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

	private int parseUnitExpression(EnclosingScope scope, boolean terminated) {
		checkNotEof();
		int start = index;
		int lhs = parseInfixExpression(scope, terminated);
		if (tryAndMatch(terminated, Is) == null) {
			return lhs;
		} else {
			int rhs = parseType(scope);
			Bytecode op = new Bytecode(Opcode.IS, lhs, rhs);
			return scope.add(op, sourceAttr(start, index - 1));
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
	private int parseInfixExpression(EnclosingScope scope, boolean terminated) {
		checkNotEof();
		int start = index;
		// Parse term
		int first = parseAccessExpression(scope, terminated);
		// See whether there is an infix operator trailing after term
		Token lookahead = tryAndMatch(terminated, INFIX_OPERATORS);
		if (lookahead != null) {
			// Yes, there is so try and parse operator sequence.
			Bytecode.Opcode opcode = OPERATOR_MAP.get(lookahead.kind);
			ArrayList<Integer> terms = new ArrayList<Integer>();
			terms.add(first);
			do {
				terms.add(parseAccessExpression(scope, terminated));
			} while (tryAndMatch(terminated, lookahead.kind) != null);
			//
			return scope.add(new Bytecode(opcode, terms), sourceAttr(start, index - 1));
		} else {
			return first;
		}
	}

	/**
	 * Parse an <i>access expression</i>, which has the form:
	 *
	 * <pre>
	 * AccessExpr::= PrimaryExpr
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
	private int parseAccessExpression(EnclosingScope scope, boolean terminated) {
		int start = index;
		int lhs = parseTermExpression(scope, terminated);
		Token token;

		while ((token = tryAndMatchOnLine(LeftSquare)) != null
				|| (token = tryAndMatch(terminated, Dot, MinusGreater)) != null) {
			switch (token.kind) {
			case LeftSquare: {
				// NOTE: expression guaranteed to be terminated by ']'.
				int rhs = parseUnitExpression(scope, true);
				// This is a plain old array access expression
				match(RightSquare);
				lhs = scope.add(new Bytecode(Opcode.ARRAY_ACCESS, lhs, rhs), sourceAttr(start, index - 1));
				break;
			}
			case Dot: {
				int rhs = parseIdentifier(scope);
				lhs = scope.add(new Bytecode(Opcode.RECORD_ACCESS, lhs, rhs), sourceAttr(start, index - 1));
				break;
			}
			}
		}

		return lhs;
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
	private int parseTermExpression(EnclosingScope scope, boolean terminated) {
		checkNotEof();

		int start = index;
		Token token = tokens.get(index);

		switch (token.kind) {
		case LeftBrace:
			return parseBracketedExpression(scope, terminated);
		case Identifier:
			if (isFunctionCall()) {
				return parseInvokeExpression(scope, start, terminated);
			} else if (scope.isDeclaredVariable(token.text)) {
				// Signals a local variable access
				match(Identifier);
				int varidx = scope.getVariableDeclaration(token.text);
				return scope.add(new Bytecode(Opcode.VARACCESS,varidx), sourceAttr(start, index - 1));
			} else {
				// Otherwise, this must be a constant access of some kind.
				// Observe that, at this point, we cannot determine whether or
				// not this is a constant-access or a package-access which marks
				// the beginning of a constant-access.
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
		case Shreak:
			return parseLogicalNotExpression(scope, terminated);
		}

		syntaxError("unrecognised term", token);
		return -1; //deadcode
	}

	private int parseConstantExpression(Token token, EnclosingScope scope) {
		match(token.kind);
		Bytecode bytecode;
		switch (token.kind) {
		case Null:
			bytecode = new Bytecode(Opcode.NULL);
			break;
		case True:
			bytecode = new Bytecode.Bool(true);
			break;
		case False:
			bytecode = new Bytecode.Bool(false);
			break;
		case IntValue: {
			BigInteger val = new BigInteger(token.text);
			bytecode = new Bytecode.Int(val);
			break;
		}
		case StringValue: {
			String str = parseString(token.text);
			// FIXME: following may be broken because of conversion between
			// UTF16 from java.lang.String.
			bytecode = new Bytecode.UTF8(str.getBytes());
			break;
		}
		default:
			syntaxError("unrecognised constant", token);
			return -1; // deadcode
		}

		Attribute attribute = new Attribute.Source(token.start, token.end(), 0);
		return scope.add(bytecode, attribute);
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
	private int parseBracketedExpression(EnclosingScope scope, boolean terminated) {
		int start = index;
		match(LeftBrace);

		// At this point, we must begin to disambiguate casts from general
		// bracketed expressions. In the case that what follows the left brace
		// is something which can only be a type, then clearly we have a cast.
		// However, in the other case, we may still have a cast since many types
		// cannot be clearly distinguished from expressions at this stage (e.g.
		// "(nat,nat)" could either be a tuple type (if "nat" is a type) or a
		// tuple expression (if "nat" is a variable or constant).

		Integer t = parseDefiniteType(scope);

		if (t != null) {
			// At this point, it's looking likely that we have a cast. However,
			// it's not certain because of the potential for nested braces. For
			// example, consider "((char) x + y)". We'll parse the outermost
			// brace and what follows *must* be parsed as either a type, or
			// bracketed type.
			if (tryAndMatch(true, RightBrace) != null) {
				// Ok, finally, we are sure that it is definitely a cast.
				int e = parseMultiExpression(scope, terminated);
				return scope.add(new Bytecode(Opcode.CAST, t, e), sourceAttr(start, index - 1));
			}
		}
		// We still may have either a cast or a bracketed expression, and we
		// cannot tell which yet.
		index = start;
		match(LeftBrace);
		int e = parseUnitExpression(scope, true);
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
				int type = parseType(scope);
				// Now, parse cast expression
				e = parseUnitExpression(scope, terminated);
				return scope.add(new Bytecode(Opcode.CAST, type, e), sourceAttr(start, index - 1));
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
	private int parseArrayInitialiserExpression(EnclosingScope scope, boolean terminated) {
		int start = index;
		match(LeftSquare);
		ArrayList<Integer> operands = new ArrayList<Integer>();

		boolean firstTime = true;
		boolean isArray = true;
		while (eventuallyMatch(RightSquare) == null) {
			if (!firstTime) {
				if (!isArray) {
					// Force failure
					match(RightSquare);
				} else if (tryAndMatch(true, SemiColon) == null) {
					match(Comma);
				} else {
					// This indicates an array
					isArray = false;
				}
			}
			firstTime = false;
			// NOTE: we require the following expression be a "non-tuple"
			// expression. That is, it cannot be composed using ',' unless
			// braces enclose the entire expression. This is because the outer
			// list constructor expression is used ',' to distinguish elements.
			// Also, expression is guaranteed to be terminated, either by ']' or
			// ','.
			operands.add(parseUnitExpression(scope, true));
		}

		Bytecode.Opcode opcode = isArray ? Opcode.ARRAY_INITIALISER : Opcode.ARRAY_GENERATOR;
		return scope.add(new Bytecode(opcode, operands), sourceAttr(start, index - 1));
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
	private int parseRecordExpression(EnclosingScope scope, boolean terminated) {
		int start = index;
		match(LeftCurly);
		HashSet<String> keys = new HashSet<String>();
		ArrayList<Integer> exprs = new ArrayList<Integer>();

		boolean firstTime = true;
		while (eventuallyMatch(RightCurly) == null) {
			if (!firstTime) {
				match(Comma);
			}
			firstTime = false;
			// Parse field name being constructed
			int fieldStart = index;
			int n = parseIdentifier(scope);
			// FIXME: Check field name is unique
//			if (keys.contains(n.text)) {
//				syntaxError("duplicate tuple key", n);
//			}
			match(Colon);
			// Parse expression being assigned to field
			// NOTE: we require the following expression be a "non-tuple"
			// expression. That is, it cannot be composed using ',' unless
			// braces enclose the entire expression. This is because the outer
			// record constructor expression is used ',' to distinguish fields.
			// Also, expression is guaranteed to be terminated, either by '}' or
			// ','.
			int e = parseUnitExpression(scope, true);

			exprs.add(scope.add(new Bytecode(Opcode.PAIR, n,e), sourceAttr(fieldStart,index-1)));
		}

		return scope.add(new Bytecode(Opcode.RECORD_INITIALISER,exprs), sourceAttr(start, index - 1));
	}

	/**
	 * Parse a length of expression, which is of the form:
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
	private int parseLengthOfExpression(EnclosingScope scope, boolean terminated) {
		int start = index;
		match(VerticalBar);
		int e = parseUnitExpression(scope, true);
		match(VerticalBar);
		return scope.add(new Bytecode(Opcode.ARRAY_LENGTH, e), sourceAttr(start, index - 1));
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
	private int parseNegationExpression(EnclosingScope scope, boolean terminated) {
		int start = index;
		match(Minus);
		int e = parseUnitExpression(scope, terminated);
		//
		return scope.add(new Bytecode(Opcode.NEG, e), sourceAttr(start, index - 1));
	}

	/**
	 * Parse an invocation expression, which has the form:
	 *
	 * <pre>
	 * InvokeExpr::= Identifier '(' [ Expr (',' Expr)* ] ')'
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
	private int parseInvokeExpression(EnclosingScope scope, int start, boolean terminated) {
		// Create a dummy nameid which will be resolved later on
		int nid = parseNameID(scope);
		// Parse arguments
		int[] args = parseInvocationArguments(scope);
		// Construct relevant bytecode
		Bytecode ivk = new Bytecode(Opcode.FUNCALL, nid, args);
		return scope.add(ivk, sourceAttr(start, index - 1));
	}

	/**
	 * <p>
	 * This function is called during parsing an expression after matching an
	 * identifier. The goal is to determine whether what follows the identifier
	 * indicates an invocation expression, or whether the identifier is just a
	 * variable access of some sort.
	 * </p>
	 * <p>
	 * Unfortunately, this function is rather "low-level". Essentially, it just
	 * moves forwards through the tokens on the current line counting the nestng
	 * level of any generic arguments it encounters. At the end, it looks to see
	 * whether or not a left brace is present as, in this position, we can only
	 * have an invocation.
	 * </p>
	 *
	 * @return
	 */
	private boolean isFunctionCall() {
		// First, attempt to parse a generic argument list if one exists.

		int myIndex = this.index + 1; // skip identifier first

		myIndex = skipLineSpace(myIndex);

		return myIndex < tokens.size() && tokens.get(myIndex).kind == LeftBrace;
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
	private int[] parseInvocationArguments(EnclosingScope scope) {
		ArrayList<Integer> arguments = new ArrayList<Integer>();
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

		return ArrayUtils.toIntArray(arguments);
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
	private int parseLogicalNotExpression(EnclosingScope scope, boolean terminated) {
		int start = index;
		match(Shreak);
		// Note: cannot parse unit expression here, because that messes up the
		// precedence. For example, !result ==> other should be parsed as
		// (!result) ==> other, not !(result ==> other).
		int e = parseUnitExpression(scope, terminated);
		//
		return scope.add(new Bytecode(Opcode.NOT, e), sourceAttr(start, index - 1));
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
	public Integer parseDefiniteType(EnclosingScope scope) {
		int start = index; // backtrack point
		try {
			int type = parseType(scope);
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
	private boolean mustParseAsType(int typeIndex, EnclosingScope scope) {
		WyalFile.Location bytecode = scope.getLocation(typeIndex);
		switch (bytecode.getOpcode()) {
		case T_ARRAY:
		case T_RECORD:
		case T_FUN:
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
	private int parseType(EnclosingScope scope) {
		int start = index;
		int first = parseUnaryType(scope);
		Token lookahead = tryAndMatch(false,Ampersand,VerticalBar);
		if(lookahead == null) {
			return first;
		} else {
			ArrayList<Integer> operands = new ArrayList<Integer>();
			operands.add(first);
			do  {
				operands.add(parseUnaryType(scope));
			} while(tryAndMatch(false,lookahead.kind) != null);
			Bytecode rt;
			if(lookahead.kind == Ampersand) {
				rt = new Bytecode(Opcode.T_INTERSECTION,operands);
			} else {
				rt = new Bytecode(Opcode.T_UNION,operands);
			}
			return scope.add(rt,sourceAttr(start, index - 1));
		}
	}

	private int parseUnaryType(EnclosingScope scope) {
		// Should match negation and reference types here!
		int start = index;
		int type = parseBaseType(scope);
		while(tryAndMatch(false,LeftSquare) != null) {
			match(RightSquare);
			type = scope.add(new Bytecode(Opcode.T_ARRAY,type), sourceAttr(start, index - 1));
		}
		return type;
	}

	private int parseBaseType(EnclosingScope scope) {
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
		case Identifier:
			return parseNominalType(scope);
		default:
			syntaxError("unknown type encountered", token);
			return -1; // deadcode
		}
	}

	private int parsePrimitiveType(EnclosingScope scope) {
		int start = index;
		Token token = tokens.get(index);
		Opcode opcode;
		switch (token.kind) {
		case Void:
			opcode = Opcode.T_VOID;
			break;
		case Any:
			opcode = Opcode.T_ANY;
			break;
		case Null:
			opcode = Opcode.T_NULL;
			break;
		case Bool:
			opcode = Opcode.T_BOOL;
			break;
		case Int:
			opcode = Opcode.T_INT;
			break;
		default:
			syntaxError("unknown primitive type encountered", token);
			return -1; // deadcode
		}
		match(token.kind);
		return scope.add(new Bytecode(opcode), sourceAttr(start,index-1));
	}

	/**
	 * Parse a negation type, which is of the form:
	 *
	 * @param scope
	 *            The enclosing scope for this expression. This identifies any
	 *            generic arguments which are in scope, and also allocated each
	 *            variable in scope to its location index.
	 * <pre>
	 * NegationType ::= '!' Type
	 * </pre>
	 *
	 * @return
	 */
	private int parseNegationType(EnclosingScope scope) {
		int start = index;
		match(Shreak);
		int element = parseType(scope);
		return scope.add(new Bytecode(Opcode.T_NEGATION, element), sourceAttr(start, index - 1));
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
	private int parseBracketedType(EnclosingScope scope) {
		int start = index;
		match(LeftBrace);
		int type = parseType(scope);
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
	private int parseRecordType(EnclosingScope scope) {
		int start = index;
		match(LeftCurly);
		List<Integer> fields = new ArrayList<Integer>();
		boolean firstTime = true;
		while (eventuallyMatch(RightCurly) == null) {
			if (!firstTime) {
				match(Comma);
			} else {
				firstTime = false;
			}
			int fieldStart = index;
			int fieldType = parseType(scope);
			int fieldName = parseIdentifier(scope);
			Bytecode bytecode = new Bytecode(Opcode.PAIR, fieldType, fieldName);
			fields.add(scope.add(bytecode, sourceAttr(fieldStart, index - 1)));
		}
		return scope.add(new Bytecode(Opcode.T_RECORD, fields), sourceAttr(start, index - 1));
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
	private int parseNominalType(EnclosingScope scope) {
		int start = index;
		//
		int nameID = parseNameID(scope);
		// this is a nominal type constructor
		return scope.add(new Bytecode(Opcode.T_NOMINAL, nameID), sourceAttr(start, index - 1));
	}

	private int parseIdentifier(EnclosingScope scope) {
		int start = index;
		String id = match(Identifier).text;
		// FIXME: this is a hack for now. Should really replace this with a
		// specific identifier bytecode.
		return scope.add(new Bytecode.Identifier(id), sourceAttr(start, index - 1));
	}

	private int parseNameID(EnclosingScope scope) {
		int start = index;
		List<Integer> components = new ArrayList<Integer>();
		components.add(parseIdentifier(scope));
		while (tryAndMatch(false, Dot) != null) {
			components.add(parseIdentifier(scope));
		}
		return scope.add(new Bytecode(Opcode.NAME_ID, components), sourceAttr(start, index - 1));
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

	private void syntaxError(String msg, Token t) {
		// FIXME: this is clearly not a sensible approach
		SyntacticElement unknown = new SyntacticElement.Impl() {
		};
		unknown.attributes().add(new Attribute.Source(t.start, t.start + t.text.length() - 1, -1));
		throw new SyntaxError(msg, entry, unknown);
	}

	// =======================================================================

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

	/**
	 * A fixed map from token kinds to their correspond bytecode opcodes.
	 */
	private static final HashMap<Token.Kind,Bytecode.Opcode> OPERATOR_MAP = new HashMap<>();

	static {
		OPERATOR_MAP.put(LogicalAnd, Bytecode.Opcode.AND);
		OPERATOR_MAP.put(LogicalOr, Bytecode.Opcode.OR);
		OPERATOR_MAP.put(LogicalImplication, Bytecode.Opcode.IMPLIES);
		OPERATOR_MAP.put(LogicalIff, Bytecode.Opcode.IFF);
		OPERATOR_MAP.put(LessEquals, Bytecode.Opcode.LTEQ);
		OPERATOR_MAP.put(LeftAngle, Bytecode.Opcode.LT);
		OPERATOR_MAP.put(GreaterEquals, Bytecode.Opcode.GTEQ);
		OPERATOR_MAP.put(RightAngle, Bytecode.Opcode.GT);
		OPERATOR_MAP.put(EqualsEquals, Bytecode.Opcode.EQ);
		OPERATOR_MAP.put(NotEquals, Bytecode.Opcode.NEQ);
		OPERATOR_MAP.put(Plus, Bytecode.Opcode.ADD);
		OPERATOR_MAP.put(Minus, Bytecode.Opcode.SUB);
		OPERATOR_MAP.put(Star, Bytecode.Opcode.MUL);
		OPERATOR_MAP.put(RightSlash, Bytecode.Opcode.DIV);
		OPERATOR_MAP.put(Percent, Bytecode.Opcode.REM);
	}

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
	private static final class EnclosingScope {
		/**
		 * Maps variables to their WyIL location.
		 */
		private final HashMap<String, Integer> environment;

		/**
		 * The enclosing source file scope
		 */
		private final WyalFile parent;

		public EnclosingScope(WyalFile parent) {
			this(new HashMap<String, Integer>(), parent);
		}

		private EnclosingScope(Map<String, Integer> environment, WyalFile parent) {
			this.environment = new HashMap<String, Integer>(environment);
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
		public int getVariableDeclaration(String name) {
			return environment.get(name);
		}

		public WyalFile.Location getLocation(String name) {
			return parent.getLocation(environment.get(name));
		}

		public WyalFile.Location getLocation(int index) {
			return parent.getLocation(index);
		}

		/**
		 * Declare a new variable in the enclosing scope.
		 *
		 * @param declartion
		 *            Index of declaration "Location"
		 * @return
		 */
		public void declareInScope(int declarationIndex) {
			WyalFile.Location decl = parent.getLocation(declarationIndex);
			Bytecode.Identifier id = (Bytecode.Identifier) decl.getOperand(1).getCode();
			environment.put(id.get(), declarationIndex);
		}

		public int add(Bytecode stmt, Attribute... attributes) {
			return add(stmt,Arrays.asList(attributes));
		}

		public int add(Bytecode bytecode, List<Attribute> attributes) {
			List<WyalFile.ConstantPoolItem> items = parent.getConstantPool();
			items.add(new WyalFile.Location(parent, WyalFile.UNKNOWN_TYPE, bytecode, attributes));
			return items.size() - 1;
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
