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

import java.io.BufferedReader;
import java.io.FileInputStream;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.io.Reader;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;

import wyal.lang.WyalFile;
import wybs.lang.Attribute;
import wybs.lang.SyntacticElement;
import wybs.lang.SyntaxError;
import wyfs.lang.Path;

/**
 * Split a source file into a list of tokens. These tokens can then be fed into
 * the parser in order to generate an Abstract Syntax Tree (AST).
 *
 * @author David J. Pearce
 *
 */
public class WyalFileLexer {
	private final Path.Entry<WyalFile> entry;
	private final StringBuilder input;
	private int pos;

	public WyalFileLexer(Path.Entry<WyalFile> entry) throws IOException {
		this.entry = entry;
		//
		Reader reader = new InputStreamReader(entry.inputStream(),"UTF8");
		BufferedReader in = new BufferedReader(reader);

        StringBuilder text = new StringBuilder();
		int len = 0;
		char[] buf = new char[1024];
		while ((len = in.read(buf)) != -1) {
			text.append(buf, 0, len);
		}
        input = text;
	}

	public WyalFileLexer(String input) {
		this.entry = null;
		this.input = new StringBuilder(input);
	}

	/**
	 * Scan all characters from the input stream and generate a corresponding
	 * list of tokens, whilst discarding all whitespace and comments.
	 *
	 * @return
	 */
	public List<Token> scan() {
		ArrayList<Token> tokens = new ArrayList<>();
		pos = 0;

		while (pos < input.length()) {
			char c = input.charAt(pos);

			if (Character.isDigit(c)) {
				tokens.add(scanNumericConstant());
			} else if (c == '"') {
				tokens.add(scanStringConstant());
			} else if (c == '\'') {
				tokens.add(scanCharacterConstant());
			} else if (isOperatorStart(c)) {
				tokens.add(scanOperator());
			} else if (Character.isLetter(c) || c == '_' || c == '$') {
				tokens.add(scanIdentifier());
			} else if (Character.isWhitespace(c)) {
				scanWhiteSpace(tokens);
			} else {
				syntaxError("unknown token encountered",pos);
			}
		}

		return tokens;
	}

	/**
	 * Scan a numeric constant. That is a sequence of digits which gives either
	 * an integer constant, or a real constant (if it includes a dot) or a byte
	 * (if it ends in a 'b').
	 *
	 * @return
	 */
	public Token scanNumericConstant() {
		int start = pos;
		while (pos < input.length() && Character.isDigit(input.charAt(pos))) {
			pos = pos + 1;
		}
		if (pos < input.length() && input.charAt(pos) == '.') {
			pos = pos + 1;
			if (pos < input.length() && input.charAt(pos) == '.') {
				// this is case for range e.g. 0..1
				pos = pos - 1;
				return new Token(Token.Kind.IntValue, input.substring(start,
						pos), start);
			}
			while (pos < input.length() && Character.isDigit(input.charAt(pos))) {
				pos = pos + 1;
			}
			return new Token(Token.Kind.RealValue, input.substring(start, pos),
					start);
		} else {
			return new Token(Token.Kind.IntValue, input.substring(start, pos),
					start);
		}
	}

	/**
	 * Scan a character constant, such as e.g. 'c'. Observe that care must be
	 * taken to properly handle escape codes. For example, '\n' is a single
	 * character constant which is made up from two characters in the input
	 * string.
	 *
	 * @return
	 */
	public Token scanCharacterConstant() {
		int start = pos;
		pos++;
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
				syntaxError("unrecognised escape character", pos);
			}
		}
		if (input.charAt(pos) != '\'') {
			syntaxError("unexpected end-of-character", pos);
		}
		pos = pos + 1;
		return new Token(Token.Kind.CharValue, input.substring(start, pos),
				start);
	}

	public Token scanStringConstant() {
		int start = pos;
		boolean escaped = false;
		pos++;
		while (pos < input.length()) {
			char c = input.charAt(pos);
			if (c == '"' && !escaped) {
				String v = input.substring(start, ++pos);
				return new Token(Token.Kind.StringValue, v, start);
			} else if(c == '\\' && !escaped) {
				escaped = true;
			} else {
				escaped = false;
			}
			pos = pos + 1;
		}
		syntaxError("unexpected end-of-string", pos - 1);
		return null;
	}

	public static final char UC_FORALL = '\u2200';
	public static final char UC_EXISTS = '\u2203';
	public static final char UC_EMPTYSET = '\u2205';
	public static final char UC_SUBSET = '\u2282';
	public static final char UC_SUBSETEQ = '\u2286';
	public static final char UC_SUPSET = '\u2283';
	public static final char UC_SUPSETEQ = '\u2287';
	public static final char UC_SETUNION = '\u222A';
	public static final char UC_SETINTERSECTION = '\u2229';
	public static final char UC_LESSEQUALS = '\u2264';
	public static final char UC_GREATEREQUALS = '\u2265';
	public static final char UC_ELEMENTOF = '\u2208';
	public static final char UC_LOGICALAND = '\u2227';
	public static final char UC_LOGICALOR = '\u2228';

	static final char[] opStarts = { ',', '(', ')', '[', ']', '{', '}', '+',
			'-', '*', '/', '%', '^', '!', '?', '=', '<', '>', ':', ';', '&', '|',
			'.', '~',
			// Unicode operators
			UC_FORALL,
			UC_EXISTS,
			UC_EMPTYSET,
			UC_SUBSET,
			UC_SUBSETEQ,
			UC_SUPSET,
			UC_SUPSETEQ,
			UC_SETUNION,
			UC_SETINTERSECTION,
			UC_LESSEQUALS,
			UC_GREATEREQUALS,
			UC_ELEMENTOF
	};

	public boolean isOperatorStart(char c) {
		for (char o : opStarts) {
			if (c == o) {
				return true;
			}
		}
		return false;
	}

	public Token scanOperator() {
		char c = input.charAt(pos);

		switch (c) {
		case '.':
			if ((pos + 1) < input.length() && input.charAt(pos + 1) == '.') {
				pos = pos + 2;
				if (pos < input.length() && input.charAt(pos) == '.') {
					return new Token(Token.Kind.DotDotDot, "...", pos++);
				} else {
					return new Token(Token.Kind.DotDot, "..", pos);
				}
			} else {
				return new Token(Token.Kind.Dot, ".", pos++);
			}
		case ',':
			return new Token(Token.Kind.Comma, ",", pos++);
		case ':':
			if ((pos + 1) < input.length() && input.charAt(pos + 1) == '=') {
				pos += 2;
				return new Token(Token.Kind.ColonEquals, ":=", pos - 2);
			} else {
				return new Token(Token.Kind.Colon, ":", pos++);
			}
		case ';':
			return new Token(Token.Kind.SemiColon, ";", pos++);
		case '|':
			if (pos + 1 < input.length() && input.charAt(pos + 1) == '|') {
				pos += 2;
				return new Token(Token.Kind.LogicalOr, "||", pos - 2);
			} else {
				return new Token(Token.Kind.VerticalBar, "|", pos++);
			}
		case '(':
			return new Token(Token.Kind.LeftBrace, "(", pos++);
		case ')':
			return new Token(Token.Kind.RightBrace, ")", pos++);
		case '[':
			return new Token(Token.Kind.LeftSquare, "[", pos++);
		case ']':
			return new Token(Token.Kind.RightSquare, "]", pos++);
		case '{':
			return new Token(Token.Kind.LeftCurly, "{", pos++);
		case '}':
			return new Token(Token.Kind.RightCurly, "}", pos++);
		case '+':
			if ((pos + 1) < input.length() && input.charAt(pos + 1) == '+') {
				pos = pos + 2;
				return new Token(Token.Kind.PlusPlus, "++", pos);
			} else {
				return new Token(Token.Kind.Plus, "+", pos++);
			}
		case '-':
			if ((pos + 1) < input.length() && input.charAt(pos + 1) == '>') {
				pos += 2;
				return new Token(Token.Kind.MinusGreater, "->", pos - 2);
			} else {
				return new Token(Token.Kind.Minus, "-", pos++);
			}
		case '*':
			return new Token(Token.Kind.Star, "*", pos++);
		case '&':
			if (pos + 1 < input.length() && input.charAt(pos + 1) == '&') {
				pos += 2;
				return new Token(Token.Kind.LogicalAnd, "&&", pos - 2);
			} else {
				return new Token(Token.Kind.Ampersand, "&", pos++);
			}
		case '/':
			if((pos+1) < input.length() && input.charAt(pos+1) == '/') {
				return scanLineComment();
			} else if((pos+1) < input.length() && input.charAt(pos+1) == '*') {
				return scanBlockComment();
			} else {
				return new Token(Token.Kind.RightSlash, "/", pos++);
			}
		case '%':
			return new Token(Token.Kind.Percent, "%", pos++);
		case '^':
			return new Token(Token.Kind.Caret, "^", pos++);
		case '!':
			if ((pos + 1) < input.length() && input.charAt(pos + 1) == '=') {
				pos += 2;
				return new Token(Token.Kind.NotEquals, "!=", pos - 2);
			} else {
				return new Token(Token.Kind.Shreak, "!", pos++);
			}
		case '=':
			if ((pos + 1) < input.length() && input.charAt(pos + 1) == '=') {
				pos += 2;
				if (pos < input.length() && input.charAt(pos) == '>') {
					pos++;
					return new Token(Token.Kind.LogicalImplication, "==>", pos - 3);
				} else {
					return new Token(Token.Kind.EqualsEquals, "==", pos - 2);
				}
			} else if ((pos + 1) < input.length() && input.charAt(pos + 1) == '>') {
				pos += 2;
				return new Token(Token.Kind.EqualsGreater, "=>", pos - 2);
			}
			break;
		case '<':
			if ((pos + 1) < input.length() && input.charAt(pos + 1) == '=') {
				pos += 2;
				if ((pos+1) < input.length() && input.charAt(pos) == '=' && input.charAt(pos+1) == '>') {
					pos += 2;
					return new Token(Token.Kind.LogicalIff, "<==>", pos - 4);
				} else {
					return new Token(Token.Kind.LessEquals, "<=", pos - 2);
				}
			} else{
				return new Token(Token.Kind.LeftAngle, "<", pos++);
			}
		case '>':
			if ((pos + 1) < input.length() && input.charAt(pos + 1) == '=') {
				pos += 2;
				return new Token(Token.Kind.GreaterEquals, ">=", pos - 2);
			} else {
				return new Token(Token.Kind.RightAngle, ">", pos++);
			}
		// =================================================================
		//
		// =================================================================
		case UC_LESSEQUALS:
			return new Token(Token.Kind.LessEquals, "" + c, pos++);
		case UC_GREATEREQUALS:
			return new Token(Token.Kind.GreaterEquals, "" + c, pos++);
		case UC_SETUNION:
			return new Token(Token.Kind.SetUnion, "" + c, pos++);
		case UC_SETINTERSECTION:
			return new Token(Token.Kind.SetIntersection, "" + c, pos++);
		case UC_ELEMENTOF:
			return new Token(Token.Kind.ElementOf, "" + c, pos++);
		case UC_SUBSET:
			return new Token(Token.Kind.Subset, "" + c, pos++);
		case UC_SUBSETEQ:
			return new Token(Token.Kind.SubsetEquals, "" + c, pos++);
		case UC_SUPSET:
			return new Token(Token.Kind.Superset, "" + c, pos++);
		case UC_SUPSETEQ:
			return new Token(Token.Kind.SupersetEquals, "" + c, pos++);
		case UC_EMPTYSET:
			return new Token(Token.Kind.EmptySet, "" + c, pos++);
		case UC_LOGICALOR:
			return new Token(Token.Kind.LogicalOr, "" + c, pos++);
		case UC_LOGICALAND:
			return new Token(Token.Kind.LogicalAnd, "" + c, pos++);
		}

		syntaxError("unknown operator encountered: " + c, pos);
		return null;
	}

	public Token scanIdentifier() {
		int start = pos;
		while (pos < input.length()
				&& (input.charAt(pos) == '_' || input.charAt(pos) == '$'
						|| input.charAt(pos) == '%' || Character
							.isLetterOrDigit(input.charAt(pos)))) {
			pos++;
		}
		String text = input.substring(start, pos);

		// now, check for keywords
		Token.Kind kind = keywords.get(text);
		if (kind == null) {
			// not a keyword, so just a regular identifier.
			kind = Token.Kind.Identifier;
		}
		return new Token(kind, text, start);
	}

	public void scanWhiteSpace(List<Token> tokens) {
		while (pos < input.length()
				&& Character.isWhitespace(input.charAt(pos))) {
			if (input.charAt(pos) == ' ' || input.charAt(pos) == '\t') {
				tokens.add(scanIndent());
			} else if (input.charAt(pos) == '\n') {
				tokens.add(new Token(Token.Kind.NewLine, input.substring(pos,
						pos + 1), pos));
				pos = pos + 1;
			} else if (input.charAt(pos) == '\r' && (pos + 1) < input.length()
					&& input.charAt(pos + 1) == '\n') {
				tokens.add(new Token(Token.Kind.NewLine, input.substring(pos,
						pos + 2), pos));
				pos = pos + 2;
			} else {
				syntaxError("unknown whitespace character encounterd: \""
						+ input.charAt(pos), pos);
			}
		}
	}

	/**
	 * Scan one or more spaces or tab characters, combining them to form an
	 * "indent".
	 *
	 * @return
	 */
	public Token scanIndent() {
		int start = pos;
		while (pos < input.length()
				&& (input.charAt(pos) == ' ' || input.charAt(pos) == '\t')) {
			pos++;
		}
		return new Token(Token.Kind.Indent, input.substring(start, pos), start);
	}

	public Token scanLineComment() {
		int start = pos;
		while (pos < input.length() && input.charAt(pos) != '\n') {
			pos++;
		}
		return new Token(Token.Kind.LineComment, input.substring(start, pos),
				start);
	}

	public Token scanBlockComment() {
		int start = pos;
		while((pos+1) < input.length() && (input.charAt(pos) != '*' || input.charAt(pos+1) != '/')) {
			pos++;
		}
		pos++;
		pos++;
		return new Token(Token.Kind.BlockComment,input.substring(start,pos),start);
	}

	/**
	 * Skip over any whitespace at the current index position in the input
	 * string.
	 *
	 * @param tokens
	 */
	public void skipWhitespace(List<Token> tokens) {
		while (pos < input.length()
				&& (input.charAt(pos) == '\n' || input.charAt(pos) == '\t')) {
			pos++;
		}
	}

	/**
	 * Raise a syntax error with a given message at given index.
	 *
	 * @param msg
	 *            --- message to raise.
	 * @param index
	 *            --- index position to associate the error with.
	 */
	private void syntaxError(String msg, int index) {
		// FIXME: this is clearly not a sensible approach
		SyntacticElement unknown = new SyntacticElement.Impl() {};
		unknown.attributes().add(new Attribute.Source(index, index, -1));
		throw new SyntaxError(msg, entry, unknown);
	}

	/**
	 * A map from identifier strings to the corresponding token kind.
	 */
	public static final HashMap<String, Token.Kind> keywords = new HashMap<String, Token.Kind>() {
		{
			// types
			put("void", Token.Kind.Void);
			put("any", Token.Kind.Any);
			put("null", Token.Kind.Null);
			put("bool", Token.Kind.Bool);
			put("int", Token.Kind.Int);
			put("real", Token.Kind.Real);
			// constants
			put("true", Token.Kind.True);
			put("false", Token.Kind.False);
			// statements
			put("assert", Token.Kind.Assert);
			put("either", Token.Kind.Either);
			put("or", Token.Kind.Or);
			put("if", Token.Kind.If);
			put("then", Token.Kind.Then);
			// expressions
			put("forall", Token.Kind.Forall);
			put("exists", Token.Kind.Exists);
			put("is", Token.Kind.Is);
			put("in", Token.Kind.In);
			// declarations
			put("function", Token.Kind.Function);
			put("import", Token.Kind.Import);
			put("define", Token.Kind.Define);
			put("constant", Token.Kind.Constant);
			// NOTE: we don't include type here because that would *prevent* it
			// from being used as a variable identifier.
			// put("type", Token.Kind.Type);
			put("where", Token.Kind.Where);
			put("ensures", Token.Kind.Ensures);
			put("requires", Token.Kind.Requires);
			put("public", Token.Kind.Public);
			put("protected", Token.Kind.Protected);
			put("private", Token.Kind.Private);
			put("package", Token.Kind.Package);
		}
	};

	/**
	 * The base class for all tokens.
	 *
	 * @author David J. Pearce
	 *
	 */
	public static class Token {

		public enum Kind {
			Identifier,
			// Constants
			True {
				@Override
				public String toString() {
					return "true";
				}
			},
			False {
				@Override
				public String toString() {
					return "true";
				}
			},
			RealValue,
			IntValue,
			CharValue,
			StringValue,
			// Types
			Null {
				@Override
				public String toString() {
					return "null";
				}
			},
			Void {
				@Override
				public String toString() {
					return "void";
				}
			},
			Any {
				@Override
				public String toString() {
					return "any";
				}
			},
			Bool {
				@Override
				public String toString() {
					return "bool";
				}
			},
			Int {
				@Override
				public String toString() {
					return "int";
				}
			},
			Real {
				@Override
				public String toString() {
					return "real";
				}
			},
			Char {
				@Override
				public String toString() {
					return "char";
				}
			},
			String {
				@Override
				public String toString() {
					return "string";
				}
			},
			// Statements
			Assert {
				@Override
				public String toString() {
					return "assert";
				}
			},
			Either {
				@Override
				public String toString() {
					return "either";
				}
			},
			Or {
				@Override
				public String toString() {
					return "or";
				}
			},
			If {
				@Override
				public String toString() {
					return "if";
				}
			},
			Then {
				@Override
				public String toString() {
					return "then";
				}
			},
			// Declarations
			Package {
				@Override
				public String toString() {
					return "package";
				}
			},
			Import {
				@Override
				public String toString() {
					return "import";
				}
			},
			Public {
				@Override
				public String toString() {
					return "public";
				}
			},
			Private {
				@Override
				public String toString() {
					return "private";
				}
			},
			Protected {
				@Override
				public String toString() {
					return "protected";
				}
			},
			Function {
				@Override
				public String toString() {
					return "function";
				}
			},
			Type {
				@Override
				public String toString() {
					return "type";
				}
			},
			Assume {
				@Override
				public String toString() {
					return "assume";
				}
			},
			Constant {
				@Override
				public String toString() {
					return "constant";
				}
			},
			Define {
				@Override
				public String toString() {
					return "define";
				}
			},
			Requires {
				@Override
				public String toString() {
					return "requires";
				}
			},
			Ensures {
				@Override
				public String toString() {
					return "ensures";
				}
			},
			Where {
				@Override
				public String toString() {
					return "where";
				}
			},
			Throws {
				@Override
				public String toString() {
					return "throws";
				}
			},
			// Expressions
			Forall {
				@Override
				public String toString() {
					return "forall";
				}
			},
			Exists {
				@Override
				public String toString() {
					return "exists";
				}
			},
			Is {
				@Override
				public String toString() {
					return "is";
				}
			},
			In {
				@Override
				public String toString() {
					return "in";
				}
			},
			Comma {
				@Override
				public String toString() {
					return ",";
				}
			},
			Colon {
				@Override
				public String toString() {
					return ":";
				}
			},
			ColonEquals {
				@Override
				public String toString() {
					return ":=";
				}
			},
			SemiColon {
				@Override
				public String toString() {
					return ";";
				}
			},
			Ampersand {
				@Override
				public String toString() {
					return "&";
				}
			},
			VerticalBar {
				@Override
				public String toString() {
					return "|";
				}
			},
			LeftBrace {
				@Override
				public String toString() {
					return "(";
				}
			},
			RightBrace {
				@Override
				public String toString() {
					return ")";
				}
			},
			LeftSquare {
				@Override
				public String toString() {
					return "[";
				}
			},
			RightSquare {
				@Override
				public String toString() {
					return "]";
				}
			},
			LeftAngle {
				@Override
				public String toString() {
					return "<";
				}
			},
			RightAngle {
				@Override
				public String toString() {
					return ">";
				}
			},
			LeftCurly {
				@Override
				public String toString() {
					return "{";
				}
			},
			RightCurly {
				@Override
				public String toString() {
					return "}";
				}
			},
			Plus {
				@Override
				public String toString() {
					return "+";
				}
			},
			PlusPlus {
				@Override
				public String toString() {
					return "++";
				}
			},
			Minus {
				@Override
				public String toString() {
					return "-";
				}
			},
			Star {
				@Override
				public String toString() {
					return "*";
				}
			},
			LeftSlash {
				@Override
				public String toString() {
					return "\\";
				}
			},
			RightSlash {
				@Override
				public String toString() {
					return "//";
				}
			},
			Percent {
				@Override
				public String toString() {
					return "%";
				}
			},
			Shreak {
				@Override
				public String toString() {
					return "!";
				}
			},
			Caret {
				@Override
				public String toString() {
					return "^";
				}
			},
			Dot {
				@Override
				public String toString() {
					return ".";
				}
			},
			DotDot {
				@Override
				public String toString() {
					return "..";
				}
			},
			DotDotDot {
				@Override
				public String toString() {
					return "...";
				}
			},
			EqualsEquals {
				@Override
				public String toString() {
					return "==";
				}
			},
			NotEquals {
				@Override
				public String toString() {
					return "!=";
				}
			},
			LessEquals {
				@Override
				public String toString() {
					return "<=";
				}
			},
			GreaterEquals {
				@Override
				public String toString() {
					return ">=";
				}
			},
			EqualsGreater {
				@Override
				public String toString() {
					return "=>";
				}
			},
			MinusGreater {
				@Override
				public String toString() {
					return "->";
				}
			},
			LogicalAnd {
				@Override
				public String toString() {
					return "&&";
				}
			},
			LogicalOr {
				@Override
				public String toString() {
					return "||";
				}
			},
			LogicalImplication {
				@Override
				public String toString() {
					return "==>";
				}
			},
			LogicalIff {
				@Override
				public String toString() {
					return "<==>";
				}
			},
			SetUnion {
				@Override
				public String toString() {
					return "" + UC_SETUNION;
				}
			},
			SetIntersection {
				@Override
				public String toString() {
					return "" + UC_SETINTERSECTION;
				}
			},
			ElementOf {
				@Override
				public String toString() {
					return "" + UC_ELEMENTOF;
				}
			},
			EmptySet {
				@Override
				public String toString() {
					return "" + UC_EMPTYSET;
				}
			},
			Subset {
				@Override
				public String toString() {
					return "" + UC_SUBSET;
				}
			},
			SubsetEquals {
				@Override
				public String toString() {
					return "" + UC_SUBSETEQ;
				}
			},
			Superset {
				@Override
				public String toString() {
					return "" + UC_SUPSETEQ;
				}
			},
			SupersetEquals {
				@Override
				public String toString() {
					return "" + UC_SUPSETEQ;
				}
			},
			// Other
			NewLine, Indent, LineComment, BlockComment
		}

		public final Kind kind;
		public final String text;
		public final int start;

		public Token(Kind kind, String text, int pos) {
			this.kind = kind;
			this.text = text;
			this.start = pos;
		}

		public int end() {
			return start + text.length() - 1;
		}
	}
}
