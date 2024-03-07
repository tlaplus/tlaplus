package tla2sany;

import java.io.IOException;
import java.nio.file.FileSystems;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.PathMatcher;
import java.text.ParseException;
import java.util.ArrayList;
import java.util.List;
import java.util.stream.Collectors;
import java.util.regex.*;

/**
 * Handles reading and parsing the corpus test files.
 */
public class CorpusParser {
	
	/**
	 * Holds info about tokens in the AST DSL.
	 */
	private static class Token {

		/**
		 * The possible kinds of tokens in the AST DSL.
		 */
		private static enum Kind {
			IDENTIFIER,
			LPAREN,
			RPAREN,
			COLON
		}
		
		/**
		 * The actual string classified as the given token kind.
		 */
		public final String lexeme;
		
		/**
		 * The token kind associated with the given lexeme.
		 */
		public final Kind kind; 
		
		/**
		 * Constructs a new instance of the token class.
		 * 
		 * @param lexeme The lexeme underlying this token.
		 * @param kind The kind of the lexeme.
		 */
		public Token(String lexeme, Kind kind) {
			this.lexeme = lexeme;
			this.kind = kind;
		}
	}

	/**
	 * Breaks the input into discrete tokens.
	 * 
	 * @param input The string input to tokenize.
	 * @return A list of tokens.
	 * @throws ParseException If an unrecognized character is encountered.
	 */
	private static List<Token> tokenize(String input) throws ParseException {
		List<Token> tokens = new ArrayList<Token>();
		int[] codepoints = input.codePoints().toArray();
		StringBuilder sb = null;
		for (int i = 0; i < codepoints.length; i++) {
			int codepoint = codepoints[i];
			if (Character.isLetter(codepoint) || '_' == codepoint) {
				if (null == sb) {
					sb = new StringBuilder();
				}
				sb.appendCodePoint(codepoint);
			} else {
				if (null != sb) {
					tokens.add(new Token(sb.toString(), Token.Kind.IDENTIFIER));
					sb = null;
				}
				if (Character.isWhitespace(codepoint)) {
					continue;
				} else if (':' == codepoint) {
					tokens.add(new Token(Character.toString(codepoint), Token.Kind.COLON));
				} else if ('(' == codepoint) {
					tokens.add(new Token(Character.toString(codepoint), Token.Kind.LPAREN));
				} else if (')' == codepoint) {
					tokens.add(new Token(Character.toString(codepoint), Token.Kind.RPAREN));
				} else {
					throw new ParseException(String.format("Unhandled char %s", Character.toString(codepoint)), i);
				}
			}
		}
		return tokens;
	}

	/**
	 * AST DSL parser helper class. Follows the parser pattern outlined in
	 * https://craftinginterpreters.com/parsing-expressions.html
	 */
	private static class ParserState {
		/**
		 * The parser's current index in the token array.
		 */
		public int current;
		
		/**
		 * The unparsed input string tokens.
		 */
		public final List<Token> tokens;
		
		/**
		 * Whether to log each token consumed.
		 */
		private final boolean log;
		
		/**
		 * Initializes the parser state with the input string.
		 * 
		 * @param token The tokens to parse.
		 * @param log Whether to log each consumed char.
		 */
		public ParserState(List<Token> tokens, boolean log) {
			this.current = 0;
			this.tokens = tokens;
			this.log = log;
		}
		
		/**
		 * Whether parse is at the end of the token array.
		 * 
		 * @return True if at end.
		 */
		public boolean isAtEnd() {
			return current == tokens.size();
		}
		
		/**
		 * Peeks the current token without consuming it.
		 * 
		 * @return The current token.
		 */
		public Token peek() {
			return tokens.get(current);
		}
		
		/**
		 * Gets the token last consumed.
		 * 
		 * @return The token last consumed.
		 */
		public Token previous() {
			return tokens.get(current - 1);
		}
		
		/**
		 * Checks whether the current token is of the given kind.
		 * 
		 * @param kind The kind to check the current token against.
		 * @return True if current token is of the given kind.
		 */
		public boolean check(Token.Kind kind) {
			if (isAtEnd()) return false;
			return peek().kind == kind;
		}
		
		/**
		 * Advances the parser and returns the token advanced past. Prints
		 * out the token to standard output if logging is flagged true.
		 * 
		 * @return The token advanced past.
		 */
		public Token advance() {
			if (!isAtEnd()) current++;
			if (log) {
				System.out.println(previous().lexeme);
			}
			return previous();
		}
		
		/**
		 * Consume the current token; if current token is not of the given
		 * kind, throw a parse exception. Also throw an exception if no
		 * further tokens remain.
		 * 
		 * @param kind The token kind to match the current token against.
		 * @return The consumed token.
		 * @throws ParseException If current token is not of the given kind.
		 */
		public Token consume(Token.Kind kind) throws ParseException {
			if (check(kind)) return advance();
			throw new ParseException(String.format("Expected %s", kind), current);
		}
	}
	
	/**
	 * Performs the actual parsing of the AST DSL by mutating a parser state
	 * in place. Thankfully S-expressions are easy to parse in a single
	 * recursive function.
	 * 
	 * @param s Parser state holding the input tokens and current index.
	 * @return Root node of the AST subtree at this point in the input.
	 * @throws ParseException If invalid S-expression syntax is encountered.
	 */
	private static AstNode parseAst(ParserState parser) throws ParseException {
		parser.consume(Token.Kind.LPAREN);
		Token nodeKind = parser.consume(Token.Kind.IDENTIFIER);
		AstNode node = AstNode.Kind.fromString(nodeKind.lexeme).asNode();
		while (!parser.isAtEnd() && !parser.check(Token.Kind.RPAREN)) {
			if (parser.check(Token.Kind.LPAREN)) {
				node.addChild(parseAst(parser));
			} else {
				String fieldName = parser.consume(Token.Kind.IDENTIFIER).lexeme;
				parser.consume(Token.Kind.COLON);
				node.addField(fieldName, parseAst(parser));
			}
		}
		parser.consume(Token.Kind.RPAREN);
		return node;
	}

	/**
	 * Parse the given S-expression string into an abstract syntax tree.
	 * 
	 * @param input The S-expression in string form.
	 * @return Root node of the AST.
	 * @throws ParseException If invalid S-expression syntax is encountered.
	 */
	private static AstNode parseAst(String input) throws ParseException {
		ParserState parser = new ParserState(tokenize(input), false);
		AstNode parseTree = parseAst(parser);
		if (!parser.isAtEnd()) {
			throw new ParseException("Unparsed tokens remain", parser.current);
		}
		return parseTree;
	}
	
	/**
	 * Class holding info about a single corpus test.
	 */
	public static class CorpusTest {
		
		/**
		 * The name of the corpus test.
		 */
		public final String name;
		
		/**
		 * The unparsed TLA+ code to be given to the parser.
		 */
		public final String tlaplusInput;
		
		/**
		 * The expected parse tree, in normalized form.
		 */
		public final AstNode expectedAst;
		
		/**
		 * Initializes corpus test info by parsing the expected syntax tree.
		 * 
		 * @param name The name of the corpus test.
		 * @param tlaplusInput The unparsed TLA+ code.
		 * @param expectedAst The expected syntax tree, as an unparsed S-expression.
		 */
		public CorpusTest(String name, String tlaplusInput, String expectedAst) throws ParseException {
			this.name = name;
			this.tlaplusInput = tlaplusInput;
			this.expectedAst = parseAst(expectedAst);
		}
	}
	
	/**
	 * Class holding info about all corpus tests within a single file.
	 */
	public static class CorpusTestFile {
		
		/**
		 * Regex for identifying test headers.
		 */
		private static final Pattern headerRegex = Pattern.compile("^===+\\|\\|\\|\r?\n(?<testName>[^\r\n]*)\r?\n===+\\|\\|\\|\r?\n", Pattern.MULTILINE);
		
		/**
		 * Regex for identifying test separators.
		 */
		private static final Pattern separatorRegex = Pattern.compile("^---+\\|\\|\\|\r?\n", Pattern.MULTILINE);

		/**
		 * The path to the corpus test file.
		 */
		public final Path path;
		
		/**
		 * Ordered list of corpus tests found in the file.
		 */
		public final List<CorpusTest> tests;
		
		/**
		 * Parses the contents of a corpus test file into a list of corpus tests.
		 * 
		 * @param path The path to the corpus test file.
		 * @param content The string content of the test file.
		 * @throws ParseException If the content contains invalid test file syntax.
		 */
		public CorpusTestFile(Path path, String content) throws ParseException {
			this.path = path;
			ArrayList<CorpusTest> tests = new ArrayList<CorpusTest>();
			Matcher headerMatcher = headerRegex.matcher(content);
			Matcher separatorMatcher = separatorRegex.matcher(content);
			boolean hasNext = headerMatcher.find();
			while (hasNext) {
				String testName = headerMatcher.group("testName");
				if (!separatorMatcher.find()) {
					throw new ParseException(String.format("%s: Test %s does not have separator", path, testName), 0);
				}
				String tlaplusInput = content.substring(headerMatcher.end(), separatorMatcher.start());
				hasNext = headerMatcher.find();
				String expectedAst =
						hasNext
						? content.substring(separatorMatcher.end(), headerMatcher.start())
						: content.substring(separatorMatcher.end());
				tests.add(new CorpusTest(testName, tlaplusInput, expectedAst));
			}
			
			if (tests.isEmpty()) {
				throw new ParseException(String.format("%s: Failed to find any tests", path), 0);
			}
			
			this.tests = tests;
		}
	}
	
	/**
	 * Gets all .txt files in the corpus tests directory then parses their contents.
	 * 
	 * @param toolsRoot Root of the TLA+ tools directory.
	 * @return A list of all corpus tests.
	 * @throws IOException If a file could not be found or opened or read.
	 * @throws ParseException If a file contains invalid test syntax.
	 */
	public static List<CorpusTestFile> getAndParseCorpusTestFiles(Path toolsRoot) throws IOException, ParseException {
		Path corpusDir = toolsRoot.resolve("test/tla2sany/corpus");
		PathMatcher matcher = FileSystems.getDefault().getPathMatcher("glob:**/*.txt");
		ArrayList<CorpusTestFile> corpus = new ArrayList<CorpusTestFile>();
		for (Path path : Files.walk(corpusDir).filter(matcher::matches).collect(Collectors.toList())) {
			String content = Files.readString(path);
			corpus.add(new CorpusTestFile(path, content));
		}
	
		return corpus;
	}
}
