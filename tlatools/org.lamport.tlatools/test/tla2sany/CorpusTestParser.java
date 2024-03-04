package tla2sany;

import java.io.IOException;
import java.nio.file.FileSystems;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.PathMatcher;
import java.nio.file.Paths;
import java.text.ParseException;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.stream.Collectors;
import java.util.regex.*;

/**
 * Handles reading and parsing the corpus test files.
 */
public class CorpusTestParser {

	/**
	 * Mutable class tracking parser state to avoid string copies.
	 */
	private static class ParserState {
		/**
		 * The parser's current index in the string.
		 */
		public int i;
		
		/**
		 * The unparsed input string.
		 */
		public final String input;
		
		/**
		 * Whether to log each character consumed.
		 */
		private final boolean log;
		
		/**
		 * Initializes the parser state with the input string.
		 * 
		 * @param input The string to parse.
		 * @param log Whether to log each consumed char.
		 */
		public ParserState(String input, boolean log) {
			this.i = 0;
			this.input = input;
			this.log = log;
		}
		
		/**
		 * Whether the input has been fully consumed.
		 * 
		 * @return True if there is no input remaining.
		 */
		public boolean isEof() {
			return i >= input.length();
		}

		/**
		 * Consumes input until encountering a non-whitespace char.
		 */
		public void consumeWhitespace() {
			while (!this.isEof() && Character.isWhitespace(input.charAt(i))) {
				this.consume();
			}
		}
		
		/**
		 * Whether the current char is the given char.
		 * 
		 * @param c The char to check.
		 * @return True if not EOF and char matches.
		 */
		public boolean matches(char c) {
			return !this.isEof() && input.charAt(i) == c;
		}
		
		/**
		 * Consumes the current char without any checks. Possibly logs this act.
		 * 
		 * @return The consumed char.
		 */
		private char consume() {
			char c = input.charAt(i);
			if (this.log) {
				System.out.println(c);
			}
			i++;
			return c;
		}
		
		/**
		 * Consume the current char if it is as expected.
		 * 
		 * @param c The expected char.
		 * @return Whether the current char was consumed.
		 */
		public boolean consumeIf(char c) {
			if (this.matches(c)) {
				this.consume();
				return true;
			} else {
				return false;
			}
		}
		
		/**
		 * Whether the current char is an identifier char.
		 * 
		 * @return True if it is an identifier char.
		 */
		public boolean isIdentifierChar() {
			return !this.isEof() && (Character.isLetter(input.charAt(i)) || input.charAt(i) == '_');
		}
		
		/**
		 * Consumes the upcoming identifier then returns it as a string.
		 * 
		 * @return The consumed identifier.
		 */
		public String consumeIdentifier() {
			StringBuilder sb = new StringBuilder();
			while (this.isIdentifierChar()) {
				sb.append(this.consume());
			}
			
			return sb.toString();
		}
		
		/**
		 * Constructs an appropriate parse exception for the current position.
		 * 
		 * @param expected The char or element that was expected instead.
		 * @return A relatively informative parse exception to throw.
		 */
		public ParseException error(String expected) {
			if (this.isEof()) {
				return new ParseException(String.format("Unexpected EOF; expected %s: %s", expected, input), i);
			} else {
				return new ParseException(String.format("Unexpected char %c; expected %s at index %d: %s", input.charAt(i), expected, i, input), i);
			}
		}
	}
	
	/**
	 * Performs the actual parsing of the AST DSL by mutating a parser state
	 * in place. Thankfully S-expressions are easy to parse in a single
	 * recursive function.
	 * 
	 * @param s Parser state holding the input string and current index.
	 * @return Root node of the AST subtree at this point in the input.
	 * @throws ParseException If invalid S-expression syntax is encountered.
	 */
	private static AstNode parseAst(ParserState s) throws ParseException {
		s.consumeWhitespace();
		// Looking for ex. (source_file ...)
		if (s.consumeIf('(')) {
			s.consumeWhitespace();
			if (!s.isIdentifierChar()) {
				throw s.error("Identifier Char");
			}
			AstNode.Kind kind = AstNode.Kind.fromString(s.consumeIdentifier());
			List<AstNode> children = new ArrayList<AstNode>();
			Map<String, AstNode> fields = new HashMap<String, AstNode>();
			s.consumeWhitespace();
			while (!s.isEof() && !s.matches(')')) {
				if (s.matches('(')) {
					// Found unnamed child ex. (source_file (module ... ))
					children.add(parseAst(s));
				} else if (s.isIdentifierChar()) {
					// Found named field child ex. (bound_op name: (...) ...)
					String fieldName = s.consumeIdentifier();
					s.consumeWhitespace();
					if (s.consumeIf(':')) {
						s.consumeWhitespace();
						if (s.matches('(')) {
							// Recurse to get actual named child
							AstNode namedChild = parseAst(s);
							fields.put(fieldName, namedChild);
							children.add(namedChild);
						} else {
							throw s.error("(");
						}
					} else {
						throw s.error(":");
					}
				} else {
					throw s.error("(");
				}
				s.consumeWhitespace();
			}
			
			if (!s.consumeIf(')')) {
				throw s.error(")");
			}
			
			return new AstNode(kind, children, fields);
		} else {
			throw s.error("(");
		}
	}
	
	/**
	 * Parse the given S-expression string into an abstract syntax tree.
	 * 
	 * @param input The S-expression in string form.
	 * @return Root node of the AST.
	 * @throws ParseException If invalid S-expression syntax is encountered.
	 */
	private static AstNode parseAst(String input) throws ParseException {
		return parseAst(new ParserState(input, false));
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
	 * @return A list of all corpus tests.
	 * @throws IOException If a file could not be found or opened or read.
	 * @throws ParseException If a file contains invalid test syntax.
	 */
	public static List<CorpusTestFile> getAndParseCorpusTestFiles() throws IOException, ParseException {
		Path corpusDir = Paths.get("test/tla2sany/corpus");
		PathMatcher matcher = FileSystems.getDefault().getPathMatcher("glob:**/*.txt");
		ArrayList<CorpusTestFile> corpus = new ArrayList<CorpusTestFile>();
		for (Path path : Files.walk(corpusDir).filter(matcher::matches).collect(Collectors.toList())) {
			String content = Files.readString(path);
			corpus.add(new CorpusTestFile(path, content));
		}
	
		return corpus;
	}
}
