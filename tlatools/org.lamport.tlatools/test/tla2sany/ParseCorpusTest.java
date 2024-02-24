package tla2sany;

import tla2sany.configuration.Configuration;
import tla2sany.parser.TLAplusParser;
import tla2sany.semantic.AbortException;
import tla2sany.semantic.BuiltInLevel;
import tla2sany.st.ParseTree;
import tla2sany.st.TreeNode;

import org.junit.Assert;
import org.junit.Before;
import org.junit.Test;

import java.io.InputStream;
import java.io.ByteArrayInputStream;
import java.io.IOException;
import java.lang.Character;
import java.nio.charset.StandardCharsets;
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

public class ParseCorpusTest {
	
	private static class ASTNode {
		public final String name;
		public final List<ASTNode> children;
		public final Map<String, ASTNode> fields;
		private final Map<ASTNode, String> fieldNames;
		public ASTNode(String name, List<ASTNode> children, Map<String, ASTNode> fields) {
			this.name = name;
			this.children = children;
			this.fields = fields;
			HashMap<ASTNode, String> fieldNames = new HashMap<ASTNode, String>();
			for (Map.Entry<String, ASTNode> entry : this.fields.entrySet()) {
				fieldNames.put(entry.getValue(), entry.getKey());
			}
			this.fieldNames = fieldNames;
		}
		
		private void toString(StringBuilder sb) {
			sb.append('(');
			sb.append(this.name);
			if (!this.children.isEmpty()) {
				sb.append(' ');
			}
			for (ASTNode child : this.children) {
				if (this.fieldNames.containsKey(child)) {
					sb.append(this.fieldNames.get(child));
					sb.append(": ");
					child.toString(sb);
				} else {
					child.toString(sb);
				}
				sb.append(' ');
			}
			sb.append(')');
		}
		
		public String toString() {
			StringBuilder sb = new StringBuilder();
			this.toString(sb);
			return sb.toString();
		}
	}
	
	private static class ParserState {
		public int i;
		public final String input;
		private final boolean log;
		public ParserState(String input, boolean log) {
			this.i = 0;
			this.input = input;
			this.log = log;
		}
		
		public boolean isEof() {
			return i >= input.length();
		}

		public void consumeWhitespace() {
			while (!this.isEof() && Character.isWhitespace(input.charAt(i))) {
				this.consume();
			}
		}
		
		public boolean matches(char c) {
			return !this.isEof() && input.charAt(i) == c;
		}
		
		public char consume() {
			char c = input.charAt(i);
			if (this.log) {
				System.out.println(c);
			}
			i++;
			return c;
		}
		
		public boolean consumeIf(char c) {
			if (this.matches(c)) {
				this.consume();
				return true;
			} else {
				return false;
			}
		}
		
		public boolean isIdentifierChar() {
			return !this.isEof() && (Character.isLetter(input.charAt(i)) || input.charAt(i) == '_');
		}
		
		public ParseException error(char expected) {
			if (this.isEof()) {
				return new ParseException(String.format("Unexpected EOF; expected %c: %s", expected, input), i);
			} else {
				return new ParseException(String.format("Unexpected char %c; expected %c: %s", input.charAt(i), expected, input), i);
			}
		}
	}
	
	private static ASTNode parseAST(ParserState s) throws ParseException {
		s.consumeWhitespace();
		if (s.consumeIf('(')) {
			s.consumeWhitespace();
			StringBuilder nameBuilder = new StringBuilder();
			while (s.isIdentifierChar()) {
				nameBuilder.append(s.consume());
			}

			ArrayList<ASTNode> children = new ArrayList<ASTNode>();
			HashMap<String, ASTNode> fields = new HashMap<String, ASTNode>();
			s.consumeWhitespace();
			while (!s.matches(')')) {
				if (s.matches('(')) {
					children.add(parseAST(s));
				} else if (s.isIdentifierChar()) {
					StringBuilder fieldNameBuilder = new StringBuilder();
					while (s.isIdentifierChar()) {
						fieldNameBuilder.append(s.consume());
					}
					s.consumeWhitespace();
					if (s.consumeIf(':')) {
						s.consumeWhitespace();
						if (s.matches('(')) {
							ASTNode namedChild = parseAST(s);
							fields.put(fieldNameBuilder.toString(), namedChild);
							children.add(namedChild);
						} else {
							throw s.error('(');
						}
					} else {
						throw s.error(':');
					}
				} else {
					throw s.error('(');
				}
				s.consumeWhitespace();
			}
			
			s.consumeIf(')');
			
			return new ASTNode(nameBuilder.toString(), children, fields);
		} else {
			throw s.error('(');
		}
	}
	
	private static boolean matchesExpectedAST(ASTNode expected, TreeNode actual) {
		System.out.println(expected.toString());
		return true;
	}
	
	private static class CorpusTest {
		public final String name;
		public final String tlaplusInput;
		public final ASTNode expectedAst;
		public CorpusTest(String name, String tlaplusInput, ASTNode expectedAst) {
			this.name = name;
			this.tlaplusInput = tlaplusInput;
			this.expectedAst = expectedAst;
		}
	}
	
	private static class CorpusTestFile {
		private static final Pattern headerRegex = Pattern.compile("^===+\\|\\|\\|\r?\n(?<testName>[^\r\n]*)\r?\n===+\\|\\|\\|\r?\n", Pattern.MULTILINE);
		private static final Pattern separatorRegex = Pattern.compile("^---+\\|\\|\\|\r?\n", Pattern.MULTILINE);
		public final Path path;
		public final List<CorpusTest> tests;
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
				tests.add(new CorpusTest(testName, tlaplusInput, parseAST(new ParserState(expectedAst, false))));
			}
			
			if (tests.isEmpty()) {
				throw new ParseException(String.format("%s: Failed to find any tests", path), 0);
			}
			
			this.tests = tests;
		}
	}
	
	private List<CorpusTestFile> corpus;
	
	@Before
	public void setup() throws IOException, ParseException, AbortException {
		Path corpusDir = Paths.get("test/tla2sany/corpus");
		PathMatcher matcher = FileSystems.getDefault().getPathMatcher("glob:**/*.txt");
		ArrayList<CorpusTestFile> corpus = new ArrayList<CorpusTestFile>();
			for (Path path : Files.walk(corpusDir).filter(matcher::matches).collect(Collectors.toList())) {
				String content = Files.readString(path);
				corpus.add(new CorpusTestFile(path, content));
			}
		
			this.corpus = corpus;

		Configuration.load(null);
		BuiltInLevel.load();
	}

	@Test
	public void test() {
		for (CorpusTestFile corpusTestFile : this.corpus) {
			for (CorpusTest corpusTest : corpusTestFile.tests) {
				String testSummary = String.format("\n%s\n%s\n%s", corpusTestFile.path, corpusTest.name, corpusTest.tlaplusInput);
				InputStream input = new ByteArrayInputStream(corpusTest.tlaplusInput.getBytes(StandardCharsets.UTF_8));
				ParseTree parser = new TLAplusParser(input, StandardCharsets.UTF_8.name());
				Assert.assertTrue(testSummary, parser.parse());
				Assert.assertTrue(matchesExpectedAST(corpusTest.expectedAst, parser.rootNode()));
			}
		}
	}
}
