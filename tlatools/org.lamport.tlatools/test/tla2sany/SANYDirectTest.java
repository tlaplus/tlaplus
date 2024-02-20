package tla2sany;

import tla2sany.parser.TLAplusParser;
import tla2sany.st.ParseTree;
import tla2sany.st.TreeNode;

import org.junit.Assert;
import org.junit.Before;
import org.junit.Test;

import java.io.InputStream;
import java.io.ByteArrayInputStream;
import java.io.File;
import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.FileSystems;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.PathMatcher;
import java.nio.file.Paths;
import java.text.ParseException;
import java.util.ArrayList;
import java.util.List;
import java.util.stream.Collectors;
import java.util.regex.*;

public class SANYDirectTest {
	
	private static class CorpusTest {
		public final String name;
		public final String tlaplusInput;
		public final String expectedAst;
		public CorpusTest(String name, String tlaplusInput, String expectedAst) {
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
				tests.add(new CorpusTest(testName, tlaplusInput, expectedAst));
			}
			
			if (tests.isEmpty()) {
				throw new ParseException(String.format("%s: Failed to find any tests", path), 0);
			}
			
			this.tests = tests;
		}
	}
	
	private List<CorpusTestFile> corpus;
	
	@Before
	public void setup() throws IOException, ParseException {
		Path corpusDir = Paths.get("test/tla2sany/corpus");
		PathMatcher matcher = FileSystems.getDefault().getPathMatcher("glob:**/*.txt");
		ArrayList<CorpusTestFile> corpus = new ArrayList<CorpusTestFile>();
			for (Path path : Files.walk(corpusDir).filter(matcher::matches).collect(Collectors.toList())) {
				String content = Files.readString(path);
				corpus.add(new CorpusTestFile(path, content));
			}
		
			this.corpus = corpus;
	}

	@Test
	public void test() {
		for (CorpusTestFile corpusTestFile : this.corpus) {
			for (CorpusTest corpusTest : corpusTestFile.tests) {
				String testSummary = String.format("\n%s\n%s\n%s", corpusTestFile.path, corpusTest.name, corpusTest.tlaplusInput);
				InputStream input = new ByteArrayInputStream(corpusTest.tlaplusInput.getBytes(StandardCharsets.UTF_8));
				ParseTree parser = new TLAplusParser(input, StandardCharsets.UTF_8.name());
				Assert.assertTrue(testSummary, parser.parse());
			}
		}
	}
}
