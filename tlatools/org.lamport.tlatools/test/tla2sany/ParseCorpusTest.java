package tla2sany;

import tla2sany.CorpusParser.CorpusTestFile;
import tla2sany.CorpusParser.CorpusTest;
import tla2sany.configuration.Configuration;
import tla2sany.parser.TLAplusParser;
import tla2sany.semantic.AbortException;
import tla2sany.semantic.BuiltInLevel;

import org.junit.Assert;
import org.junit.Before;
import org.junit.Test;

import java.io.InputStream;
import java.io.ByteArrayInputStream;
import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.text.ParseException;
import java.util.List;

public class ParseCorpusTest {
	
	private List<CorpusTestFile> corpus;
	
	@Before
	public void setup() throws IOException, ParseException, AbortException {
		Path toolsRoot = Paths.get(System.getProperty("basedir"));
		this.corpus = CorpusParser.getAndParseCorpusTestFiles(toolsRoot);
		Configuration.load(null);
		BuiltInLevel.load();
	}

	@Test
	public void test() throws ParseException {
		int testCount = 0;
		for (CorpusTestFile corpusTestFile : this.corpus) {
			System.out.println(corpusTestFile.path);
			for (CorpusTest corpusTest : corpusTestFile.tests) {
				// keeping this here because it is useful to debug why a specific test fails
				if (!corpusTest.name.equals("Nonfix Prefix Operators")) {
					//continue;
				}
				System.out.println(corpusTest.name);
				String testSummary = String.format("\n%s\n%s\n%s", corpusTestFile.path, corpusTest.name, corpusTest.tlaplusInput);
				InputStream input = new ByteArrayInputStream(corpusTest.tlaplusInput.getBytes(StandardCharsets.UTF_8));
				TLAplusParser parser = new TLAplusParser(input, StandardCharsets.UTF_8.name());
				Assert.assertTrue(testSummary, parser.parse());
				System.out.println(corpusTest.expectedAst);
				AstNode actual = SanyTranslator.toAst(parser);
				System.out.println(actual);
				corpusTest.expectedAst.testEquality(actual);
				testCount++;
			}
		}
		System.out.println(String.format("Total corpus test count: %d", testCount));
		List<AstNode.Kind> unused = AstNode.Kind.getUnused();
		System.out.println(String.format("Total unused node kinds: %d", unused.size()));
		System.out.println(AstNode.Kind.getUnused());
	}
}
