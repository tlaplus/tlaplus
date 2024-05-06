package tla2sany;

import util.AstNode;
import util.CorpusParser;
import util.CorpusParser.CorpusTestFile;
import util.CorpusParser.CorpusTest;
import tla2sany.configuration.Configuration;
import tla2sany.parser.TLAplusParser;
import tla2sany.semantic.AbortException;
import tla2sany.semantic.BuiltInLevel;
import tlc2.tool.CommonTestCase;

import org.junit.Assert;
import org.junit.BeforeClass;
import org.junit.Test;

import java.io.InputStream;
import java.io.ByteArrayInputStream;
import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.text.ParseException;
import java.util.EnumSet;
import java.util.List;

/**
 * Runs all corpus tests through SANY, checking its syntax parsing.
 */
public class ParseCorpusTest {
	
	/**
	 * The parsed corpus test files.
	 */
	private static List<CorpusTestFile> corpus;
	
	/**
	 * Loads all corpus test files and performs static initialization of SANY.
	 * 
	 * @throws IOException If corpus test file cannot be found or read.
	 * @throws ParseException If corpus test file fails to parse.
	 * @throws AbortException If SANY static initialization fails.
	 */
	@BeforeClass
	public static void setup() throws IOException, ParseException, AbortException {
		// Load corpus test files.
		Path corpusDir = Paths.get(CommonTestCase.BASE_DIR).resolve("test/tla2sany/corpus");
		ParseCorpusTest.corpus = CorpusParser.getAndParseCorpusTestFiles(corpusDir);
		
		// Static initialization of SANY.
		Configuration.load(null);
		BuiltInLevel.load();
	}
	
	/**
	 * Iterates through each corpus test in each corpus test file, feeds the
	 * raw TLA+ input into SANY, translates SANY's output to the format
	 * expected by the test, then compares this translated output to the
	 * expected parse tree associated with that test.
	 * 
	 * @throws ParseException If translating SANY's output fails.
	 */
	@Test
	public void testEntireTlaPlusSyntaxParserCorpus() throws ParseException {
		int testCount = 0;
		for (CorpusTestFile corpusTestFile : ParseCorpusTest.corpus) {
			System.out.println(corpusTestFile.path);
			for (CorpusTest corpusTest : corpusTestFile.tests) {
				// Sometimes you just want to run a single test so you can
				// trace it in the debugger; to do that, put its name in the
				// if-statement then uncomment the continue statement.
				// Keeping this here because it was very useful during
				// development of the translate function.
				if (!corpusTest.name.equals("Subexpression Tree Navigation")) {
					//continue;
				}
				System.out.println(corpusTest.name);
				byte[] inputBytes = corpusTest.tlaplusInput.getBytes(StandardCharsets.UTF_8);
				InputStream inputStream = new ByteArrayInputStream(inputBytes);
				TLAplusParser parser = new TLAplusParser(inputStream, StandardCharsets.UTF_8.name());
				String testSummary = String.format(
						"%s/%s\n%s",
						corpusTestFile.path,
						corpusTest.name,
						corpusTest.tlaplusInput);
				Assert.assertTrue(testSummary, parser.parse());
				System.out.println(String.format("Expect: %s", corpusTest.expectedAst));
				AstNode actual = SanyTranslator.toAst(parser);
				System.out.println(String.format("Actual: %s", actual));
				corpusTest.expectedAst.testEquality(actual);
				testCount++;
			}
		}
		Assert.assertTrue(testCount > 0);
		System.out.println(String.format("Total corpus test count: %d", testCount));
	}

	/**
	 * After parsing all the corpus tests, ensures that every single node
	 * kind enum has been used - this gives us good confidence that the tests
	 * exercise nearly all valid TLA+ syntax rules.
	 */
	@Test
	public void testAllTlaPlusNodesUsed() {
		EnumSet<AstNode.Kind> unused = AstNode.Kind.getUnusedTlaPlusNodeKinds();
		System.out.println(String.format("Total unused node kinds: %d", unused.size()));
		System.out.println(unused);
		Assert.assertEquals(0, unused.size());
	}
}
