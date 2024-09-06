package util;

import java.text.ParseException;
import java.util.List;

import util.CorpusParser.CorpusTest;
import util.CorpusParser.CorpusTestFile;

import org.junit.Assert;

/**
 * Functionality to run a parser against a corpus of syntax tests.
 */
public class SyntaxCorpusTestRunner {

	/**
	 * A parser can implement this interface to be subjected to a corpus of
	 * syntax tests.
	 */
	public interface IParserTestTarget {
		
		/**
		 * Performs parsing. Returns null in case of parse error. Returns
		 * standardized AST if successful. Throws ParseException if process
		 * of translating to standardized AST encounters an error.
		 * 
		 * @param input The input to be parsed.
		 * @return Null if parse error, AST if successful.
		 * @throws ParseException If translation to standardized AST fails.
		 */
		public AstNode parse(String input) throws ParseException;
	}
	
	/**
	 * 
	 * @param corpus
	 * @param parser
	 * @throws ParseException
	 */
	public static void run(List<CorpusTestFile> corpus, IParserTestTarget parser) throws ParseException {
		int testCount = 0;
		for (CorpusTestFile corpusTestFile : corpus) {
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

				if (corpusTest.attributes.contains(CorpusTest.Attribute.SKIP)) {
					System.out.println("Skipped.");
					continue;
				}

				testCount++;

				String testSummary = String.format(
						"%s/%s\n%s",
						corpusTestFile.path,
						corpusTest.name,
						corpusTest.tlaplusInput);
				AstNode actual = parser.parse(corpusTest.tlaplusInput);
				if (corpusTest.attributes.contains(CorpusTest.Attribute.ERROR)) {
					System.out.println("Expecting failure.");
					Assert.assertNull(testSummary, actual);
				} else {
					Assert.assertNotNull(testSummary, actual);
					System.out.println(String.format("Expect: %s", corpusTest.expectedAst));
					System.out.println(String.format("Actual: %s", actual));
					corpusTest.expectedAst.testEquality(actual);
				}
			}
		}

		Assert.assertTrue(testCount > 0);
		System.out.println(String.format("Total corpus test count: %d", testCount));
	}
}
