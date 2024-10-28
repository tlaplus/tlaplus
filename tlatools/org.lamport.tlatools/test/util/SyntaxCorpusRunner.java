package util;

import java.text.ParseException;
import java.util.Arrays;
import java.util.List;
import java.util.function.Function;

import util.SyntaxCorpusFileParser.CorpusTest;
import util.SyntaxCorpusFileParser.CorpusTestFile;

import org.junit.Assert;

/**
 * Functionality to run a parser against a corpus of syntax tests.
 */
public class SyntaxCorpusRunner {

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
	 * A default predicate indicating to run all tests.
	 *
	 * @param test The test to decide whether to run or not.
	 * @return Always true, as all tests should be run.
	 */
	public static boolean runAllTests(CorpusTest test) {
		return true;
	}

	/**
	 * A helper function to construct a predicate that will only run tests
	 * whose names are contained in the given list of names. Useful when
	 * debugging syntax tree translation code.
	 *
	 * @param testNames The names of the tests to run.
	 * @return A predicate only returning true for the given test names.
	 */
	public static Function<CorpusTest, Boolean> runSpecificTests(String... testNames) {
		return test -> Arrays
			.stream(testNames)
			.anyMatch(name -> test.name.equalsIgnoreCase(name));
	}

	/**
	 * A helper function to construct a predicate that will run all tests
	 * *except* those whose names are contained in the given list of names.
	 * Useful when something is going wrong with the translation function.
	 *
	 * @param testNames The names of the tests to skip.
	 * @return A predicate only returning false for the given test names.
	 */
	public static Function<CorpusTest, Boolean> skipSpecificTests(String... testNames) {
		return test -> !Arrays
			.stream(testNames)
			.anyMatch(name -> test.name.equalsIgnoreCase(name));
	}

	/**
	 * A default predicate indicating no syntax test failures are expected.
	 *
	 * @param test The test for which a failure can be expected or not.
	 * @return Always false, as all tests are expected to pass.
	 */
	public static boolean expectNoFailures(CorpusTest test) {
		return false;
	}

	/**
	 * A helper function to construct a predicate asserting that a test will
	 * fail if its name is in the given list of failing test names.
	 *
	 * @param failingTestNames The names of tests that are expected to fail.
	 * @return A predicate only returning true for the given test names.
	 */
	public static Function<CorpusTest, Boolean> expectFailures(String... failingTestNames) {
		return test -> Arrays
			.stream(failingTestNames)
			.anyMatch(name -> test.name.equalsIgnoreCase(name));
	}

	/**
	 * Subjects the given parser to the given corpus of syntax tests,
	 * filtering both the tests and their results according to some
	 * predicates.
	 *
	 * @param corpus The corpus of syntax tests.
	 * @param parser The parser test target.
	 * @param shouldRun Predicate determining whether to run a test.
	 * @param expectFailure Predicate identifying known-failing tests.
	 * @throws ParseException
	 */
	public static void run(
		List<CorpusTestFile> corpus,
		IParserTestTarget parser,
		Function<CorpusTest, Boolean> shouldRun,
		Function<CorpusTest, Boolean> expectFailure
	) throws ParseException {
		int testCount = 0;
		for (CorpusTestFile corpusTestFile : corpus) {
			System.out.println(corpusTestFile.path);
			for (CorpusTest corpusTest : corpusTestFile.tests) {
				if (!shouldRun.apply(corpusTest)) {
					continue;
				}

				System.out.println(corpusTest.name);

				if (corpusTest.attributes.contains(CorpusTest.Attribute.SKIP)) {
					System.out.println("Skipped.");
					continue;
				}

				testCount++;

				boolean isErrorTest = corpusTest.attributes.contains(CorpusTest.Attribute.ERROR);
				String testSummary = String.format(
						"%s/%s\nExpecting: %s\n%s",
						corpusTestFile.path,
						corpusTest.name,
						isErrorTest ? "Error" : "Success",
						corpusTest.tlaplusInput);

				if (expectFailure.apply(corpusTest)) {
					System.out.println("Expecting failure.");
					try {
						AstNode actual = parser.parse(corpusTest.tlaplusInput);
						Assert.assertNotEquals(testSummary, isErrorTest, null == actual);
					} catch (ParseException e) {
						Assert.assertFalse(testSummary, isErrorTest);
					}
				} else {
					if (isErrorTest) {
						System.out.println("Expecting parser rejection.");
						AstNode actual = parser.parse(corpusTest.tlaplusInput);
						Assert.assertNull(testSummary, actual);
					} else {
						AstNode actual = parser.parse(corpusTest.tlaplusInput);
						Assert.assertNotNull(testSummary, actual);
						System.out.println(String.format("Expect: %s", corpusTest.expectedAst));
						System.out.println(String.format("Actual: %s", actual));
						corpusTest.expectedAst.testEquality(actual);
					}
				}
			}
		}

		Assert.assertTrue(testCount > 0);
		System.out.println(String.format("Total corpus test count: %d", testCount));
	}
}
