package tla2sany.parser;

import util.AstNode;
import util.SyntaxCorpusFileParser;
import util.SyntaxCorpusFileParser.CorpusTest;
import util.SyntaxCorpusRunner;
import tla2sany.api.ModuleSyntaxTree;
import tla2sany.api.SANYFrontend;
import tla2sany.api.Resolver;
import tla2sany.api.StringResolver;
import tla2sany.api.Frontend;
import tlc2.tool.CommonTestCase;

import org.junit.Assert;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameter;
import org.junit.runners.Parameterized.Parameters;
import org.junit.Test;

import java.io.IOException;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.text.ParseException;
import java.util.EnumSet;
import java.util.List;

/**
 * Runs all corpus tests through SANY, checking its syntax parsing.
 */
@RunWith(Parameterized.class)
public class TlaPlusSyntaxCorpusTests {

	/**
	 * Loads all corpus test files.
	 *
	 * @throws IOException If corpus test file cannot be found or read.
	 * @throws ParseException If corpus test file fails to parse.
	 */
	@Parameters(name = "{index}: {0}")
	public static List<CorpusTest> getTests() throws IOException, ParseException {
		Path corpusDir = Paths.get(CommonTestCase.BASE_DIR).resolve("test/tla2sany/corpus");
		return SyntaxCorpusFileParser.getAllTestsUnder(corpusDir);
	}

	/**
	 * Implements a parser test target interface for SANY.
	 */
	private class SanyParserTestTarget implements SyntaxCorpusRunner.IParserTestTarget {

		/**
		 * {@inheritDoc}
		 */
		public AstNode parse(String input) throws ParseException {
			Frontend parser = new SANYFrontend();
			final String moduleName = "Test";
			Resolver resolver = new StringResolver(moduleName, input);
			try {
				final ModuleSyntaxTree syntax = parser.processSyntax(moduleName, resolver);
				return TlaPlusParserOutputTranslator.toAst(syntax.root);
			} catch (tla2sany.parser.ParseException | TokenMgrError e) {
				return null;
			}
		}
	}

	@Parameter
	public CorpusTest test;

	/**
	 * Feeds the raw TLA+ test input into SANY, translates SANY's output to
	 * the format expected by the test, then compares this translated output
	 * to the expected parse tree associated with that test.
	 *
	 * @throws ParseException If translating SANY's output fails.
	 */
	@Test
	public void testAll() throws ParseException {
		SanyParserTestTarget parser = new SanyParserTestTarget();
		SyntaxCorpusRunner.run(
			test,
			parser,
			SyntaxCorpusRunner::runAllTests,
			SyntaxCorpusRunner.expectFailures(
				// TODO: analyze Cartesian product parsing logic to figure
				// out whether this should be considered a syntax bug or
				// should actually be kicked up to a semantic error.
				// Ref https://github.com/tlaplus/tlapm/issues/162
				"Cartesian Product as Parameter",

				// https://github.com/tlaplus/tlaplus/issues/430
				"Named Theorem After Submodule (GH tlaplus/tlaplus #430)",

				// https://github.com/tlaplus/tlaplus/issues/487
				"Conjunct Inside Ambiguous Case (GH tlaplus/tlaplus #487)",
				"Unicode Conjunct Inside Ambiguous Case (GH tlaplus/tlaplus #487)",

				// https://github.com/tlaplus/tlaplus/issues/596
				"Decimal No Leading Zero (GH tlaplus/tlaplus #596)",

				// https://github.com/tlaplus/tlaplus/issues/616
				"Invalid Use of LOCAL in LET/IN",
				"Invalid Use of LOCAL in Proof",

				// https://github.com/tlaplus/tlaplus/issues/737
				"Step Expression Requiring Lookahead",

				// https://github.com/tlaplus/tlaplus/issues/802
				"String with Backtick",

				// https://github.com/tlaplus/tlaplus/issues/812
				"String with comment start",

				// https://github.com/tlaplus/tlaplus/issues/884
				"Nonfix Minus (GH tlaplus/tlaplus #GH884)",
				"Nonfix Submodule Excl (GH tlaplus/tlaplus #GH884)",
				"Nonfix Double Exclamation Operator (GH TSTLA #GH97, GH tlaplus/tlaplus #884)",

				// https://github.com/tlaplus/tlaplus/issues/885
				"Label with Subexpression Prefix (GH tlaplus/tlaplus #885)",

				// https://github.com/tlaplus/tlaplus/issues/888
				"Empty Tuple Quantification (GH tlaplus/tlaplus #888)",

				// https://github.com/tlaplus/tlaplus/issues/893
				"Negative Prefix Op on RHS of Infix (GH tlaplus/tlaplus #893)",

				// https://github.com/tlaplus/tlaplus/issues/1021
				"Mistaken Set Filter Tuples Test"
			)
		);
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
