package tla2sany.parser;

import util.AstNode;
import util.SyntaxCorpusFileParser;
import util.SyntaxCorpusFileParser.CorpusTestFile;
import util.SyntaxCorpusRunner;
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
public class TlaPlusSyntaxCorpusTests {
	
	/**
	 * The parsed corpus test files.
	 */
	private static List<CorpusTestFile> corpus;
	
	/**
	 * Loads all corpus test files and performs static initialization of SANY.
	 * 
	 * @throws IOException If corpus test file cannot be found or read.
	 * @throws ParseException If corpus test file fails to parse.
	 */
	@BeforeClass
	public static void setup() throws IOException, ParseException {
		// Load corpus test files.
		Path corpusDir = Paths.get(CommonTestCase.BASE_DIR).resolve("test/tla2sany/corpus");
		TlaPlusSyntaxCorpusTests.corpus = SyntaxCorpusFileParser.getAllUnder(corpusDir);
	}
	
	/**
	 * Implements a parser test target interface for SANY.
	 */
	private class SanyParserTestTarget implements SyntaxCorpusRunner.IParserTestTarget {

		/**
		 * {@inheritDoc}
		 */
		public AstNode parse(String input) throws ParseException {
			byte[] inputBytes = input.getBytes(StandardCharsets.UTF_8);
			InputStream inputStream = new ByteArrayInputStream(inputBytes);
			TLAplusParser parser = new TLAplusParser(inputStream, StandardCharsets.UTF_8.name());
			return parser.parse() ? TlaPlusParserOutputTranslator.toAst(parser) : null;
		}
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
	public void testAll() throws ParseException {
		SanyParserTestTarget parser = new SanyParserTestTarget();
		SyntaxCorpusRunner.run(
			corpus,
			parser,
			SyntaxCorpusRunner.skipSpecificTests(
				// TODO: fix syntax tree translation functions for these.
				"Number Set Definitions"
			),
			SyntaxCorpusRunner.expectFailures(
				// TODO: analyze Cartesian product parsing logic to figure
				// out whether this should be considered a syntax bug or
				// should actually be kicked up to a semantic error.
				// Ref https://github.com/tlaplus/tlapm/issues/162
				"Cartesian Product as Parameter"
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
