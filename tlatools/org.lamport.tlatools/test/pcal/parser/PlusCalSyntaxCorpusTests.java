package pcal.parser;

import java.util.EnumSet;
import java.util.List;
import java.io.IOException;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.text.ParseException;

import util.AstNode;
import util.SyntaxCorpusFileParser;
import util.SyntaxCorpusFileParser.CorpusTestFile;
import util.SyntaxCorpusRunner;

import pcal.exception.ParseAlgorithmException;
import tlc2.tool.CommonTestCase;
import pcal.AST;

import org.junit.Assert;
import org.junit.BeforeClass;
import org.junit.Test;
import org.junit.Ignore;

/**
 * Runs all corpus tests through the PlusCal parser, checking its syntax parsing.
 */
public class PlusCalSyntaxCorpusTests {

	/**
	 * The parsed corpus test files.
	 */
	private static List<CorpusTestFile> corpus;
	
	/**
	 * Loads all corpus test files.
	 * 
	 * @throws IOException If corpus test file cannot be found or read.
	 * @throws ParseException If corpus test file fails to parse.
	 */
	@BeforeClass
	public static void setup() throws IOException, ParseException {
		Path corpusDir = Paths.get(CommonTestCase.BASE_DIR).resolve("test/pcal/parser/corpus");
		PlusCalSyntaxCorpusTests.corpus = SyntaxCorpusFileParser.getAllUnder(corpusDir);
	}
	
	/**
	 * Implements a parser test target interface for the PlusCal parser.
	 */
	private class PlusCalParserTestTarget implements SyntaxCorpusRunner.IParserTestTarget {

		/**
		 * {@inheritDoc}
		 */
		public AstNode parse(String input) throws ParseException {
			try {
				AST plusCalAst = PlusCalParserOutputTranslator.parse(input);
				return PlusCalParserOutputTranslator.translate(plusCalAst);
			} catch (ParseAlgorithmException e) {
				return null;
			}
		}
	}

	/**
	 * Iterates through each corpus test in each corpus test file, feeds the
	 * raw input into the PlusCal parser, translates the output to the format
	 * expected by the test, then compares this translated output to the
	 * expected parse tree associated with that test.
	 * 
	 * @throws ParseException If translating PlusCal's output fails.
	 */
	@Test
	public void testAll() throws ParseException {
		PlusCalParserTestTarget parser = new PlusCalParserTestTarget();
		SyntaxCorpusRunner.run(corpus, parser);
	}

	/**
	 * After parsing all the corpus tests, ensures that every single node
	 * kind enum has been used - this gives us good confidence that the tests
	 * exercise nearly all valid PlusCal syntax rules.
	 * 
	 * TODO: This will fail until a full PlusCal syntax test corpus has been
	 * created; thus it is marked ignore.
	 */
	@Test
	@Ignore
	public void testAllPlusCalNodesUsed() {
		EnumSet<AstNode.Kind> unused = AstNode.Kind.getUnusedPlusCalNodeKinds();
		System.out.println(String.format("Total unused node kinds: %d", unused.size()));
		System.out.println(unused);
		Assert.assertEquals(0, unused.size());
	}
}
