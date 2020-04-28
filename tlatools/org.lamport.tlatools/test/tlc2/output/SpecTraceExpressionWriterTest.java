package tlc2.output;

import static org.junit.Assert.assertTrue;

import java.io.File;
import java.io.IOException;
import java.util.ArrayList;
import java.util.List;

import org.junit.Before;
import org.junit.Test;

import tla2sany.drivers.FrontEndException;
import tla2sany.drivers.SANY;
import tla2sany.modanalyzer.SpecObj;
import tlc2.model.Formula;
import tlc2.model.MCState;
import tlc2.model.TraceExpressionInformationHolder;
import util.TLAConstants;
import util.TestPrintStream;

/**
 * The genesis for these tests is regressions that were introduced by beautification changes made as part of #393.
 * 
 * As future spec-generation methods are touched, something implementing them should be added below.
 */
public class SpecTraceExpressionWriterTest {
	static private final String TRIVIAL_TWO_STATE_DEADLOCK_PREAMBLE
			= "VARIABLE x, y\n"
					+ "XIncr == (x' = x * 2)\n"
					+ "            /\\ (x < 8)\n"
					+ "            /\\ UNCHANGED y\n"
					+ "YIncr == (y' = x + y)\n"
					+ "            /\\ (y < 15)\n"
					+ "            /\\ UNCHANGED x\n";
	static private final String[] TRIVIAL_TWO_STATE_DEADLOCK_INIT
			= new String[] {
					"TestInit",
					"TestInit == x \\in 1 .. 10 /\\ y \\in 1 .. 10\n"
				};
	static private final String[] TRIVIAL_TWO_STATE_DEADLOCK_NEXT
			= new String[] {
					"TestNext",
					"TestNext == YIncr \\/ XIncr\n"
				};
	static private final String ERROR_STATE_IP
			= "1: <Initial predicate>\n"
					+ "/\\ x = 8\n"
					+ "/\\ y = 7\n";
	static private final String ERROR_STATE_1
			= "2: <YIncr line 8, col 10 to line 10, col 26 of module Bla>\n"
					+ "/\\ x = 8\n"
					+"/\\ y = 15\n";

	
	private SpecTraceExpressionWriter writer;
	private File tlaFile;
	private File cfgFile;
	
	@Before
	public void setUp() throws IOException {
		tlaFile = File.createTempFile("sptewt_", ".tla");
		tlaFile.deleteOnExit();
		cfgFile = File.createTempFile("sptewt_", ".cfg");
		cfgFile.deleteOnExit();
		
		final String tlaFilename = tlaFile.getName();
		final int baseNameLength = tlaFilename.length() - TLAConstants.Files.TLA_EXTENSION.length();
		final String specName = tlaFilename.substring(0, baseNameLength);
		writer = new SpecTraceExpressionWriter();
		writer.addPrimer(specName, "Naturals");
		writer.appendContentToBuffers(TRIVIAL_TWO_STATE_DEADLOCK_PREAMBLE, null);
	}
	
	private void concludeTest() throws FrontEndException, IOException {
		writer.writeFiles(tlaFile, cfgFile);
		
		final SpecObj so = new SpecObj(tlaFile.getAbsolutePath(), null);
		final TestPrintStream printStream = new TestPrintStream();
		
		final int result = SANY.frontEndMain(so, tlaFile.getAbsolutePath(), printStream);
		if (result != 0) {
			throw new FrontEndException("Parsing returned a non-zero success code (" + result + ")");
		}
	}
	
	private List<MCState> generateStatesForDeadlockCondition() { 
		final List<MCState> states = new ArrayList<>();
		
		states.add(MCState.parseState(ERROR_STATE_IP));
		states.add(MCState.parseState(ERROR_STATE_1));

		return states;
	}
	
	@Test
	public void testInitNextWithNoError() throws Exception {
		writer.addInitNextDefinitions(TRIVIAL_TWO_STATE_DEADLOCK_INIT, TRIVIAL_TWO_STATE_DEADLOCK_NEXT,
									  "writerTestInit", "writerTextNext");

		concludeTest();
	}
	
	@Test
	public void testInitNextWithError() throws Exception {
		final List<MCState> trace = generateStatesForDeadlockCondition();
		final StringBuilder tempCFGBuffer = new StringBuilder();
		final StringBuilder[] tlaBuffers
				= SpecTraceExpressionWriter.addInitNextToBuffers(tempCFGBuffer, trace, null, "STEWInit", "STEWNext",
						 										 "STEWAC", TRIVIAL_TWO_STATE_DEADLOCK_NEXT[0], true);
		
		writer.appendContentToBuffers(tlaBuffers[0].toString(), tempCFGBuffer.toString());
		writer.addTraceFunction(trace);
		writer.appendContentToBuffers(tlaBuffers[1].toString(), null);
		
		concludeTest();
	}
	
	@Test
	public void testInitNextWithErrorAndTraceExpression() throws Exception {
		final List<MCState> trace = generateStatesForDeadlockCondition();
		writer.addTraceFunction(trace);

		final List<Formula> expressions = new ArrayList<>();
		expressions.add(new Formula("ENABLED XIncr"));
		expressions.add(new Formula("y # 7"));
		final TraceExpressionInformationHolder[] traceExpressions
						= writer.createAndAddVariablesAndDefinitions(expressions, "writerTestTraceExpressions");
		writer.addInitNext(trace, traceExpressions, "STEWInit", "STEWNext", "STEWAC", TRIVIAL_TWO_STATE_DEADLOCK_NEXT[0]);
		
		concludeTest();
	}

	
	@Test
	public void testMultilineTraceExpression() throws Exception {
		final List<MCState> trace = generateStatesForDeadlockCondition();
		writer.addTraceFunction(trace);

		final List<Formula> expressions = new ArrayList<>();
		expressions.add(new Formula("\n"
				+ "/\\ y # 7\n"
				+ "/\\ \\/ TRUE\n"
				+ " \\* Comment"
				+ "   \\/ FALSE"));
		// Named expression
		final Formula e = new Formula("namedExpression == \n"
				+ "  (* A commend \n over two lines*)"
				+ "  /\\ \\/ TRUE\n"
				+ " \\* Comment"
				+ "     \\/ FALSE");
		assertTrue(e.isNamed());
		expressions.add(e);
		final TraceExpressionInformationHolder[] traceExpressions
						= writer.createAndAddVariablesAndDefinitions(expressions, "writerTestTraceExpressions");
		writer.addInitNext(trace, traceExpressions, "STEWInit", "STEWNext", "STEWAC", TRIVIAL_TWO_STATE_DEADLOCK_NEXT[0]);
		
		concludeTest();
	}
}
