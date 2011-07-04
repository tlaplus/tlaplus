package org.lamport.tla.toolbox.tool.tlc.output.source;

import java.util.HashMap;
import java.util.Iterator;
import java.util.List;
import java.util.Map;

import org.eclipse.jface.text.BadLocationException;
import org.junit.After;
import org.junit.AfterClass;
import org.junit.Assert;
import org.junit.Before;
import org.junit.Test;
import org.lamport.tla.toolbox.tool.tlc.output.data.TLCState;
import org.lamport.tla.toolbox.tool.tlc.output.data.TLCVariable;
import org.lamport.tla.toolbox.tool.tlc.output.data.TLCVariableValue;

public class StateTagBasedTLCOutputIncrementalParserTest {

	private static final int STATE_NUM = 1;
	private static final String LABEL = " <Initial predicate>";
	private static final int EXPECTED_VARS = 41;

	//TODO make multiple values work
	private static final long STATES = 1L;

	private String state;
	private Map<String, String> vars = new HashMap<String,String>();
	
	private TagBasedTLCOutputIncrementalParser parser;
	private DummyListener testListener;
	private static Map<String, Map<String, Long>> results = new HashMap<String, Map<String, Long>>();;

	@Before
	public void setUp() {
		vars.put("pos_f", "defaultInitValue");
		vars.put("foundTokenSpecs", "<<>>");
		vars.put("delim", "defaultInitValue");
		vars.put("leftTok", "defaultInitValue");
		vars.put("left_", "defaultInitValue");
		vars.put("returnVal", "defaultInitValue");
		vars.put("delimLen_", "defaultInitValue");
		vars.put("line", "( 0 :> \";\" @@"
			+ "1 :> \";\" @@"
			+ "2 :> \";\" @@"
			+ "3 :> \";\" @@"
			+ "4 :> \";\" @@"
			+ "5 :> \";\" @@"
			+ "6 :> \";\" @@"
			+ "7 :> \";\" @@"
			+ "8 :> \";\" @@"
			+ "9 :> \";\" @@"
			+ "10 :> \"f\" @@"
			+ "11 :> \"(\" @@"
			+ "12 :> \"b\" @@"
			+ "13 :> \")\" @@"
			+ "14 :> \" \" @@"
			+ "15 :> \";\" @@"
			+ "16 :> \";\" @@"
			+ "17 :> \";\" @@"
			+ "18 :> \";\" @@"
			+ "19 :> \";\" @@"
			+ "20 :> \";\" @@"
			+ "21 :> \";\" @@"
			+ "22 :> \";\" @@"
			+ "23 :> \";\" @@"
			+ "24 :> \";\" )(");
		vars.put("jdelim_", "defaultInitValue");
		vars.put("i", "defaultInitValue");
		vars.put("foundBangToken", "defaultInitValue");
		vars.put("pos", "defaultInitValue");
		vars.put("pc", "\"Lbl_77\"");
		vars.put("ipos_", "defaultInitValue");
		vars.put("pos_fi", "defaultInitValue");
		vars.put("pos_fin", "defaultInitValue");
		vars.put("notDone", "defaultInitValue");
		vars.put("pos_find", "defaultInitValue");
		vars.put("temp1", "defaultInitValue");
		vars.put("temp2", "defaultInitValue");
		vars.put("temp3", "defaultInitValue");
		vars.put("delimLen", "defaultInitValue");
		vars.put("rt", "defaultInitValue");
		vars.put("notLastToken", "FALSE");
		vars.put("ipos", "defaultInitValue");
		vars.put("left", "defaultInitValue");
		vars.put("token", "<<>>");
		vars.put("rt_", "defaultInitValue");
		vars.put("rightTok", "defaultInitValue");
		vars.put("jdelim", "defaultInitValue");
		vars.put("tokIdx", "defaultInitValue");
		vars.put("pos_", "defaultInitValue");
		vars.put("curPos", "11");
		vars.put("delim_", "defaultInitValue");
		vars.put("tokArray", "defaultInitValue");
		vars.put("lastToken", "FALSE");
		vars.put("currentToken", "defaultInitValue");
		vars.put("stack", "<<>>");
		vars.put("tempVar1", "defaultInitValue");
		vars.put("tempVar2", "defaultInitValue");
		vars.put("tempVar3", "defaultInitValue");
		
		StringBuffer buf = new StringBuffer();
		
		// start tag
		buf.append("@!@!@STARTMSG 2217:4 @!@!@\n");
		
		// state num and state label
		buf.append(STATE_NUM + ":" + LABEL + "\n");
		
		// trace expression
		StringBuffer te = new StringBuffer();
		for (Map.Entry<String, String> entry: vars.entrySet()) {
			String key = entry.getKey();
			String value = entry.getValue();
			te.append("/\\ " + key + " = " + value + "\n");
		}
		buf.append(te);
		
		// end tag
		buf.append("@!@!@ENDMSG 2217 @!@!@\n");
		
		this.state = buf.toString();
		
		this.parser = new TagBasedTLCOutputIncrementalParser("foobar", 0, false);
		
		// Register test listener with parser output
		ITLCOutputSource source = parser.getSource();
		testListener = new DummyListener();
		source.addTLCOutputListener(testListener);
	}
	
	@After
	public void tearDown() {
		MethodInvocationCounter.clear();
	}

	@AfterClass
	public static void printStatistics() {
		
		// print invocation statistics
		for (Map.Entry<String, Map<String, Long>> entry: results.entrySet()) {
			StringBuffer buf = new StringBuffer();

			// method name
			String methodName = entry.getKey();
			buf.append("MethodName: ");
			buf.append(methodName);
			buf.append("\n\t");
			
			for (Map.Entry<String, Long> subEntry: entry.getValue().entrySet()) {
				// mode
				String parserMode = subEntry.getKey();
				buf.append("Mode: ");
				buf.append(parserMode);
				
				// invocations
				Long invocations = subEntry.getValue();
				buf.append(" : ");
				buf.append(invocations);
				buf.append("\n\t");
			}
			System.out.println(buf.toString());
		}

	}

	/*
	 *  State by state
	 */
	@Test
	public void parseStateByState()
			throws BadLocationException {

		for(int i = 0; i < STATES; i++) {
			parser.addIncrement(state);
		}
		parser.done();

		collectInvocationStatistics("parseStateByState");
		verifyParserOutput();
	}

	/*
	 * Line by line
	 */
	@Test
	public void parseLineByLine()
			throws BadLocationException {
		final String[] lines = state.split("\n");
		for(int i = 0; i < STATES; i++) {
			for (int j = 0; j < lines.length; j++) {
				parser.addIncrement(lines[j] + "\n");
			}
		}
		parser.done();

		collectInvocationStatistics("parseLineByLine");
		verifyParserOutput();
	}

	/*
	 * Fully
	 */
	@Test
	public void parseAllAtOnce()
			throws BadLocationException {
		String states = "";
		for(int i = 0; i < STATES; i++) {
			states += state + "\n";
		}

		// measure single line performance
		parser.addIncrement(states);
		parser.done();

		collectInvocationStatistics("parseAllAtOnce");
		verifyParserOutput();
	}

	private void collectInvocationStatistics(String parserMode) {
		final Map<String, Long> invocations = MethodInvocationCounter.getInvocations();
		for (Map.Entry<String, Long> entry: invocations.entrySet()) {
			Map<String, Long> value = results.get(entry.getKey());
			if(value == null) {
				value = new HashMap<String, Long>();
				results.put(entry.getKey(), value);
			}
			value.put(parserMode, entry.getValue());
		}
	}

	// verify parser finished successfully recognizing all STATES
	private void verifyParserOutput() {
		// expected, since tests call done()
		Assert.assertTrue(testListener.isDone());
		
		// confirm parser has recognized all states
		final List<TLCState> parsedStates = testListener.getStates();
		Assert.assertEquals(STATES, parsedStates.size());
		
		// check each state individually
		for (Iterator<TLCState> iterator = parsedStates.iterator(); iterator.hasNext();) {
			final TLCState tlcState = iterator.next();
			
			final int stateNumber = tlcState.getStateNumber();
			Assert.assertEquals(STATE_NUM, stateNumber);
			
			final String label = tlcState.getLabel();
			Assert.assertEquals(LABEL, label);
			
			final TLCVariable[] variables = tlcState.getVariables();
			Assert.assertEquals(EXPECTED_VARS, variables.length);
			for (int i = 0; i < variables.length; i++) {
				final TLCVariable tlcVariable = variables[i];
				final String varName = tlcVariable.getName();
				final String expectedValue = vars.get(varName.trim());
				
				TLCVariableValue actualValue = tlcVariable.getValue();
				Assert.assertEquals(expectedValue, actualValue.toString());
			}
		}
		
		Assert.assertEquals(STATES, testListener.getRegions().size());
	}
}
