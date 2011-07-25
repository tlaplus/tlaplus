package org.lamport.tla.toolbox.tool.tlc.output.source;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.net.URL;
import java.util.ArrayList;
import java.util.List;

import junit.framework.Assert;

import org.eclipse.jface.text.BadLocationException;
import org.eclipse.jface.text.ITypedRegion;
import org.junit.Before;
import org.junit.Test;

import tlc2.output.MP;

public class TagBasedTLCOutputIncrementalParserTest {

	private List<String> input = new ArrayList<String>();
	
	@Before
	public void setUp() throws Exception {

		URL url = this.getClass().getClassLoader().getResource("files/ShortFindOp.out");
        InputStream inputStream = url.openConnection().getInputStream();
		BufferedReader reader = new BufferedReader(new InputStreamReader(inputStream));
		
		// Read the input fully here
		String line;
		while((line = reader.readLine()) != null) {
			input.add(line);
		}
		
		reader.close();
	}
	
	@Test
	public void testNoNewline() throws IOException {
		TagBasedTLCOutputIncrementalParser parser = new TagBasedTLCOutputIncrementalParser("", 0, false);

		
		// read in test input and feed it to the parser
		try {
			parser.addIncrement("@!@!@STARTMSG 2262:0 @!@!@");
		} catch (BadLocationException e) {
			return;
		}
		Assert.fail("Parser is expected to throw BLE on input without newline");
	}
	
	@Test
	public void testAddIncrementTLCHeader() throws IOException {
		TagBasedTLCOutputIncrementalParser parser = new TagBasedTLCOutputIncrementalParser("", 0, false);

		
		// read in test input and feed it to the parser
		try {
			parser.addIncrement("@!@!@STARTMSG 2262:0 @!@!@\n");
			parser.addIncrement("TLC2 Version 2.03 of 10 April 2011\n");
			parser.addIncrement("@!@!@ENDMSG 2262 @!@!@\n");
		} catch (BadLocationException e) {
			Assert.fail(e.getMessage());
		}
		
		parser.done();
	}

	@Test
	public void testAddIncrementState() throws IOException {
		TagBasedTLCOutputIncrementalParser parser = new TagBasedTLCOutputIncrementalParser("", 0, false);
		
		// read in test input and feed it to the parser
		try {
			parser.addIncrement("@!@!@STARTMSG 2217:4 @!@!@\n");
			parser.addIncrement("1: <Initial predicate>\n");
			parser.addIncrement("/\\ pos_f = defaultInitValue\n");
			parser.addIncrement("/\\ foundTokenSpecs = <<>>\n");
			parser.addIncrement("/\\ delim = defaultInitValue\n");
			parser.addIncrement("/\\ leftTok = defaultInitValue\n");
			parser.addIncrement("/\\ left_ = defaultInitValue\n");
			parser.addIncrement("/\\ returnVal = defaultInitValue\n");
			parser.addIncrement("/\\ delimLen_ = defaultInitValue\n");
			parser.addIncrement("/\\ line = ( 0 :> \";\" @@\n");
			parser.addIncrement("1 :> \";\" @@\n");
			parser.addIncrement("2 :> \";\" @@\n");
			parser.addIncrement("3 :> \";\" @@\n");
			parser.addIncrement("4 :> \";\" @@\n");
			parser.addIncrement("5 :> \";\" @@\n");
			parser.addIncrement("6 :> \";\" @@\n");
			parser.addIncrement("7 :> \";\" @@\n");
			parser.addIncrement("8 :> \";\" @@\n");
			parser.addIncrement("9 :> \";\" @@\n");
			parser.addIncrement("10 :> \"f\" @@\n");
			parser.addIncrement("11 :> \"(\" @@\n");
			parser.addIncrement("12 :> \"b\" @@\n");
			parser.addIncrement("13 :> \")\" @@\n");
			parser.addIncrement("14 :> \" \" @@\n");
			parser.addIncrement("15 :> \";\" @@\n");
			parser.addIncrement("16 :> \";\" @@\n");
			parser.addIncrement("17 :> \";\" @@\n");
			parser.addIncrement("18 :> \";\" @@\n");
			parser.addIncrement("19 :> \";\" @@\n");
			parser.addIncrement("20 :> \";\" @@\n");
			parser.addIncrement("21 :> \";\" @@\n");
			parser.addIncrement("22 :> \";\" @@\n");
			parser.addIncrement("23 :> \";\" @@\n");
			parser.addIncrement("24 :> \";\" )(\n");
			parser.addIncrement("/\\ jdelim_ = defaultInitValue\n");
			parser.addIncrement("/\\ i = defaultInitValue\n");
			parser.addIncrement("/\\ foundBangToken = defaultInitValue\n");
			parser.addIncrement("/\\ pos = defaultInitValue\n");
			parser.addIncrement("/\\ pc = \"Lbl_77\"\n");
			parser.addIncrement("/\\ ipos_ = defaultInitValue\n");
			parser.addIncrement("/\\ pos_fi = defaultInitValue\n");
			parser.addIncrement("/\\ pos_fin = defaultInitValue\n");
			parser.addIncrement("/\\ notDone = defaultInitValue\n");
			parser.addIncrement("/\\ pos_find = defaultInitValue\n");
			parser.addIncrement("/\\ temp1 = defaultInitValue\n");
			parser.addIncrement("/\\ temp2 = defaultInitValue\n");
			parser.addIncrement("/\\ temp3 = defaultInitValue\n");
			parser.addIncrement("/\\ delimLen = defaultInitValue\n");
			parser.addIncrement("/\\ rt = defaultInitValue\n");
			parser.addIncrement("/\\ notLastToken = FALSE\n");
			parser.addIncrement("/\\ ipos = defaultInitValue\n");
			parser.addIncrement("/\\ left = defaultInitValue\n");
			parser.addIncrement("/\\ token = <<>>\n");
			parser.addIncrement("/\\ rt_ = defaultInitValue\n");
			parser.addIncrement("/\\ rightTok = defaultInitValue\n");
			parser.addIncrement("/\\ jdelim = defaultInitValue\n");
			parser.addIncrement("/\\ tokIdx = defaultInitValue\n");
			parser.addIncrement("/\\ pos_ = defaultInitValue\n");
			parser.addIncrement("/\\ curPos = 11\n");
			parser.addIncrement("/\\ delim_ = defaultInitValue\n");
			parser.addIncrement("/\\ tokArray = defaultInitValue\n");
			parser.addIncrement("/\\ lastToken = FALSE\n");
			parser.addIncrement("/\\ currentToken = defaultInitValue\n");
			parser.addIncrement("/\\ stack = <<>>\n");
			parser.addIncrement("/\\ tempVar1 = defaultInitValue\n");
			parser.addIncrement("/\\ tempVar2 = defaultInitValue\n");
			parser.addIncrement("/\\ tempVar3 = defaultInitValue\n");
			parser.addIncrement("@!@!@ENDMSG 2217 @!@!@\n");
		} catch (BadLocationException e) {
			Assert.fail(e.getMessage());
		}
		
		parser.done();
	}

	@Test
	public void testAddPrintTStmt() throws IOException {
		TagBasedTLCOutputIncrementalParser parser = new TagBasedTLCOutputIncrementalParser("", 0, false);
		// Register test listener with parser output

		ITLCOutputSource source = parser.getSource();
		DummyListener testListener = new DummyListener();
		source.addTLCOutputListener(testListener);
		
		// read in test input and feed it to the parser
		try {
			parser.addIncrement("UC\n");
			parser.addIncrement("@!@!@STARTMSG 2189:0 @!@!@\n");
			parser.addIncrement("C\n");
			parser.addIncrement("@!@!@ENDMSG 2189 @!@!@\n");
		} catch (BadLocationException e) {
			Assert.fail(e.getMessage());
		}
		
		parser.done();

		// expected, since tests call done()
		Assert.assertTrue(testListener.isDone());

		// all regions detected?
		final List<ITypedRegion> regions = testListener.getRegions();
		Assert.assertNotNull(regions);
		Assert.assertEquals("Not all regions detected", 2, regions.size());

		// detected what kind of region?
		int none = 0;
		int out = 0;
		for (ITypedRegion region : regions) {
			if (region instanceof TLCRegion) {
				TLCRegion tlcRegion = (TLCRegion) region;
				switch (tlcRegion.getSeverity()) {
				case MP.NONE:
					none++;
				}
			} else {
				out++;
			}
		}
		Assert.assertEquals("Not all TLCRegions detected", 1, none);
		Assert.assertEquals("Not all non-TLCRegions detected", 1, out);
	}
	
	@Test
	public void testAddPrintTStmtFull() throws IOException {
		TagBasedTLCOutputIncrementalParser parser = new TagBasedTLCOutputIncrementalParser("", 0, false);
		// Register test listener with parser output

		ITLCOutputSource source = parser.getSource();
		DummyListener testListener = new DummyListener();
		source.addTLCOutputListener(testListener);

		// read in test input and feed it to the parser
		try {
			parser.addIncrement("@!@!@STARTMSG 2262:0 @!@!@\n");
			parser.addIncrement("TLC2 Version 2.03 of 10 March 2011\n");
			parser.addIncrement("@!@!@ENDMSG 2262 @!@!@\n");
			parser.addIncrement("@!@!@STARTMSG 2187:0 @!@!@\n");
			parser.addIncrement("Running in Model-Checking mode.\n");
			parser.addIncrement("@!@!@ENDMSG 2187 @!@!@\n");
			parser.addIncrement("@!@!@STARTMSG 2220:0 @!@!@\n");
			parser.addIncrement("Starting SANY...\n");
			parser.addIncrement("@!@!@ENDMSG 2220 @!@!@\n");
			parser.addIncrement("Parsing file MC.tla\n");
			parser.addIncrement("Parsing file Test.tla\n");
			parser.addIncrement("Parsing file /toolbox/plugins/org.lamport.tla.toolbox_1.0.0/StandardModules/TLC.tla\n");
			parser.addIncrement("Parsing file /tla/toolbox/plugins/org.lamport.tla.toolbox_1.0.0/StandardModules/Naturals.tla\n");
			parser.addIncrement("Parsing file /tla/toolbox/plugins/org.lamport.tla.toolbox_1.0.0/StandardModules/Sequences.tla\n");
			parser.addIncrement("Semantic processing of module Naturals\n");
			parser.addIncrement("Semantic processing of module Sequences\n");
			parser.addIncrement("Semantic processing of module TLC\n");
			parser.addIncrement("Semantic processing of module Test\n");
			parser.addIncrement("Semantic processing of module MC\n");
			parser.addIncrement("@!@!@STARTMSG 2219:0 @!@!@\n");
			parser.addIncrement("SANY finished.\n");
			parser.addIncrement("@!@!@ENDMSG 2219 @!@!@\n");

			parser.addIncrement("@!@!@STARTMSG 2185:0 @!@!@\n");
			parser.addIncrement("S\n");
			parser.addIncrement("@!@!@ENDMSG 2185 @!@!@\n");

			parser.addIncrement("SomeUserContent\n");
			parser.addIncrement("<<\"$!@$!@$!@$!@$!\", 999>>\n");

			parser.addIncrement("@!@!@STARTMSG 2189:0 @!@!@\n");
			parser.addIncrement("C\n");
			parser.addIncrement("@!@!@ENDMSG 2189 @!@!@\n");

			parser.addIncrement("@!@!@STARTMSG 2190:0 @!@!@\n");
			parser.addIncrement("Finished computing initial states: 0 distinct states generated.\n");
			parser.addIncrement("@!@!@ENDMSG 2190 @!@!@\n");
			parser.addIncrement("@!@!@STARTMSG 2193:0 @!@!@\n");
			parser.addIncrement("Model checking completed. No error has been found.\n");
			parser.addIncrement("  Estimates of the probability that TLC did not check all reachable states\n");
			parser.addIncrement("  because two distinct states had the same fingerprint:\n");
			parser.addIncrement("  calculated (optimistic):  val = 0\n");
			parser.addIncrement("  based on the actual fingerprints:  val = 1.1E-19\n");
			parser.addIncrement("@!@!@ENDMSG 2193 @!@!@\n");
			parser.addIncrement("@!@!@STARTMSG 2200:0 @!@!@\n");
			parser.addIncrement("Progress(0) at 2011-07-21 10:14:49: 0 states generated, 0 distinct states found, 0 states left on queue.\n");
			parser.addIncrement("@!@!@ENDMSG 2200 @!@!@\n");
			parser.addIncrement("@!@!@STARTMSG 2199:0 @!@!@\n");
			parser.addIncrement("0 states generated, 0 distinct states found, 0 states left on queue.\n");
			parser.addIncrement("@!@!@ENDMSG 2199 @!@!@\n");
			parser.addIncrement("@!@!@STARTMSG 2194:0 @!@!@\n");
			parser.addIncrement("The depth of the complete state graph search is 0.\n");
			parser.addIncrement("@!@!@ENDMSG 2194 @!@!@\n");
			parser.addIncrement("@!@!@STARTMSG 2186:0 @!@!@\n");
			parser.addIncrement("Finished. (2011-07-21 10:14:49)\n");
			parser.addIncrement("@!@!@ENDMSG 2186 @!@!@\n");
		} catch (BadLocationException e) {
			Assert.fail(e.getMessage());
		}

		parser.done();

		// expected, since tests call done()
		Assert.assertTrue(testListener.isDone());

		// all regions detected?
		final List<ITypedRegion> regions = testListener.getRegions();
		Assert.assertNotNull(regions);
		Assert.assertEquals("Not all regions detected", 14, regions.size());

		// detected what kind of region?
		int none = 0;
		int out = 0;
		for (ITypedRegion region : regions) {
			if (region instanceof TLCRegion) {
				TLCRegion tlcRegion = (TLCRegion) region;
				switch (tlcRegion.getSeverity()) {
				case MP.NONE:
					none++;
				}
			} else {
				out++;
			}
		}
		Assert.assertEquals("Not all TLCRegions detected", 12, none);
		Assert.assertEquals("Not all non-TLCRegions detected", 2, out);
	}

	@Test
	public void testAddOneLevelNesting() throws IOException {
		TagBasedTLCOutputIncrementalParser parser = new TagBasedTLCOutputIncrementalParser("", 0, false);
		// Register test listener with parser output

		ITLCOutputSource source = parser.getSource();
		DummyListener testListener = new DummyListener();
		source.addTLCOutputListener(testListener);

		// read in test input and feed it to the parser
		try {
			parser.addIncrement("@!@!@STARTMSG 2185:0 @!@!@\n");
			parser.addIncrement("someText\n");
			parser.addIncrement("@!@!@ENDMSG 2185 @!@!@\n");
			
			// <nested content>
			parser.addIncrement("@!@!@STARTMSG 2105:1 @!@!@\n");
			parser.addIncrement("0 level\n");

			// 1st level
			parser.addIncrement("@!@!@STARTMSG 2154:0 @!@!@\n");
			parser.addIncrement("1st level\n");
			parser.addIncrement("@!@!@ENDMSG 2154 @!@!@\n");
			
			parser.addIncrement("@!@!@ENDMSG 2105 @!@!@\n");
			// </nested content>
			
			parser.addIncrement("@!@!@STARTMSG 2186:0 @!@!@\n");
			parser.addIncrement("someText\n");
			parser.addIncrement("@!@!@ENDMSG 2186 @!@!@\n");
		} catch (BadLocationException e) {
			Assert.fail(e.getMessage());
		}

		parser.done();

		// expected, since tests call done()
		Assert.assertTrue(testListener.isDone());

		// all regions detected?
		final List<ITypedRegion> regions = testListener.getRegions();
		Assert.assertNotNull(regions);
		Assert.assertEquals("Not all or too many regions detected", 3, regions.size());
	}

	@Test
	public void testAddTwoLevelNesting() throws IOException {
		TagBasedTLCOutputIncrementalParser parser = new TagBasedTLCOutputIncrementalParser("", 0, false);
		// Register test listener with parser output

		ITLCOutputSource source = parser.getSource();
		DummyListener testListener = new DummyListener();
		source.addTLCOutputListener(testListener);

		// read in test input and feed it to the parser
		try {
			parser.addIncrement("@!@!@STARTMSG 2185:0 @!@!@\n");
			parser.addIncrement("someText\n");
			parser.addIncrement("@!@!@ENDMSG 2185 @!@!@\n");
			
			// <nested content>
			parser.addIncrement("@!@!@STARTMSG 2105:1 @!@!@\n");
			parser.addIncrement("0 level\n");

			// 1st level
			parser.addIncrement("@!@!@STARTMSG 2154:0 @!@!@\n");
			parser.addIncrement("1st level\n");
			
			// 2nd level
			parser.addIncrement("@!@!@STARTMSG 2178:0 @!@!@\n");
			parser.addIncrement("2nd level\n");
			parser.addIncrement("@!@!@ENDMSG 2178 @!@!@\n");

			parser.addIncrement("@!@!@ENDMSG 2154 @!@!@\n");
			
			parser.addIncrement("@!@!@ENDMSG 2105 @!@!@\n");
			// </nested content>
			
			parser.addIncrement("@!@!@STARTMSG 2186:0 @!@!@\n");
			parser.addIncrement("someText\n");
			parser.addIncrement("@!@!@ENDMSG 2186 @!@!@\n");
		} catch (BadLocationException e) {
			Assert.fail(e.getMessage());
		}

		parser.done();

		// expected, since tests call done()
		Assert.assertTrue(testListener.isDone());

		// all regions detected?
		final List<ITypedRegion> regions = testListener.getRegions();
		Assert.assertNotNull(regions);
		Assert.assertEquals("Not all or too many regions detected", 3, regions.size());
	}
}
