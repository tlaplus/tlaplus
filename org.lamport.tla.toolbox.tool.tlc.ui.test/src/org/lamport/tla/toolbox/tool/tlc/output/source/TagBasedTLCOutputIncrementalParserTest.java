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
import org.junit.Before;
import org.junit.Test;

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
}
