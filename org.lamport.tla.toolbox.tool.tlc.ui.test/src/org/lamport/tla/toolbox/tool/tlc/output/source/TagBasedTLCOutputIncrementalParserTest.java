package org.lamport.tla.toolbox.tool.tlc.output.source;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.net.URL;
import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;
import java.util.Random;
import java.util.Stack;

import junit.framework.Assert;

import org.eclipse.jface.text.BadLocationException;
import org.eclipse.jface.text.ITypedRegion;
import org.junit.Before;
import org.junit.Test;

public class TagBasedTLCOutputIncrementalParserTest {

	private List<String> input = new ArrayList<String>();
	private final Random rnd = new Random(System.currentTimeMillis());
	
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
	public void testAddIncrementTLCHeader() throws IOException {
		TagBasedTLCOutputIncrementalParser parser = new TagBasedTLCOutputIncrementalParser("", 0, false);

		
		// read in test input and feed it to the parser
		try {
			parser.addIncrement("@!@!@STARTMSG 2262:0 @!@!@");
			parser.addIncrement("TLC2 Version 2.03 of 10 April 2011");
			parser.addIncrement("@!@!@ENDMSG 2262 @!@!@");
			
			TagBasedTLCAnalyzer tagAnalyzer = parser.getTagAnalyzer();
			Stack<ITypedRegion> stack = tagAnalyzer.getStack();
			
			// 1 start tag + 1 end tag + 1 user content
			Assert.assertEquals(3, stack.size());
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
			parser.addIncrement("@!@!@STARTMSG 2217:4 @!@!@");
			parser.addIncrement("1: <Initial predicate>");
			parser.addIncrement("/\\ pos_f = defaultInitValue");
			parser.addIncrement("/\\ foundTokenSpecs = <<>>");
			parser.addIncrement("/\\ delim = defaultInitValue");
			parser.addIncrement("/\\ leftTok = defaultInitValue");
			parser.addIncrement("/\\ left_ = defaultInitValue");
			parser.addIncrement("/\\ returnVal = defaultInitValue");
			parser.addIncrement("/\\ delimLen_ = defaultInitValue");
			parser.addIncrement("/\\ line = ( 0 :> \";\" @@");
			parser.addIncrement("1 :> \";\" @@");
			parser.addIncrement("2 :> \";\" @@");
			parser.addIncrement("3 :> \";\" @@");
			parser.addIncrement("4 :> \";\" @@");
			parser.addIncrement("5 :> \";\" @@");
			parser.addIncrement("6 :> \";\" @@");
			parser.addIncrement("7 :> \";\" @@");
			parser.addIncrement("8 :> \";\" @@");
			parser.addIncrement("9 :> \";\" @@");
			parser.addIncrement("10 :> \"f\" @@");
			parser.addIncrement("11 :> \"(\" @@");
			parser.addIncrement("12 :> \"b\" @@");
			parser.addIncrement("13 :> \")\" @@");
			parser.addIncrement("14 :> \" \" @@");
			parser.addIncrement("15 :> \";\" @@");
			parser.addIncrement("16 :> \";\" @@");
			parser.addIncrement("17 :> \";\" @@");
			parser.addIncrement("18 :> \";\" @@");
			parser.addIncrement("19 :> \";\" @@");
			parser.addIncrement("20 :> \";\" @@");
			parser.addIncrement("21 :> \";\" @@");
			parser.addIncrement("22 :> \";\" @@");
			parser.addIncrement("23 :> \";\" @@");
			parser.addIncrement("24 :> \";\" )(");
			parser.addIncrement("/\\ jdelim_ = defaultInitValue");
			parser.addIncrement("/\\ i = defaultInitValue");
			parser.addIncrement("/\\ foundBangToken = defaultInitValue");
			parser.addIncrement("/\\ pos = defaultInitValue");
			parser.addIncrement("/\\ pc = \"Lbl_77\"");
			parser.addIncrement("/\\ ipos_ = defaultInitValue");
			parser.addIncrement("/\\ pos_fi = defaultInitValue");
			parser.addIncrement("/\\ pos_fin = defaultInitValue");
			parser.addIncrement("/\\ notDone = defaultInitValue");
			parser.addIncrement("/\\ pos_find = defaultInitValue");
			parser.addIncrement("/\\ temp1 = defaultInitValue");
			parser.addIncrement("/\\ temp2 = defaultInitValue");
			parser.addIncrement("/\\ temp3 = defaultInitValue");
			parser.addIncrement("/\\ delimLen = defaultInitValue");
			parser.addIncrement("/\\ rt = defaultInitValue");
			parser.addIncrement("/\\ notLastToken = FALSE");
			parser.addIncrement("/\\ ipos = defaultInitValue");
			parser.addIncrement("/\\ left = defaultInitValue");
			parser.addIncrement("/\\ token = <<>>");
			parser.addIncrement("/\\ rt_ = defaultInitValue");
			parser.addIncrement("/\\ rightTok = defaultInitValue");
			parser.addIncrement("/\\ jdelim = defaultInitValue");
			parser.addIncrement("/\\ tokIdx = defaultInitValue");
			parser.addIncrement("/\\ pos_ = defaultInitValue");
			parser.addIncrement("/\\ curPos = 11");
			parser.addIncrement("/\\ delim_ = defaultInitValue");
			parser.addIncrement("/\\ tokArray = defaultInitValue");
			parser.addIncrement("/\\ lastToken = FALSE");
			parser.addIncrement("/\\ currentToken = defaultInitValue");
			parser.addIncrement("/\\ stack = <<>>");
			parser.addIncrement("/\\ tempVar1 = defaultInitValue");
			parser.addIncrement("/\\ tempVar2 = defaultInitValue");
			parser.addIncrement("/\\ tempVar3 = defaultInitValue");
			parser.addIncrement("@!@!@ENDMSG 2217 @!@!@");
			
			TagBasedTLCAnalyzer tagAnalyzer = parser.getTagAnalyzer();
			Stack<ITypedRegion> stack = tagAnalyzer.getStack();

			// 1 start tag + 1 end tag + 1 user content
			Assert.assertEquals(3, stack.size());
		} catch (BadLocationException e) {
			Assert.fail(e.getMessage());
		}
		
		parser.done();
	}
	
	@Test
	public void testAddIncrement() throws IOException {
		TagBasedTLCOutputIncrementalParser parser = new TagBasedTLCOutputIncrementalParser("", 0, false);

		long start = System.currentTimeMillis();
		
		// read in test input and feed it to the parser
		try {
			for (Iterator<String> itr = input.iterator(); itr.hasNext();) {
				String input = "";

				// read in several lines at once to simulate system.in behavior
				int numLinesToRead = rnd.nextInt(10);
				for (int i = 0; i <= numLinesToRead && itr.hasNext(); i++) {
					input += itr.next() + "\n";
				}
				System.out.println(input + " [length: " + input.length() + "]");
				
				// split the input into random chunks to simulate what the
				// parser normally reads from system.in
				int splitAt = rnd.nextInt(input.length() + 1);
				
				String head = input.substring(0, splitAt);
				String tail = input.substring(splitAt);
				// just make sure we didn't screw up
				Assert.assertEquals(input, head + tail);

				// feed it to the parser
				parser.addIncrement(head);
				parser.addIncrement(tail);
				
				// do sanity checks on the document after parsing a line 
//				final IDocument document = parser.getDocument();
				
				// addIncrement internally uses replace -> number of lines stays at 1
//				Assert.assertEquals("Document has unexpected number of lines",
//						numLinesToRead, document.getNumberOfLines());
				
				
//				Lines are appended to the old document
//				Assert.assertEquals(line, document.get());
				
//				Assert.assertEquals(input.length(), document.getLength());
			}
		} catch (BadLocationException e) {
			Assert.fail(e.getMessage());
		}
		
		parser.done();

		// expect that time elapsed is less than x
		long elapsed = System.currentTimeMillis() - start;
		Assert.assertTrue("", elapsed < 60 * 1000);
	}
}
