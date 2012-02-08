// Copyright (c) Feb 6, 2012 Microsoft Corporation.  All rights reserved.
package org.lamport.tla.toolbox.tool.tlc.output.source;

import static org.junit.Assert.assertTrue;
import static org.junit.Assert.fail;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.net.URL;
import java.util.List;

import junit.framework.Assert;

import org.eclipse.jface.text.BadLocationException;
import org.eclipse.jface.text.ITypedRegion;
import org.junit.Test;

public class Bug267Test {

	public String getInput(String name) throws Exception {
		URL url = this.getClass().getClassLoader().getResource(name);
        InputStream inputStream = url.openConnection().getInputStream();
		BufferedReader reader = new BufferedReader(new InputStreamReader(inputStream));
		
		// Read the input fully here
		StringBuffer buf = new StringBuffer();
		String line;
		while((line = reader.readLine()) != null) {
			buf.append(line);
			buf.append("\n");
		}
		
		reader.close();

		return buf.toString();
	}
	
	@Test
	public void testSuccess() throws Exception {
		final TagBasedTLCOutputIncrementalParser parser = new TagBasedTLCOutputIncrementalParser("", 0, false);
		
		final Bug267Listener listener = new Bug267Listener();

		final ITLCOutputSource source = parser.getSource();
		source.addTLCOutputListener(listener);
		
		// read in test input and feed it to the parser
		try {
			parser.addIncrement(getInput("files/Bug267success.out"));
		} catch (BadLocationException e) {
			fail();
		}
		
		source.removeTLCOutputListener(listener);
		
		assertTrue(listener.getErrors().size() == 2);
	}
	
	@Test
	public void testAdd2154And2132Nested() throws IOException {
		TagBasedTLCOutputIncrementalParser parser = new TagBasedTLCOutputIncrementalParser("", 0, false);
		// Register test listener with parser output

		ITLCOutputSource source = parser.getSource();
		DummyListener testListener = new DummyListener();
		source.addTLCOutputListener(testListener);

		final String startTag = "@!@!@STARTMSG 2154:0 @!@!@\n";
		final String text = "Attempted to apply the operator overridden by the Java method\n"
				+ "public static tlc2.value.Value tlc2.module.TLC.Assert(tlc2.value.Value,tlc2.value.Value),\n"
				+ "but it produced the following error:\n";
		final String endTag = "@!@!@ENDMSG 2154 @!@!@\n";
		
		final String nestedStartTag = "@!@!@STARTMSG 2132:0 @!@!@\n";
		final String nestedText = "The first argument of Assert evaluated to FALSE; the second argument was:\n\"Failure of assertion.\"\n";
		final String nestedEndTag = "@!@!@ENDMSG 2132 @!@!@\n";

		final String fullText = startTag + text + nestedStartTag + nestedText + nestedEndTag + endTag;
		
		// read in test input and feed it to the parser
		try {

			parser.addIncrement(startTag);
			
				parser.addIncrement(text);
				
				parser.addIncrement(nestedStartTag);
	
					parser.addIncrement(nestedText);
				
				parser.addIncrement(nestedEndTag);
			
			parser.addIncrement(endTag);
			
		} catch (BadLocationException e) {
			Assert.fail(e.getMessage());
		}

		parser.done();

		// expected, since tests call done()
		Assert.assertTrue(testListener.isDone());

		// all regions detected?
		final List<ITypedRegion> regions = testListener.getRegions();
		Assert.assertNotNull(regions);
		Assert.assertEquals("Not all or too many regions detected", 1, regions.size());

		// assert that the input text can be found with the given region
		final TLCRegionContainer region = (TLCRegionContainer) regions.get(0); // safe due to previous assert
		final ITypedRegion[] subRegions = region.getSubRegions();
		
		// outter text
		final ITypedRegion subRegionsOutter = subRegions[1];
		final String regionText = fullText.substring(
				subRegionsOutter.getOffset(), subRegionsOutter.getOffset()
						+ subRegionsOutter.getLength());
		Assert.assertEquals(text, regionText);
		
		// nested/inner text
		final ITypedRegion subRegionsNested = subRegions[0];
		final String nestedRegionText = fullText.substring(
				subRegionsNested.getOffset(), subRegionsNested.getOffset()
						+ subRegionsNested.getLength() + 1);
		Assert.assertEquals(nestedText, nestedRegionText);
	}

	@Test
	public void testAdd2132Region() throws IOException {
		TagBasedTLCOutputIncrementalParser parser = new TagBasedTLCOutputIncrementalParser("", 0, false);
		// Register test listener with parser output

		ITLCOutputSource source = parser.getSource();
		DummyListener testListener = new DummyListener();
		source.addTLCOutputListener(testListener);

		final String startTag = "@!@!@STARTMSG 2132:0 @!@!@\n";
		final String text = "The first argument of Assert evaluated to FALSE; the second argument was:\n\"Failure of assertion.\"\n";
		final String endTag = "@!@!@ENDMSG 2132 @!@!@\n";
		
		// read in test input and feed it to the parser
		try {

			parser.addIncrement(startTag);
			parser.addIncrement(text);
			parser.addIncrement(endTag);
			
		} catch (BadLocationException e) {
			Assert.fail(e.getMessage());
		}
		
		parser.done();
		
		// expected, since tests call done()
		Assert.assertTrue(testListener.isDone());
		
		// all regions detected?
		final List<ITypedRegion> regions = testListener.getRegions();
		Assert.assertNotNull(regions);
		Assert.assertEquals("Not all or too many regions detected", 1, regions.size());
		
		// assert that the input text can be found with the given region
		final ITypedRegion region = regions.get(0); // safe due to previous assert
		final String regionText = (startTag + text + endTag).substring(
				region.getOffset(), region.getOffset() + region.getLength()
				+ 1);
		Assert.assertEquals(text, regionText);
	}

	@Test
	public void testAdd2154Region() throws IOException {
		TagBasedTLCOutputIncrementalParser parser = new TagBasedTLCOutputIncrementalParser("", 0, false);
		// Register test listener with parser output

		ITLCOutputSource source = parser.getSource();
		DummyListener testListener = new DummyListener();
		source.addTLCOutputListener(testListener);

		final String startTag = "@!@!@STARTMSG 2154:0 @!@!@\n";
		final String text = "Attempted to apply the operator overridden by the Java method\n"
				+ "public static tlc2.value.Value tlc2.module.TLC.Assert(tlc2.value.Value,tlc2.value.Value),\n"
				+ "but it produced the following error:\n";
		final String endTag = "@!@!@ENDMSG 2154 @!@!@\n";

		// read in test input and feed it to the parser
		try {

			parser.addIncrement(startTag);
			parser.addIncrement(text);
			parser.addIncrement(endTag);
			
		} catch (BadLocationException e) {
			Assert.fail(e.getMessage());
		}

		parser.done();
		// expected, since tests call done()
		Assert.assertTrue(testListener.isDone());

		// all regions detected?
		final List<ITypedRegion> regions = testListener.getRegions();
		Assert.assertNotNull(regions);
		Assert.assertEquals("Not all or too many regions detected", 1, regions.size());

		// assert that the input text can be found with the given region
		final ITypedRegion region = regions.get(0); // safe due to previous assert
		final String regionText = (startTag + text + endTag).substring(
				region.getOffset(), region.getOffset() + region.getLength()
				+ 1);
		Assert.assertEquals(text, regionText);
	}
}
