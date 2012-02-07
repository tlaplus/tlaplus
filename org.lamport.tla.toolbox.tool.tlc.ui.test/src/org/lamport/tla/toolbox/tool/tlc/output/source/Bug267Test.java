// Copyright (c) Feb 6, 2012 Microsoft Corporation.  All rights reserved.
package org.lamport.tla.toolbox.tool.tlc.output.source;

import static org.junit.Assert.assertTrue;
import static org.junit.Assert.fail;

import java.io.BufferedReader;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.net.URL;

import org.eclipse.jface.text.BadLocationException;
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
		
		assertTrue(listener.getErrors().size() == 2);
	}
	
	@Test
	public void testBug267() throws Exception {
		final TagBasedTLCOutputIncrementalParser parser = new TagBasedTLCOutputIncrementalParser("", 0, false);
	
		final Bug267Listener listener = new Bug267Listener();

		final ITLCOutputSource source = parser.getSource();
		source.addTLCOutputListener(listener);
		
		// read in test input and feed it to the parser
		try {
			parser.addIncrement(getInput("files/Bug267failure.out"));
		} catch (BadLocationException e) {
			fail();
		}
		
		assertTrue(listener.getErrors().size() == 2);
	}
}
