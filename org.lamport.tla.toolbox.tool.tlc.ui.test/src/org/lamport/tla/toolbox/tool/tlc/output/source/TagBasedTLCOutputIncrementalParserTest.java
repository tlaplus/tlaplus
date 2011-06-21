package org.lamport.tla.toolbox.tool.tlc.output.source;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.net.URL;
import java.util.ArrayList;
import java.util.Iterator;
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
	public void testAddIncrement() throws IOException {
		TagBasedTLCOutputIncrementalParser parser = new TagBasedTLCOutputIncrementalParser("", 0, false);

		long start = System.currentTimeMillis();
		
		// read in test input and feed it to the parser
		try {
			for (Iterator<String> itr = input.iterator(); itr.hasNext();) {
				parser.addIncrement(itr.next());
			}
		} catch (BadLocationException e) {
			Assert.fail(e.getMessage());
		}
		
		parser.done();

		// expect that time elapsed is less than x
		long elapsed = System.currentTimeMillis() - start;
		Assert.assertTrue("", elapsed < 60 * 1000);
	}

//	@Test
	public void testAddIncrementForTraceExplorer() throws IOException {
		TagBasedTLCOutputIncrementalParser parser = new TagBasedTLCOutputIncrementalParser("", 0, true);

		long start = System.currentTimeMillis();
		
		// read in test input and feed it to the parser
		try {
			for (Iterator<String> itr = input.iterator(); itr.hasNext();) {
				parser.addIncrement(itr.next());
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
