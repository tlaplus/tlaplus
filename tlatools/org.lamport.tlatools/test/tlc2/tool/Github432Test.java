/*******************************************************************************
 * Copyright (c) 2019 Microsoft Research. All rights reserved. 
 *
 * The MIT License (MIT)
 * 
 * Permission is hereby granted, free of charge, to any person obtaining a copy 
 * of this software and associated documentation files (the "Software"), to deal
 * in the Software without restriction, including without limitation the rights
 * to use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies
 * of the Software, and to permit persons to whom the Software is furnished to do
 * so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all
 * copies or substantial portions of the Software. 
 * 
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS
 * FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR
 * COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN
 * AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION
 * WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 *
 * Contributors:
 *   Markus Alexander Kuppe - initial API and implementation
 ******************************************************************************/
package tlc2.tool;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.FileWriter;
import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.StandardCopyOption;
import java.util.concurrent.atomic.AtomicInteger;

import org.junit.Assert;
import org.junit.Test;

import tlc2.output.EC;
import tlc2.tool.liveness.ModelCheckerTestCase;

public class Github432Test extends ModelCheckerTestCase {
	private static final AtomicInteger TEST_COUNTER = new AtomicInteger(0);
	
	private static final String CONFIG_FILE = "Github432.cfg";
	private static final String CONFIG_FILE_BACKUP = "Github432.cfg_bak";
	
	private static final String HUMANS_TOKEN = "%1%";
	private static final String OTHERS_TOKEN = "%2%";
	
	
	private String[] expectedWarnings;
	
	public Github432Test() {
		super("Github432");
	}

	@Override
	protected void beforeSetUp() {
		final int testNumber = TEST_COUNTER.getAndIncrement();
		final String humans;
		final String others;
		
		switch (testNumber) {
			case 0:
				humans = "Alice";
				others = "Cat, Dog";
				expectedWarnings = new String[] {"", "Humans", "has", "s"};
				break;
			case 1:
				humans = "";
				others = "Emu";
				expectedWarnings = new String[] {"s", "Humans, and Others", "have", ""};
				break;
			case 2:
				humans = "Frank, Glenda";
				others = "";
				expectedWarnings = new String[] {"", "Others", "has", "s"};
				break;
			default:
				humans = "Hauser, Ignatio";
				others = "Jackal, Kangaroo";
				expectedWarnings = null;
				break;
		}
		
		try {
			createConfigFile(humans, others);
		} catch (final Exception e) {
			revertConfigFile();
			
			Assert.fail(e.getMessage());
		}
	}
	
	@Override
	protected void beforeTearDown() {
		revertConfigFile();
	}
	
	@Override
	protected void assertExitStatus() {
		// We don't care - and the spec actually fails for test-b
	}
	
	private void compareToExpectedResults(final String[] array) {
		Assert.assertNotNull("Reported parameters should not be null.", array);
		Assert.assertEquals("Expected warnings should be the same cardinality of the reported parameters encountered.",
							expectedWarnings.length, array.length);
		for (int i = 0; i < array.length; i++) {
			Assert.assertEquals(expectedWarnings[i], array[i]);
		}
	}
	
	@Test
	public void testA() throws FileNotFoundException, IOException {
		if (expectedWarnings != null) {
			compareToExpectedResults((String[])recorder.getRecords(EC.TLC_SYMMETRY_SET_TOO_SMALL).get(0));
		} else {
			Assert.assertFalse(recorder.recorded(EC.TLC_SYMMETRY_SET_TOO_SMALL));
		}
	}
	
	@Test
	public void testB() throws FileNotFoundException, IOException {
		if (expectedWarnings != null) {
			compareToExpectedResults((String[])recorder.getRecords(EC.TLC_SYMMETRY_SET_TOO_SMALL).get(0));
		} else {
			Assert.assertFalse(recorder.recorded(EC.TLC_SYMMETRY_SET_TOO_SMALL));
		}
	}
	
	@Test
	public void testC() throws FileNotFoundException, IOException {
		if (expectedWarnings != null) {
			compareToExpectedResults((String[])recorder.getRecords(EC.TLC_SYMMETRY_SET_TOO_SMALL).get(0));
		} else {
			Assert.assertFalse(recorder.recorded(EC.TLC_SYMMETRY_SET_TOO_SMALL));
		}
	}
	
	@Test
	public void testD() throws FileNotFoundException, IOException {
		if (expectedWarnings != null) {
			compareToExpectedResults((String[])recorder.getRecords(EC.TLC_SYMMETRY_SET_TOO_SMALL).get(0));
		} else {
			Assert.assertFalse(recorder.recorded(EC.TLC_SYMMETRY_SET_TOO_SMALL));
		}
	}
	
	private void createConfigFile(final String humans, final String others) throws IOException {
		final File configFile = new File(BASE_DIR + TEST_MODEL + CONFIG_FILE);
		final File backup = new File(BASE_DIR + TEST_MODEL + CONFIG_FILE_BACKUP);
		
		if (backup.exists()) {
			Assert.fail("Github432 test state is incoherent: the backup file already exists at "
							+ backup.getAbsolutePath());
		}
		
		try {
			Files.move(configFile.toPath(), backup.toPath(), StandardCopyOption.ATOMIC_MOVE);
		} catch (final IOException e) {
			Assert.fail(e.getMessage());
		}
		
		try {
			try (final BufferedWriter bw = new BufferedWriter(new FileWriter(configFile))) {
				try (final BufferedReader br = new BufferedReader(new FileReader(backup))) {
					boolean humansFound = false;
					boolean othersFound = false;
					String line;
					while ((line = br.readLine()) != null) {
						int index = humansFound ? -1 : line.indexOf(HUMANS_TOKEN);
						if (index == -1) {
							index = othersFound ? -1 : line.indexOf(OTHERS_TOKEN);

							if (index == -1) {
								bw.write(line);
							} else {
								final int secondStart = index + OTHERS_TOKEN.length();
								final String convertedLine = line.substring(0, index) + others
																	+ line.substring(secondStart);
								bw.write(convertedLine);
								othersFound = true;
							}
						} else {
							final int secondStart = index + HUMANS_TOKEN.length();
							final String convertedLine = line.substring(0, index) + humans
																+ line.substring(secondStart);
							bw.write(convertedLine);
							humansFound = true;
						}
						
						bw.newLine();
					}
				}
			}
		} catch (final IOException e) {
			
			revertConfigFile();
			
			Assert.fail(e.getMessage());
		}
	}
	
	private void revertConfigFile() {
		final File backup = new File(BASE_DIR + TEST_MODEL + CONFIG_FILE_BACKUP);
		
		if (backup.exists()) {
			final File configFile = new File(BASE_DIR + TEST_MODEL + CONFIG_FILE);

			try {
				Files.move(backup.toPath(), configFile.toPath(), StandardCopyOption.REPLACE_EXISTING);
			} catch (final IOException e) {
				Assert.fail(e.getMessage());
			}
		}
	}
}
