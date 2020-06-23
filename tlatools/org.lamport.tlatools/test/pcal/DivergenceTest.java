/*******************************************************************************
 * Copyright (c) 2020 Microsoft Research. All rights reserved. 
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
package pcal;

import java.io.File;
import java.io.IOException;

import org.junit.Ignore;
import org.junit.Test;

import tla2sany.drivers.SANY;
import util.TestPrintStream;
import util.ToolIO;

// Plz can haz https://openjdk.java.net/jeps/355 ?
public class DivergenceTest extends PCalTest {
	@Test
	public void divergenceTest00() throws IOException {
		final String filename = "divergenceTest001" + System.currentTimeMillis();
		final String absolutePath = writeFile(System.getProperty("java.io.tmpdir") + File.separator + filename,
				"---- MODULE " + filename + " ----\n" +
				"\n" +
				"(*\n" +
				"--algorithm a\n" +
				"begin\n" +
				"  skip;\n" +
				"end algorithm; *)\n" +
				"\\* BEGIN TRANSLATION\n" +
				"VARIABLE pc\n" +
				"\n" +
				"vars == << pc >>\n" +
				"\n" +
				"Init == /\\ pc = \"Lbl_1\"\n" +
				"\n" +
				"Lbl_1 == /\\ pc = \"Lbl_1\"\n" +
				"         /\\ TRUE\n" +
				"         /\\ pc' = \"Done\"\n" +
				"\n" +
				"(* Allow infinite stuttering to prevent deadlock on termination. *)\n" +
				"Terminating == pc = \"Done\" /\\ UNCHANGED vars\n" +
				"\n" +
				"Next == Lbl_1\n" +
				"           \\/ Terminating\n" +
				"\n" +
				"Spec == Init /\\ [][Next]_vars\n" +
				"\n" +
				"Termination == <>(pc = \"Done\")\n" +
				"\n" +
				"\\* END TRANSLATION\n" +
				"\n=========================");
		test(filename, absolutePath, "Semantic processing of module " + filename);
	}

	@Test
	public void divergenceTest01() throws IOException {
		final String filename = "divergenceTest01" + System.currentTimeMillis();
		final String absolutePath = writeFile(System.getProperty("java.io.tmpdir") + File.separator + filename,
				"---- MODULE " + filename + " ----\n" +
				"\n" +
				"(*\n" +
				"--algorithm a\n" +
				"begin\n" +
				"  skip;\n" +
				"end algorithm; *)\n" +
				"\\* BEGIN TRANSLATION - the hash of the PCal code: PCal-6d2bf9f0e5d0cc207316a004ca8a0713\n" +
				"VARIABLE pc\n" +
				"\n" +
				"vars == << pc >>\n" +
				"\n" +
				"Init == /\\ pc = \"Lbl_1\"\n" +
				"\n" +
				"Lbl_1 == /\\ pc = \"Lbl_1\"\n" +
				"         /\\ TRUE\n" +
				"         /\\ pc' = \"Done\"\n" +
				"\n" +
				"(* Allow infinite stuttering to prevent deadlock on termination. *)\n" +
				"Terminating == pc = \"Done\" /\\ UNCHANGED vars\n" +
				"\n" +
				"Next == Lbl_1\n" +
				"           \\/ Terminating\n" +
				"\n" +
				"Spec == Init /\\ [][Next]_vars\n" +
				"\n" +
				"Termination == <>(pc = \"Done\")\n" +
				"\n" +
				"\\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-c42acd1a2a013bcd259342cfe120880f\n" +
				"\n=========================");
		test(filename, absolutePath, "Semantic processing of module " + filename);
	}

	@Test
	public void divergenceTest02() throws IOException {
		final String filename = "divergenceTest02" + System.currentTimeMillis();
		final String absolutePath = writeFile(System.getProperty("java.io.tmpdir") + File.separator + filename,
				"---- MODULE " + filename + " ----\n" +
				"\n" +
				"(*\n" +
				"--algorithm a\n" +
				"begin\n" +
				"  print \"msg\";\n" + // PlusCal diverged
				"end algorithm; *)\n" +
				"\\* BEGIN TRANSLATION - the hash of the PCal code: PCal-6d2bf9f0e5d0cc207316a004ca8a0713\n" +
				"VARIABLE pc\n" +
				"\n" +
				"vars == << pc >>\n" +
				"\n" +
				"Init == /\\ pc = \"Lbl_1\"\n" +
				"\n" +
				"Lbl_1 == /\\ pc = \"Lbl_1\"\n" +
				"         /\\ TRUE\n" +
				"         /\\ pc' = \"Done\"\n" +
				"\n" +
				"(* Allow infinite stuttering to prevent deadlock on termination. *)\n" +
				"Terminating == pc = \"Done\" /\\ UNCHANGED vars\n" +
				"\n" +
				"Next == Lbl_1\n" +
				"           \\/ Terminating\n" +
				"\n" +
				"Spec == Init /\\ [][Next]_vars\n" +
				"\n" +
				"Termination == <>(pc = \"Done\")\n" +
				"\n" +
				"\\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-c42acd1a2a013bcd259342cfe120880f\n" +
				"\n=========================");
		test(filename, absolutePath, "!! WARNING: Either the PlusCal or its TLA+ translation has changed in the specification for "
				+ filename + " since the last time translation was performed.");
	}

	@Test
	public void divergenceTest03() throws IOException {
		final String filename = "divergenceTest03" + System.currentTimeMillis();
		final String absolutePath = writeFile(System.getProperty("java.io.tmpdir") + File.separator + filename,
				"---- MODULE " + filename + " ----\n" +
				"\n" +
				"(*\n" +
				"--algorithm a\n" +
				"begin\n" +
				"  skip;\n" +
				"end algorithm; *)\n" +
				"\\* BEGIN TRANSLATION - the hash of the PCal code: PCal-6d2bf9f0e5d0cc207316a004ca8a0713\n" +
				"VARIABLE pc\n" +
				"\n" +
				"vars == << pc >>\n" +
				"\n" +
				"Init == /\\ pc = \"Lbl_1\"\n" +
				"\n" +
				"Lbl_1 == /\\ pc = \"Lbl_1\"\n" +
				"         /\\ TRUE\n" +
				"         /\\ pc' = \"Done\"\n" +
				"\n" +
				"(* Allow infinite stuttering to prevent deadlock on termination. *)\n" +
				"Terminating == pc = \"Done\" /\\ UNCHANGED vars\n" +
				"\n" +
				"Next == Lbl_1\n" + // TLA+ diverged.
				"\n" +
				"Spec == Init /\\ [][Next]_vars\n" +
				"\n" +
				"Termination == <>(pc = \"Done\")\n" +
				"\n" +
				"\\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-c42acd1a2a013bcd259342cfe120880f\n" +
				"\n=========================");
		test(filename, absolutePath, "!! WARNING: Either the PlusCal or its TLA+ translation has changed in the specification for "
				+ filename + " since the last time translation was performed.");
	}

	@Test
	public void divergenceTest04() throws IOException {
		final String filename = "divergenceTest04" + System.currentTimeMillis();
		final String absolutePath = writeFile(System.getProperty("java.io.tmpdir") + File.separator + filename,
				"---- MODULE " + filename + " ----\n" +
				"\n" +
				"(*\n" +
				"--algorithm a\n" +
				"begin\n" +
				"  print \"msg\";\n" + // PlusCal diverged
				"end algorithm; *)\n" +
				"\\* BEGIN TRANSLATION - the hash of the PCal code: PCal-6d2bf9f0e5d0cc207316a004ca8a0713\n" +
				"VARIABLE pc\n" +
				"\n" +
				"vars == << pc >>\n" +
				"\n" +
				"Init == /\\ pc = \"Lbl_1\"\n" +
				"\n" +
				"Lbl_1 == /\\ pc = \"Lbl_1\"\n" +
				"         /\\ TRUE\n" +
				"         /\\ pc' = \"Done\"\n" +
				"\n" +
				"(* Allow infinite stuttering to prevent deadlock on termination. *)\n" +
				"Terminating == pc = \"Done\" /\\ UNCHANGED vars\n" +
				"\n" +
				"Next == Lbl_1\n" + // TLA+ diverged.
				"\n" +
				"Spec == Init /\\ [][Next]_vars\n" +
				"\n" +
				"Termination == <>(pc = \"Done\")\n" +
				"\n" +
				"\\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-c42acd1a2a013bcd259342cfe120880f\n" +
				"\n=========================");
		test(filename, absolutePath, "!! WARNING: Either the PlusCal or its TLA+ translation has changed in the specification for "
				+ filename + " since the last time translation was performed.");
	}

	@Test
	public void divergenceTest05() throws IOException {
		final String filename = "divergenceTest05" + System.currentTimeMillis();
		final String absolutePath = writeFile(System.getProperty("java.io.tmpdir") + File.separator + filename,
				"---- MODULE " + filename + " ----\n" +
				"\n" +
				"(*\n" +
				"--algorithm a\n" +
				"begin\n" +
				"  skip;\n" +
				"end algorithm; *)\n" +
				"\n=========================");
		test(filename, absolutePath, "PlusCal was found in the specification for "+ filename +" but no TLA+ translation could be found.");
	}

	@Test
	@Ignore
	public void divergenceTest06() throws IOException {
		final String filename = "divergenceTest06" + System.currentTimeMillis();
		final String absolutePath = writeFile(System.getProperty("java.io.tmpdir") + File.separator + filename,
				"---- MODULE " + filename + " ----\n" +
				"\n" +
				"(*\n" +
				"--algorithm a\n" +
				"begin\n" +
				"  skip;\n" +
				"end algorithm; *)\n" +
				"\\* BEGIN TRANSLATION\n" +
				"VARIABLE pc\n" +
				"\n" +
				"vars == << pc >>\n" +
				"\n" +
				"Init == /\\ pc = \"Lbl_1\"\n" +
				"\n" +
				"Lbl_1 == /\\ pc = \"Lbl_1\"\n" +
				"         /\\ TRUE\n" +
				"         /\\ pc' = \"Done\"\n" +
				"\n" +
				"(* Allow infinite stuttering to prevent deadlock on termination. *)\n" +
				"Terminating == pc = \"Done\" /\\ UNCHANGED vars\n" +
				"\n" +
				"Next == Lbl_1\n" + // TLA+ diverged, but no hash.
				"\n" +
				"Spec == Init /\\ [][Next]_vars\n" +
				"\n" +
				"Termination == <>(pc = \"Done\")\n" +
				"\n" +
				"\\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-c42acd1a2a013bcd259342cfe120880f\n" +
				"\n=========================");
		test(filename, absolutePath, "!! WARNING: Either the PlusCal or its TLA+ translation has changed in the specification for "
				+ filename + " since the last time translation was performed.");
	}
	
 	private void test(final String filename, final String absolutePath, final String expected) {
		// Parse with SANY and check for errors (collects parse errors into ToolIO.out)
		final TestPrintStream testPrintStream = new TestPrintStream();
		ToolIO.out = testPrintStream;
		SANY.SANYmain(new String[] { absolutePath });
		testPrintStream.assertSubstring(expected);
		testPrintStream.assertSubstring("Semantic processing of module " + filename);
	}

}
