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

import org.junit.Test;

import tla2sany.drivers.SANY;
import util.TestPrintStream;
import util.ToolIO;


//TODO The asserts below could be strengthened if the error message about the divergence would include the actual hash mismatch.

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
		// Parse with SANY and check for errors (collects parse errors into ToolIO.out)
		final TestPrintStream testPrintStream = new TestPrintStream();
		ToolIO.out = testPrintStream;
		SANY.SANYmain(new String[] { absolutePath });
		testPrintStream.assertSubstring("Semantic processing of module " + filename);
		testPrintStream.assertNoSubstring("!! WARNING " + filename);
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
				"\\* BEGIN TRANSLATION (chksum(PCal) \\in STRING /\\ chksum(TLA+) \\in STRING)\n" +
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
		// Parse with SANY and check for errors (collects parse errors into ToolIO.out)
		final TestPrintStream testPrintStream = new TestPrintStream();
		ToolIO.out = testPrintStream;
		SANY.SANYmain(new String[] { absolutePath });
		testPrintStream.assertSubstring("Semantic processing of module " + filename);
		testPrintStream.assertNoSubstring("!! WARNING " + filename);
	}

	@Test
	public void divergenceTest01fair() throws IOException {
		final String filename = "divergenceTest01" + System.currentTimeMillis();
		final String absolutePath = writeFile(System.getProperty("java.io.tmpdir") + File.separator + filename,
				"---- MODULE " + filename + " ----\n" +
				"\n" +
				"(*\n" +
				"--fair algorithm a\n" + // Divergence because "fair" was added after the translation.
				"begin\n" +
				"  skip;\n" +
				"end algorithm; *)\n" +
				"\\* BEGIN TRANSLATION (checksum(PlusCal) = \"4860ac97\" /\\ chksum(TLA+) \\in STRING)\n" +
				"\\* END TRANSLATION\n" +
				"\n=========================");
		// Parse with SANY and check for errors (collects parse errors into ToolIO.out)
		final TestPrintStream testPrintStream = new TestPrintStream();
		ToolIO.out = testPrintStream;
		SANY.SANYmain(new String[] { absolutePath });
		testPrintStream.assertSubstring("Semantic processing of module " + filename);
		testPrintStream.assertSubstring(String.format(
				"!! WARNING: The PlusCal algorithm in module %s has changed since its last translation.",
				filename));
	}
	
	@Test
	public void divergenceTest01unfair() throws IOException {
		final String filename = "divergenceTest01" + System.currentTimeMillis();
		final String absolutePath = writeFile(System.getProperty("java.io.tmpdir") + File.separator + filename,
				"---- MODULE " + filename + " ----\n" +
				"\n" +
				"(*\n" +
				"--algorithm a\n" + // Divergence because "fair" was removed after the translation.
				"begin\n" +
				"  skip;\n" +
				"end algorithm; *)\n" +
				"\\* BEGIN TRANSLATION (checksum(PlusCal) = \"7c28162a\" /\\ chksum(TLA+) \\in STRING)\n" +
				"\\* END TRANSLATION\n" +
				"\n=========================");
		// Parse with SANY and check for errors (collects parse errors into ToolIO.out)
		final TestPrintStream testPrintStream = new TestPrintStream();
		ToolIO.out = testPrintStream;
		SANY.SANYmain(new String[] { absolutePath });
		testPrintStream.assertSubstring("Semantic processing of module " + filename);
		testPrintStream.assertSubstring(String.format(
				"!! WARNING: The PlusCal algorithm in module %s has changed since its last translation.",
				filename));
	}
	
	@Test
	public void divergenceTestIndentation() throws IOException {
		final String filename = "divergenceTest01" + System.currentTimeMillis();
		final String absolutePath = writeFile(System.getProperty("java.io.tmpdir") + File.separator + filename,
				"---- MODULE " + filename + " ----\n" +
				"\n" +
				"(*\n" +
				"--algorithm a\nvariable f;" + 
				"begin\n" +
				"  f := /\\ TRUE\n" + 
				"    /\\ TRUE;\n" +  // Divergence because indentation was changed after the translation.
				"end algorithm; *)\n" +
				"\\* BEGIN TRANSLATION (checksum(PlusCal) = \"996afab0\" /\\ chksum(TLA+) \\in STRING)\n" +
				"\\* END TRANSLATION\n" +
				"\n=========================");
		// Parse with SANY and check for errors (collects parse errors into ToolIO.out)
		final TestPrintStream testPrintStream = new TestPrintStream();
		ToolIO.out = testPrintStream;
		SANY.SANYmain(new String[] { absolutePath });
		testPrintStream.assertSubstring("Semantic processing of module " + filename);
		testPrintStream.assertSubstring(String.format(
				"!! WARNING: The PlusCal algorithm in module %s has changed since its last translation.",
				filename));
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
				"\\* BEGIN TRANSLATION (chksum(PCal) = \"4860ac97\" /\\ chksum(TLA+) = \"af3d9146\")\n" +
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
		// Parse with SANY and check for errors (collects parse errors into ToolIO.out)
		final TestPrintStream testPrintStream = new TestPrintStream();
		ToolIO.out = testPrintStream;
		SANY.SANYmain(new String[] { absolutePath });
		testPrintStream.assertSubstring("Semantic processing of module " + filename);
		testPrintStream.assertSubstring(String.format(
				"!! WARNING: The PlusCal algorithm in module %s has changed since its last translation.",
				filename));
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
				"\\* BEGIN TRANSLATION (checksum(PlusCal) = \"4860ac97\" /\\ ChkSum(tla+) = \"af3d9146\")\n" +
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
				"\\* END TRANSLATION\n" +
				"\n=========================");
		// Parse with SANY and check for errors (collects parse errors into ToolIO.out)
		final TestPrintStream testPrintStream = new TestPrintStream();
		ToolIO.out = testPrintStream;
		SANY.SANYmain(new String[] { absolutePath });
		testPrintStream.assertSubstring("Semantic processing of module " + filename);
		testPrintStream.assertSubstring(String.format(
				"!! WARNING: The TLA+ translation in module %s has changed since its last translation.",
				filename));
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
				"\\* BEGIN TRANSLATION   (checksum(PlusCal) = \"4860ac97\" /\\ ChkSum(tla+) = \"af3d9146\")  \n" +
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
				"\\* END TRANSLATION\n" +
				"\n=========================");
		// Parse with SANY and check for errors (collects parse errors into ToolIO.out)
		final TestPrintStream testPrintStream = new TestPrintStream();
		ToolIO.out = testPrintStream;
		SANY.SANYmain(new String[] { absolutePath });
		testPrintStream.assertSubstring("Semantic processing of module " + filename);
		testPrintStream.assertSubstring(String.format(
				"!! WARNING: The PlusCal algorithm and its TLA+ translation in module %s filename since the last translation.",
				filename));
	}
	@Test
	public void divergenceTest05() throws IOException {
		final String filename = "divergenceTest04" + System.currentTimeMillis();
		final String absolutePath = writeFile(System.getProperty("java.io.tmpdir") + File.separator + filename,
				"---- MODULE " + filename + " ----\n" +
				"\n" +
				"(*\n" +
				"--algorithm a\n" +
				"begin\n" +
				"  print \"msg\";\n" + // PlusCal diverged
				"end algorithm; *)\n" +
				"\\* BEGIN TRANSLATION   (checksum(PlusCal) \\in  STRING /\\ ChkSum(tla+) \\in STRING)  \n" +
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
				"\\* END TRANSLATION\n" +
				"\n=========================");
		// Parse with SANY and check for errors (collects parse errors into ToolIO.out)
		final TestPrintStream testPrintStream = new TestPrintStream();
		ToolIO.out = testPrintStream;
		SANY.SANYmain(new String[] { absolutePath });
		testPrintStream.assertSubstring("Semantic processing of module " + filename);
		testPrintStream.assertNoSubstring(String.format(
				"!! WARNING:",
				filename));
	}

	@Test
	public void divergenceTest06() throws IOException {
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
		// Parse with SANY and check for errors (collects parse errors into ToolIO.out)
		final TestPrintStream testPrintStream = new TestPrintStream();
		ToolIO.out = testPrintStream;
		SANY.SANYmain(new String[] { absolutePath });
		testPrintStream.assertSubstring("Semantic processing of module " + filename);
		testPrintStream.assertNoSubstring("!! WARNING " + filename);
	}
}
