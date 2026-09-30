/*******************************************************************************
 * Copyright (c) 2026 NVIDIA Corp. All rights reserved.
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
package tlc2.tool.impl;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;
import static org.junit.Assert.fail;

import java.io.File;
import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;

import org.junit.Rule;
import org.junit.Test;
import org.junit.rules.TemporaryFolder;

import tlc2.output.EC;
import tlc2.tool.ConfigFileException;
import tlc2.util.Vect;

/**
 * https://github.com/tlaplus/tlaplus/issues/1455: a lexical error in a model
 * configuration must not be taken for the end of the file.
 */
public class Github1455ModelConfigTest {

	@Rule
	public final TemporaryFolder folder = new TemporaryFolder();

	private ModelConfig parse(final String contents) throws IOException {
		final File cfg = folder.newFile("Github1455.cfg");
		Files.write(cfg.toPath(), contents.getBytes(StandardCharsets.UTF_8));
		final ModelConfig config = new ModelConfig(cfg.getAbsolutePath(), null);
		config.parse();
		return config;
	}

	private void assertLexicalError(final String contents) throws IOException {
		try {
			parse(contents);
			fail("Expected a ConfigFileException for a configuration with a lexical error:\n" + contents);
		} catch (ConfigFileException e) {
			assertEquals(EC.CFG_LEXICAL_ERROR, e.errorCode);
		}
	}

	private void assertLexicalError(final String contents, final int line) throws IOException {
		try {
			parse(contents);
			fail("Expected a ConfigFileException for a configuration with a lexical error:\n" + contents);
		} catch (ConfigFileException e) {
			assertEquals(EC.CFG_LEXICAL_ERROR, e.errorCode);
			assertTrue("Expected the error to be reported at line " + line + ", but got: " + e.getMessage(),
					e.getMessage().contains("at line " + line));
		}
	}

	@Test
	public void testControlWithoutLexicalError() throws IOException {
		final ModelConfig config = parse("INIT Init\nNEXT Next\nCHECK_DEADLOCK FALSE\nINVARIANT Never\n");
		assertEquals("Init", config.getInit());
		assertEquals("Next", config.getNext());
		final Vect<?> invariants = config.getInvariants();
		assertEquals(1, invariants.size());
		assertEquals("Never", invariants.elementAt(0));
	}

	@Test
	public void testControlTerminatedStringConstant() throws IOException {
		final ModelConfig config = parse("INIT Init\nNEXT Next\nCONSTANT N = \"abc\"\nINVARIANT Never\n");
		assertEquals(1, config.getConstants().size());
		assertEquals(1, config.getInvariants().size());
	}

	@Test
	public void testControlLineCommentWithoutTrailingNewline() throws IOException {
		final ModelConfig config = parse("INIT Init\nNEXT Next\nINVARIANT Never\n\\* INVARIANT Other");
		assertEquals(1, config.getInvariants().size());
	}

	@Test
	public void testUnterminatedStringBeforeInvariant() throws IOException {
		assertLexicalError("INIT Init\nNEXT Next\nCHECK_DEADLOCK FALSE\n\"unterminated\nINVARIANT Never\n", 4);
	}

	@Test
	public void testUnterminatedStringAtEndOfFile() throws IOException {
		assertLexicalError("INIT Init\nNEXT Next\nINVARIANT Never\n\"unterminated\n");
	}

	@Test
	public void testUnterminatedStringInsideInvariantList() throws IOException {
		assertLexicalError("INIT Init\nNEXT Next\nINVARIANT Inv \"unterminated\nPROPERTY Prop\n", 3);
	}

	@Test
	public void testUnterminatedStringBeforeInit() throws IOException {
		assertLexicalError("\"unterminated\nINIT Init\nNEXT Next\n", 1);
	}

	@Test
	public void testIllegalCharacterBeforeInvariant() throws IOException {
		assertLexicalError("INIT Init\nNEXT Next\n`\nINVARIANT Never\n", 3);
	}

	@Test
	public void testUnterminatedBlockCommentBeforeInvariant() throws IOException {
		assertLexicalError("INIT Init\nNEXT Next\n(* unterminated\nINVARIANT Never\n");
	}

	@Test
	public void testUnterminatedStringConstantValue() throws IOException {
		assertLexicalError("INIT Init\nNEXT Next\nCONSTANT N = \"abc\nINVARIANT Never\n", 3);
	}

	@Test
	public void testUnterminatedStringInConstantSet() throws IOException {
		assertLexicalError("INIT Init\nNEXT Next\nCONSTANT N = {1, \"a\nINVARIANT Never\n", 3);
	}

	@Test
	public void testIllegalCharacterAfterConstant() throws IOException {
		assertLexicalError("INIT Init\nNEXT Next\nCONSTANT N = 1\n`\nINVARIANT Never\n", 4);
	}
}
