/*******************************************************************************
 * Copyright (c) 2026 The Linux Foundation. All rights reserved.
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
 ******************************************************************************/
package tla2sany.xml;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;

import org.junit.Assert;
import org.junit.Test;

import tla2sany.semantic.SemanticErrorCorpusTests;

/**
 * Tests to provoke various {@link XMLExporterExitCode} values, checking both
 * the {@link XMLExporter#run} and {@link XMLExporter#moduleToXML(String...)}
 * methods.
 */
public class TestXMLExporterErrors {

  @Test
  public void testHelpReturnsOk() {
    try {
      XMLExporter.moduleToXML("-help");
    } catch (XMLExportingException e) {
      Assert.fail();
    }

    final int actual = XMLExporter.run("-help");
    Assert.assertEquals(XMLExporterExitCode.OK, XMLExporterExitCode.fromCode(actual));
  }

  @Test
  public void testNoArgs() {
    try {
      XMLExporter.moduleToXML();
      Assert.fail();
    } catch (XMLExportingException e) {
      Assert.assertEquals(XMLExporterExitCode.ARGS_PARSING_FAILURE, e.code());
    }

    final int actual = XMLExporter.run();
    Assert.assertEquals(XMLExporterExitCode.ARGS_PARSING_FAILURE, XMLExporterExitCode.fromCode(actual));
  }

  @Test
  public void testIncludeDirWithoutSpec() {
    try {
      XMLExporter.moduleToXML("-I", "SomeDir");
      Assert.fail();
    } catch (XMLExportingException e) {
      Assert.assertEquals(XMLExporterExitCode.ARGS_PARSING_FAILURE, e.code());
    }

    final int actual = XMLExporter.run("-I", "SomeDir");
    Assert.assertEquals(XMLExporterExitCode.ARGS_PARSING_FAILURE, XMLExporterExitCode.fromCode(actual));
  }

  @Test
  public void testCannotFindSpec() {
    try {
      XMLExporter.moduleToXML("ThisModuleDoesNotExist.tla");
      Assert.fail();
    } catch (XMLExportingException e) {
      Assert.assertEquals(XMLExporterExitCode.SPEC_PARSING_FAILURE, e.code());
    }

    final int actual = XMLExporter.run("ThisModuleDoesNotExist.tla");
    Assert.assertEquals(XMLExporterExitCode.SPEC_PARSING_FAILURE, XMLExporterExitCode.fromCode(actual));
  }

  @Test
  public void testSpecParseFailure() throws IOException {
    final String modulePath = SemanticErrorCorpusTests.getTestFiles().get(0).modulePath.toString();
    try {
      XMLExporter.moduleToXML(modulePath);
      Assert.fail();
    } catch (XMLExportingException e) {
      Assert.assertEquals(XMLExporterExitCode.SPEC_PARSING_FAILURE, e.code());
    }

    final int actual = XMLExporter.run(modulePath);
    Assert.assertEquals(XMLExporterExitCode.SPEC_PARSING_FAILURE, XMLExporterExitCode.fromCode(actual));
  }

  /**
   * Writes a module with the given body to a temporary file, naming the module
   * after the file. The modules of the tests below hold characters that are
   * hostile to editors and diffs, so they are generated instead of checked in.
   *
   * @param body The body of the module.
   * @return The path of the module file.
   */
  private static String writeModule(final String body) throws IOException {
    final Path file = Files.createTempFile("SanyTest", ".tla");
    final String fileName = file.getFileName().toString();
    final String moduleName = fileName.substring(0, fileName.length() - ".tla".length());
    Files.writeString(file, String.format("---- MODULE %s ----\n%s\n====\n", moduleName, body));
    return file.toString();
  }

  /**
   * Asserts that exporting the module with the given body is rejected because
   * XML cannot represent one of its characters, and that the error names the
   * character so that the user can find it.
   *
   * @param body The body of the module to export.
   */
  private static void assertUnrepresentableCharacter(final String body) throws IOException {
    final String modulePath = writeModule(body);
    try {
      XMLExporter.moduleToXML(modulePath);
      Assert.fail();
    } catch (XMLExportingException e) {
      Assert.assertEquals(XMLExporterExitCode.XML_UNREPRESENTABLE_CHARACTER, e.code());
      Assert.assertFalse(e.code().isBug());
      Assert.assertTrue(e.getMessage(), e.getMessage().contains("U+0000"));
    }

    final int actual = XMLExporter.run(modulePath);
    Assert.assertEquals(
        XMLExporterExitCode.XML_UNREPRESENTABLE_CHARACTER,
        XMLExporterExitCode.fromCode(actual));
  }

  /**
   * No version of XML can represent a null character, not even as a numeric
   * character reference, so a spec containing one has to be rejected. Before,
   * the serializer failed on it and the exporter asked the user to report a
   * bug in itself. SANY has no escape denoting a null character, so it can
   * only enter a string literal as a raw character in the source.
   */
  @Test
  public void testNullCharacterInStringLiteral() throws IOException {
    assertUnrepresentableCharacter("op == \"a\u0000b\"");
  }

  /**
   * A null character in a comment used to be worse than one in a string
   * literal: the export succeeded, but wrote the character as the reference
   * &#0; that no parser accepts, so the exporter silently produced a document
   * nobody can read.
   */
  @Test
  public void testNullCharacterInComment() throws IOException {
    assertUnrepresentableCharacter("\\* comment a\u0000b\nop == 1");
  }
}
