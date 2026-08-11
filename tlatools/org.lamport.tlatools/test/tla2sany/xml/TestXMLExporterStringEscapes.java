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
 ******************************************************************************/
package tla2sany.xml;

import java.io.ByteArrayOutputStream;
import java.io.File;
import java.io.PrintStream;
import java.io.StringReader;

import javax.xml.parsers.DocumentBuilder;
import javax.xml.parsers.DocumentBuilderFactory;

import org.junit.After;
import org.junit.Assert;
import org.junit.Before;
import org.junit.Test;
import org.w3c.dom.Document;
import org.w3c.dom.NodeList;
import org.xml.sax.InputSource;

import tlc2.tool.CommonTestCase;
import util.ToolIO;

/**
 * The XML exporter writes the value of a string literal to the XML output
 * after TLA⁺ escape sequences in it have been resolved; the escapes are in
 * fact resolved by the parser, which overwrites the source text of the
 * literal, so the value is the only representation of it that survives. XML
 * 1.0 character data cannot hold most control characters - not even as
 * numeric character references - so a spec containing the \f escape (form
 * feed, U+000C) cannot be exported at all, and is rejected with
 * {@link XMLExporterExitCode#XML_UNREPRESENTABLE_CHARACTER}.
 *
 * This reproducer was found while running the standardized TLA⁺ syntax corpus
 * (also present in test/tla2sany/corpus) through SANY as part of the work to
 * use SANY as TLAPM's parser backend; see
 * https://github.com/tlaplus/tlapm/pull/275#issuecomment-5241074153 and the
 * XML output format tracking issue
 * https://github.com/tlaplus/tlaplus/issues/1313
 */
public class TestXMLExporterStringEscapes {

  private static final String MODULE_DIR =
      CommonTestCase.BASE_PATH + "sany" + File.separator;

  private final PrintStream toolOut = ToolIO.out;
  private final PrintStream toolErr = ToolIO.err;
  private final ByteArrayOutputStream outStream = new ByteArrayOutputStream();
  private final ByteArrayOutputStream errStream = new ByteArrayOutputStream();

  @Before
  public void captureOutput() {
    ToolIO.out = new PrintStream(this.outStream);
    ToolIO.err = new PrintStream(this.errStream);
  }

  @After
  public void restoreOutput() {
    ToolIO.out = this.toolOut;
    ToolIO.err = this.toolErr;
  }

  /**
   * Exports the given module and returns the sole exported string literal
   * value, failing the test if the export did not succeed.
   *
   * @param moduleName The name of a module in the test-model/sany directory.
   * @return The text content of the module's only StringValue element.
   */
  private String exportSoleStringValue(final String moduleName) throws Exception {
    final int actual = XMLExporter.run(MODULE_DIR + moduleName + ".tla");
    Assert.assertEquals(
        this.errStream.toString(),
        XMLExporterExitCode.OK,
        XMLExporterExitCode.fromCode(actual));
    final DocumentBuilderFactory factory = DocumentBuilderFactory.newInstance();
    factory.setNamespaceAware(true);
    final DocumentBuilder builder = factory.newDocumentBuilder();
    final Document doc = builder.parse(new InputSource(new StringReader(this.outStream.toString())));
    final NodeList values = doc.getElementsByTagName("StringValue");
    Assert.assertEquals(1, values.getLength());
    return values.item(0).getTextContent();
  }

  /**
   * The escape sequences that XML 1.0 can represent are exported with their
   * escapes resolved, so this is also a record of the exporter's current
   * (lossy) treatment of string literals: the source-level escape structure
   * is not recoverable from the XML.
   */
  @Test
  public void testSupportedStringEscapes() throws Exception {
    Assert.assertEquals("\\ \n \r \t \"", exportSoleStringValue("StringEscapes"));
  }

  /**
   * SANY parses the \f escape but cannot export the form feed it denotes, so
   * the spec is rejected instead of exported. Declaring XML 1.1, which can
   * represent the character as a reference, would not help: neither xmlm - the
   * parser TLAPM reads the export with - nor expat accepts such a reference
   * whichever version the document declares, so the failure would only move
   * into the consumer. Being able to export the spec needs the representation
   * of string values to change; see the tracking issue named above.
   */
  @Test
  public void testFormFeedStringEscapeIsRejected() {
    final String modulePath = MODULE_DIR + "StringFormFeedEscape.tla";
    try {
      XMLExporter.moduleToXML(modulePath);
      Assert.fail();
    } catch (XMLExportingException e) {
      Assert.assertEquals(XMLExporterExitCode.XML_UNREPRESENTABLE_CHARACTER, e.code());
      Assert.assertTrue(e.getMessage(), e.getMessage().contains("U+000C"));
    }

    Assert.assertEquals(
        XMLExporterExitCode.XML_UNREPRESENTABLE_CHARACTER,
        XMLExporterExitCode.fromCode(XMLExporter.run(modulePath)));
  }
}
