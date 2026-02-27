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

    try {
      final int actual = XMLExporter.run("-help");
      Assert.assertEquals(XMLExporterExitCode.OK, XMLExporterExitCode.fromCode(actual));
    } catch (XMLExportingException e) {
      Assert.fail();
    }
  }

  @Test
  public void testNoArgs() {
    try {
      XMLExporter.moduleToXML();
      Assert.fail();
    } catch (XMLExportingException e) {
      Assert.assertEquals(XMLExporterExitCode.ARGS_PARSING_FAILURE, e.code());
    }

    try {
      final int actual = XMLExporter.run();
      Assert.assertEquals(XMLExporterExitCode.ARGS_PARSING_FAILURE, XMLExporterExitCode.fromCode(actual));
    } catch (XMLExportingException e) {
      Assert.fail();
    }
  }
  
  @Test
  public void testIncludeDirWithoutSpec() {
    try {
      XMLExporter.moduleToXML("-I", "SomeDir");
      Assert.fail();
    } catch (XMLExportingException e) {
      Assert.assertEquals(XMLExporterExitCode.ARGS_PARSING_FAILURE, e.code());
    }

    try {
      final int actual = XMLExporter.run("-I", "SomeDir");
      Assert.assertEquals(XMLExporterExitCode.ARGS_PARSING_FAILURE, XMLExporterExitCode.fromCode(actual));
    } catch (XMLExportingException e) {
      Assert.fail();
    }
  }

  @Test
  public void testCannotFindSpec() {
    try {
      XMLExporter.moduleToXML("ThisModuleDoesNotExist.tla");
      Assert.fail();
    } catch (XMLExportingException e) {
      Assert.assertEquals(XMLExporterExitCode.SPEC_PARSING_FAILURE, e.code());
    }

    try {
      XMLExporter.run("ThisModuleDoesNotExist.tla");
      Assert.fail();
    } catch (XMLExportingException e) {
      Assert.assertEquals(XMLExporterExitCode.SPEC_PARSING_FAILURE, e.code());
    }
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

    try {
      XMLExporter.run(modulePath);
      Assert.fail();
    } catch (XMLExportingException e) {
      Assert.assertEquals(XMLExporterExitCode.SPEC_PARSING_FAILURE, e.code());
    }
  }
}
