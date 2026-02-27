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

import java.io.File;

import org.junit.Assert;
import org.junit.Test;

import tla2sany.semantic.ExternalModuleTable;

/**
 * Regression test for {@link XMLExporter} handling of {@link tla2sany.semantic.DecimalNode}
 * instances; previously, it would result in a XML schema validation failure.
 */
public class TestDecimalXMLExport {

	private static final String BASE_DIR = System.getProperty("basedir", System.getProperty("user.dir", "."));
	private static final String TEST_MODEL = "test-model" + File.separator;
	private static final String BASE_PATH = System.getProperty("basepath", BASE_DIR + File.separator + TEST_MODEL);

  @Test
  public void test() throws XMLExportingException {
    final ExternalModuleTable emt = XMLExporter.parseSpec(BASE_PATH + "Decimal.tla");
    final String output = XMLExporter.specToXMLString(emt, false, false, false, false);
    Assert.assertTrue(output.contains("<integralPart>000123</integralPart>"));
    Assert.assertTrue(output.contains("<fractionalPart>456000</fractionalPart>"));
  }
}
