package tla2sany.xml;

import java.io.ByteArrayOutputStream;
import java.io.File;
import java.io.PrintStream;

import org.junit.Assert;
import org.junit.Test;

import util.ToolIO;

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
    ByteArrayOutputStream out = new ByteArrayOutputStream();
    ToolIO.out = new PrintStream(out);
    Assert.assertEquals(0, XMLExporter.run(BASE_PATH + "Decimal.tla"));
    String output = out.toString();
    Assert.assertTrue(output.contains("<integralPart>000123</integralPart>"));
    Assert.assertTrue(output.contains("<fractionalPart>456000</fractionalPart>"));
  }
}
