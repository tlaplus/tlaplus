package tla2sany.xml;

import java.io.ByteArrayOutputStream;
import java.io.PrintStream;

import org.junit.After;
import org.junit.Assert;
import org.junit.Before;
import org.junit.Test;

import util.ToolIO;

public class TestXMLExporterHelpText {

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

  private String getHelpText() {
    ByteArrayOutputStream out = new ByteArrayOutputStream();
    XMLExporter.printUsage(new PrintStream(out));
    return out.toString();
  }

  @Test
  public void testPrintHelpText() throws XMLExportingException {
    Assert.assertEquals(0, XMLExporter.run("-help"));
    String out = this.outStream.toString();
    String err = this.errStream.toString();
    Assert.assertNotEquals(out, 0, out.length());
    Assert.assertTrue(out, out.contains(getHelpText()));
    Assert.assertEquals(err, 0, err.length());
  }

  @Test
  public void testPrintHelpTextOnNoArgs() throws XMLExportingException {
    Assert.assertEquals(1, XMLExporter.run());
    String out = this.outStream.toString();
    String err = this.errStream.toString();
    Assert.assertEquals(out, 0, out.length());
    Assert.assertNotEquals(err, 0, err.length());
    Assert.assertTrue(err, err.contains(getHelpText()));
  }

  @Test
  public void testPrintHelpTextOnUnknownArg() throws XMLExportingException {
    Assert.assertEquals(1, XMLExporter.run("-InvalidArg"));
    String out = this.outStream.toString();
    String err = this.errStream.toString();
    Assert.assertEquals(out, 0, out.length());
    Assert.assertNotEquals(err, 0, err.length());
    Assert.assertTrue(err, err.contains(getHelpText()));
  }

  @Test
  public void testPrintHelpTextOnNonexistentFile() throws XMLExportingException {
    Assert.assertEquals(1, XMLExporter.run("DoesNotExist.tla"));
    String out = this.outStream.toString();
    String err = this.errStream.toString();
    Assert.assertEquals(out, 0, out.length());
    Assert.assertNotEquals(err, 0, err.length());
    Assert.assertTrue(err, err.contains(getHelpText()));
  }
}