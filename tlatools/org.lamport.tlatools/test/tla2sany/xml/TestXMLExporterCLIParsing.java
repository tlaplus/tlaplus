package tla2sany.xml;

import java.util.function.Supplier;

import org.junit.Assert;
import org.junit.Test;

import tla2sany.xml.XMLExporter.RunOptions;

public class TestXMLExporterCLIParsing {

  private static RunOptions parse(String... args) {
    return XMLExporter.parseArgs(args);
  }

  private static void assertThrows(Supplier<RunOptions> f) {
    try {
      f.get();
      Assert.fail();
    } catch (IllegalArgumentException e) {
      // Success
    }
  }

  @Test
  public void testBadCLIArgs() {
    assertThrows(() -> parse());
    assertThrows(() -> parse("Test.tla", "Test2.tla"));
    assertThrows(() -> parse("-I", "Test.tla"));
    assertThrows(() -> parse("Test.tla", "-I"));
    assertThrows(() -> parse("Test.tla", "-I", "dir_path", "-o", "Test2.tla"));
  }

  @Test
  public void testGoodCLIArgs() {
    String expectedTla = "Test.tla";

    RunOptions actual = parse(expectedTla);
    Assert.assertNotNull(actual);
    Assert.assertFalse(actual.OfflineMode);
    Assert.assertFalse(actual.PrettyPrint);
    Assert.assertEquals(0, actual.Include.length);
    Assert.assertEquals(expectedTla, actual.TlaFile);

    actual = parse("-h");
    Assert.assertNull(actual);

    actual = parse("-o", expectedTla);
    Assert.assertNotNull(actual);
    Assert.assertTrue(actual.OfflineMode);
    Assert.assertFalse(actual.PrettyPrint);
    Assert.assertEquals(0, actual.Include.length);
    Assert.assertEquals(expectedTla, actual.TlaFile);

    actual = parse(expectedTla, "-p");
    Assert.assertNotNull(actual);
    Assert.assertFalse(actual.OfflineMode);
    Assert.assertTrue(actual.PrettyPrint);
    Assert.assertEquals(0, actual.Include.length);
    Assert.assertEquals(expectedTla, actual.TlaFile);

    actual = parse("-p", expectedTla, "-o");
    Assert.assertNotNull(actual);
    Assert.assertTrue(actual.OfflineMode);
    Assert.assertTrue(actual.PrettyPrint);
    Assert.assertEquals(0, actual.Include.length);
    Assert.assertEquals(expectedTla, actual.TlaFile);

    actual = parse("-p", expectedTla, "-I", "dirname");
    Assert.assertNotNull(actual);
    Assert.assertFalse(actual.OfflineMode);
    Assert.assertTrue(actual.PrettyPrint);
    Assert.assertEquals(1, actual.Include.length);
    Assert.assertEquals(expectedTla, actual.TlaFile);

    actual = parse("-o", expectedTla, "-I", "dirname", "-I", "dirname2");
    Assert.assertNotNull(actual);
    Assert.assertTrue(actual.OfflineMode);
    Assert.assertFalse(actual.PrettyPrint);
    Assert.assertEquals(2, actual.Include.length);
    Assert.assertEquals("dirname", actual.Include[0]);
    Assert.assertEquals("dirname2", actual.Include[1]);
    Assert.assertEquals(expectedTla, actual.TlaFile);

    actual = parse("-o", expectedTla, "-I", "dirname", "-h", "-I", "dirname2");
    Assert.assertNull(actual);
  }
}