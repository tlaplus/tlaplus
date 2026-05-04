package tla2sany.drivers;

import java.nio.file.Path;
import java.nio.file.Paths;

import org.junit.Assert;
import org.junit.Test;

import tlc2.tool.CommonTestCase;
import util.TestPrintStream;
import util.ToolIO;

/**
 * Test the relative precedences of SANY's various methods of searching for
 * an EXTENDed or INSTANCEd module.
 */
public class IncludeDirPrecedenceTest {

  private static final Path SPEC_DIR = Paths.get(CommonTestCase.BASE_DIR).resolve("test/tla2sany/drivers/");
  private static final Path SPEC_SUBDIR = SPEC_DIR.resolve("include/");
  private static final Path SPEC_SUBDIR_OTHER = SPEC_DIR.resolve("other/");
  private static final Path SPEC_PATH = SPEC_DIR.resolve("IncludeDirPrecedenceTest.tla");
  private static final String EXTENDED_SPEC_NAME = "IncludeDirPrecedenceTestTarget.tla";
  private static final Path EXTENDED_SPEC_PATH_SAME_DIR = SPEC_DIR.resolve(EXTENDED_SPEC_NAME);
  private static final Path EXTENDED_SPEC_PATH_SUBDIR = SPEC_SUBDIR.resolve(EXTENDED_SPEC_NAME);
  private static final Path PROPERTY_SPEC_PATH = SPEC_DIR.resolve("TlaLibraryPropertyTest.tla");
  private static final Path EXTENDED_PROPERTY_SPEC_PATH = SPEC_SUBDIR.resolve("TlaLibraryPropertyTestTarget.tla");
  private static final Path EXTENDED_PROPERTY_SPEC_PATH_OTHER = SPEC_SUBDIR_OTHER.resolve("TlaLibraryPropertyTestTarget.tla");
  
  private static void setOrClear(String key, String value) {
		if (null == value) {
		  System.clearProperty(key);
		} else {
		  System.setProperty(key, value);
		}
  }

  /**
   * Without any specified include dirs, SANY should find the module in the
   * same directory as the base module.
   */
  @Test
  public void testNoIncludeDir() throws SANYExitException {
    final TestPrintStream out = new TestPrintStream();
    ToolIO.out = out;
		SANY.SANYmain0(new String[] {SPEC_PATH.toString()});
		out.assertContains(SPEC_PATH.toString());
		out.assertContains(EXTENDED_SPEC_PATH_SAME_DIR.toString());
		out.assertNoSubstring(EXTENDED_SPEC_PATH_SUBDIR.toString());
  }
  
  /**
   * Baseline test to ensure below tests are actually testing what we think:
   * ensure SANY cannot find a spec in the include dir by default.
   */
  @Test
  public void testCannotFindSpec() {
    final TestPrintStream out = new TestPrintStream();
    ToolIO.out = out;
    try {
      SANY.SANYmain0(new String[] {PROPERTY_SPEC_PATH.toString()});
      Assert.fail();
    } catch (SANYExitException e) {
      Assert.assertEquals(SanyExitCode.ERROR, e.getEnumeratedExitCode());
      out.assertContains(PROPERTY_SPEC_PATH.toString());
    }
  }
 
  /**
   * Tests that SANY will resolve specs in the CWD. This resolves the error
   * in the {@link IncludeDirPrecedenceTest#testCannotFindSpec()} test.
   */
  @Test
  public void testUserDir() throws SANYExitException {
    final String oldUserDir = ToolIO.getUserDir();
    final String oldUserDirProp = System.getProperty("user.dir");

    final TestPrintStream out = new TestPrintStream();
    ToolIO.out = out;
    ToolIO.setUserDir(SPEC_SUBDIR.toString());
    System.setProperty("user.dir", SPEC_SUBDIR.toString());

		SANY.SANYmain0(new String[] {PROPERTY_SPEC_PATH.toString()});

		out.assertContains(PROPERTY_SPEC_PATH.toString());
		out.assertContains(EXTENDED_PROPERTY_SPEC_PATH.toString());

		ToolIO.setUserDir(oldUserDir);
		setOrClear("user.dir", oldUserDirProp);
  }

  /**
   * SANY should find an imported module if it is on the TLA-Library system
   * property list of search paths. This resolves the error in the
   * {@link IncludeDirPrecedenceTest#testCannotFindSpec()} test.
   */
  @Test
  public void testTlaLibraryProperty() throws SANYExitException {
    final String oldProperty = System.getProperty("TLA-Library");

    final TestPrintStream out = new TestPrintStream();
    ToolIO.out = out;
    System.setProperty("TLA-Library", SPEC_SUBDIR.toString());

		SANY.SANYmain0(new String[] {PROPERTY_SPEC_PATH.toString()});

		out.assertContains(PROPERTY_SPEC_PATH.toString());
		out.assertContains(EXTENDED_PROPERTY_SPEC_PATH.toString());
		
		setOrClear("TLA-Library", oldProperty);
  }

  /**
   * Even when the TLA-Library property is defined, specs in the same dir as
   * the base module take precedence over it.
   */
  @Test
  public void testTlaLibraryPropertyOverruled() throws SANYExitException {
    final String oldProperty = System.getProperty("TLA-Library");

    final TestPrintStream out = new TestPrintStream();
    ToolIO.out = out;
    System.setProperty("TLA-Library", SPEC_SUBDIR.toString());

		SANY.SANYmain0(new String[] {SPEC_PATH.toString()});

		out.assertContains(SPEC_PATH.toString());
		out.assertContains(EXTENDED_SPEC_PATH_SAME_DIR.toString());
		out.assertNoSubstring(EXTENDED_SPEC_PATH_SUBDIR.toString());

		setOrClear("TLA-Library", oldProperty);
  }

  /**
   * When running SANY from a particular directory, specs found in the
   * TLA-Library property should take precedence over specs found in the CWD.
   */
  @Test
  public void testUserDirOverruledByTlaLibraryProperty() throws SANYExitException {
    final String oldTlaLibProp = System.getProperty("TLA-Library");
    final String oldUserDir = ToolIO.getUserDir();
    final String oldUserDirProp = System.getProperty("user.dir");

    final TestPrintStream out = new TestPrintStream();
    ToolIO.out = out;
    System.setProperty("TLA-Library", SPEC_SUBDIR_OTHER.toString());
    ToolIO.setUserDir(SPEC_SUBDIR.toString());
    System.setProperty("user.dir", SPEC_SUBDIR.toString());

		SANY.SANYmain0(new String[] {PROPERTY_SPEC_PATH.toString()});

		out.assertContains(PROPERTY_SPEC_PATH.toString());
		out.assertContains(EXTENDED_PROPERTY_SPEC_PATH_OTHER.toString());
		out.assertNoSubstring(EXTENDED_SPEC_PATH_SUBDIR.toString());

		setOrClear("user.dir", oldUserDirProp);
		ToolIO.setUserDir(oldUserDir);
		setOrClear("TLA-Library", oldTlaLibProp);
  }
}
