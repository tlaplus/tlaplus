package tlc2.debug;

import util.ParserAPI;
import util.UniqueString;

import java.util.HashSet;
import java.util.List;
import java.util.Set;

import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameter;
import org.junit.runners.Parameterized.Parameters;
import org.junit.Assert;

import tla2sany.semantic.ModuleNode;
import tla2sany.st.Location;

/**
 * {@link TLCBreakpointExpression#getScopedIdentifiers(ModuleNode, Location)}
 * tests, to check that various nested TLA+ syntax constructs have their
 * introduced identifiers appropriately recorded.
 */
@RunWith(Parameterized.class)
public class GetScopedIdentifiersTests {

  private static class TestCase {
    public final String input;
    public final String terminator;
    public final Set<String> expected;
    public TestCase(String input, String terminator, String... expected) {
      this.input = input;
      this.terminator = terminator;
      this.expected = new HashSet<String>(List.of(expected));
    }
    public String toString() {
    	return this.input;
    }
  }

  /**
   * A wrapper in which to interpolate test cases to form a valid module.
   */
  private static final String wrapper =
    "---- MODULE Test ----\n"
    + "VARIABLE x\n"
    + "CONSTANT y\n"
    + "%s\n"
    + "TRUE%s\n"
    + "====";

  /**
   * The location of the expression TRUE in the wrapper. This assumes that
   * each test case input is a single line.
   */
  private static final Location location
    = new Location(UniqueString.of("Test"), 5, 1, 5, 2);

  /**
   * A set of test cases for finding scoped identifiers. Each input should
   * consist of an incomplete operator definition & expression that can be
   * terminated by expression TRUE located at the start of the next line,
   * along with a variable-length list of identifiers accessible at the
   * point of the TRUE expression. A terminator to be appended after TRUE is
   * also accepted - for example ⟩ or ) or ] or }.
   */
  @Parameters(name = "{0}")
  public static TestCase[] testCases() {
    return new TestCase[] {
      new TestCase("op ≜", ""),
      new TestCase("op(i, j, k) ≜", "", "j", "i", "k"),
      new TestCase("op(i) ≜ ∀ j ∈ {} :", "", "i", "j"),
      new TestCase("op ≜ ∀ i, j ∈ {} :", "", "i", "j"),
      new TestCase("op ≜ ∀ ⟨i, j, k⟩ ∈ {} :", "", "i", "j", "k"),
      new TestCase("op(i, j) ≜ LET k == TRUE l == TRUE IN", "", "i", "j", "k", "l"),
      new TestCase("op ≜ LET i(j, k) == ", " IN TRUE", "i", "j", "k"),
      new TestCase("op ≜ LET RECURSIVE i i == TRUE IN", "", "i"),
      new TestCase("op ≜ LET i == TRUE j ==", " IN TRUE", "i", "j"),
      new TestCase("op(i) ≜ [j, k ∈ {} ↦", "]", "i", "j", "k"),
      new TestCase("op ≜ [⟨i, j, k⟩ ∈ {} ↦", "]", "i", "j", "k"),
      new TestCase("op(i, j) ≜ {k ∈ {} :", "}", "i", "j", "k"),
      new TestCase("RECURSIVE op(_, _) op(f(_,_), i) ≜ op(LAMBDA j, k : ", ", TRUE)", "f", "i", "j", "k"),
      new TestCase("op ≜ {⟨i, j, k⟩ ∈ {} : ", "}", "i", "j", "k"),
      new TestCase("op(i) ≜ {j ∈ {} : ", "}", "i", "j"),
      new TestCase("op ≜ {", ": i, j ∈ {}}", "i", "j"),
      new TestCase("op ≜ {", ": ⟨i, j, k⟩ ∈ {}}", "i", "j", "k"),
      // This is a bug that needs to be fixed! More likely this will get fixed
      // when support is added to the semantic checker to introduce "ghost"
      // expressions at arbitrary points in the semantic tree, rendering all
      // of this functionality redundant.
      new TestCase("op(_+_) ≜", "", "+"),
    };
  }

  @Parameter
  public TestCase testCase;

  /**
   * Run all the test cases and check the identifiers are found as expected.
   */
  @Test
  public void test() {
    String input = String.format(wrapper, testCase.input, testCase.terminator);
    ModuleNode parsed = ParserAPI.parse(input);
    Assert.assertNotNull(parsed);
    Assert.assertEquals(1, parsed.getOpDefs().length);
    Set<String> actual = TLCBreakpointExpression.getScopedIdentifiers(parsed, location);
    Assert.assertEquals(testCase.expected, actual);
  }
}