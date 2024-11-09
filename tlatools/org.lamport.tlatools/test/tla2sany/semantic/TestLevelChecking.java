package tla2sany.semantic;

import java.nio.charset.StandardCharsets;
import java.io.InputStream;
import java.io.ByteArrayInputStream;

import org.junit.Test;
import org.junit.Assert;

import tla2sany.parser.TLAplusParser;
import tla2sany.st.TreeNode;

/**
 * Some basic tests for the level-checking process.
 */
public class TestLevelChecking {

  /**
   * A test case for the level-checker.
   */
  private static class LevelCheckingTestCase {

    /**
     * Interpolate expressions into this string to form semantically-valid
     * TLA+ parse inputs.
     */
    private static final String INPUT_FORMAT_STRING =
      "---- MODULE Test ----\n" +
      "CONSTANT c\n" +
      "VARIABLE x\n" +
      "op == %s\n" +
      "====";

    /**
     * The string parse input.
     */
    public final String Input;

    /**
     * The expected level-checking result on the input.
     */
    public final boolean ExpectedLevelCheckingResult;

    /**
     * Initializes a new instance of the {@link LevelCheckingTestCase} class.
     *
     * @param input The parse input, as a module body.
     * @param expected The expected level-checking result on the input.
     */
    public LevelCheckingTestCase(String input, boolean expected) {
      this.Input = String.format(INPUT_FORMAT_STRING, input);
      this.ExpectedLevelCheckingResult = expected;
    }

    /**
     * Summarize this test for error reporting purposes.
     *
     * @param log The semantic & level-checker error log.
     * @return A string summary of the test and its result.
     */
    public String summarize(Errors log) {
      return String.format(
        "Input:\n%s\nLog:\n%s",
        this.Input, log.toString());
    }
  }

  /**
   * A corpus of tests for the level-checker.
   */
  private static final LevelCheckingTestCase[] TestCases = new LevelCheckingTestCase[] {

    /**
     * Before some refactoring to remove the config.jj parser that
     * initialized the various built-in operators and their levels, the \lnot
     * operator (logical negation) also had its synonym \neg initialized as a
     * built-in operator. Theoretically this should not be necessary, since
     * operator synonym resolution should happen before any operator details
     * are fetched. Here we test whether that hypothesis is true.
     */
    new LevelCheckingTestCase("\\neg c",         true),

    /**
     * Also during the work to remove config.jj, it was found that the dot .
     * record access operator did not have its level constraints set. This
     * was eventually found to not be an issue because it had its constraints
     * set as $RcdSelect instead the "." representation. Here we test that
     * this hypothesis is true. For further info, see this issue:
     * https://github.com/tlaplus/tlaplus/issues/1008
     */
    new LevelCheckingTestCase("c.foo",           true),

    /**
     * This is another test of the dot record access operator to ensure it is
     * actually possible to go beyond its level constraints, so they are set
     * appropriately.
     */
    new LevelCheckingTestCase("([]c).foo",       false),

    /**
     * Various tests to increase coverage of {@link OpApplNode} level-
     * checking, especially with regard to temporal operators and their
     * unicode equivalents.
     */
    // Constant-level parameters
    new LevelCheckingTestCase("[]c",             true),
    new LevelCheckingTestCase("□c",              true),
    new LevelCheckingTestCase("<>c",             true),
    new LevelCheckingTestCase("◇c",              true),

    // Variable-level parameters
    new LevelCheckingTestCase("[]x",             true),
    new LevelCheckingTestCase("□x",              true),
    new LevelCheckingTestCase("<>x",             true),
    new LevelCheckingTestCase("◇x",              true),

    // Action-level parameters
    new LevelCheckingTestCase("[](x')",          false),
    new LevelCheckingTestCase("□(x')",           false),
    new LevelCheckingTestCase("<>(x')",          false),
    new LevelCheckingTestCase("◇(x')",           false),
    new LevelCheckingTestCase("[][c]_x",         true),
    new LevelCheckingTestCase("□[c]_x",          true),
    new LevelCheckingTestCase("[]<<c>>_x",       false),
    new LevelCheckingTestCase("□⟨c⟩_x",          false),
    new LevelCheckingTestCase("<><<c>>_x",       true),
    new LevelCheckingTestCase("◇⟨c⟩_x",          true),
    new LevelCheckingTestCase("<>[c]_x",         false),
    new LevelCheckingTestCase("◇[c]_x",          false),

    // Leads-to and plus-arrow
    new LevelCheckingTestCase("c ~> c",          true),
    new LevelCheckingTestCase("x' ~> c",         false),
    new LevelCheckingTestCase("c ~> x'",         false),
    new LevelCheckingTestCase("c ↝ c",           true),
    new LevelCheckingTestCase("x' ↝ c",          false),
    new LevelCheckingTestCase("c ↝ x'",          false),
    new LevelCheckingTestCase("c -+-> c",        true),
    new LevelCheckingTestCase("x' -+-> c",       false),
    new LevelCheckingTestCase("c -+-> x'",       false),
    new LevelCheckingTestCase("c ⇸ c",           true),
    new LevelCheckingTestCase("x' ⇸ c",          false),
    new LevelCheckingTestCase("c ⇸ x'",          false),

    // Infix ops can have temporal or action but not both
    new LevelCheckingTestCase("c /\\ c",         true),
    new LevelCheckingTestCase("c ∧ c",           true),
    new LevelCheckingTestCase("x /\\ c",         true),
    new LevelCheckingTestCase("x ∧ c",           true),
    new LevelCheckingTestCase("[]c /\\ c",       true),
    new LevelCheckingTestCase("□c ∧ c",          true),
    new LevelCheckingTestCase("c /\\ x'",        true),
    new LevelCheckingTestCase("c ∧ x'",          true),
    new LevelCheckingTestCase("[]c /\\ x'",      false),
    new LevelCheckingTestCase("□c ∧ x'",         false),

    // Quantifiers & temporal formulas
    new LevelCheckingTestCase("∀ v ∈ c  : v",    true),
    new LevelCheckingTestCase("∃ v ∈ x  : v",    true),
    new LevelCheckingTestCase("∀ v ∈ x' : v",    true),
    new LevelCheckingTestCase("∃ v ∈ x  : □v",   true),
    new LevelCheckingTestCase("∀ v ∈ x' : □v",   false),
    new LevelCheckingTestCase("∃ v ∈ □x : v",    false),
  };

  /**
   * Checks the syntax of the given input and builds a parse tree from it.
   *
   * @param input The string input to parse.
   * @return A parse tree.
   */
  private static TreeNode checkSyntax(String input) {
    byte[] inputBytes = input.getBytes(StandardCharsets.UTF_8);
    InputStream inputStream = new ByteArrayInputStream(inputBytes);
    TLAplusParser parser = new TLAplusParser(inputStream, StandardCharsets.UTF_8.name());
    Assert.assertTrue(input, parser.parse());
    return parser.rootNode();
  }

  /**
   * Performs semantic checking & reference resolution on a parse tree.
   *
   * @param parseTree The parse tree to check.
   * @param log The error log.
   * @return A parse tree annotated with semantic information.
   */
  private static ModuleNode checkSemantic(TreeNode parseTree, Errors log) {
    Context.reInit();
    Generator gen = new Generator(null, log);
    SemanticNode.setError(log);
    ModuleNode semanticTree = null;
    try {
      semanticTree = gen.generate(parseTree);
    } catch (AbortException e) {
      Assert.fail(e.toString() + log.toString());
    }
    Assert.assertTrue(log.toString(), log.isSuccess());
    Assert.assertNotNull(log.toString(), semanticTree);
    return semanticTree;
  }

  /**
   * Runs the level-checking algorithm on a semantic tree.
   *
   * @param semanticTree The semantic tree to level-check.
   * @return Whether level checking succeeded.
   */
  private static boolean checkLevel(ModuleNode semanticTree) {
    return semanticTree.levelCheck(1);
  }

  /**
   * Runs all level-checker tests in the corpus.
   */
  @Test
  public void testAll() {
    for (LevelCheckingTestCase testCase : TestLevelChecking.TestCases) {
      Errors log = new Errors();
      TreeNode parseTree = checkSyntax(testCase.Input);
      ModuleNode semanticTree = checkSemantic(parseTree, log);
      boolean actualLevelCheckingResult = checkLevel(semanticTree);
      Assert.assertEquals(testCase.summarize(log), log.isSuccess(), actualLevelCheckingResult);
      Assert.assertEquals(testCase.summarize(log), testCase.ExpectedLevelCheckingResult, actualLevelCheckingResult);
    }
  }
}