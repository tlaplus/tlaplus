/*******************************************************************************
 * Copyright (c) 2024 Linux Foundation. All rights reserved.
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
package tla2sany.semantic;

import java.io.IOException;
import java.nio.file.FileSystems;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.PathMatcher;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.Hashtable;
import java.util.List;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import java.util.stream.Collectors;

import org.junit.Assert;
import org.junit.Assume;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameter;
import org.junit.runners.Parameterized.Parameters;
import org.junit.Test;

import tla2sany.drivers.SANY;
import tla2sany.drivers.SemanticException;
import tla2sany.explorer.ExploreNode;
import tla2sany.explorer.ExplorerVisitor;
import tla2sany.modanalyzer.SpecObj;
import tla2sany.output.LogLevel;
import tla2sany.output.RecordedSanyOutput;
import tla2sany.parser.ParseException;
import tlc2.tool.CommonTestCase;
import util.FilenameToStream;
import util.SimpleFilenameToStream;

/**
 * Run all semantic corpus tests through SANY, testing its semantic analysis
 * and level checking. This is done in two ways:
 *
 * 1. For testing reference resolution, an operator RefersTo(op, id) is
 *    defined; the op is any identifier (an {@link OpApplNode}) referring to
 *    a definition. The id is a string used to identify the operator being
 *    referred to, by way of prepending a comment to that operator's
 *    definition containing a string ID.
 *
 * 2. For testing level-checking, an operator IsLevel(expr, level) is defined
 *    accepting an expression (which could be an operator reference or label)
 *    along with an assertion about its level.
 *
 * Both RefersTo and IsLevel are defined in a module Semantics.tla which is
 * included in the test corpus directory and resolved during parsing. The
 * test module is then searched to find all assertions, then their parameters
 * are analyzed to see whether the assertions are correct.
 */
@RunWith(Parameterized.class)
public class SemanticCorpusTests {

  private static class SemanticTestCase {
    public final Path ModulePath;
    public SemanticTestCase(Path modulePath) {
      this.ModulePath = modulePath;
    }
    // Used by JUnit to identify this test case.
    public String toString() {
      return this.ModulePath.getFileName().toString();
    }
  }

  private static class SemanticsModule {
    public final ExternalModuleTable Modules;
    public final OpDefNode RefersTo;
    public final OpDefNode IsLevel;
    public final OpDefNode ConstantLevel;
    public final OpDefNode VariableLevel;
    public final OpDefNode ActionLevel;
    public final OpDefNode TemporalLevel;
    public SemanticsModule(ExternalModuleTable modules) {
      this.Modules = modules;
      ModuleNode semanticsModule = modules.getModuleNode("Semantics");
      this.RefersTo = semanticsModule.getOpDef("RefersTo");
      this.IsLevel = semanticsModule.getOpDef("IsLevel");
      this.ConstantLevel = semanticsModule.getOpDef("ConstantLevel");
      this.VariableLevel = semanticsModule.getOpDef("VariableLevel");
      this.ActionLevel = semanticsModule.getOpDef("ActionLevel");
      this.TemporalLevel = semanticsModule.getOpDef("TemporalLevel");
    }
    public int getExpectedLevel(final SymbolNode level) {
      if (this.ConstantLevel == level) {
        return LevelConstants.ConstantLevel;
      } else if (this.VariableLevel == level) {
        return LevelConstants.VariableLevel;
      } else if (this.ActionLevel == level) {
        return LevelConstants.ActionLevel;
      } else if (this.TemporalLevel == level) {
        return LevelConstants.TemporalLevel;
      } else {
        throw new IllegalArgumentException("Not a level: " + level.getName());
      }
    }
    public List<OpApplNode> findRefersToAssertions() {
      return findAllReferences(this.Modules.getRootModule(), this.RefersTo);
    }
    public List<OpApplNode> findIsLevelAssertions() {
      return findAllReferences(this.Modules.getRootModule(), this.IsLevel);
    }
  }

  /**
   * The directory containing all the semantic corpus test files.
   */
  private static final String CORPUS_DIR = "test/tla2sany/semantic/corpus";

  /**
   * Finds all semantic corpus test files.
   * TODO: Modify this so it works when tests are run against tla2tools.jar,
   * where files cannot be resolved using a {@link Path} in this way. Likely
   * this will need to hook into resource loading logic exposed in the new
   * SANY API.
   */
  @Parameters(name = "{index}: {0}")
  public static List<SemanticTestCase> getTestFiles() throws IOException {
    Path corpusDir = Paths.get(CommonTestCase.BASE_DIR).resolve(CORPUS_DIR);
    PathMatcher matcher = FileSystems.getDefault().getPathMatcher("glob:**/*.tla");
    return Files
      .walk(corpusDir)
      .filter(matcher::matches)
      .map(SemanticTestCase::new)
      .collect(Collectors.toList());
  }

  /**
   * The current semantic corpus file to test.
   */
  @Parameter
  public SemanticTestCase testCase;

  /**
   * Check all reference & level assertions in the current test file.
   */
  @Test
  public void test() {
    // https://github.com/tlaplus/tlaplus/issues/1130
    Assume.assumeFalse("NegativeOpTest.tla".equals(this.testCase.toString()));

    // Parse test case
    final ExternalModuleTable modules = parse(this.testCase.ModulePath);
    final SemanticsModule semantics = new SemanticsModule(modules);

    // Check semantic resolution assertions
    final List<OpApplNode> refersToAssertions = semantics.findRefersToAssertions();
    checkRefersToAssertions(refersToAssertions);

    // Check level-checking assertions
    final List<OpApplNode> isLevelAssertions = semantics.findIsLevelAssertions();
    checkLevelAssertions(isLevelAssertions, semantics);
  }

  private static ExternalModuleTable parse(Path rootModulePath) {
    final FilenameToStream fts = new SimpleFilenameToStream(rootModulePath.getParent().toString());
    final SpecObj spec = new SpecObj(rootModulePath.toString(), fts);
    final RecordedSanyOutput out = new RecordedSanyOutput(LogLevel.INFO);
    SANY.frontEndInitialize();
    try {
      SANY.frontEndParse(spec, out);
    } catch (ParseException e) {
      Assert.fail(e.toString() + out.toString());
    }
    try {
      SANY.frontEndSemanticAnalysis(spec, out, true);
    } catch (SemanticException e) {
      Assert.fail(e.toString() + out.toString());
    }
    Assert.assertTrue(out.toString(), spec.parseErrors.isSuccess());
    Assert.assertTrue(out.toString(), spec.semanticErrors.isSuccess());
    Assert.assertTrue(out.toString(), spec.semanticErrors.getWarningDetails().isEmpty());
    return spec.getExternalModuleTable();
  }

  /**
   * In the current module under test, check all RefersTo usages to ensure
   * they really do refer to the operator labeled with the correct ID.
   *
   * @param assertions Assertions that a given identifier refers to a
   *                   definition labeled with a specific ID.
   */
  private static void checkRefersToAssertions(List<OpApplNode> assertions) {
    for (OpApplNode assertion : assertions) {
      final ExprOrOpArgNode[] parameters = assertion.getArgs();
      SymbolNode symbol = ((OpApplNode)parameters[0]).getOperator();
      if (symbol instanceof OpDefNode) {
        // Go to original op in module imported by INSTANCE
        symbol = ((OpDefNode)symbol).getSource();
      }
      final String expectedId = ((StringNode)parameters[1]).getRep().toString();
      final String actualId = getId(symbol);
      Assert.assertEquals(assertion.getLocation().toString(), expectedId, actualId);
    }
  }

  /**
   * Given a node in the semantic parse tree, find its preceding comment (if
   * it exists) then parse the string ID from it.
   *
   * @param symbol The node for which to find the comment-tagged ID.
   * @return The comment-tagged ID, or null if it does not exist.
   */
  private static String getId(SymbolNode symbol) {
    final String[] comments = symbol.getPreComments();
    return 0 == comments.length ? null : parseCommentId(comments[0]);
  }

  /**
   * A regex pattern to match & extract an ID from a comment.
   */
  private static final Pattern COMMENT_PATTERN = Pattern.compile("\\(\\*\\s*ID:\\s*(?<id>\\S+)\\s*\\*\\)");

  /**
   * Parse a comment to extract the ID.
   *
   * @param comment The comment, as a string.
   * @return The ID extracted from the comment.
   */
  private static String parseCommentId(String comment) {
    final Matcher m = COMMENT_PATTERN.matcher(comment);
    return m.matches() ? m.group("id") : null;
  }

  /**
   * Finds all references to the given operator definition in this module.
   * This is used to find assertions; however, since we are using these
   * assertions to test semantic resolution, it is somewhat circular to find
   * them by relying on the very mechanism that is undergoing testing. Thus
   * we cross-check this by dropping down to the syntax tree level to ensure
   * all references are found appropriately.
   *
   * TODO: Actually implement the syntax-level validation.
   *
   * @param module The module in which to search for references.
   * @param def The definition for which to find references.
   * @return A list of all references to the definition in the module.
   */
  private static List<OpApplNode> findAllReferences(ModuleNode module, OpDefNode def) {
    List<OpApplNode> assertions = new ArrayList<OpApplNode>();
    final ExplorerVisitor<Void> visitor = new ExplorerVisitor<Void>() {
      public void postVisit(final ExploreNode node) {
        if (node instanceof OpApplNode) {
          final OpApplNode op = (OpApplNode)node;
          if (op.getOperator() == def) {
            assertions.add(op);
          }
        }
      }
    };
    module.walkGraph(new Hashtable<>(), visitor);
    return assertions;
  }

  /**
   * In the current module under test, check all IsLevel usages to ensure
   * they really do assert the correct level of a label or expression.
   *
   * @param assertions Assertions that a given label or expression has a
   *                   supplied level.
   */
  private static void checkLevelAssertions(
    List<OpApplNode> assertions,
    SemanticsModule semantics
  ) {
    for (OpApplNode assertion : assertions) {
      ExprOrOpArgNode[] parameters = assertion.getArgs();
      int expectedLevel = semantics.getExpectedLevel(((OpApplNode)parameters[1]).getOperator());
      Assert.assertEquals(assertion.toString(), expectedLevel, parameters[0].getLevel());
    }
  }
}
