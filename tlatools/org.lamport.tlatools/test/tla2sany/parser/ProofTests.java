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
package tla2sany.parser;

import java.util.Arrays;
import java.util.List;

import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameter;
import org.junit.runners.Parameterized.Parameters;

import org.junit.Assert;

import tla2sany.output.SilentSanyOutput;
import tla2sany.st.SyntaxTreeConstants;
import tla2sany.st.TreeNode;

/**
 * Tests to ensure SANY attaches the appropriate proof level and name info to
 * proofs and proof steps. The primary motivation for writing these was to
 * ensure that the new {@link TreeNode#getProofLevel()} method works. Otherwise,
 * {@link TlaPlusSyntaxCorpusTests} are a better choice for testing tricky
 * proof parsing itself.
 */
@RunWith(Parameterized.class)
public class ProofTests {

  /**
   * Class holding info about the expected proof AST.
   */
  public static class AST {
    public static enum Kind {
      PROOF,
      PROOF_STEP
    }
    public final Kind kind;
    public final String name;
    public final int level;
    public final List<AST> children;
    private AST(Kind kind, String name, int level, List<AST> children) {
      this.kind = kind;
      this.name = name;
      this.level = level;
      this.children = children;
    }
  }

  private static AST proof(int level, AST... children) {
    return new AST(AST.Kind.PROOF, null, level, Arrays.asList(children));
  }

  private static AST step(String name, AST... children) {
    return new AST(AST.Kind.PROOF_STEP, name, -1, Arrays.asList(children));
  }

  private static AST step(AST... children) {
    return new AST(AST.Kind.PROOF_STEP, "", -1, Arrays.asList(children));
  }

  /**
   * The test cases, consisting of a TLA+ proof for input to the parser, and
   * the expected proof AST.
   */
  @Parameters(name = "{index}: {0}")
  public static Object[][] getTests() {
    return new Object[][] {
      new Object[] {
        "PROOF <1>a A <1>b QED",
        proof(1, step("a"), step("b"))
      },
      new Object[] {
        "<1>a A <1>b QED",
        proof(1, step("a"), step("b"))
      },
      new Object[] {
        "<1>a. A PROOF <+> A <*> QED <1>b.. QED",
        proof(1,
          step("a", proof(2,
            step(),
            step()
          )),
          step("b")
        )
      },
      new Object[] {
        "<*> A <+> A <*> QED <+> QED <*> QED",
        proof(0,
          step(proof(1,
            step(),
            step(proof(2,
              step()
            ))
          )),
          step()
        )
      }
    };
  }

  /**
   * The unparsed TLA+ for input to the parser.
   */
  @Parameter(0)
  public String proof;

  /**
   * The expected proof AST.
   */
  @Parameter(1)
  public AST expected;

  /**
   * Processes the actual syntax tree to check whether it matches the
   * expected syntax tree in terms of structure, proof level, and name.
   *
   * @param expected The expected syntax tree.
   * @param actual The actual syntax tree.
   */
  private static void match(final AST expected, final TreeNode actual) {
    Assert.assertEquals(expected.level, actual.getProofLevel());
    final TreeNode[] actualChildren = actual.heirs();
    switch (expected.kind) {
      case PROOF: {
        Assert.assertEquals(SyntaxTreeConstants.N_Proof, actual.getKind());
        int i = actualChildren[0].getKind() == TLAplusParserConstants.PROOF ? 1 : 0;
        for (final AST expectedChild : expected.children) {
          match(expectedChild, actualChildren[i]);
          i++;
        }
        Assert.assertEquals(actualChildren.length, i);
        break;
      }
      case PROOF_STEP: {
        Assert.assertEquals(SyntaxTreeConstants.N_ProofStep, actual.getKind());
        String actualName = actualChildren[0].getImage();
        actualName = actualName.substring(actualName.indexOf('>') + 1);
        actualName = actualName.contains(".") ? actualName.substring(0, actualName.indexOf('.')) : actualName;
        Assert.assertEquals(expected.name, actualName);
        final TreeNode actualChild = actualChildren[actualChildren.length - 1];
        if (actualChild.isKind(SyntaxTreeConstants.N_Proof)) {
          Assert.assertEquals(1, expected.children.size());
          match(expected.children.get(0), actualChild);
        }
        break;
      }
    }
  }

  /**
   * Parses test case input and checks whether it is as expected.
   */
  @Test
  public void test() throws ParseException {
    final TLAplusParser parser = new TLAplusParser(new SilentSanyOutput(), this.proof.getBytes());
    parser.token_source.SwitchTo(TLAplusParserConstants.SPEC);
    final SyntaxTreeNode actual = parser.Proof();
    match(this.expected, actual);
  }
}