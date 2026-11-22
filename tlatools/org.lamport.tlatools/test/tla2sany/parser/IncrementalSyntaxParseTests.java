/*******************************************************************************
 * Copyright (c) 2025 Linux Foundation. All rights reserved.
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

import java.nio.charset.StandardCharsets;

import org.junit.Assert;
import org.junit.Test;

import tla2sany.output.SilentSanyOutput;
import tla2sany.st.SyntaxTreeConstants;

/**
 * Tests for parsing TLA+ incrementally, at the expression or definition
 * level instead of the full module level. This only tests the syntax parser
 * and not the semantic or level-checking code.
 */
public class IncrementalSyntaxParseTests {

  public static TLAplusParser parser(String input) {
    final TLAplusParser parser = new TLAplusParser(new SilentSanyOutput(), input.getBytes(StandardCharsets.UTF_8));
    parser.token_source.SwitchTo(TLAplusParserConstants.SPEC);
    parser.belchDEF();
    return parser;
  }

  @Test
  public void testParseBasicOpDef() throws ParseException {
    final SyntaxTreeNode result = parser("op == 0").OperatorOrFunctionDefinition();
    Assert.assertNotNull(result);
    Assert.assertEquals(SyntaxTreeConstants.N_OperatorDefinition, result.getKind());
    Assert.assertEquals(SyntaxTreeConstants.N_IdentLHS, result.getHeirs()[0].getKind());
    Assert.assertEquals("op", result.getHeirs()[0].getHeirs()[0].getImage());
    Assert.assertEquals(TLAplusParserConstants.DEF, result.getHeirs()[1].getKind());
    Assert.assertEquals(SyntaxTreeConstants.N_Number, result.getHeirs()[2].getKind());
    Assert.assertEquals("0", result.getHeirs()[2].getHeirs()[0].getImage());
  }

  @Test
  public void testParseBasicExpression() throws ParseException {
    final SyntaxTreeNode result = parser("0").Expression();
    Assert.assertNotNull(result);
    Assert.assertEquals(SyntaxTreeConstants.N_Number, result.getKind());
    Assert.assertEquals("0", result.getHeirs()[0].getImage());
  }

  @Test
  public void testParseConjunctionList() throws ParseException {
    final SyntaxTreeNode result = parser("  /\\ TRUE\n  /\\ FALSE\n  /\\ TRUE").Expression();
    Assert.assertNotNull(result);
    Assert.assertEquals(SyntaxTreeConstants.N_ConjList, result.getKind());
    Assert.assertEquals(3, result.getHeirs().length);
  }

  /**
   * Asserts that the expression parses as an infix expression whose left
   * operand is a tuple with a single element of the given kind.
   */
  private static void assertTupleInfix(final SyntaxTreeNode result, final int elementKind) {
    Assert.assertEquals(SyntaxTreeConstants.N_InfixExpr, result.getKind());
    final SyntaxTreeNode tuple = result.getHeirs()[0];
    Assert.assertEquals(SyntaxTreeConstants.N_Tuple, tuple.getKind());
    Assert.assertEquals(elementKind, tuple.getHeirs()[1].getKind());
  }

  @Test
  public void testTupleBoundLookahead() throws ParseException {
    final String definition = "Inv == << [<< ENABLED <<x' = 1 - x>>_x >> EXCEPT ![1] = FALSE] >> \\in {<<<<FALSE>>>>}";
    final SyntaxTreeNode def = parser(definition).OperatorOrFunctionDefinition();
    Assert.assertEquals(SyntaxTreeConstants.N_OperatorDefinition, def.getKind());
    assertTupleInfix(def.getHeirs()[2], SyntaxTreeConstants.N_Except);

    final SyntaxTreeNode module = new TLAplusParser(new SilentSanyOutput(), ("---- MODULE EnabledTuple ----\n" + definition
        + "\n====").getBytes(StandardCharsets.UTF_8)).CompilationUnit();
    Assert.assertEquals(SyntaxTreeConstants.N_Module, module.getKind());

    assertTupleInfix(parser("<< {<< ENABLED <<x' = 1 - x>>_x >>} >> \\in {<<<<FALSE>>>>}").Expression(),
        SyntaxTreeConstants.N_SetEnumerate);
    assertTupleInfix(parser("<< [<<x, <<Next>>_x>> EXCEPT ![1] = y] >> \\in S").Expression(),
        SyntaxTreeConstants.N_Except);
    assertTupleInfix(parser("<< f[<<Next>>_x] >> \\in S").Expression(), SyntaxTreeConstants.N_FcnAppl);
    assertTupleInfix(parser("⟨[⟨ENABLED ⟨x' = 1 - x⟩_x⟩ EXCEPT ![1] = FALSE]⟩ ∈ {⟨⟨FALSE⟩⟩}").Expression(),
        SyntaxTreeConstants.N_Except);

    final SyntaxTreeNode setEnum = parser("{<<1, 2>> \\in S}").Expression();
    Assert.assertEquals(SyntaxTreeConstants.N_SetEnumerate, setEnum.getKind());
    Assert.assertEquals(SyntaxTreeConstants.N_InfixExpr, setEnum.getHeirs()[1].getKind());

    final SyntaxTreeNode action = parser("[<<x', y'>> \\in R]_<<x, y>>").Expression();
    Assert.assertEquals(SyntaxTreeConstants.N_ActionExpr, action.getKind());
    Assert.assertEquals(SyntaxTreeConstants.N_InfixExpr, action.getHeirs()[1].getKind());

    for (String input : new String[] {"[⟨x, y⟩ ∈ S ↦ x]", "[<<>> \\in S |-> TRUE]"}) {
      Assert.assertEquals(SyntaxTreeConstants.N_FcnConst, parser(input).Expression().getKind());
    }
    Assert.assertEquals(SyntaxTreeConstants.N_SubsetOf, parser("{<<x, y, z>> \\in S : P(x, y, z)}").Expression().getKind());
  }

  @Test
  public void testTupleMembershipFunctionConstructor() throws ParseException {
    final SyntaxTreeNode result = parser("[<<x, y>> \\in S |-> x + y]").Expression();
    Assert.assertEquals(SyntaxTreeConstants.N_FcnConst, result.getKind());
  }
}
