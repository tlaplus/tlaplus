package formatter;

import static org.junit.Assert.*;
import org.junit.Test;

import static formatter.Utils.assertSpecEquals;


public class CommentsTest {
    @Test
    public void moduleLevelCommentBlock() {
        var input = "---------- MODULE TowerOfHanoi -----\n" +
                "EXTENDS Naturals\n" +
                "\n" +
                "(***************************************************************************)\n" +
                "(* TRUE iff i is a power of two                                            *)\n" +
                "(***************************************************************************)\n" +
                "IsTwo(i) == i - 2 = 0\n" +
                "====";
        var expected = "---------- MODULE TowerOfHanoi -----\n" +
                "EXTENDS Naturals\n" +
                "\n" +
                "(***************************************************************************)\n" +
                "(* TRUE iff i is a power of two                                            *)\n" +
                "(***************************************************************************)\n" +
                "IsTwo(i) == i - 2 = 0\n" +
                "====";
        assertSpecEquals(expected, input);
    }

    @Test
    public void moduleLevelCommentInline() {
        var input = "---------- MODULE TowerOfHanoi -----\n" +
                "EXTENDS Naturals\n" +
                "\n" +
                "\\* TRUE iff i is a power of two\n" +
                "IsTwo(i) == i - 2 = 0\n" +
                "====";
        var expected = "---------- MODULE TowerOfHanoi -----\n" +
                "EXTENDS Naturals\n" +
                "\n" +
                "\\* TRUE iff i is a power of two\n" +
                "IsTwo(i) == i - 2 = 0\n" +
                "====";
        assertSpecEquals(expected, input);
    }

    @Test
    public void variablesWithInlineComments() {
        // This tests that inline comments on multi-line VARIABLES declarations are preserved.
        // In SANY's AST, inline comments after a token are stored as pre-comments of the NEXT token.
        // So "clock, \* local clock" has the comment stored as pre-comment of "req".
        // The trailing comment after the last variable is attached to the next declaration.
        var input = "---------- MODULE Test -----\n" +
                "VARIABLES\n" +
                "  clock,    \\* local clock\n" +
                "  req       \\* requests\n" +
                "\n" +
                "Init == TRUE\n" +
                "====";
        // The formatted output preserves comments, but trailing comment moves to next line
        var expected = "---------- MODULE Test -----\n" +
                "VARIABLES\n" +
                "  clock,    \\* local clock\n" +
                "  req\n" +
                "\\* requests\n" +
                "Init == TRUE\n" +
                "====";
        assertSpecEquals(expected, input);
    }

    @Test
    public void variablesWithMultiLineBlockComments() {
        // This tests that multi-line block comments following VARIABLES declarations
        // are preserved correctly, not joined on a single line with commas between them.
        // This is a bug that was causing parse errors in specifications/Prisoners/Prisoners.tla
        var input = "---------- MODULE Test -----\n" +
                "VARIABLES\n" +
                "  switchAUp,\n" +
                "  switchBUp,\n" +
                "    (***********************************************************************)\n" +
                "    (* The states of the two switches, represented by boolean-valued       *)\n" +
                "    (* variables.                                                          *)\n" +
                "    (***********************************************************************)\n" +
                "  count\n" +
                "\n" +
                "Init == TRUE\n" +
                "====";
        // Block comments should be on separate lines, not joined with commas
        var expected = "---------- MODULE Test -----\n" +
                "VARIABLES\n" +
                "  switchAUp,\n" +
                "  switchBUp,\n" +
                "    (***********************************************************************)\n" +
                "    (* The states of the two switches, represented by boolean-valued       *)\n" +
                "    (* variables.                                                          *)\n" +
                "    (***********************************************************************)\n" +
                "  count\n" +
                "\n" +
                "Init == TRUE\n" +
                "====";
        assertSpecEquals(expected, input);
    }

    @Test
    public void commentsPreserveTrailingWhitespace() {
        // Trailing whitespace in comments should be preserved because SANY's AST
        // preserves it, and stripping it changes semantic equality.
        var input = "---------- MODULE Test -----\n" +
                "EXTENDS Naturals\n" +
                "\n" +
                "\\* Comment with trailing space \n" +
                "IsTwo(i) == i - 2 = 0\n" +
                "====";
        var expected = "---------- MODULE Test -----\n" +
                "EXTENDS Naturals\n" +
                "\n" +
                "\\* Comment with trailing space \n" +
                "IsTwo(i) == i - 2 = 0\n" +
                "====";
        assertSpecEquals(expected, input);
    }

    @Test
    public void constantsWithInlineComments() {
        // This tests that inline comments on multi-line CONSTANT declarations are preserved.
        // Similar to VARIABLES, SANY stores inline comments as pre-comments of the NEXT token.
        var input = "---------- MODULE Test -----\n" +
                "CONSTANT Jug,      \\* The set of all jugs.\n" +
                "         Capacity, \\* Capacity of each jug.\n" +
                "         Goal      \\* The goal amount.\n" +
                "\n" +
                "Init == TRUE\n" +
                "====";
        // The formatted output preserves comments. The trailing comment moves to the next line.
        var expected = "---------- MODULE Test -----\n" +
                "CONSTANT Jug,    \\* The set of all jugs.\n" +
                "         Capacity,    \\* Capacity of each jug.\n" +
                "         Goal\n" +
                "\\* The goal amount.\n" +
                "Init == TRUE\n" +
                "====";
        assertSpecEquals(expected, input);
    }

    @Test
    public void constantsWithOperatorParameters() {
        // This tests that CONSTANT declarations with operator parameters like Op(_,_)
        // preserve their parameters when formatted with comments.
        var input = "---------- MODULE Test -----\n" +
                "CONSTANTS\n" +
                "    Hash,                   \\* Comment 1\n" +
                "    CalculateHash(_,_,_),   \\* Comment 2\n" +
                "    Other                   \\* Comment 3\n" +
                "\n" +
                "ASSUME TRUE\n" +
                "====";
        // The operator parameters should be preserved
        var expected = "---------- MODULE Test -----\n" +
                "CONSTANTS Hash,    \\* Comment 1\n" +
                "         CalculateHash(_,_,_),    \\* Comment 2\n" +
                "         Other\n" +
                "\\* Comment 3\n" +
                "ASSUME TRUE\n" +
                "====";
        assertSpecEquals(expected, input);
    }

    @Test
    public void localInstanceWithBlockComment() {
        // This tests that block comments before LOCAL INSTANCE declarations are preserved.
        var input = "---------- MODULE Test -----\n" +
                "(* Block comment *)\n" +
                "LOCAL INSTANCE Naturals\n" +
                "====";
        var expected = "---------- MODULE Test -----\n" +
                "(* Block comment *)\n" +
                "LOCAL INSTANCE Naturals\n" +
                "====";
        assertSpecEquals(expected, input);
    }

    @Test
    public void commentsRespectProperIndentationContext() {
        var input = "---------- MODULE TestModule -----\n" +
                "EXTENDS Naturals\n" +
                "\n" +
                "Foo == \n" +
                "  LET \n" +
                "    (* This comment should be indented to match the LET context *)\n" +
                "    (* Even if the original has extra indentation *)\n" +
                "    x == 1\n" +
                "  IN x + 1\n" +
                "====";
        var expected = "---------- MODULE TestModule -----\n" +
                "EXTENDS Naturals\n" +
                "\n" +
                "Foo == LET (* This comment should be indented to match the LET context *)\n" +
                "           (* Even if the original has extra indentation *)\n" +
                "           x == 1 IN x + 1\n" +
                "====";
        assertSpecEquals(expected, input);
    }

    @Test
    public void variablesWithCommentBeforeFirstVariable() {
        // This tests that a comment BEFORE the first variable is preserved.
        // The comment appears as preComment on the first variable node.
        var input = "---------- MODULE Test -----\n" +
                "VARIABLES\n" +
                "    \\* type annotation\n" +
                "    x\n" +
                "\n" +
                "Init == TRUE\n" +
                "====";
        var expected = "---------- MODULE Test -----\n" +
                "VARIABLES\n" +
                "    \\* type annotation\n" +
                "  x\n" +
                "\n" +
                "Init == TRUE\n" +
                "====";
        assertSpecEquals(expected, input);
    }

    @Test
    public void tupleWithCommentOnClosingBracket() {
        // Comment after last element before >> is attached as preComment to >> bracket.
        // The formatter must preserve it.
        var input = "---------- MODULE Test -----\n" +
                "Foo == <<1, 2, 3 \\* trailing comment\n" +
                ">>\n" +
                "====";
        var expected = "---------- MODULE Test -----\n" +
                "Foo == << 1, 2, 3 \\* trailing comment\n" +
                "  >>\n" +
                "====";
        assertSpecEquals(expected, input);
    }

    @Test
    public void tupleWithPrecedingComments() {
        // This tests that line comments before a tuple expression are preserved.
        // The comments are attached to the opening << bracket in SANY's AST.
        var input = "---------- MODULE Test -----\n" +
                "Foo ==\n" +
                "\\* Comment before tuple\n" +
                "<<1, 2>>\n" +
                "====";
        // Comment is preserved but formatting puts it inline after ==
        var expected = "---------- MODULE Test -----\n" +
                "Foo == \\* Comment before tuple\n" +
                "  << 1, 2 >>\n" +
                "====";
        assertSpecEquals(expected, input);
    }

    @Test
    public void constantsWithCommaFirstComments() {
        // In comma-first style, inline comments after a constant end up as preComments
        // on the comma node (not the next constant). Comma-first formatting is preserved
        // so that SANY re-attaches comments to the same AST nodes.
        var input = "---------- MODULE Test -----\n" +
                "CONSTANTS\n" +
                "    N \\* comment on N\n" +
                ",   R \\* comment on R\n" +
                ",   M\n" +
                "\n" +
                "Init == TRUE\n" +
                "====";
        var expected = "---------- MODULE Test -----\n" +
                "CONSTANTS\n" +
                "    N    \\* comment on N\n" +
                ",   R    \\* comment on R\n" +
                ",   M\n" +
                "\n" +
                "Init == TRUE\n" +
                "====";
        assertSpecEquals(expected, input);
    }

    @Test
    public void recordConstructorWithCommentOnComma() throws Exception {
        // Comments attached to comma separators in record constructors should be preserved.
        // In comma-first style, SANY attaches the comment to the comma node as a preComment.
        var input = "---- MODULE Test ----\n" +
                "Foo == [ a |-> 1\n" +
                "  \\* comment on comma\n" +
                "  , b |-> 2 ]\n" +
                "====";
        var formatter = new TLAPlusFormatter(input);
        var formatted = formatter.getOutput();
        assertTrue("Comment on comma in record constructor should be preserved. Got:\n" + formatted,
                formatted.contains("\\* comment on comma"));
        // Verify semantic preservation: AST of formatted output matches original
        var reformatter = new TLAPlusFormatter(formatted);
        Utils.assertAstEquals(formatter.root, reformatter.root);
    }

    @Test
    public void infixConjunctionWithComments() throws Exception {
        // When conjunction /\ items are NOT aligned at the same column, SANY parses them
        // as infix operators (N_InfixExpr) rather than a bulleted list (N_ConjList).
        // Comments on infix /\ operators are attached to the inner INFIX_OP token (kind=373)
        // inside the N_GenInfixOp wrapper (kind=359). GenInfixOpConstruct must process
        // its children to preserve these comments.
        var input = "---- MODULE Test ----\n" +
                "EXTENDS Naturals\n" +
                "VARIABLES a, b, c\n" +
                "Op == /\\ a = 1 \\* comment1\n" +
                "        /\\ b = 2 \\* comment2\n" +
                "        /\\ c = 3\n" +
                "====";
        var formatter = new TLAPlusFormatter(input);
        var formatted = formatter.getOutput();
        assertTrue("Comment on infix conjunction should be preserved. Got:\n" + formatted,
                formatted.contains("\\* comment1"));
        assertTrue("Comment on infix conjunction should be preserved. Got:\n" + formatted,
                formatted.contains("\\* comment2"));
        // Verify semantic preservation: AST of formatted output matches original
        var reformatter = new TLAPlusFormatter(formatted);
        Utils.assertAstEquals(formatter.root, reformatter.root);
    }

    @Test
    public void recordConstructorBracketWithPreComment() throws Exception {
        // When a comment appears between { and [ in a set containing a record constructor,
        // SANY attaches it to the [ as a pre-comment. The RcdConstructorConstruct must
        // use buildChild for brackets to preserve these comments.
        var input = "---- MODULE Test ----\n" +
                "Foo == { \\* comment on bracket\n" +
                "    [a |-> 1, b |-> 2] }\n" +
                "====";
        var formatter = new TLAPlusFormatter(input);
        var formatted = formatter.getOutput();
        assertTrue("Comment on record constructor bracket should be preserved. Got:\n" + formatted,
                formatted.contains("\\* comment on bracket"));
        var reformatter = new TLAPlusFormatter(formatted);
        Utils.assertAstEquals(formatter.root, reformatter.root);
    }

    @Test
    public void setEnumerateClosingBraceWithPreComment() throws Exception {
        // When a comment appears before } in a set enumeration,
        // SANY attaches it to the } as a pre-comment. SetEnumerateConstruct must
        // use buildChild for braces to preserve these comments.
        var input = "---- MODULE Test ----\n" +
                "Foo == { 1, 2 \\* comment on brace\n" +
                "       }\n" +
                "====";
        var formatter = new TLAPlusFormatter(input);
        var formatted = formatter.getOutput();
        assertTrue("Comment on closing brace should be preserved. Got:\n" + formatted,
                formatted.contains("\\* comment on brace"));
        var reformatter = new TLAPlusFormatter(formatted);
        Utils.assertAstEquals(formatter.root, reformatter.root);
    }

    @Test
    public void parenExprClosingParenWithPreComment() throws Exception {
        // When a comment appears before ) in a parenthesized expression,
        // SANY attaches it to the ) as a pre-comment. ParenExprConstruct must
        // use buildChild for parens to preserve these comments.
        var input = "---- MODULE Test ----\n" +
                "EXTENDS Naturals\n" +
                "VARIABLE x\n" +
                "Foo == ( x = 1 \\* comment on paren\n" +
                "       )\n" +
                "====";
        var formatter = new TLAPlusFormatter(input);
        var formatted = formatter.getOutput();
        assertTrue("Comment on closing paren should be preserved. Got:\n" + formatted,
                formatted.contains("\\* comment on paren"));
        var reformatter = new TLAPlusFormatter(formatted);
        Utils.assertAstEquals(formatter.root, reformatter.root);
    }

    @Test
    public void modulePrefixWithPreComments() throws Exception {
        // When comments appear before a module-prefixed reference like N!Nat,
        // SANY attaches them to the ID_PREFIX_ELEMENT child of ID_PREFIX.
        // IdPrefixConstruct must process children to preserve these comments.
        var input = "---- MODULE Test ----\n" +
                "LOCAL N == INSTANCE Naturals\n" +
                "Op ==\n" +
                "  \\* comment on module ref\n" +
                "  N!Nat\n" +
                "====";
        var formatter = new TLAPlusFormatter(input);
        var formatted = formatter.getOutput();
        assertTrue("Comment on module prefix reference should be preserved. Got:\n" + formatted,
                formatted.contains("\\* comment on module ref"));
        var reformatter = new TLAPlusFormatter(formatted);
        Utils.assertAstEquals(formatter.root, reformatter.root);
    }

    @Test
    public void constantsWithCommentBeforeFirstConstant() {
        // This tests that a comment BEFORE the first constant is preserved.
        // The comment appears as preComment on the constant node.
        var input = "---------- MODULE Test -----\n" +
                "CONSTANTS\n" +
                "    \\* Number of philosophers\n" +
                "    NP\n" +
                "\n" +
                "ASSUME TRUE\n" +
                "====";
        var expected = "---------- MODULE Test -----\n" +
                "CONSTANTS\n" +
                "    \\* Number of philosophers\n" +
                "    NP\n" +
                "\n" +
                "ASSUME TRUE\n" +
                "====";
        assertSpecEquals(expected, input);
    }

    @Test
    public void blockCommentIndentationPreservedInPlusCal() throws Exception {
        // Block comments inside PlusCal algorithm blocks have indentation that SANY
        // stores in preComment strings (e.g., '\n    (*'). The formatter must preserve
        // this indentation to maintain AST equality after re-parsing.
        // Reproduces the BPConProof.tla failure (Category 4: AST mismatch).
        var input = "---- MODULE Spec ----\n" +
                "EXTENDS Naturals\n" +
                "(**************************************************************************\n" +
                "  algorithm Alg {\n" +
                "    variable x = 0;\n" +
                "  \n" +
                "    (*********************************************************************)\n" +
                "    (* Indented block comment with 4 spaces                              *)\n" +
                "    (*********************************************************************)\n" +
                "    macro Foo() { x := x + 1 }\n" +
                "  }\n" +
                "  \n" +
                "  Below is the TLA+ translation.\n" +
                "  **************************************************************************)\n" +
                "\\* BEGIN TRANSLATION\n" +
                "VARIABLES x\n" +
                "\n" +
                "Init == x = 0\n" +
                "Next == x' = x + 1\n" +
                "\\* END TRANSLATION\n" +
                "====";
        var formatter = new TLAPlusFormatter(input);
        var formatted = formatter.getOutput();
        var reformatter = new TLAPlusFormatter(formatted);
        Utils.assertAstEquals(formatter.root, reformatter.root);
    }

}
