package formatter.constructs.impl;

import org.junit.jupiter.api.Test;

import static formatter.Utils.assertSpecEquals;

public class FcnConstConstructTest {

    @Test
    void testSingleBoundFunctionConstant() {
        var input = "----- MODULE Test -----\n" +
                "CONSTANT Nodes\n" +
                "isLeaf == [n \\in Nodes |-> TRUE]\n" +
                "====";
        var expected = "----- MODULE Test -----\n" +
                "CONSTANT Nodes\n" +
                "isLeaf == [n \\in Nodes |-> TRUE]\n" +
                "====";
        assertSpecEquals(expected, input);
    }

    @Test
    void testCommentBeforeFunctionConstant() {
        // Comment attached to the opening [ should be preserved
        var input = "----- MODULE Test -----\n" +
                "CONSTANT S\n" +
                "op ==\n" +
                "    \\* comment on fcn const\n" +
                "    [s \\in S |-> TRUE]\n" +
                "====";
        var expected = "----- MODULE Test -----\n" +
                "CONSTANT S\n" +
                "op == \\* comment on fcn const\n" +
                "    [s \\in S |-> TRUE]\n" +
                "====";
        assertSpecEquals(expected, input);
    }

    @Test
    void testMultiBoundFunctionConstant() {
        // This is the btree.tla bug - multi-bound function constants like
        // [n \in Nodes, k \in Keys |-> NIL] were losing the |-> NIL part
        var input = "----- MODULE Test -----\n" +
                "CONSTANTS Nodes, Keys, NIL\n" +
                "childOf == [n \\in Nodes, k \\in Keys |-> NIL]\n" +
                "====";
        var expected = "----- MODULE Test -----\n" +
                "CONSTANTS Nodes, Keys, NIL\n" +
                "childOf == [n \\in Nodes, k \\in Keys |-> NIL]\n" +
                "====";
        assertSpecEquals(expected, input);
    }
}
