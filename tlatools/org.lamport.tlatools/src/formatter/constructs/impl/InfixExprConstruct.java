package formatter.constructs.impl;

import com.opencastsoftware.prettier4j.Doc;
import formatter.constructs.ConstructContext;
import formatter.constructs.NodeKind;
import formatter.constructs.TlaConstruct;
import tla2sany.st.TreeNode;

/**
 * Construct implementation for infix expressions.
 * Handles formatting of expressions with infix operators (e.g., a + b, x :> y).
 * Example: S \in Z
 */
public class InfixExprConstruct implements TlaConstruct {

    @Override
    public String getName() {
        return "INFIX_EXPR";
    }

    @Override
    public int getSupportedNodeKind() {
        return NodeKind.INFIX_EXPR.getId();
    }

    @Override
    public Doc buildDoc(TreeNode node, ConstructContext context, int indentSize) {
        assert (node.zero() != null);
        assert (node.zero().length >= 3);
        // Expected structure:
        // zero[0]: left operand
        // zero[1]: infix operator
        // zero[2]: right operand
        // example: 1 .. 2

        TreeNode leftNode = node.zero()[0];
        TreeNode opNode = node.zero()[1];
        Doc leftOperand = context.buildChild(leftNode);
        Doc operator = context.buildChild(opNode);
        Doc rightOperand = context.buildChild(node.zero()[2]);

        int leftKind = leftNode.getKind();
        boolean leftIsConjDisjList = leftKind == NodeKind.CONJ_LIST.getId()
                || leftKind == NodeKind.DISJ_LIST.getId();

        if (leftIsConjDisjList) {
            // Left is a bulleted list: put operator+right on a new line.
            // Do NOT use .align() -- alignment would place operator+right at the same
            // column as the list items, causing SANY to absorb it into the list.
            return leftOperand
                    .appendLine(operator.appendSpace(rightOperand));
        }

        return Doc.group(
                leftOperand
                        .appendSpace(operator)
                        .appendLineOrSpace(rightOperand).indent(indentSize)
        );
    }
}