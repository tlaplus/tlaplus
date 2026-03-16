package formatter.constructs.impl;

import com.opencastsoftware.prettier4j.Doc;
import formatter.constructs.ConstructContext;
import formatter.constructs.NodeKind;
import formatter.constructs.TlaConstruct;
import tla2sany.st.TreeNode;

/**
 * Construct implementation for field-value pairs in records.
 * Handles formatting of field |-> value expressions.
 */
public class FieldValConstruct implements TlaConstruct {

    @Override
    public String getName() {
        return "FIELD_VAL";
    }

    @Override
    public int getSupportedNodeKind() {
        return NodeKind.FIELD_VAL.getId();
    }

    @Override
    public Doc buildDoc(TreeNode node, ConstructContext context, int indentSize) {
        assert (node.zero() != null && node.zero().length >= 3);
        // Expected structure:
        // zero[0]: field name/expression
        // zero[1]: |-> operator
        // zero[2]: value expression

        Doc field = context.buildChild(node.zero()[0]);
        Doc operator = context.buildChild(node.zero()[1]);
        Doc value = context.buildChild(node.zero()[2]);
        return Doc.group(
                field
                        .appendSpace(operator)
                        .appendLineOrSpace(value).indent(indentSize)
        );
    }
}