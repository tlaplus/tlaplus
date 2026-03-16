package formatter.constructs.impl;

import com.opencastsoftware.prettier4j.Doc;
import formatter.constructs.ConstructContext;
import formatter.constructs.NodeKind;
import formatter.constructs.TlaConstruct;
import tla2sany.st.TreeNode;

/**
 * Construct implementation for IF-THEN-ELSE expressions.
 */
public class IfThenElseConstruct implements TlaConstruct {

    @Override
    public String getName() {
        return "IF_THEN_ELSE";
    }

    @Override
    public int getSupportedNodeKind() {
        return NodeKind.IF_THEN_ELSE.getId();
    }

    @Override
    public Doc buildDoc(TreeNode node, ConstructContext context, int indentSize) {
        assert (node.zero() != null);
        assert (node.zero().length >= 6);
        // Expected structure:
        // zero[0]: IF keyword (kind=50)
        // zero[1]: condition expression  
        // zero[2]: THEN keyword (kind=62)
        // zero[3]: then expression
        // zero[4]: ELSE keyword (kind=45)
        // zero[5]: else expression
        var indentIfSize = "IF".length();
        Doc ifKey = context.buildChild(node.zero()[0]);
        Doc condition = Doc.group(context.buildChild(node.zero()[1])).indent(indentIfSize);
        Doc thenKey = context.buildChild(node.zero()[2]);
        Doc thenExpr = Doc.group(context.buildChild(node.zero()[3])).indent(indentIfSize);
        Doc elseKey = context.buildChild(node.zero()[4]);
        Doc elseExpr = Doc.group(context.buildChild(node.zero()[5])).indent(indentIfSize);
        return Doc.group(ifKey.appendSpace(condition)
                .appendLineOrSpace(thenKey.appendSpace(thenExpr)
                        .appendLineOrSpace(elseKey.appendSpace(elseExpr))));
    }
}