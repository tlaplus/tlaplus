package formatter.constructs.impl;

import com.opencastsoftware.prettier4j.Doc;
import formatter.constructs.ConstructContext;
import formatter.constructs.NodeKind;
import formatter.constructs.TlaConstruct;
import tla2sany.st.TreeNode;

/**
 * Construct implementation for ASSUME/ASSUMPTION constructs.
 * Formats "ASSUME expr" or "ASSUMPTION expr" with proper indentation.
 * The node structure is expected to have two children:
 * - The first child is the ASSUME keyword.
 * - the second child is either an expression or a sequence of expressions.
 * <p>
 * Example: ASSUME x > 0
 * ASSUME X == <expr> (this are 4 nodes in one())
 */
public class AssumptionConstruct implements TlaConstruct {
    @Override
    public String getName() {
        return "N_Assumption";
    }

    @Override
    public int getSupportedNodeKind() {
        return NodeKind.ASSUMPTION.getId();
    }

    @Override
    public Doc buildDoc(TreeNode node, ConstructContext context, int indentSize) {
        var o = node.one();
        assert (o != null && o.length >= 2);
        var assume = context.buildChild(o[0]);
        var ret = assume.appendSpace(context.buildChild(o[1]).indent(o[0].getImage().length() + 1));
        if (o.length == 2) {
            return ret;
        }
        // More than one expression, need to handle line breaks
        // this is the case when ASSUME X == <expr>.
        ret = ret.appendSpace(context.buildChild(o[2])); // ==
        var content = context.buildChild(o[3]); // <expr>
        return ret.appendSpace(content);
    }
}
