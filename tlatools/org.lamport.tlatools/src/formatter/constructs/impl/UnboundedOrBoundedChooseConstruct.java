package formatter.constructs.impl;

import com.opencastsoftware.prettier4j.Doc;
import formatter.constructs.ConstructContext;
import formatter.constructs.NodeKind;
import formatter.constructs.TlaConstruct;
import tla2sany.st.TreeNode;

/**
 * Example: CHOOSEe\inS:TRUE
 */
public class UnboundedOrBoundedChooseConstruct implements TlaConstruct {
    @Override
    public String getName() {
        return "N_UnBoundedOrBoundedChoose";
    }

    @Override
    public int getSupportedNodeKind() {
        return NodeKind.UNBOUND_OR_BOUND_CHOOSE.getId();
    }

    @Override
    public Doc buildDoc(TreeNode node, ConstructContext context, int indentSize) {
        var z = node.zero();
        assert (z != null);
        var chooseKey = context.buildChild(z[0]);
        var elName = context.buildChild(z[1]);
        var maybeBound = context.buildChild(z[2]);
        var colon = context.buildChild(z[3]);
        var expr = context.buildChild(z[4]);
        return Doc.group(
                chooseKey.appendSpace(elName)
                        .appendSpace(maybeBound.append(colon))
                        .appendLineOrSpace(Doc.group(expr).indent(indentSize))
        ).indent(indentSize);
    }
}
