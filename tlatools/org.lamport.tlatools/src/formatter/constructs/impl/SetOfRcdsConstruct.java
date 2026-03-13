package formatter.constructs.impl;

import com.opencastsoftware.prettier4j.Doc;
import formatter.constructs.ConstructContext;
import formatter.constructs.NodeKind;
import formatter.constructs.TlaConstruct;
import tla2sany.st.TreeNode;

/**
 * Handles set of records constructs.
 * Example: '[type:{TerminationMessageType},pid:SlushLoopProcess]'
 */
public class SetOfRcdsConstruct implements TlaConstruct {
    @Override
    public String getName() {
        return "N_SetOfRcds";
    }

    @Override
    public int getSupportedNodeKind() {
        return NodeKind.SET_OF_RCDS.getId();
    }

    @Override
    public Doc buildDoc(TreeNode node, ConstructContext context, int indentSize) {
        var z = node.zero();
        assert (z != null && z.length >= 3);
        var ret = context.buildChild(z[0]);
        for (int i = 1; i < z.length - 1; i++) {
            var doc = context.buildChild(z[i]);
            if (z[i].getImage().equals(",") || i == 1) {
                ret = ret.append(doc);
            } else {
                ret = ret.appendLineOrSpace(doc);
            }
        }
        return ret.indent(indentSize).appendLineOrSpace(context.buildChild(z[z.length - 1])); // ]
    }
}
