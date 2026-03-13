package formatter.constructs.impl;

import com.opencastsoftware.prettier4j.Doc;
import formatter.constructs.ConstructContext;
import formatter.constructs.NodeKind;
import formatter.constructs.TlaConstruct;
import tla2sany.st.TreeNode;

/**
 * Handles EXCEPT components.
 * For example, in the expression: [f EXCEPT ![k] = e]
 * This construct handles the part: [k]
 * Example: [r0 EXCEPT !.b = @ \cup {2}]
 * the `.b` part.
 */
public class ExceptComponentConstruct implements TlaConstruct {
    @Override
    public String getName() {
        return "N_ExceptComponent";
    }

    @Override
    public int getSupportedNodeKind() {
        return NodeKind.EXCEPT_COMPONENT.getId();
    }

    @Override
    public Doc buildDoc(TreeNode node, ConstructContext context, int indentSize) {
        var z = node.zero();
        assert (z != null);
        assert (z.length >= 2);
        var d = context.buildChild(z[0]);
        for (int i = 1; i < z.length; i++) {
            assert (z[i] != null);
            d = d.append(context.buildChild(z[i]));
        }
        return d;
    }
}
