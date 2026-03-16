package formatter.constructs.impl;

import com.opencastsoftware.prettier4j.Doc;
import formatter.constructs.ConstructContext;
import formatter.constructs.NodeKind;
import formatter.constructs.TlaConstruct;
import tla2sany.st.TreeNode;

/**
 * Example: 'OTHER->0'
 */
public class OtherArmConstruct implements TlaConstruct {
    @Override
    public String getName() {
        return "N_OtherArm";
    }

    @Override
    public int getSupportedNodeKind() {
        return NodeKind.OTHER_ARM.getId();
    }

    @Override
    public Doc buildDoc(TreeNode node, ConstructContext context, int indentSize) {
        var z = node.zero();
        assert (z != null && z.length == 3);
        var other = context.buildChild(z[0]);
        var arrow = context.buildChild(z[1]);
        var value = context.buildChild(z[2]);
        return Doc.group(
                other.append(arrow).appendLineOrSpace(value)
        ).indent(other.toString().length() + 1);
    }
}
