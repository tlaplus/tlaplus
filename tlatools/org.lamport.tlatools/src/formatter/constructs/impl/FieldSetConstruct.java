package formatter.constructs.impl;

import com.opencastsoftware.prettier4j.Doc;
import formatter.constructs.ConstructContext;
import formatter.constructs.NodeKind;
import formatter.constructs.TlaConstruct;
import tla2sany.st.TreeNode;

/**
 * Handles field set definitions, e.g., `field: {1, 2, 3}`.
 * The node structure is:
 * N_FieldSet
 * |
 * +-- field name (identifier or string)
 * +-- colon
 * +-- SetEnumerate
 * Example: `type:{QueryMessageType}`
 */
public class FieldSetConstruct implements TlaConstruct {
    @Override
    public String getName() {
        return "N_FieldSet";
    }

    @Override
    public int getSupportedNodeKind() {
        return NodeKind.FIELD_SET.getId();
    }

    @Override
    public Doc buildDoc(TreeNode node, ConstructContext context, int indentSize) {
        var z = node.zero();
        assert (z != null && z.length == 3);
        return context.buildChild(z[0]) // field name;
                .append(context.buildChild(z[1])) // colon
                .append(context.buildChild(z[2])); // SetEnumerate
    }
}
