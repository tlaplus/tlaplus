package formatter.constructs.impl;

import com.opencastsoftware.prettier4j.Doc;
import formatter.constructs.ConstructContext;
import formatter.constructs.NodeKind;
import formatter.constructs.TlaConstruct;
import tla2sany.st.TreeNode;

/**
 * Handles record component access, e.g., `record.field` or `record["field"]`.
 * The node structure is:
 * N_RecordComponent
 * |
 * +-- field name (identifier or string)
 * +-- dot or open bracket
 * +-- property (identifier or string)
 */
public class RecordComponentConstruct implements TlaConstruct {
    @Override
    public String getName() {
        return "N_RecordComponent";
    }

    @Override
    public int getSupportedNodeKind() {
        return NodeKind.RECORD_COMPONENT.getId();
    }

    @Override
    public Doc buildDoc(TreeNode node, ConstructContext context, int indentSize) {
        var z = node.zero();
        assert (z != null && z.length == 3);
        return context.buildChild(z[0]) // field name;
                .append(context.buildChild(z[1])) // dot
                .append(context.buildChild(z[2])); // prop
    }
}
