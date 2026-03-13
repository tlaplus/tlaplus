package formatter.constructs.impl;

import com.opencastsoftware.prettier4j.Doc;
import formatter.constructs.ConstructContext;
import formatter.constructs.NodeKind;
import formatter.constructs.TlaConstruct;
import tla2sany.st.TreeNode;

/**
 * Construct implementation for N_MaybeBound with hri: '\inS'
 * Handles variable bindings with the \in S operator.
 * Example: `\in S` from `CHOOSE e \in S: TRUE`
 *
 */
public class MaybeBoundConstruct implements TlaConstruct {
    @Override
    public String getName() {
        return "N_MaybeBound";
    }

    @Override
    public int getSupportedNodeKind() {
        return NodeKind.MAYBE_BOUND.getId();
    }

    @Override
    public Doc buildDoc(TreeNode node, ConstructContext context, int indentSize) {
        var z = node.zero();
        // Example: CHOOSE c : c \notin Color, it will create an empty MaybeBound
        if (z == null) {
            return Doc.empty();
        }
        assert (z.length >= 2); // \in, set

        return Doc.group(
                context
                        .buildChild(z[0])
                        .appendSpace(context.buildChild(z[1]).indent(indentSize))
        );
    }
}