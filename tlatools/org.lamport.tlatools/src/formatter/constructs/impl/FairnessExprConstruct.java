package formatter.constructs.impl;

import com.opencastsoftware.prettier4j.Doc;
import formatter.constructs.ConstructContext;
import formatter.constructs.NodeKind;
import formatter.constructs.TlaConstruct;
import tla2sany.st.TreeNode;

import java.util.Arrays;
import java.util.stream.Collectors;

/**
 * Example: WF_vars(A) or SF_vars(A)
 */
public class FairnessExprConstruct implements TlaConstruct {
    @Override
    public String getName() {
        return "N_FairnessExpr";
    }

    @Override
    public int getSupportedNodeKind() {
        return NodeKind.FAIRNESS_EXPR.getId();
    }

    @Override
    public Doc buildDoc(TreeNode node, ConstructContext context, int indentSize) {
        var z = node.zero();
        assert (z != null);
        assert (z.length == 5); // WF_ or SF_, vars, (, action, )
        var zDocs = Arrays.stream(z).map(context::buildChild).collect(Collectors.toList());
        return Doc.group(
                zDocs.get(0) // WF_ or SF_
                        .append(zDocs.get(1)) // vars
                        .append(zDocs.get(2)) // (
                        .appendLineOrEmpty(zDocs.get(3).indent(indentSize)) // action
                        .append(zDocs.get(4))); // )
    }
}
