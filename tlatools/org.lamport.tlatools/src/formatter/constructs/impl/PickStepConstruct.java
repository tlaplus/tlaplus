package formatter.constructs.impl;

import com.opencastsoftware.prettier4j.Doc;
import formatter.constructs.ConstructContext;
import formatter.constructs.NodeKind;
import formatter.constructs.TlaConstruct;
import tla2sany.st.TreeNode;

/**
 * Handles proof PICK steps (N_PickStep, kind 442).
 * <p>
 * Structure: zero[] = [PICK, QuantBound, ..., ":", body_expr]
 * <p>
 * The body expression (often a conjunction list) must start on a new line
 * with consistent indentation to preserve valid TLA+ parsing.
 */
public class PickStepConstruct implements TlaConstruct {

    @Override
    public String getName() {
        return "N_PickStep";
    }

    @Override
    public int getSupportedNodeKind() {
        return NodeKind.PICK_STEP.getId();
    }

    @Override
    public Doc buildDoc(TreeNode node, ConstructContext context, int indentSize) {
        var z = node.zero();
        assert (z != null && z.length >= 3);

        // Build: PICK <bounds> : <body>
        // z[0] = PICK, z[1..n-2] = QuantBounds (with commas), z[n-1] = ":", z[n] = body
        Doc header = context.buildChild(z[0]); // PICK
        for (int i = 1; i < z.length - 1; i++) {
            header = header.appendSpace(context.buildChild(z[i]));
        }

        Doc body = context.buildChild(z[z.length - 1]);

        // Check if body is a conjunction/disjunction list - must go on new line
        int bodyKind = z[z.length - 1].getKind();
        if (bodyKind == NodeKind.CONJ_LIST.getId() || bodyKind == NodeKind.DISJ_LIST.getId()) {
            return header.append(Doc.line().append(body).indent(indentSize));
        }

        // Simple bodies can stay on same line if they fit
        return Doc.group(
                header.append(Doc.lineOrSpace().append(body).indent(indentSize))
        );
    }
}
