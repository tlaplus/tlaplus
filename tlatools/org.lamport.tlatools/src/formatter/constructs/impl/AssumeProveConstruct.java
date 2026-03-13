package formatter.constructs.impl;

import com.opencastsoftware.prettier4j.Doc;
import formatter.constructs.ConstructContext;
import formatter.constructs.NodeKind;
import formatter.constructs.TlaConstruct;
import tla2sany.st.TreeNode;

/**
 * Handles ASSUME/PROVE blocks in proofs (N_AssumeProve).
 * <p>
 * Structure: zero[] = [ASSUME, assumption1, comma, assumption2, ..., PROVE, expr]
 * All children are rendered with spaces; line breaks handled by Doc.group.
 */
public class AssumeProveConstruct implements TlaConstruct {

    @Override
    public String getName() {
        return "N_AssumeProve";
    }

    @Override
    public int getSupportedNodeKind() {
        return NodeKind.ASSUME_PROVE.getId();
    }

    @Override
    public Doc buildDoc(TreeNode node, ConstructContext context, int indentSize) {
        var z = node.zero();
        assert (z != null && z.length >= 3);

        // Find the PROVE keyword position to split assumptions from prove-expr
        int proveIdx = -1;
        for (int i = 0; i < z.length; i++) {
            if (z[i].getImage().equals("PROVE")) {
                proveIdx = i;
                break;
            }
        }
        assert proveIdx >= 0;

        // Build ASSUME section: ASSUME <assumptions with commas>
        Doc assumeDoc = context.buildChild(z[0]); // ASSUME keyword
        for (int i = 1; i < proveIdx; i++) {
            assumeDoc = assumeDoc.appendSpace(context.buildChild(z[i]));
        }

        // Build PROVE section: PROVE <expr>
        Doc proveDoc = context.buildChild(z[proveIdx]); // PROVE keyword
        for (int i = proveIdx + 1; i < z.length; i++) {
            proveDoc = proveDoc.appendSpace(context.buildChild(z[i]));
        }

        // Group ASSUME and PROVE with a line-or-space break between them
        return Doc.group(assumeDoc.append(
                Doc.lineOrSpace().append(proveDoc)));
    }
}
