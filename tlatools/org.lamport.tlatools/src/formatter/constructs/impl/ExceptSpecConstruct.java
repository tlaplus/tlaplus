package formatter.constructs.impl;

import com.opencastsoftware.prettier4j.Doc;
import formatter.constructs.ConstructContext;
import formatter.constructs.NodeKind;
import formatter.constructs.TlaConstruct;
import tla2sany.st.TreeNode;

/**
 * Handles EXCEPT specifications like ![from]=towers[from]-disk
 * Also handles chained components like ![r].smoking = FALSE
 */
public class ExceptSpecConstruct implements TlaConstruct {
    @Override
    public String getName() {
        return "N_ExceptSpec";
    }

    @Override
    public int getSupportedNodeKind() {
        return NodeKind.EXCEPT_SPEC.getId();
    }

    @Override
    public Doc buildDoc(TreeNode node, ConstructContext context, int indentSize) {
        var z = node.zero();
        assert (z != null);
        // Structure: ! <ExceptComponent>+ = <value>
        // There can be multiple ExceptComponents (e.g., ![r].smoking = FALSE)
        // - z[0] is always the bang (!)
        // - z[1..n-2] are ExceptComponents
        // - z[n-1] is the equals sign (=)
        // - z[n] is the value expression
        assert (z.length >= 4); // minimum: ! comp = value

        var bang = context.buildChild(z[0]);

        // Build all except components (indices 1 to length-3)
        Doc exceptComps = context.buildChild(z[1]);
        for (int i = 2; i < z.length - 2; i++) {
            exceptComps = exceptComps.append(context.buildChild(z[i]));
        }

        var eq = context.buildChild(z[z.length - 2]);
        var infixExpr = context.buildChild(z[z.length - 1]);
        return bang
                .append(exceptComps)
                .appendSpace(eq)
                .appendLineOrSpace(infixExpr);
    }
}
