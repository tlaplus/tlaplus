package formatter.constructs.impl;

import com.opencastsoftware.prettier4j.Doc;
import formatter.constructs.ConstructContext;
import formatter.constructs.NodeKind;
import formatter.constructs.TlaConstruct;
import tla2sany.st.TreeNode;

/**
 * N_OpArgs' hri: '([i\in1..N|->coef[i]*seq[i]])'
 * Chcek: N_OpApplication
 */
public class OpArgsConstruct implements TlaConstruct {
    @Override
    public String getName() {
        return "OpArgs";
    }

    @Override
    public int getSupportedNodeKind() {
        return NodeKind.OP_ARGS.getId();
    }

    @Override
    public Doc buildDoc(TreeNode node, ConstructContext context, int indentSize) {
        var z = node.zero();
        assert (z != null);
        var expr = context.buildChild(z[1]);
        for (int i = 2; i < z.length - 1; i++) {
            var doc = context.buildChild(z[i]);
            if (z[i].getImage().equals(",") || z[i].getImage().equals(":")) {
                expr = expr.append(doc);
            } else {
                expr = expr.appendSpace(doc);
            }
        }
        var lbracket = context.buildChild(z[0]); // (
        var rbracket = context.buildChild(z[z.length - 1]); // )
        return lbracket
                .append(expr.indent(indentSize))
                .append(rbracket);
    }
}
