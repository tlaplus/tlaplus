package formatter.constructs.impl;

import com.opencastsoftware.prettier4j.Doc;
import formatter.constructs.ConstructContext;
import formatter.constructs.NodeKind;
import formatter.constructs.TlaConstruct;
import tla2sany.st.TreeNode;

/**
 * Example: LAMBDA i: i % 2 = 0
 */
public class LambdaConstruct implements TlaConstruct {
    @Override
    public String getName() {
        return "N_Lambda";
    }

    @Override
    public int getSupportedNodeKind() {
        return NodeKind.LAMBDA.getId();
    }

    @Override
    public Doc buildDoc(TreeNode node, ConstructContext context, int indentSize) {
        var z = node.zero();
        assert (z != null);
        assert (z.length >= 4); // LAMBDA, var(s), :, expr
        var doc = context.buildChild(z[0]); // LAMBDA
        var ret = doc;
        var i = 1;
        while (!z[i].getImage().equals(":")) {
            doc = context.buildChild(z[i]);
            if (z[i].getImage().equals(",")) {
                ret = ret.append(doc);
            } else {
                ret = ret.appendLineOrSpace(doc);
            }
            i++;
        }
        ret = ret.append(context.buildChild(z[i])); // :
        ret = ret.append(context.buildChild(z[i + 1]));
        return ret;
    }
}
