package formatter.constructs.impl;

import com.opencastsoftware.prettier4j.Doc;
import formatter.constructs.ConstructContext;
import formatter.constructs.NodeKind;
import formatter.constructs.TlaConstruct;
import tla2sany.st.TreeNode;

/**
 * Example: `{Partitions(<<x>>\oseq,wt-x):x\inS}`
 * Example: RecordCombine(S, T) ==\n" +
 * "   {rc(s, t):s \\in S, t \\in T}
 */
public class SetOfAllConstruct implements TlaConstruct {
    @Override
    public String getName() {
        return "N_SetOfAll";
    }

    @Override
    public int getSupportedNodeKind() {
        return NodeKind.SET_OF_ALL.getId();
    }

    @Override
    public Doc buildDoc(TreeNode node, ConstructContext context, int indentSize) {
        var z = node.zero();
        var ret = context.buildChild(z[0]); // {
        for (int i = 1; i < z.length - 1; i++) {
            var doc = context.buildChild(z[i]);
            if (z[i].getImage().equals(",") || z[i].getImage().equals(":") || i == 1) {
                ret = ret.append(doc);
            } else {
                ret = ret.appendLineOrSpace(doc);
            }
        }
        return ret.indent(indentSize).appendLineOrEmpty(context.buildChild(z[z.length - 1])); // }
    }
}
