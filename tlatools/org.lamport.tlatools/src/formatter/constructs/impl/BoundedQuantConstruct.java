package formatter.constructs.impl;

import com.opencastsoftware.prettier4j.Doc;
import formatter.constructs.ConstructContext;
import formatter.constructs.NodeKind;
import formatter.constructs.TlaConstruct;
import tla2sany.st.TreeNode;

import java.util.ArrayList;
import java.util.List;

// \E coef \in [1..N -> -1..1] or \A QuantBound : ConjList.
public class BoundedQuantConstruct implements TlaConstruct {
    @Override
    public String getName() {
        return "BOUNDED_QUANT";
    }

    @Override
    public int getSupportedNodeKind() {
        // N_BoundedQuant
        return NodeKind.BOUNDED_QUANT.getId();
    }

    @Override
    public Doc buildDoc(TreeNode node, ConstructContext context, int indentSize) {
        var z = node.zero();
        var exists = context.buildChild(z[0]);
        List<Doc> elementDocs = new ArrayList<>();
        for (int i = 1; i < z.length - 2; i++) {
            TreeNode child = z[i];
            assert (child != null);
            if (child.getHumanReadableImage().equals(",")) {
                continue;
            }
            Doc elementDoc = context.buildChild(child);
            elementDocs.add(elementDoc);
        }

        Doc content = BracketedListHelper.joinWithComma(elementDocs);
        return Doc.group(
                exists.appendSpace(content)
                        .append(Doc.text(":"))
                        .appendLineOrSpace(context.buildChild(z[z.length - 1])).indent(indentSize)
        );
    }
}
