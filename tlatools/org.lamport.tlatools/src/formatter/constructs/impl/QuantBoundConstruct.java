package formatter.constructs.impl;

import com.opencastsoftware.prettier4j.Doc;
import formatter.constructs.ConstructContext;
import formatter.constructs.NodeKind;
import formatter.constructs.TlaConstruct;
import tla2sany.st.TreeNode;

import java.util.ArrayList;
import java.util.List;

/**
 * 'N_QuantBound' hri: 'i\in1..N'
 */
public class QuantBoundConstruct implements TlaConstruct {
    @Override
    public String getName() {
        return "QuantBound";
    }

    @Override
    public int getSupportedNodeKind() {
        return NodeKind.QUANT_BOUND.getId();
    }

    @Override
    public Doc buildDoc(TreeNode node, ConstructContext context, int indentSize) {
        var z = node.zero();
        var i = 0;
        List<Doc> elementDocs = new ArrayList<>();
        while (!z[i].getImage().equals("\\in")) {
            if (!z[i].getImage().equals(",")) {
                elementDocs.add(context.buildChild(z[i]));
            }
            i++;
        }
        var lastIndex = z.length - 1;
        var set = context.buildChild(z[lastIndex]);
        Doc content = elementDocs.get(0);
        for (i = 1; i < elementDocs.size(); i++) {
            content = content.append(Doc.text(",")).appendLineOrSpace(elementDocs.get(i));
        }

        return Doc.group(
                content.appendSpace(Doc.text("\\in"))
                        .appendLineOrSpace(set.indent(indentSize))
        );
    }
}
