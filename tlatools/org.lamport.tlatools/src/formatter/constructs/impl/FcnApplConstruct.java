package formatter.constructs.impl;

import com.opencastsoftware.prettier4j.Doc;
import formatter.constructs.ConstructContext;
import formatter.constructs.NodeKind;
import formatter.constructs.TlaConstruct;
import tla2sany.st.TreeNode;

import java.util.ArrayList;
import java.util.List;

/**
 * Example: 'N_FcnAppl' hri: 'coef[i]'
 * Example: towers[from] or CR[n - 1, v]
 */
public class FcnApplConstruct implements TlaConstruct {
    @Override
    public String getName() {
        return "FcnAppl";
    }

    @Override
    public int getSupportedNodeKind() {
        return NodeKind.FCN_APPL.getId();
    }

    @Override
    public Doc buildDoc(TreeNode node, ConstructContext context, int indentSize) {
        var z = node.zero();
        var o = node.one();

        var generalId = context.buildChild(z[0]);

        List<Doc> elementDocs = new ArrayList<>();
        for (int i = 1; i < o.length - 1; i++) {
            TreeNode child = o[i];
            assert (child != null);
            if (child.getHumanReadableImage().equals(",")) {
                continue;
            }
            Doc elementDoc = context.buildChild(child);
            elementDocs.add(elementDoc);
        }

        Doc content = elementDocs.get(0);
        for (int i = 1; i < elementDocs.size(); i++) {
            content = content.append(Doc.text(",")).appendLineOrSpace(elementDocs.get(i));
        }


        return Doc.group(
                generalId.append(Doc.text("["))
                        .appendLineOrEmpty(content).indent(indentSize)
                        .appendLineOrEmpty(Doc.text("]"))
        );
    }
}
