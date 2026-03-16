package formatter.constructs.impl;

import com.opencastsoftware.prettier4j.Doc;
import formatter.constructs.ConstructContext;
import formatter.constructs.NodeKind;
import formatter.constructs.TlaConstruct;
import tla2sany.st.TreeNode;

import java.util.ArrayList;
import java.util.List;

/**
 * Name/signature of an operatore
 * the x in `x == TRUE` or `x(a,b) == TRUE`
 */
public class IdentLHSConstruct implements TlaConstruct {
    @Override
    public String getName() {
        return "N_IdentLHS";
    }

    @Override
    public int getSupportedNodeKind() {
        return NodeKind.IDENT_LHS.getId();
    }

    @Override
    public Doc buildDoc(TreeNode node, ConstructContext context, int indentSize) {
        var z = node.zero();
        assert (z != null && z.length > 0);
        var name = context.buildChild(z[0]);
        if (z.length == 1) {
            // simple case
            return name;
        }

        List<Doc> elementDocs = new ArrayList<>();
        for (int i = 2; i < z.length - 1; i++) {
            TreeNode child = z[i];
            assert (child != null);
            if (child.getHumanReadableImage().equals(",")) {
                continue;
            }
            Doc elementDoc = context.buildChild(child);
            elementDocs.add(elementDoc);
        }

        Doc content = elementDocs.get(0);
        for (int i = 1; i < elementDocs.size(); i++) {
            content = content.append(Doc.text(",")).appendSpace(elementDocs.get(i));
        }

        return
                name
                        .append(Doc.text("("))
                        .append(content)
                        .append(Doc.text(")"));
    }
}
