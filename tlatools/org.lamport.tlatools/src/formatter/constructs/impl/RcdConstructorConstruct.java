package formatter.constructs.impl;

import com.opencastsoftware.prettier4j.Doc;
import formatter.constructs.ConstructContext;
import formatter.constructs.NodeKind;
import formatter.constructs.TlaConstruct;
import tla2sany.st.TreeNode;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

/**
 * Construct implementation for record constructors.
 * Handles formatting of record expressions like [field1 |-> value1, field2 |-> value2].
 * See FieldValConstruct for "field1 |-> value1".
 */
public class RcdConstructorConstruct implements TlaConstruct {

    @Override
    public String getName() {
        return "RCD_CONSTRUCTOR";
    }

    @Override
    public int getSupportedNodeKind() {
        return NodeKind.RCD_CONSTRUCTOR.getId();
    }

    @Override
    public Doc buildDoc(TreeNode node, ConstructContext context, int indentSize) {
        TreeNode[] z = node.zero();
        assert (z != null && z.length >= 3);

        List<Doc> fieldDocs = new ArrayList<>();
        Map<Integer, String[]> commaComments = new HashMap<>();
        int fieldIndex = 0;
        for (int i = 1; i < z.length - 1; i++) {
            var child = z[i];
            assert (child != null);
            if (child.getHumanReadableImage().equals(",")) {
                String[] preComments = child.getPreComments();
                if (preComments != null && preComments.length > 0) {
                    commaComments.put(fieldIndex, preComments);
                }
                continue;
            }
            fieldDocs.add(context.buildChild(child));
            fieldIndex++;
        }

        Doc content = fieldDocs.get(0);
        for (int i = 1; i < fieldDocs.size(); i++) {
            String[] comments = commaComments.get(i);
            if (comments != null) {
                for (String comment : comments) {
                    content = content.appendLine(Doc.text(ConstructContext.stripAndNormalizeComment(comment)));
                }
                content = content.appendLine(Doc.text(", ").append(fieldDocs.get(i)));
            } else {
                content = content.append(Doc.text(",").appendLineOrSpace(fieldDocs.get(i)));
            }
        }

        return BracketedListHelper.wrapInBrackets(
                context.buildChild(z[0]),
                content,
                context.buildChild(z[z.length - 1]),
                "[ ".length());
    }
}