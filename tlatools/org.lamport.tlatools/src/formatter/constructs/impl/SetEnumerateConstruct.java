package formatter.constructs.impl;

import com.opencastsoftware.prettier4j.Doc;
import formatter.constructs.ConstructContext;
import formatter.constructs.NodeKind;
import formatter.constructs.TlaConstruct;
import tla2sany.st.TreeNode;

import java.util.List;

/**
 * Construct implementation for set enumerations.
 * Handles formatting of set expressions like {element1, element2, element3}.
 */
public class SetEnumerateConstruct implements TlaConstruct {

    @Override
    public String getName() {
        return "SET_ENUMERATE";
    }

    @Override
    public int getSupportedNodeKind() {
        return NodeKind.SET_ENUMERATE.getId();
    }

    @Override
    public Doc buildDoc(TreeNode node, ConstructContext context, int indentSize) {
        TreeNode[] z = node.zero();
        assert (z != null && z.length >= 2);

        List<Doc> elementDocs = BracketedListHelper.collectElements(z, context);

        if (elementDocs.isEmpty()) {
            return Doc.text("{}");
        }

        return BracketedListHelper.wrapInBrackets(
                context.buildChild(z[0]),
                BracketedListHelper.joinWithComma(elementDocs),
                context.buildChild(z[z.length - 1]),
                "{ ".length());
    }
}