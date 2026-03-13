package formatter.constructs.impl;

import com.opencastsoftware.prettier4j.Doc;
import formatter.constructs.ConstructContext;
import formatter.constructs.NodeKind;
import formatter.constructs.TlaConstruct;
import tla2sany.st.TreeNode;

import java.util.List;

/**
 * Construct implementation for tuples.
 * Handles formatting of tuple expressions like <<element1, element2, element3>>.
 */
public class TupleConstruct implements TlaConstruct {

    @Override
    public String getName() {
        return "TUPLE";
    }

    @Override
    public int getSupportedNodeKind() {
        return NodeKind.TUPLE.getId();
    }

    @Override
    public Doc buildDoc(TreeNode node, ConstructContext context, int indentSize) {
        TreeNode[] z = node.zero();
        assert (z != null && z.length >= 2);

        TreeNode openBracket = z[0];
        Doc openDoc = ConstructContext.addComments(openBracket, Doc.text("<<"));

        List<Doc> elementDocs = BracketedListHelper.collectElements(z, context);

        if (elementDocs.isEmpty()) {
            return ConstructContext.addComments(openBracket, Doc.text("<<>>"));
        }

        Doc closeDoc = ConstructContext.addComments(z[z.length - 1], Doc.text(">>"));

        return BracketedListHelper.wrapInBrackets(
                openDoc,
                BracketedListHelper.joinWithComma(elementDocs),
                closeDoc,
                "<< ".length());
    }
}