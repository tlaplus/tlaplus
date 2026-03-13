package formatter.constructs.impl;

import com.opencastsoftware.prettier4j.Doc;
import formatter.constructs.ConstructContext;
import formatter.constructs.NodeKind;
import formatter.constructs.TlaConstruct;
import tla2sany.st.TreeNode;

/**
 * Construct implementation for operator definitions.
 * Handles formatting of "Op == expr" constructs.
 * N_IdentLHS == expr
 * S == 1 or S(x) == x + 1
 * or a \odot b == c
 * node.one()[0].zero()[0] is (usually) the identifier.
 * node.one()[1] has the == sign.
 */
public class OperatorConstruct implements TlaConstruct {

    @Override
    public String getName() {
        return "OPERATOR";
    }

    @Override
    public int getSupportedNodeKind() {
        return NodeKind.OPERATOR_DEFINITION.getId();
    }

    @Override
    public Doc buildDoc(TreeNode node, ConstructContext context, int indentSize) {
        var o = node.one();
        assert (o != null && o.length >= 3);

        // zero[] contains qualifiers like LOCAL
        Doc qualifier = Doc.empty();
        if (node.zero() != null && node.zero().length > 0) {
            for (TreeNode z : node.zero()) {
                qualifier = qualifier.append(context.buildChild(z)).appendSpace(Doc.empty());
            }
        }

        var name = context.buildChild(o[0]);
        var exprNode = context.buildChild(o[2]);

        int exprKind = o[2].getKind();
        boolean isConjDisjList = exprKind == NodeKind.CONJ_LIST.getId()
                || exprKind == NodeKind.DISJ_LIST.getId();

        if (isConjDisjList) {
            // Always break after == for conjunction/disjunction lists
            return qualifier.append(name
                    .appendSpace(Doc.text("=="))
                    .append(Doc.line().append(exprNode)
                            .indent(indentSize)));
        }

        return qualifier.append(name
                .appendSpace(Doc.text("=="))
                .append(Doc
                        .group(Doc.lineOrSpace().append(exprNode))
                        .indent(indentSize)));
    }
}