package formatter.constructs.impl;

import com.opencastsoftware.prettier4j.Doc;
import formatter.constructs.ConstructContext;
import formatter.constructs.NodeKind;
import formatter.constructs.TlaConstruct;
import tla2sany.st.TreeNode;

public class TimesConstruct implements TlaConstruct {

    @Override
    public String getName() {
        return "N_Times";
    }

    @Override
    public int getSupportedNodeKind() {
        return NodeKind.TIMES.getId();
    }

    @Override
    public Doc buildDoc(TreeNode node, ConstructContext context, int indentSize) {
        var z = node.zero();
        assert (z != null);
        assert (z.length >= 3);
        // Expected structure (chained):
        // zero[0]: A, zero[1]: \X, zero[2]: B [, zero[3]: \X, zero[4]: C ...]

        Doc result = context.buildChild(z[0]);
        for (int i = 1; i + 1 < z.length; i += 2) {
            Doc operator = context.buildChild(z[i]);
            Doc operand = context.buildChild(z[i + 1]);
            result = result.appendSpace(operator).appendLineOrSpace(operand);
        }

        return Doc.group(result.indent(indentSize));
    }
}
