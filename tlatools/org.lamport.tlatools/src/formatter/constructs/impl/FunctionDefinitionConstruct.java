package formatter.constructs.impl;

import com.opencastsoftware.prettier4j.Doc;
import formatter.constructs.ConstructContext;
import formatter.constructs.NodeKind;
import formatter.constructs.TlaConstruct;
import tla2sany.st.TreeNode;

import java.util.Arrays;
import java.util.stream.Collectors;

/**
 * Handles function definition constructs.
 * Example: `f[x \in S] == expr`
 * Example: `HostOf[pid \in SlushLoopProcess \cup SlushQueryProcess] == ...`
 */
public class FunctionDefinitionConstruct implements TlaConstruct {
    @Override
    public String getName() {
        return "N_FunctionDefinition";
    }

    @Override
    public int getSupportedNodeKind() {
        return NodeKind.FUNCTION_DEFINITION.getId();
    }

    @Override
    public Doc buildDoc(TreeNode node, ConstructContext context, int indentSize) {
        var o = node.one();
        assert (o != null && o.length >= 6);
        var oDoc = Arrays.stream(o).map(context::buildChild).collect(Collectors.toList());
        var boundVars = oDoc.get(2);
        for (int i = 3; i < o.length - 3; i++) {
            if (o[i].getImage().equals(",")) {
                boundVars = boundVars.append(oDoc.get(i));
                continue;
            }
            boundVars = boundVars.appendLineOrSpace(oDoc.get(i));
        }

        return Doc.group(
                oDoc.get(0) // function name
                        .append(oDoc.get(1))// [
                        .append(boundVars) // one or more comma separated bound variables
                        .append(oDoc.get(o.length - 3)) // ]
                        .appendSpace(oDoc.get(o.length - 2)) // ==
                        .appendLineOrSpace(oDoc.get(o.length - 1)) // expr
        ).indent(indentSize);
    }
}
