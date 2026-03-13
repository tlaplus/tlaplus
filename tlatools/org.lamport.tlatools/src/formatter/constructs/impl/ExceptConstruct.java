package formatter.constructs.impl;

import com.opencastsoftware.prettier4j.Doc;
import formatter.constructs.ConstructContext;
import formatter.constructs.NodeKind;
import formatter.constructs.TlaConstruct;
import tla2sany.st.TreeNode;

import java.util.Arrays;
import java.util.stream.Collectors;

/**
 * Example: [towersEXCEPT![from]=towers[from]-disk,![to]=towers[to]+disk]
 */
public class ExceptConstruct implements TlaConstruct {
    @Override
    public String getName() {
        return "N_Except";
    }

    @Override
    public int getSupportedNodeKind() {
        return NodeKind.EXCEPT.getId();
    }

    @Override
    public Doc buildDoc(TreeNode node, ConstructContext context, int indentSize) {
        var z = node.zero();
        assert (z != null);
        var zDoc = Arrays.stream(z).map(context::buildChild).collect(Collectors.toList());
        var lSPar = zDoc.get(0);
        var rSPar = zDoc.get(z.length - 1);
        var name = zDoc.get(1);
        var exceptKey = zDoc.get(2);
        var comps = zDoc.get(3);
        for (int i = 4; i < zDoc.size() - 1; i++) {
            var el = zDoc.get(i);
            if (z[i].getImage().equals(",")) {
                continue;
            }
            if (z[i].getImage().equals("]")) {
                break;
            }
            comps = comps.append(Doc.text(",")).appendLineOrSpace(el);
        }
        return Doc.group(
                lSPar.append(name)
                        .appendSpace(exceptKey)
                        .appendLineOrSpace(comps)
                        .append(rSPar)
        );
    }
}
