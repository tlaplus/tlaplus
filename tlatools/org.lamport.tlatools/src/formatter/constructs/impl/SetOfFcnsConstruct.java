package formatter.constructs.impl;

import com.opencastsoftware.prettier4j.Doc;
import formatter.constructs.ConstructContext;
import formatter.constructs.NodeKind;
import formatter.constructs.TlaConstruct;
import tla2sany.st.TreeNode;

import java.util.Arrays;
import java.util.List;
import java.util.stream.Collectors;

public class SetOfFcnsConstruct implements TlaConstruct {
    @Override
    public String getName() {
        return "N_SetOfFcns";
    }

    @Override
    public int getSupportedNodeKind() {
        return NodeKind.SET_OF_FCNS.getId();
    }

    @Override
    public Doc buildDoc(TreeNode node, ConstructContext context, int indentSize) {
        var z = node.zero();
        assert (z != null && z.length == 5);
        List<Doc> zDoc = Arrays.stream(z).map(context::buildChild).collect(Collectors.toList());
        var par = zDoc.get(0);
        var domain = zDoc.get(1);
        var mapSymbol = zDoc.get(2);
        var codomain = zDoc.get(3);
        var endPar = zDoc.get(4);
        return Doc.group(par
                .append(domain)
                .appendLineOrSpace(mapSymbol)
                .appendLineOrSpace(codomain)
                .append(endPar)
        );

    }
}
