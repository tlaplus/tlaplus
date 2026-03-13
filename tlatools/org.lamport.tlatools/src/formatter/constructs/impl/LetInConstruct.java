package formatter.constructs.impl;

import com.opencastsoftware.prettier4j.Doc;
import formatter.constructs.ConstructContext;
import formatter.constructs.NodeKind;
import formatter.constructs.TlaConstruct;
import tla2sany.st.TreeNode;

import java.util.Arrays;
import java.util.List;
import java.util.stream.Collectors;

public class LetInConstruct implements TlaConstruct {
    @Override
    public String getName() {
        return "N_LetIn";
    }

    @Override
    public int getSupportedNodeKind() {
        return NodeKind.LET_IN.getId();
    }

    @Override
    public Doc buildDoc(TreeNode node, ConstructContext context, int indentSize) {
        var z = node.zero();
        assert (z != null && z.length >= 4);
        List<Doc> zDoc = Arrays.stream(z).map(context::buildChild).collect(Collectors.toList());

        return Doc.group(
                zDoc.get(0) // let
                        .appendSpace(zDoc.get(1).align()) // definitions
                        .appendLineOrSpace(zDoc.get(2)) // in
                        .appendSpace(zDoc.get(3).indent("LET ".length())) // body
        );
    }
}
