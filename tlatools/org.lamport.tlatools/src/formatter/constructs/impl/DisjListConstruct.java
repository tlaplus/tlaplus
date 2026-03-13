package formatter.constructs.impl;

import com.opencastsoftware.prettier4j.Doc;
import formatter.constructs.ConstructContext;
import formatter.constructs.NodeKind;
import formatter.constructs.TlaConstruct;
import tla2sany.st.TreeNode;

import java.util.Arrays;
import java.util.List;
import java.util.stream.Collectors;

public class DisjListConstruct implements TlaConstruct {
    @Override
    public String getName() {
        return "N_DisjList";
    }

    @Override
    public int getSupportedNodeKind() {
        return NodeKind.DISJ_LIST.getId();
    }

    @Override
    public Doc buildDoc(TreeNode node, ConstructContext context, int indentSize) {
        var z = node.zero();
        assert (z != null && z.length > 0);
        List<Doc> zDoc = Arrays.stream(z)
                .map(context::buildChild)
                .collect(Collectors.toList());
        return Doc.intersperse(Doc.line(), zDoc).align();
    }
}
