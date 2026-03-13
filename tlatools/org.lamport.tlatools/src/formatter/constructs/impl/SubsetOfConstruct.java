package formatter.constructs.impl;

import com.opencastsoftware.prettier4j.Doc;
import formatter.constructs.ConstructContext;
import formatter.constructs.NodeKind;
import formatter.constructs.TlaConstruct;
import tla2sany.st.TreeNode;

import java.util.Arrays;
import java.util.List;
import java.util.stream.Collectors;

/**
 * Example: {x\in1..max:/\(r-1)=<(wt-x)/\wt=<x*r}
 */
public class SubsetOfConstruct implements TlaConstruct {

    @Override
    public String getName() {
        return "N_SubsetOf";
    }

    @Override
    public int getSupportedNodeKind() {
        return NodeKind.SUBSET_OF.getId();
    }

    @Override
    public Doc buildDoc(TreeNode node, ConstructContext context, int indentSize) {
        var z = node.zero();
        List<Doc> zDoc = Arrays.stream(z).map(context::buildChild).collect(Collectors.toList());
        var header = zDoc.get(0) // {
                .append(zDoc.get(1)) // x or a tuple like <<r,t>>
                .appendSpace(zDoc.get(2)) //\in
                .appendSpace(zDoc.get(3)) // S
                .append(zDoc.get(4)); // :
        return Doc.group(
                header
                        .appendLineOrSpace(zDoc.get(5)) // predicate
                        .indent(indentSize)
                        .appendLineOrEmpty(zDoc.get(6))); // }
    }
}
