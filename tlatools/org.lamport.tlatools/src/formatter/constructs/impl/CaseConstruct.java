package formatter.constructs.impl;

import com.opencastsoftware.prettier4j.Doc;
import formatter.constructs.ConstructContext;
import formatter.constructs.NodeKind;
import formatter.constructs.TlaConstruct;
import tla2sany.st.TreeNode;

import java.util.ArrayList;
import java.util.List;

public class CaseConstruct implements TlaConstruct {
    @Override
    public String getName() {
        return "N_Case";
    }

    @Override
    public int getSupportedNodeKind() {
        return NodeKind.CASE.getId();
    }

    /*
      /\ pc =
           [
             self \in ProcSet
             |->
             CASE self \in SlushQueryProcess -> "QueryReplyLoop"
             [] self \in SlushLoopProcess -> "RequireColorAssignment"
             [] self = "ClientRequest" -> "ClientRequestLoop"
           ]
     */
    @Override
    public Doc buildDoc(TreeNode node, ConstructContext context, int indentSize) {
        var z = node.zero();
        assert (z != null && z.length >= 3);
        List<Doc> caseDocs = new ArrayList<>();
        for (int i = 0; i < z.length; i += 2) {
            var bracket = context.buildChild(z[i]);
            var caseArm = context.buildChild(z[i + 1]);
            caseDocs.add(bracket.appendSpace(caseArm));
        }
        return Doc.intersperse(Doc.line(), caseDocs).align();
    }
}
