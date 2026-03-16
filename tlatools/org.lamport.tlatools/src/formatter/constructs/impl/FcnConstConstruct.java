package formatter.constructs.impl;

import com.opencastsoftware.prettier4j.Doc;
import formatter.constructs.ConstructContext;
import formatter.constructs.NodeKind;
import formatter.constructs.TlaConstruct;
import tla2sany.st.TreeNode;

/**
 *
 * pc = [self \in ProcSet |-> CASE self = 0 -> "TM"
 * [] self \in ResourceManagers -> "RM"]
 */
public class FcnConstConstruct implements TlaConstruct {
    @Override
    public String getName() {
        return "FcnConst";
    }

    @Override
    public int getSupportedNodeKind() {
        return NodeKind.FCN_CONST.getId();
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
        assert (z != null && z.length >= 5);

        // Structure for function constants:
        // Single bound: [ qBound |-> expr ]
        //   z[0]=[ z[1]=qBound z[2]=|-> z[3]=expr z[4]=]
        // Multi-bound: [ qBound1 , qBound2 |-> expr ]
        //   z[0]=[ z[1]=qBound1 z[2]=, z[3]=qBound2 z[4]=|-> z[5]=expr z[6]=]

        // Find the |-> symbol (it's always 3rd from the end: |-> expr ])
        int mapSymbolIndex = z.length - 3;

        // Build all quantifier bounds (from index 1 to mapSymbolIndex-1, inclusive)
        Doc qBounds = context.buildChild(z[1]);
        for (int i = 2; i < mapSymbolIndex; i++) {
            qBounds = qBounds.append(context.buildChild(z[i])); // comma
            i++;
            if (i < mapSymbolIndex) {
                qBounds = qBounds.appendSpace(context.buildChild(z[i])); // next bound
            }
        }

        var mapSymbol = context.buildChild(z[mapSymbolIndex]); // |->
        var mapExpr = context.buildChild(z[mapSymbolIndex + 1]); // expression
        // z[mapSymbolIndex + 2] = ]

        return Doc.group(
                context.buildChild(z[0]) // [
                        .append(qBounds)
                        .appendSpace(mapSymbol)
                        .appendLineOrSpace(mapExpr).indent(indentSize)
        ).appendLineOrEmpty(context.buildChild(z[mapSymbolIndex + 2])); // ]
    }
}
