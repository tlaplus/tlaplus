package formatter.constructs.impl;

import formatter.constructs.NodeKind;

/**
 * Example: `-` (as in -1).
 */
public class GenInfixOp extends AbstractAppendImageConstruct {
    @Override
    public int getSupportedNodeKind() {
        return NodeKind.GEN_PREFIX_OP.getId();
    }

    @Override
    public String getName() {
        return "N_GenInfixOp";
    }
}
