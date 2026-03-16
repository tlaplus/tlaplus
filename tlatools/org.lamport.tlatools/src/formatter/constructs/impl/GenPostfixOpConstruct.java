package formatter.constructs.impl;

import formatter.constructs.NodeKind;

public class GenPostfixOpConstruct extends AbstractAppendImageConstruct {
    @Override
    public int getSupportedNodeKind() {
        return NodeKind.GEN_POSTFIX_OP.getId();
    }

    @Override
    public String getName() {
        return "N_GenPostfixOp";
    }
}
