package formatter.constructs.impl;

import formatter.constructs.NodeKind;

/**
 * Example: 'R**T'
 */
public class InfixLhsConstruct extends AbstractAppendImageConstruct {
    @Override
    public int getSupportedNodeKind() {
        return NodeKind.INFIX_LHS.getId();
    }

    @Override
    public String getName() {
        return "N_InfixLHS";
    }
}
