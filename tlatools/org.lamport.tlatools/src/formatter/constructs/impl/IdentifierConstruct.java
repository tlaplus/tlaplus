package formatter.constructs.impl;

import formatter.constructs.NodeKind;

public class IdentifierConstruct extends AbstractAppendImageConstruct {

    @Override
    public String getName() {
        return "IDENTIFIER";
    }

    @Override
    public int getSupportedNodeKind() {
        return NodeKind.GENERAL_ID.getId();
    }
}