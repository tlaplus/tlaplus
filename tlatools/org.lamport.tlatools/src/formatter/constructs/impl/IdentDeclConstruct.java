package formatter.constructs.impl;

import formatter.constructs.NodeKind;

public class IdentDeclConstruct extends AbstractAppendImageConstruct {

    @Override
    public int getSupportedNodeKind() {
        return NodeKind.IDENT_DECL.getId();
    }

    @Override
    public String getName() {
        return "N_IdentDecl";
    }
}
