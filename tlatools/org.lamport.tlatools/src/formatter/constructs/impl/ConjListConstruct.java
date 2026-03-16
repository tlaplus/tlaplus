package formatter.constructs.impl;

import formatter.constructs.NodeKind;

public class ConjListConstruct extends DisjListConstruct {
    @Override
    public String getName() {
        return "N_ConjList";
    }

    @Override
    public int getSupportedNodeKind() {
        return NodeKind.CONJ_LIST.getId();
    }

}
