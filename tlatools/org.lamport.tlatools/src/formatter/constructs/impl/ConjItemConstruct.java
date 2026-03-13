package formatter.constructs.impl;

import formatter.constructs.NodeKind;

public class ConjItemConstruct extends DisjItemConstruct {
    @Override
    public String getName() {
        return "N_ConjItem";
    }

    @Override
    public int getSupportedNodeKind() {
        return NodeKind.CONJ_ITEM.getId();
    }
}
