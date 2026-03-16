package formatter.constructs.impl;

import formatter.constructs.NodeKind;

/**
 * Construct implementation for generic infix operators.
 * Handles formatting of infix operators like :>, @@, /\, \/, etc.
 * Uses AbstractAppendImageConstruct to process children via buildChild,
 * which preserves comments attached to inner operator tokens (kind=373).
 */
public class GenInfixOpConstruct extends AbstractAppendImageConstruct {

    @Override
    public String getName() {
        return "GEN_INFIX_OP";
    }

    @Override
    public int getSupportedNodeKind() {
        return NodeKind.GEN_INFIX_OP.getId();
    }
}
