// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
package tla2sany.parser;

final class OSelement {
    final Operator op;
    final SyntaxTreeNode node;
    int kind;

    OSelement(final SyntaxTreeNode n) {
        node = n;
        op = null;
    }

    OSelement(final SyntaxTreeNode n, final Operator o) {
        node = n;
        op = o;
    }

    Operator getOperator() {
        return op;
    }

    SyntaxTreeNode getNode() {
        return node;
    }

    boolean isOperator() {
        return op != null;
    }
}