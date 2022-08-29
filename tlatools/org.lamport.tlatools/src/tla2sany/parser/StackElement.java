// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
package tla2sany.parser;

class StackElement {
    final int Kind;
    final int Offset;

    StackElement(final int o, final int k) {
        Kind = k;
        Offset = o;
    }
}
