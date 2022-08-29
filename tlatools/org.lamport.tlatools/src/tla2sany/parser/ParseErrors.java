// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
package tla2sany.parser;

import java.util.ArrayList;

public final class ParseErrors implements tla2sany.st.ParseErrors {
    private final ArrayList<ParseError> loe;

    ParseErrors() {
        loe = new ArrayList<>();
    }

    boolean empty() {
        return loe.isEmpty();
    }

    void push(final ParseError pe) {
        loe.add(pe);
    }

    @Override
    public tla2sany.st.ParseError[] errors() {
        final tla2sany.st.ParseError[] pes = new tla2sany.st.ParseError[loe.size()];
        for (int lvi = 0; lvi < pes.length; lvi++)
            pes[lvi] = loe.get(lvi);
        return pes;
    }
}
