// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
package tla2sany.parser;

import java.util.Vector;

public final class ParseErrors implements tla2sany.st.ParseErrors {
  private Vector loe;

  ParseErrors() { loe = new Vector(); };
  final boolean empty() { return loe.isEmpty(); }

  final void push( ParseError pe ) {
    loe.addElement( pe );
  }

  public final tla2sany.st.ParseError[] errors() {
    tla2sany.st.ParseError[] pes = new tla2sany.st.ParseError[ loe.size() ];
    for (int lvi = 0; lvi < pes.length; lvi++ )
      pes[ lvi ] = (ParseError)loe.elementAt( lvi );
    return pes;
  }
}
