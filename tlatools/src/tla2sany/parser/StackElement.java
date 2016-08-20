// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
package tla2sany.parser;

class StackElement {
  int Kind;
  int Offset;

  StackElement( int o, int k) { Kind = k; Offset = o; }

	@Override
	public String toString() {
		return "StackElement [Kind=" + Kind + ", Offset=" + Offset + "]";
	}
}
