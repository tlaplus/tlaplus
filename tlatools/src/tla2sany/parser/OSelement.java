// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
package tla2sany.parser;

final class OSelement {
  Operator op;
  SyntaxTreeNode  node;
  int kind;

  OSelement( SyntaxTreeNode n ) { node = n; op = null; }
  OSelement( SyntaxTreeNode n, Operator o ) { node = n; op = o; }

  final Operator getOperator() { return op; }
  final SyntaxTreeNode  getNode() { return node; }
  final boolean  isOperator() { return op != null; }
}