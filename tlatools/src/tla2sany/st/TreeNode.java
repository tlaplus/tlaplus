// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// jcg wrote this.
// last revised February 3rd 2000

// Interface to the syntax tree node data structure.

package tla2sany.st;

public interface TreeNode {
  public TreeNode[]             heirs();           // always returns an array, never null
  public String                 getFilename();
  public Location               getLocation();
  public String                 getImage();
  public int                    getKind();
  public boolean                isKind( int k );
  public TreeNode[]             zero();
  public TreeNode[]             one();
  public util.UniqueString      getUS();
  public String[]               getPreComments();  // always returns an array, never null
//  public String[]               getPostComments(); // always returns an array, never null
  public boolean                local();
  public void                   printST(int indentation);
}
