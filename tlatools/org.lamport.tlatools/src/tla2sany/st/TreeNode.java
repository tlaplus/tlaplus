// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// jcg wrote this.
// last revised February 3rd 2000

// Interface to the syntax tree node data structure.

package tla2sany.st;

public interface TreeNode {
    TreeNode[] heirs();           // always returns an array, never null

    String getFilename();

    Location getLocation();

    String getImage();

    int getKind();

    boolean isKind(int k);

    TreeNode[] zero();

    TreeNode[] one();

    util.UniqueString getUS();

    String[] getPreComments();  // always returns an array, never null

    //  public String[]               getPostComments(); // always returns an array, never null
    boolean local();

    void printST(int indentation);

    String getHumanReadableImage();
}
