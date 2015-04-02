// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// jcg wrote this.
// Last modified on Wed  1 July 2009 at 16:30:00 PST by lamport
// last revised February 1st 2000

/***************************************************************************
* I think that the following comment is obsolete because the offending     *
* variable (lastSN) was eliminated when post-comments were eliminated.     *
***************************************************************************/
// XXX Watch out !!!
// This code uses a static variable to hold the last SyntaxTreeNode 
// previously generated from a Token. This is necessary to properly attach 
// the comments, but unfortunately makes the code non-reentrant.
//
// Removing this variable would require modifying the signature of 
// constructors which are extensively used, or possibly use a trick to 
// memorize these pointers for each thread.
 
package tla2sany.parser;

import tla2sany.semantic.ASTConstants;
import tla2sany.st.Location;
import tla2sany.st.SyntaxTreeConstants;
import tla2sany.st.TreeNode;
import tla2sany.utilities.Strings;
import util.UniqueString;

// The SyntaxTreeNode is the node of the syntax tree. It holds key 
// information from the tokens (string, position). Heirs are held in two 
// arrays. This is a trick to facilitate construction, and also to test 
// for the presence of the LOCAL token more easily.

// all strings are resolved internally to UniqueString.

/* methods
 * various constructors
 * kind manipulation : getKind, setKind, isKind
 * heirs()
 * getLocation()
 * getFileName, and US version.
 * possibly other methods to facilitate the semantic analysis.
 */

public class SyntaxTreeNode implements TreeNode, SyntaxTreeConstants, 
             ASTConstants {

  private static SyntaxTreeNode[] nullArray   = new SyntaxTreeNode[0];
  protected SyntaxTreeNode[]      zero, one;
    /***********************************************************************
    * The arrays `zero' and `one' describe the sequence of heirs, which    *
    * equals                                                               *
    *                                                                      *
    *   [i \in 1..zero.length |-> zero[i]]                                 *
    *        \o [i \in 1..one.length |-> one[i]]                           *
    *                                                                      *
    * Why there are two different arrays and how they are used is, of      *
    * course, completely undocumented.  The use I've found so far is:      *
    *                                                                      *
    *    For an N_OperatorDefinition, N_FunctionDefinition,                *
    *    N_ModuleDefinition, or N_Instance node, the optional "LOCAL"      *
    *    token is placed in the zero field (which is thus null if          *
    *    there is no "LOCAL" token, and the rest of the heirs are in       *
    *    the one field.                                                    *
    ***********************************************************************/
  int                             kind        = 0;
    /***********************************************************************
    * The type/kind of node.  The list of all kinds of non-terminal nodes  *
    * is in st/SyntaxTreeConstants.java.  If this is a terminal/token      *
    * node, formed from a token t, then `kind' seems to equal t.kind.      *
    * The list of all token kinds is in                                    *
    * parser/TLAplusParserConstants.java.  (That list begins with          *
    * "int EOF = 0" and ends with "int ProofStepLexeme = 222".)  Another   *
    * (currently incomplete) list is in documentation/token-kinds.txt.     *
    ***********************************************************************/
  public UniqueString             image       = null;
    /***********************************************************************
    * For a token node formed from a Token t, this equals t.image.  For a  *
    * non-terminal node, it is the name of the node type.                  *
    ***********************************************************************/

  public UniqueString             originalImage  = null;
    /***********************************************************************
    * This is a hack for dealing with step numbers of the form <*>...      *
    * and <+>...  .  For those step numbers, originalImage is the actual   *
    * image, while image is the UniqueString of the string obtained by     *
    * substituting the correct level number for the "*" or "+".            *
    *                                                                      *
    * This may result in strange error messages if the modified image is   *
    * printed instead of the originalImage.  If that turns out to be a     *
    * problem, Perhaps the error message generator can be changed to print *
    * originalImage if it's not null.                                      *
    *                                                                      *
    * (Added by LL 13 Oct 2007.)                                           *
    ***********************************************************************/

  int []                          location    = new int[4];
    /***********************************************************************
    *    location[0] = beginning line number                               *
    *    location[1] = beginning column number                             *
    *    location[2] = beginning line number                               *
    *    location[3] = beginning column number                             *
    *                                                                      *
    * If the node contains a single token t, then these are the four       *
    * values t.beginLine, t.beginColumn, t.endLine, and t.endColumn.  The  *
    * comments in parser/Token.java say that these "describe" the          *
    * positions of the first and last characters of the token, but they    *
    * don't say how they describe those positions.  (Since they're of      *
    * type int, we can at least assume that the descriptions are not in    *
    * English prose.)                                                      *
    *                                                                      *
    * For a node containing multiple tokens, it appears that under the     *
    * usual lexicographical ordering of pairs, <<location[0],              *
    * location[1]>> is the min of the values <<beginLine, beginColumn>>    *
    * of its tokens and that <<location[2], location[3]>> is the max of    *
    * the values <<endLine, endColumn>> of its tokens.                     *
    ***********************************************************************/
    
  private UniqueString            fileName    = null;
    /***********************************************************************
    * fileName seems to be the name of the module containing this node.    *
    ***********************************************************************/
  private static final String []  ns          = new String[0];
    /***********************************************************************
    * This just seemed to be a constant, so it was changed to a static     *
    * final field by LL on 21 Aug 2007.                                    *
    ***********************************************************************/
  private String []               preComment  = ns;
    /***********************************************************************
    * This is an array of length 0 unless this is a token node, in which   *
    * case it is the sequence of comments that immediately precede the     *
    * token in the input stream.                                           *
    ***********************************************************************/

//  private static SyntaxTreeNode   lastSN      = null;
    /***********************************************************************
    * In the original TLA+1 syntax, there were two kinds of comments:      *
    * pre-comments began "(*." or "\*." and post-comments didn't.          *
    * Pre-comments were attached to the following token node and           *
    * post-comments were attached to the previous token node.  This        *
    * distinction was eliminated in TLA+2, in which all comments are       *
    * pre-comments.                                                        *
    *                                                                      *
    * The field lastSN seems to be the static variable warned about in     *
    * the comments near the beginning of the file.  It was apparently set  *
    * equal to the last "token" node (node consisting of a single token)   *
    * that was created.  When a post-comment was discovered (attached by   *
    * javacc to the next token), lastSN.postComment was set to that        *
    * post-comment.                                                        *
    ***********************************************************************/

  public static SyntaxTreeNode nullSTN =
    new SyntaxTreeNode( UniqueString.uniqueStringOf("***I do not exist***") );

  public SyntaxTreeNode() {
    zero = nullArray; one = nullArray;
  }

  public SyntaxTreeNode( UniqueString fn ) {
    kind = 0; 
    image = fn;
    zero = nullArray;
    one = nullArray;
    location[0] = 0; location[1] = 0; location[2] = 0; location[3] = 0;
    fileName = UniqueString.uniqueStringOf("--TLA+ BUILTINS--");
  }


  public SyntaxTreeNode(UniqueString fn, Token t) {
    this.kind = t.kind; 
    this.image = UniqueString.uniqueStringOf( t.image );
    zero = nullArray; 
    one = nullArray;
    location[0] = t.beginLine;
    location[1] = t.beginColumn;
    location[2] = t.endLine;
    location[3] = t.endColumn;
    fileName = fn;
    preComment = comments( t );
  }


  public SyntaxTreeNode(UniqueString fn, int kind, Token t) {
    this.kind = kind;
//  this.image = SyntaxNodeImage[ kind ];
    /***********************************************************************
    * I have no idea why this was commented out, or by whom.               *
    ***********************************************************************/
    this.image = UniqueString.uniqueStringOf( t.image );
    zero = nullArray;
    one = nullArray;
    location[0] = t.beginLine;
    location[1] = t.beginColumn;
    location[2] = t.endLine;
    location[3] = t.endColumn;
    fileName = fn;
    preComment = comments( t );
  }


  public SyntaxTreeNode(UniqueString fn, int kind, SyntaxTreeNode a[]) {
    this.kind = kind;
    image = SyntaxNodeImage[ kind ];
    zero = a;
    fileName = fn;
    updateLocation();
  }


  public SyntaxTreeNode( int kind, SyntaxTreeNode a[]) {
    this.kind = kind;
    image = SyntaxNodeImage[ kind ];
    zero = a;
    fileName = a[0].fileName;
    updateLocation();
  }

  // This constructor used only in Generator class for handling @  in 
  // EXCEPT construct
  public SyntaxTreeNode( int kind, SyntaxTreeNode a[], boolean ignored) {
    this.kind = kind;
    zero = a;
  }


  public SyntaxTreeNode(UniqueString fn, int kind, SyntaxTreeNode a, 
                        SyntaxTreeNode b[]) {
    this.kind = kind;
    image = SyntaxNodeImage[ kind ];
    if (a != null) {
      zero = new SyntaxTreeNode[1]; 
      zero[0] = a;
    }
    one = b;
    fileName = fn;
    updateLocation();
  }


  public SyntaxTreeNode(UniqueString fn, int kind, SyntaxTreeNode a[], 
                        SyntaxTreeNode b[]) {
    this.kind = kind;
    image = SyntaxNodeImage[ kind ];
    zero = a;
    one = b;
    fileName = fn;
    updateLocation();
  }


  public SyntaxTreeNode(int kind, SyntaxTreeNode a, SyntaxTreeNode b) {
    this.kind = kind;
    image = SyntaxNodeImage[ kind ];
    fileName = a.fileName;
    zero = new SyntaxTreeNode[2];
    zero[0] = a;
    zero[1] = b;
    updateLocation();
  }


  public SyntaxTreeNode(int kind, SyntaxTreeNode a, SyntaxTreeNode b, 
                        SyntaxTreeNode c) {
    this.kind = kind;
    image = SyntaxNodeImage[ kind ];
    fileName = a.fileName;
    zero = new SyntaxTreeNode[3];
    zero[0] = a; 
    zero[1] = b;
    zero[2] = c;
    updateLocation();
  }


  public final int       getKind()         { return kind; }


         final void      setKind( int k )  { kind = k ; }


  public final boolean   isKind( int k )   { return kind == k; }


  public final String [] getPreComments()  { return preComment; }

   /***********************************************************************
   * For a token node, returns its pre-comments.  Otherwise, it returns   *
   * the pre-comments attached to the first token-node descendant of      *
   * this node.                                                           *
   ***********************************************************************/
  public final String [] getAttachedComments() {
    if (this.kind < SyntaxTreeConstants.NULL_ID) { return preComment; } ;
    if (this.heirs().length == 0) {
        String[] res = new String[0] ;
     /** 
      * On 3 Jul 2009 LL replaced the following code with this.  It
      * appears that this method was never used until printing of 
      * comments in debug mode was added in Jul 2009.
      */
//      String[] res = new String[1] ;
//      res[0] = "No left-most token node???" ;
      return res ; } ;
    return ((SyntaxTreeNode) this.heirs()[0]).getAttachedComments() ;
   }

  public boolean isGenOp() {
    if ( kind == N_GenPrefixOp || kind == N_GenNonExpPrefixOp || 
         kind == N_GenInfixOp || kind == N_GenPostfixOp )
       return true;
    else
      return false;
  }


  private static Token nullToken = new Token();


  private final String[] comments( Token t ) {
     Token nextPre  = nullToken;
     int cPre = 0;

     if (t.specialToken == null) {
       return ns; } ;

     Token tmp_t = t.specialToken;
     while (tmp_t != null) {
         cPre++;
         tmp_t.next = nextPre;
         nextPre = tmp_t;
         tmp_t = tmp_t.specialToken; } ;

     String []aPre = new String[ cPre ];
     tmp_t = nextPre; 
     cPre = 0;
     while (tmp_t != nullToken) { 
       aPre[ cPre ] = tmp_t.image; 
       cPre++; 
       tmp_t = tmp_t.next; } ; 
     return aPre;
  }

  /**
   * Through some piece of stupidity whose origin is lost to history,
   * the heirs() method declares its return value type to be
   * TreeNode[].  This results in a lot of needless type casting, 
   * since the only class that implements the TreeNode interface
   * seems to be SyntaxTreeNode.  Eclipse doesn't seem to be able
   * to find the errors that are caused by simply changing the
   * return type of heirs() to SyntaxTreeNode[]; it just finds errors
   * when it runs ant.  So, LL added this method, which is line-for-line
   * identical to heirs() except for the declaration of the return type.
   */
  public final SyntaxTreeNode[] getHeirs() {
    if ( zero == null && one == null ) {
      return nullArray;
    } else {
      SyntaxTreeNode result[];
      if ( zero != null ) {
        if ( one != null ) {
          result = new SyntaxTreeNode[ zero.length + one.length ];
          System.arraycopy(zero, 0, result, 0, zero.length);
          System.arraycopy(one, 0, result, zero.length, one.length);
        } else {
          result = new SyntaxTreeNode[ zero.length ];
          System.arraycopy(zero, 0, result, 0, zero.length);
        }
      } else {
        result = new SyntaxTreeNode[ one.length ];
        System.arraycopy(one, 0, result, 0, one.length);
      }
      return result;
    }
  }
  
  public final TreeNode[] heirs() {
    if ( zero == null && one == null ) {
      return nullArray;
    } else {
      SyntaxTreeNode result[];
      if ( zero != null ) {
        if ( one != null ) {
          result = new SyntaxTreeNode[ zero.length + one.length ];
          System.arraycopy(zero, 0, result, 0, zero.length);
          System.arraycopy(one, 0, result, zero.length, one.length);
        } else {
          result = new SyntaxTreeNode[ zero.length ];
          System.arraycopy(zero, 0, result, 0, zero.length);
        }
      } else {
        result = new SyntaxTreeNode[ one.length ];
        System.arraycopy(one, 0, result, 0, one.length);
      }
      return result;
    }
  }
  

  public final String         getFilename() {return fileName.toString(); }

  public final UniqueString   getFN() { return fileName; }

  public final Location       getLocation( ) {
    return new Location( fileName, location[0], location[1], location[2], 
                         location[3] );
   }

  public final String         getImage() { return image.toString(); }

  public final UniqueString   getUS() { return image; }

  public final SyntaxTreeNode first() {
    //System.out.println( image);
    if (zero != null) return zero[0]; else return one[0]; 
  }
  
	public String getHumanReadableImage() {
		if (zero != null && zero.length > 0) {
			final StringBuffer buf = new StringBuffer(zero.length);
			for (SyntaxTreeNode z : zero) {
				buf.append(z.getHumanReadableImage());
			}
			if (one != null && one.length > 0) {
				for (SyntaxTreeNode o : one) {
					buf.append(o.getHumanReadableImage());
				}
			}
			return buf.toString();
		} else {
			final String string = image.toString();
			// See SyntaxTreeNodeConstants. The strings below are the ones with
			// which non-human-readable images start.
			if (string.startsWith("N_")) {
				return "";
			}
			if (string.startsWith("Not a node")) {
				return "";
			}
			if (string.startsWith("Token")) {
				return "";
			}
			return string;
		}
	}
  
  /******************
 * Bogus old version
 */
//  private void updateLocation() {
//    int lvi = 0;
//    location[0] = java.lang.Integer.MAX_VALUE;
//    location[1] = java.lang.Integer.MAX_VALUE;
//    location[2] = java.lang.Integer.MIN_VALUE;
//    location[3] = java.lang.Integer.MIN_VALUE;
//
//    if ( zero != null) {
//      for ( lvi = 0; lvi < zero.length; lvi++ ) {
//        if ( zero[lvi].location[0] != java.lang.Integer.MAX_VALUE ) {
//          location[0] = Math.min ( location[0], zero[lvi].location[0] );
//          if ( location[0] == zero[lvi].location[0] )
//            location[1] = Math.min ( location[1], zero[lvi].location[1]) ;
//          location[2] = Math.max ( location[2], zero[lvi].location[2]);
//          if ( location[2] == zero[lvi].location[2] )
//            location[3] = Math.max ( location[3], zero[lvi].location[3]);
//        }
//      }
//    }
//
//    if ( one != null) {
//      for ( lvi=0; lvi < one.length; lvi++ ) {
//        if ( one[lvi].location[0] != java.lang.Integer.MAX_VALUE ) {
//          location[0] = Math.min ( location[0], one[lvi].location[0] );
//          if ( location[0] == one[lvi].location[0] )
//            location[1] = Math.min ( location[1], one[lvi].location[1]) ;
//          location[2] = Math.max ( location[2], one[lvi].location[2]);
//          if ( location[2] == one[lvi].location[2] )
//            location[3] = Math.max ( location[3], one[lvi].location[3]);
//        }
//      }
//    }
//  }

  /**
   * updateLocation() computes the location field from the location fields
   * of the heirs (descendants).  This would seem to be a matter of just
   * copying the location fields of the first and last heirs, in the 
   * obvious way.  However, there seem to be some nodes with no heirs
   * that have their locations set to
   *  
   *   (java.lang.Integer.MAX_VALUE, ...MAX_VALUE, ...MIN_VALUE, ...MIN_VALUE)
   * 
   * The only ones I've found are N_IdPrefix nodes, which don't have any
   * corresponding tokens in the module.  Instead of being efficient and
   * looking for the first and last heirs that have a real location, we
   * write a simple loop that works regardless of how the heirs are
   * ordered.   LL 26 Nov 2009
   */
  private void updateLocation() {
      int lvi = 0;
      location[0] = java.lang.Integer.MAX_VALUE;
      location[1] = java.lang.Integer.MAX_VALUE;
      location[2] = java.lang.Integer.MIN_VALUE;
      location[3] = java.lang.Integer.MIN_VALUE;
      
      if ( zero != null) {
        for ( lvi = 0; lvi < zero.length; lvi++ ) {

            if ( (zero[lvi].location[0] < location[0] )
                  || (zero[lvi].location[0] == location[0] && zero[lvi].location[1] < location[1])) {
            location[0] = zero[lvi].location[0] ;
            location[1] = zero[lvi].location[1] ;
           }
          if ( (zero[lvi].location[2] > location[2] )
                  || (zero[lvi].location[2] == location[2] && zero[lvi].location[3] > location[3])) {
            location[2] = zero[lvi].location[2] ;
            location[3] = zero[lvi].location[3] ;
           }
        }
      }

      if ( one != null) {
          for ( lvi = 0; lvi < one.length; lvi++ ) {
              if ( (one[lvi].location[0] < location[0] )
                      || (one[lvi].location[0] == location[0] && one[lvi].location[1] < location[1])) {
                location[0] = one[lvi].location[0] ;
                location[1] = one[lvi].location[1] ;
               }
              if ( (one[lvi].location[2] > location[2] )
                      || (one[lvi].location[2] == location[2] && one[lvi].location[3] > location[3])) {
                location[2] = one[lvi].location[2] ;
                location[3] = one[lvi].location[3] ;
               }
            }
      }
    }


  public final tla2sany.st.TreeNode[] one() { return one; }

  public final tla2sany.st.TreeNode[] zero() { return zero; }

  /*************************************************************************
  * Aha! This seems to prove that whenever a node may start with "LOCAL",  *
  * the "LOCAL" token is put in the array zero and the rest of the tokens  *
  * are put in the array one.                                              *
  *************************************************************************/
  public final boolean local() { return zero!= null; }

  public void printST(int indentLevel) {

    String      operator = "";
    TreeNode [] heirs    = this.heirs();

    if (image != null && image.toString().equals("N_OperatorDefinition")) {
       if (((SyntaxTreeNode)(heirs()[0])).image.toString().equals(
                                              "N_IdentLHS")) {
          operator = "*" + ((SyntaxTreeNode)(((SyntaxTreeNode)(
                              heirs()[0])).heirs()[0])).image.toString();
       }
       if (((SyntaxTreeNode)(heirs()[1])).image.toString().equals(
                                                    "N_IdentLHS")) {
          operator = ((SyntaxTreeNode)(((SyntaxTreeNode)(
                              heirs()[1])).heirs()[0])).image.toString();
       }
       if (((SyntaxTreeNode)(heirs()[0])).image.toString().equals(
                                                    "N_InfixLHS")) {
          operator = ((SyntaxTreeNode)(((SyntaxTreeNode)(
                            heirs()[0])).heirs()[1])).image.toString();
       }
    }

    for (int i = 0; i < indentLevel; i++) System.out.print(Strings.blanks[2]);
    
    System.out.print((image == null ? "(" + SyntaxNodeImage[kind].toString() 
         + ")" : image.toString()) 
         + "\t" + (operator != "" ? operator + "\t" : "")
         + "  #heirs: " + heirs.length + "\t"
         + "  kind:   " + kind + PreCommentToString(preComment) + "\n"      
                  // Printing of preComment added by LL on 2 Jul 2009
    );

    for (int i=0; i<heirs.length; i++) {
      if (heirs[i] != null)
        ((SyntaxTreeNode)heirs[i]).printST(indentLevel+1);  
                // Indent 1 more level
      else {
        for (int j = 0; j <= indentLevel; j++) {
            System.out.print(Strings.blanks[2]);} ;
        System.out.println("<null>");
      } // end else
    } // end for
    
  } // end method
 
  public static String PreCommentToString(String[] pcarray) {
    if (pcarray == null || pcarray.length == 0) {return "";};
    String res = "\n preComment: ";
    for (int i = 0; i < pcarray.length; i++) {
      res = res +  ((i==0)?"":"\n             ") + i + " " + pcarray[i];
    };
    return res ;
  }
  }
