// Copyright (c) 2003 Compaq Corporation.  All rights reserved.

/***************************************************************************
* CLASS Symbol                                                             *
*                                                                          *
* A Symbol object describes a built-in symbol of TLA.  It is essentially   *
* a record, with its fields made public.  It contains the following        *
* fields:                                                                  *
*                                                                          *
*    TLAString     : How the symbol appears in the input file.             *
*                                                                          *
*    TeXString     : The LaTeX input to print the symbol.                  *
*                                                                          *
*    symbolType    : A classification.                                     *
*                                                                          *
*    alignmentType : Two symbols are candidates for alignment iff          *
*                    they have the same non-zero alignmentType.            *
***************************************************************************/
package tla2tex;

public class Symbol
  { public String TLAString;
      /*********************************************************************
      * The TLA representation of the symbol.  There is a different        *
      * Symbol object for each way of writing the same symbol--for         *
      * example, there are separate symbol objects for "#" and "/=".       *
      *********************************************************************/

    public String TeXString;
      /*********************************************************************
      * The TeX input that prints the symbol.                              *
      *********************************************************************/
      
    public int symbolType ;
      /*********************************************************************
      * The type of symbol it is.  Here are the possibilities:             *
      *********************************************************************/
                                                 /* Examples              */
                                                 /* ~~~~~~~~              */
      public static final int INFIX        =  1 ;  /* "+"  ":"  "-"       */
      public static final int PREFIX       =  2 ;  /*"\A" "ENABLED"       */
      public static final int POSTFIX      =  3 ;  /* "^#" "'"            */
      public static final int LEFT_PAREN   =  4 ;  /* "("  "<<"           */
      public static final int RIGHT_PAREN  =  5 ;  /* ")"  ">>"           */
      public static final int SUBSCRIPTED  =  6 ;  /* "WF_" "]_"          */
      public static final int KEYWORD      =  7 ;  /* "THEOREM"           */
      public static final int PUNCTUATION  =  8 ;  /* ","                 */
      public static final int MISC         =  9 ;  /* "-."                */
      public static final int NOT_A_SYMBOL = 10 ;  
        /*******************************************************************
        * For convenience, we define a value that's not a symbol type.     *
        *******************************************************************/
      
    public boolean pcal = false ;  
      // True iff this is a PlusCal symbol.
    
    public int alignmentType ;
      /*********************************************************************
      * Two symbols can be inner-aligned iff they have the same alignment  *
      * type.  However, an alignment type of 0 means that the symbol       *
      * cannot be inner-aligned.  See the FindAlignments class for an      *
      * explanation of inner-alignment.                                    *
      *********************************************************************/
 
    public Symbol(String tla, String tex, int stype, int atype)
      /*********************************************************************
      * The constructor for a non-PlusCal Symbol object.                   *
      *********************************************************************/
      { TLAString     = tla   ;
        TeXString     = tex   ;
        symbolType    = stype ;
        alignmentType = atype ;
        pcal          = false ;
      };

    public Symbol(String tla, String tex, int stype, int atype, boolean plusCal)
      /*********************************************************************
      * The constructor used for a PlusCal Symbol object.                  *
      *********************************************************************/
      { TLAString     = tla   ;
        TeXString     = tex   ;
        symbolType    = stype ;
        alignmentType = atype ;
        pcal          = plusCal ;
      };

      public String toString() 
      /*********************************************************************
      * To print a Symbol object for debugging.                            *
      *********************************************************************/
      { return "[TLAString |-> " + TLAString     
                 + ", TeXString |-> " + TeXString
                 + ", symbolType |-> " + symbolType
                 + ", alignmentType |-> " + alignmentType + "]";
      };  

  }

/* Last modified on Tue 18 Sep 2007 at  6:51:56 PST by lamport */