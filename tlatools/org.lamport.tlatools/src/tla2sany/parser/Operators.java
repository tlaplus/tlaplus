// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Last modified onFri  2 Mar 2007 at 15:40:00 PST by lamport
/***************************************************************************
* 2 Mar 2007: enum <- Enum                                                 *
***************************************************************************/

package tla2sany.parser;

import java.util.Enumeration;
import java.util.Hashtable;

import util.UniqueString;

public class Operators {
  static public int assocNone = 0;
  static public int assocLeft = 1;
  static public int assocRight = 2;

  /*************************************************************************
  * The following appear to be classes of operators.                       *
  *************************************************************************/
  static public int nofix = 0;
    /***********************************************************************
    * What is a nofix operator?????????                                    *
    ***********************************************************************/
  static public int prefix = 1;
  static public int postfix = 2;
  static public int infix = 3;
  static public int nfix = 4;// \X
    /***********************************************************************
    * The only operator of class nfix seems to be \X (aka \times).         *
    ***********************************************************************/
  static Hashtable<String, Object> DefinitionTable = new Hashtable<String, Object>();
    /***********************************************************************
    * Contains the Operator objects for all operators.  It is constructed  *
    * from the data in ConfigConstants.defaultConfig.                      *
    ***********************************************************************/
  static Hashtable<String, String> BuiltinTable = new Hashtable<String, String>();
    /***********************************************************************
    * It appears that this is not used.                                    *
    ***********************************************************************/
  
  // TODO: appears to be unused
  static public void addOperator(String name, Operator op) {
	DefinitionTable.put(name, op);
  }
  
  static public Operator getOperator(String name) {
	return (Operator) DefinitionTable.get(name);
  }

  static public Operator getMixfix( Operator op ) {
     if (op.isPrefix()) return op;
     else {
       String id = op.getIdentifier() + ".";
       return (Operator) DefinitionTable.get( id );
     }
  }
  
  // TODO appears to be unused
  static public boolean existsOperator( String name ) {
	return ( DefinitionTable.get( name ) != null );
  }

  static public void addSynonym(String template, String match ) {
    /*
       do make sure that the operator already exists.
       We make the new definition point to the other one.
    */
    Operator n = (Operator) DefinitionTable.get( match );
    if (n != null) {
      DefinitionTable.put(template, n);
    } /* else {
       error
    } */
  }
  
  /*************************************************************************
  * resolveSynonym has the property that                                   *
  *                                                                        *
  *    resolveSynonym(a) = resolveSynonym(b)                               *
  *                                                                        *
  * iff either a = b or a and b are synonyms (like (+) and \oplus).  If a  *
  * has no synonmys, then resolveSynonym(a) = a.                           *
  *************************************************************************/
  /** @deprecated */
  static public UniqueString resolveSynonym( UniqueString name ) {
    Operator n = (Operator) DefinitionTable.get( name.toString() );
    if ( n == null ) return name;
    else return UniqueString.uniqueStringOf(n.getIdentifier());
  }

  // TODO appears to be unused
  static public void addBuiltinAssoc( String symbol, String builtin ) {
    BuiltinTable.put( symbol, builtin );
  }

/* debugging help */
  static public void printTable() {
    System.out.println("printing Operators table");
    Enumeration Enum = DefinitionTable.keys();
    while( Enum.hasMoreElements() ) { System.out.println("-> " + ((UniqueString)Enum.nextElement()).toString() ); }
  }

// shouldn't be necessary
//  static public Operator operatorFromASTNode ( ASTNode tn ) {
//     Operator n = (Operator) DefinitionTable.get( tn.getToken().image );
//        return n;
//  }

}
