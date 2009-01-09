// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Last modified on Fri  2 Mar 2007 at 15:51:59 PST by lamport
/***************************************************************************
* 2 Mar 2007: enum <- Enum                                                 *
***************************************************************************/


package tla2sany.explorer;

import java.io.EOFException;
import java.io.IOException;
import java.io.InputStreamReader;
import java.util.Enumeration;
import java.util.Hashtable;
import java.util.Iterator;
import java.util.StringTokenizer;

import tla2sany.semantic.ExternalModuleTable;
import tla2sany.semantic.FormalParamNode;
import tla2sany.semantic.Generator;
import tla2sany.semantic.OpDefOrDeclNode;
import tla2sany.semantic.SemanticNode;
import tla2sany.semantic.SymbolNode;
import tla2sany.utilities.Vector;
import util.UniqueString;


// This class implements the explorer tool for traversing
// and examining the semantic graph and associated data structures
// of a TLA specification

public class Explorer {

    public  Generator         generator;

    // Next three vars used in reading commands from keyboard
    private InputStreamReader inStream = new InputStreamReader(System.in);
    private final int         inCapacity = 100;
    private StringBuffer      input = new StringBuffer(inCapacity);
    private int               lineLength;

    // semNodesTable contains various nodes in the semantic graph keyed 
    // by their UIDs
    private Hashtable         semNodesTable = new Hashtable();

    // variables used in parsing commands
    private int               ntokens;
    private StringTokenizer   inputTokens;
    private String            inputString;
    private String            firstToken,secondToken;
    private Integer           icmd,icmd2 = null;
    private ExploreNode       obj;

    private ExternalModuleTable       mt;


    // Constructor
    public Explorer (ExternalModuleTable mtarg) {

      mt = mtarg;

    }


    /* Reads one line from "inStream" into "input".
       Returns "false" if there is an EOF; "true" otherwise
    */

    private boolean getLine() {
      try {
        lineLength=0;
        input.setLength(inCapacity);
	do { 
          input.setCharAt(lineLength,(char)inStream.read()); 
          lineLength++;
	}
	while (input.charAt(lineLength-1) != '\n' & lineLength < inCapacity );
        input.setLength(lineLength);
      } 
      catch (EOFException e) {
	  return false;
      }
      catch (IOException e) {
	System.out.println("***I/O exception on keyboard input; " + e);
	System.exit(-1);
      }
      if (lineLength >= inCapacity) {
        System.out.println("Input line too long; line limited to " + inCapacity
                           + " chars.  Line ignored.");
        input.setLength(0);
      }

      return true;
    }



    // Integer command
    private void printNode(int depth) {

      // See if the object requested is already in the table
      if ((obj = (ExploreNode)semNodesTable.get(icmd)) != null) {
	//Print tree to depth of icmd2
        System.out.println(((ExploreNode)obj).toString(depth));
        System.out.print("\n" + ((ExploreNode)obj).levelDataToString());
      } else { 
        // object requested is not in semNodesTable 
        System.out.println("No such node encountered yet");
      }
    } // end method


    private void lookUpAndPrintSyntaxTree(String symbName) {

      Vector symbolVect = new Vector(8);  // Initial room for 8 symbols with same name


      // Collect in Vector symbols all SymbolNodes in the semNodesTable whose name == symbName

      for ( Enumeration Enum = semNodesTable.elements(); Enum.hasMoreElements(); ) {

        Object semNode = Enum.nextElement();

        if ( semNode instanceof SymbolNode && 
             ((SymbolNode)semNode).getName() == UniqueString.uniqueStringOf(symbName) ) {

          symbolVect.addElement(semNode);

        }
      }

      // Print them all
      for (int i = 0; i < symbolVect.size(); i++ ) {
        SymbolNode sym = (SymbolNode)(symbolVect.elementAt(i));
        ((SemanticNode)(sym)).getTreeNode().printST(0);
        System.out.println();
      }

    }


    private void lookUpAndPrintDef(String symbName) {

      Vector symbolVect = new Vector(8);  // Initial room for 8 symbols with same name


      // Collect in Vector symbols all SymbolNodes in the semNodesTable whose name == symbName

      for ( Enumeration Enum = semNodesTable.elements(); Enum.hasMoreElements(); ) {

        Object semNode = Enum.nextElement();

        if ( semNode instanceof SymbolNode && 
             ((SymbolNode)semNode).getName() == UniqueString.uniqueStringOf(symbName) ) {

          symbolVect.addElement(semNode);

        }
      }

      // Print them all
      for (int i = 0; i < symbolVect.size(); i++ ) {
        SymbolNode sym = (SymbolNode)(symbolVect.elementAt(i));
        if (sym instanceof OpDefOrDeclNode) {
	  if ( ((OpDefOrDeclNode)sym).getOriginallyDefinedInModuleNode() != null ) {
            System.out.print( "Module: " + ((OpDefOrDeclNode)sym).getOriginallyDefinedInModuleNode().getName() + "\n" );
	  } else {
            System.out.print( "Module: " + "null" + "\n");
	  }
	} else if (sym instanceof FormalParamNode) {
          System.out.print( "Module: " + ((FormalParamNode)sym).getModuleNode().getName() );
	}
        System.out.println( ((ExploreNode)(symbolVect.elementAt(i))).toString(100) );
        System.out.println();
      }

    }

    private void levelDataPrint(String symbName) {

      Vector symbolVect = new Vector(8);  // Initial room for 8 symbols with same name


      // Collect in Vector symbols all SymbolNodes in the semNodesTable whose name == symbName

      for ( Enumeration Enum = semNodesTable.elements(); Enum.hasMoreElements(); ) {

        Object semNode = Enum.nextElement();

        if ( semNode instanceof SymbolNode && 
             ((SymbolNode)semNode).getName() == UniqueString.uniqueStringOf(symbName) ) {

          symbolVect.addElement(semNode);

        }
      }

      // Print them all
      for (int i = 0; i < symbolVect.size(); i++ ) {
        SymbolNode sym = (SymbolNode)(symbolVect.elementAt(i));
        if (sym instanceof OpDefOrDeclNode) {
	  if ( ((OpDefOrDeclNode)sym).getOriginallyDefinedInModuleNode() != null ) {
            System.out.print( "Module: " + ((OpDefOrDeclNode)sym).getOriginallyDefinedInModuleNode().getName() + "\n" );
	  } else {
            System.out.print( "Module: " + "null" + "\n" );
	  }
	} else if (sym instanceof FormalParamNode) {
          System.out.print( "Module: " + ((FormalParamNode)sym).getModuleNode().getName() + "\n" );
	}
        System.out.println( ((ExploreNode)(sym)).levelDataToString() );
        System.out.println();
      }

    }


    private void executeCommand() throws ExplorerQuitException {

      // At this point icmd (firsToken) may be null, but icmd2 
      // (second token) is always non-null

      // Integers as commands start printing at the node having icmd == UID; 
      // non-integer commands do something else
        
      if (icmd != null) { // first token is an integer

        printNode(icmd2.intValue());

      } else {      // the first token is not an integer

        // non-integer commands
        if (firstToken.toLowerCase().startsWith("qu")) { 
          // "quit" command
          throw new ExplorerQuitException();

        } else if (firstToken.toLowerCase().equals("mt")) {

          // Print the semantic graph, rooted in the Module Table
	  // excluding built-ins and ops defined in module Naturals
	  if (icmd2 != null) { 
            mt.printExternalModuleTable(icmd2.intValue(),false);
          } else {
            mt.printExternalModuleTable(2, false);
          }

        } else if (firstToken.toLowerCase().equals("mt*")) {

          // Print the semantic graph, rooted in the Module Table
	  // including builtins and ops defined in Naturals
	  if (icmd2 != null) { 
            mt.printExternalModuleTable(icmd2.intValue(),true);
          } else {
            mt.printExternalModuleTable(2,true);
          }

        } else if (firstToken.toLowerCase().startsWith("cst")) {
          printSyntaxTree();

        } else if (firstToken.toLowerCase().startsWith("s")) {
	  if (secondToken != null) {
            lookUpAndPrintSyntaxTree(secondToken);
	  } else {
            System.out.println("***Error: You must indicate what name you want to print the syntax tree of.");
	  }

        } else if (firstToken.toLowerCase().startsWith("d")) {
	  if (secondToken != null) {
            lookUpAndPrintDef(secondToken);
	  } else {
            System.out.println("***Error: You must indicate what name you want to print the definition of.");
	  }

        } else if (firstToken.toLowerCase().startsWith("l")) {
	  if (secondToken != null) {
            levelDataPrint(secondToken);
	  } else {
            System.out.println("***Error: You must indicate what name you want to print the level data of.");
	  }

        } else {
	  // unknown command
          System.out.println("Unknown command: " + firstToken.toString());
          return;
        }

      } // end else

    }


    private void parseAndExecuteCommand() throws ExplorerQuitException {

      icmd = null;
      icmd2 = null;
      ntokens = 0;

      // Do nothing if cmd line contains no tokens
      if (!inputTokens.hasMoreElements()) return;

      // Process first token
      ntokens++;
      firstToken = (String)(inputTokens.nextElement());

      // Try parsing first token as an Integer
      try {
        icmd = Integer.valueOf(firstToken);
      }
      catch (Exception e) { }

      //Process second token (if present)
      if (inputTokens.hasMoreElements()) {
        ntokens++;
        secondToken = (String)(inputTokens.nextElement());
  
        // Try parsing second token as an Integer
        try {
          icmd2 = Integer.valueOf(secondToken);
        }
        catch (Exception e) { }
      }

      // A single token command defaults the depth to 20, except for
      // "mt" command, which defaults to 2
      if (ntokens < 2 || (icmd2 != null && icmd2.intValue() < 0)) {
	if (firstToken.toLowerCase().startsWith("mt")) {
          icmd2 = new Integer(2);
        } else {
          icmd2 = new Integer(4);
        }
      }

      if (inputTokens.hasMoreElements()) {
        System.out.println("Command has too many tokens");
        return;
      }

      executeCommand();

    } // end method


    public void printSyntaxTree () {

      Integer key;

      // Prepare to iterate over ExternalModuleTable entries
      Iterator modules = mt.moduleHashTable.values().iterator();
      ExternalModuleTable.ExternalModuleTableEntry mte;

      // For each entry ExternalModuleTableEntry mte in the ExternalModuleTable mt ... 
      while (modules.hasNext()) {
        key = new Integer(-1);

        mte = (ExternalModuleTable.ExternalModuleTableEntry)(modules.next());

        // Did the module parse correctly?
        if (mte != null) {
          if (mte.getModuleNode() != null ) {
            key = new Integer(mte.getModuleNode().getUid());

            // Make an entry in the semNodesTable for this ModuleNode
            semNodesTable.put(key,mte.getModuleNode());

            // Print the concrete syntax tree for this ExternalModuleTableEntry
            System.out.println("\n*** Concrete Syntax Tree for Module " + key);

            tla2sany.st.TreeNode stn = mte.getModuleNode().getTreeNode();
            stn.printST(0);    // Zero indentation level

            System.out.println("\n*** End of concrete syntax tree for Module " 
                               + key);
          } else {
            System.out.println("\n*** Null ExternalModuleTableEntry.  " +
                      "\n*** Next module did not parse, and cannot be printed.");
          }
        } else {
          System.out.println("*** Null SemanticNode in ExternalModuleTableEntry.  " +
                      "/n*** Next module did not parse, and cannot be printed.");
        }

      }
    }


    public void main() throws ExplorerQuitException {

      if (mt==null) {
        System.out.println("*** module table == null in Explorer.main() ***");
        return;
      }

      // Get all semNodes in semNodeTable
      mt.walkGraph(semNodesTable);

      // Print initial user input prompt
      System.out.println("\n\n*** TLA+ semantic graph exploration tool v 1.0 (DRJ)");
      System.out.print("\n>>");  

      // Main command interpreter loop
      while (getLine()) {

        inputTokens = new StringTokenizer(input.toString());

        parseAndExecuteCommand();

        // Print next user prompt
        System.out.print("\n>>");

      } // end while

   } // end main() method

} // end class
