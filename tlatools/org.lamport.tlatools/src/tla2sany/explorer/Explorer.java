// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Last modified on Fri  2 Mar 2007 at 15:51:59 PST by lamport
/***************************************************************************
 * 2 Mar 2007: enum <- Enum                                                 *
 ***************************************************************************/

package tla2sany.explorer;

import tla2sany.semantic.*;
import util.UniqueString;

import java.io.EOFException;
import java.io.IOException;
import java.io.InputStreamReader;
import java.util.*;

/*
 * TL - 2014
 * Executing the SANY jar with the -d flag enters debugging mode (which is the explorer)
 * Here one can type mt to see all semantical objects parsed and one can enter the object id to see
 * a more elaborated output
 *
 */

// This class implements the explorer tool for traversing
// and examining the semantic graph and associated data structures
// of a TLA specification

public class Explorer {

    // Next three vars used in reading commands from keyboard
    private final InputStreamReader inStream = new InputStreamReader(System.in);
    private static final int inCapacity = 100;
    private final StringBuilder input = new StringBuilder(inCapacity);
    // semNodesTable contains various nodes in the semantic graph keyed
    // by their UIDs
    private final Hashtable<Integer, ExploreNode> semNodesTable = new Hashtable<>();
    private final ExternalModuleTable mt;
    public Generator generator;
    private int lineLength;
    // variables used in parsing commands
    private int ntokens;
    private StringTokenizer inputTokens;
    private String firstToken, secondToken;
    private Integer icmd, icmd2 = null;
    private ExploreNode obj;

    // Constructor
    public Explorer(final ExternalModuleTable mtarg) {

        mt = mtarg;

    }

    /*
     * Reads one line from "inStream" into "input". Returns "false" if there is an
     * EOF; "true" otherwise
     */

    private boolean getLine() {
        try {
            lineLength = 0;
            input.setLength(inCapacity);
            do {
                input.setCharAt(lineLength, (char) inStream.read());
                lineLength++;
            } while (input.charAt(lineLength - 1) != '\n' && lineLength < inCapacity);
            input.setLength(lineLength);
        } catch (final EOFException e) {
            return false;
        } catch (final IOException e) {
            System.out.println("***I/O exception on keyboard input; " + e);
            System.exit(-1);
        }
        if (lineLength >= inCapacity) {
            System.out.println("Input line too long; line limited to " + inCapacity + " chars.  Line ignored.");
            input.setLength(0);
        }

        return true;
    }

    // Integer command
    private void printNode(final int depth) {

        // See if the object requested is already in the table
        if ((obj = semNodesTable.get(icmd)) != null) {
            // Print tree to depth of icmd2
            System.out.println(obj.toString(depth));
            System.out.print("\n" + obj.levelDataToString());
        } else {
            // object requested is not in semNodesTable
            System.out.println("No such node encountered yet");
        }
    } // end method

    private void lookUpAndPrintSyntaxTree(final String symbName) {

        final ArrayList<SymbolNode> symbolVect = new ArrayList<>(8); // Initial room for 8 symbols with same name

        // Collect in ArrayList symbols all SymbolNodes in the semNodesTable whose name ==
        // symbName

        for (final Enumeration<ExploreNode> Enum = semNodesTable.elements(); Enum.hasMoreElements(); ) {

            final ExploreNode semNode = Enum.nextElement();

            if (semNode instanceof SymbolNode
                    && ((SymbolNode) semNode).getName() == UniqueString.uniqueStringOf(symbName)) {

                symbolVect.add((SymbolNode) semNode);

            }
        }

        // Print them all
        for (final SymbolNode sym : symbolVect) {
            sym.getTreeNode().printST(0);
            System.out.println();
        }

    }

    private void lookUpAndPrintDef(final String symbName) {

        final ArrayList<SymbolNode> symbolVect = new ArrayList<>(8); // Initial room for 8 symbols with same name

        // Collect in ArrayList symbols all SymbolNodes in the semNodesTable whose name ==
        // symbName

        for (final Enumeration<ExploreNode> Enum = semNodesTable.elements(); Enum.hasMoreElements(); ) {

            final ExploreNode semNode = Enum.nextElement();

            if (semNode instanceof SymbolNode
                    && ((SymbolNode) semNode).getName() == UniqueString.uniqueStringOf(symbName)) {

                symbolVect.add((SymbolNode) semNode);

            }
        }

        // Print them all
        for (final SymbolNode sym : symbolVect) {
            if (sym instanceof OpDefOrDeclNode) {
                if (((OpDefOrDeclNode) sym).getOriginallyDefinedInModuleNode() != null) {
                    System.out.print(
                            "Module: " + ((OpDefOrDeclNode) sym).getOriginallyDefinedInModuleNode().getName() + "\n");
                } else {
                    System.out.print("Module: " + "null" + "\n");
                }
            } else if (sym instanceof FormalParamNode) {
                System.out.print("Module: " + ((FormalParamNode) sym).getModuleNode().getName());
            }
            System.out.println(((ExploreNode) sym).toString(100));
            System.out.println();
        }

    }

    private void levelDataPrint(final String symbName) {

        final ArrayList<SymbolNode> symbolVect = new ArrayList<>(8); // Initial room for 8 symbols with same name

        // Collect in ArrayList symbols all SymbolNodes in the semNodesTable whose name ==
        // symbName

        for (final Enumeration<ExploreNode> Enum = semNodesTable.elements(); Enum.hasMoreElements(); ) {

            final ExploreNode semNode = Enum.nextElement();

            if (semNode instanceof SymbolNode sn
                    && sn.getName() == UniqueString.uniqueStringOf(symbName)) {

                symbolVect.add(sn);

            }
        }

        // Print them all
        for (final SymbolNode sym : symbolVect) {
            if (sym instanceof OpDefOrDeclNode ododn) {
                if (ododn.getOriginallyDefinedInModuleNode() != null) {
                    System.out.print(
                            "Module: " + ((OpDefOrDeclNode) sym).getOriginallyDefinedInModuleNode().getName() + "\n");
                } else {
                    System.out.print("Module: " + "null" + "\n");
                }
            } else if (sym instanceof FormalParamNode fpn) {
                System.out.print("Module: " + fpn.getModuleNode().getName() + "\n");
            }
            System.out.println(((ExploreNode) (sym)).levelDataToString());
            System.out.println();
        }

    }

    private void executeCommand() throws ExplorerQuitException {

        // At this point icmd (firsToken) may be null, but icmd2
        // (second token) is always non-null

        // Integers as commands start printing at the node having icmd == UID;
        // non-integer commands do something else

        if (icmd != null) { // first token is an integer

            printNode(icmd2);

        } else { // the first token is not an integer

            // non-integer commands
            if (firstToken.toLowerCase().startsWith("qu")) {
                // "quit" command
                throw new ExplorerQuitException();

            } else if (firstToken.equalsIgnoreCase("mt")) {

                // Print the semantic graph, rooted in the Module Table
                // excluding built-ins and ops defined in module Naturals
                mt.printExternalModuleTable(Objects.requireNonNullElse(icmd2, 2), false);

            } else if (firstToken.equalsIgnoreCase("mt*")) {

                // Print the semantic graph, rooted in the Module Table
                // including builtins and ops defined in Naturals
                mt.printExternalModuleTable(Objects.requireNonNullElse(icmd2, 2), true);

            } else if (firstToken.equalsIgnoreCase("dot")) {
                dotSemanticGraph();
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
                System.out.println("Unknown command: " + firstToken);
            }

        } // end else

    }

    private void parseAndExecuteCommand() throws ExplorerQuitException {

        icmd = null;
        icmd2 = null;
        ntokens = 0;

        // Do nothing if cmd line contains no tokens
        if (!inputTokens.hasMoreElements())
            return;

        // Process first token
        ntokens++;
        firstToken = (String) (inputTokens.nextElement());

        // Try parsing first token as an Integer
        try {
            icmd = Integer.valueOf(firstToken);
        } catch (final Exception e) {
        }

        // Process second token (if present)
        if (inputTokens.hasMoreElements()) {
            ntokens++;
            secondToken = (String) (inputTokens.nextElement());

            // Try parsing second token as an Integer
            try {
                icmd2 = Integer.valueOf(secondToken);
            } catch (final Exception e) {
            }
        }

        // A single token command defaults the depth to 20, except for
        // "mt" command, which defaults to 2
        if (ntokens < 2 || (icmd2 != null && icmd2 < 0)) {
            if (firstToken.toLowerCase().startsWith("mt")) {
                icmd2 = 2;
            } else {
                icmd2 = 4;
            }
        }

        if (inputTokens.hasMoreElements()) {
            System.out.println("Command has too many tokens");
            return;
        }

        executeCommand();

    } // end method

    public void dotSemanticGraph() {
        final DotExplorerVisitor visitor = new DotExplorerVisitor(mt.getRootModule());
        mt.getRootModule().walkGraph(visitor.getTable(), visitor);
        visitor.done();
    }

    public void printSyntaxTree() {

        int key;

        // Prepare to iterate over ExternalModuleTable entries
        final Iterator<ExternalModuleTable.ExternalModuleTableEntry> modules = mt.moduleHashTable.values().iterator();
        ExternalModuleTable.ExternalModuleTableEntry mte;

        // For each entry ExternalModuleTableEntry mte in the ExternalModuleTable mt ...
        while (modules.hasNext()) {

            mte = modules.next();

            // Did the module parse correctly?
            if (mte != null) {
                if (mte.getModuleNode() != null) {
                    key = mte.getModuleNode().getUid();

                    // Make an entry in the semNodesTable for this ModuleNode
                    semNodesTable.put(key, mte.getModuleNode());

                    // Print the concrete syntax tree for this ExternalModuleTableEntry
                    System.out.println("\n*** Concrete Syntax Tree for Module " + key);

                    final tla2sany.st.TreeNode stn = mte.getModuleNode().getTreeNode();
                    stn.printST(0); // Zero indentation level

                    System.out.println("\n*** End of concrete syntax tree for Module " + key);
                } else {
                    System.out.println("""

                            *** Null ExternalModuleTableEntry. \s
                            *** Next module did not parse, and cannot be printed.""");
                }
            } else {
                System.out.println("*** Null SemanticNode in ExternalModuleTableEntry.  "
                        + "/n*** Next module did not parse, and cannot be printed.");
            }

        }
    }

    public void main(final String[] args) throws ExplorerQuitException {

        if (mt == null) {
            System.out.println("*** module table == null in Explorer.main() ***");
            return;
        }

        final List<String> asList = Arrays.asList(args);
        // Passing single token commands as command line parameter skips Explorer's
        // interpreter mode.
        if (asList.contains("cst")) {
            inputTokens = new StringTokenizer("cst");
            parseAndExecuteCommand();
            System.exit(0);
        } else if (asList.contains("dot")) {
            inputTokens = new StringTokenizer("dot");
            parseAndExecuteCommand();
            System.exit(0);
        } else if (asList.contains("mt")) {
            inputTokens = new StringTokenizer("mt");
            parseAndExecuteCommand();
            System.exit(0);
        } else if (asList.contains("mt*")) {
            inputTokens = new StringTokenizer("mt*");
            parseAndExecuteCommand();
            System.exit(0);
        } else {
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
        }

    } // end main() method

} // end class
