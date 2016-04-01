Note: The following files produced by javacc have been edited.

   parser/ParseException.java
     The method at the end of this file was added--I believe by J-Ch
      The method in question seems to be getShortMessage().

   configuration/Configuration.java 
   configuration/ASCII_CharStream.java 
   configuration/ConfigurationTokenManager
     These have small bug fixes introduced by David Jefferson. Search for 
     "DRJ" to find them.  These files were originally produced by running
     javacc on config.jj, a grammar file that specifies the 
     parsing of the string ConfigConstants.defaultConfig.
     I suspect that current the version of javacc would not produce
     the ASCI_CharStream.java file, but I'm not sure.  I just know that 
     running javacc on tla+.jj doesn't produce such a file.

tlasany/drivers directory
-----------------
FrontEndException.java
  Simple extension to Exception to create an exception specific to the FrontEnd

InitException.java
  Simple extension to Exception to create an exception specific to the FrontEnd

SemanticException.java
  Simple extension to Exception to create an exception specific to the FrontEnd

SANY.java
   static SANYmain
     The main driver, called by tlasany/SANY.java.  It handles
     the command line and calles frontEndMain.
   static frontEndMain
     The real main driver, called by SANYmain.
   static frontEndInitialize
     [called from] frontEndMain
     initializes Configuration, Context, level data.
     throws InitException in case of problems.
   static frontEndParse
     [called from] frontEndMain
     loads and parse the spec file.
     uses SpecObj.loadSpec
   static frontEndSemanticAnalysis
     [called from] frontEndMain
     Coming out of parsing, we have all the modules required to analyse 
     the file from the SpecObj. They are organized in a vector, ordered 
     from modules with no dependencies to modules with most dependencies.
     Semantic analysis is done incrementally, with the context of each 
     module stored in a gobal table for easy retrieval.

==================================================================
tlasany/parser directory
-----------------------

This directory contains classes implementing the parser.  There are
different group of classes:
   1. implementing support for identifying matching alignments
   2. implementing the expression parser
   3. implementing the parser
   4. support

1. Implementing support for identifying matching alignments
-----------------------------------------------------------
BracketStack.java
   class to support the enforcement of alignment as delimiter in TLA+, e.g.
     /\
     /\
       /\
       /\
     /\
   we keep track of the kind of "bracket", e.g.  AND, OR, but
   identified from the type of STN. It is organized as a stack as
   operators are embedded in expressions.  Stacks are created,
   pushed or popped.  With the top reference, we can compare whether
   an operator will be aligned, to the right or the left.

StackElement.java
   An element in BracketStack

2. Implementing the expression parser
-------------------------------------
Expression parser:
   The "high level" parser simply pushed expression elements on a stack,
   on which well formed expressions are reduced, according to precedence
   + associativity rules.

OSelement.java
   Defines the objects that go on the operator stack: the operator and
   the syntax node.  An OSelement object can be viewed as an
   information cache, really.

Operator.java
   The Operator object associated with an operator defines the symbol
   and its properties--e.g.  "+" is infix.  An operator will also have
   low and high precedence levels, to direct the order in which
   expressions are evaluated.  e.g.  a*b+c is (a*b)+c

   Note that there is a lack of modularity between Operator and
   Operators.  An interface should be defined to define in one place
   constant values (nofix, infix, ...)  and string representations
   thereof.

OperatorStack.java
   This class name is a misnommer.  Or rather a short for Operator
   Expression Reduction Stack.  It is also really a stack of stacks.
   See comments in file.

   Operators are pushed onto the stack, and reduction operations called
   periodically.  As well as a final operation once we have captured
   all elements of the expression.

Operators.java
   Creates and manages all symbols defined in the grammar.  Initialized
   by Configuration.

3. implementing the parser
--------------------------
SyntaxTreeNode.java

The following are automatically generated from tla+.jj, the
implementation of the parser.
   ParseException.java
   SimpleCharStream.java
   TLAplusParser.java
   TLAplusParserConstants.java
   TLAplusParserTokenManager.java
   TokenMgrError.java 
   Token.java

The ParseException.java file produced by javacc must be modified for
use by the other parser files.  The modification consists of adding the
method getShortMessage(), whose current code is given at the end of
this file.  That method is called by code in TLAplusParser.java that is
obtained from the tla+.jj grammar file.

4. Support
----------
ParseError.java
   An exception.
ParseErrors.java
   An array of ParseError objects.


Note:
The current directory also contains ASCII_CharStream.java, which is
obsolete.  It was constructed by an earlier version of javacc, which
now constructs SimpleCharStream.java instead.

==================================================================
tlasany/st directory
-----------------------

st (short for Syntax Tree) creates an abstract view of the parse tree.
It was created for decoupling from other operations, but its use is
certainly not strictly necessary.

Only Location and SyntaxTreeNode are required.

Location.java
  A location specifies the position of a syntactic unit in the source
  - beginLine() start line of a syntactic unit
  - beginColumn() start line of a syntactic unit
  - endLine() start column of a syntactic unit
  - endColumn() end column of a syntactic unit
  - source() returns source file
  - toString() returns a pprintable version of content

SyntaxTreeConstants.java
   Interface defining all constants for SyntaxTreeNodes.  This extends
   the numbering of tokens, which is done by javacc and put in
   TLAplusParserConstants.java, to SyntaxTreeNode objects' `kind'
   field.  Both tokens and nodes are in the syntax tree.  This class
   also contains an array of strings which gives a printable version of
   the tree node kinds.

The ParseError and ParseErrors interfaces in this directory (st) are
implemented by the classes of the same name in the parser/ directory.
These interfaces are also implemented by classes in modanalyzer/.
------
ParseError.java
  interface for a parse error
  prescribes
  - String reportedError()
  - String defaultError()

ParseErrors.java
  interface to an Array of Parse Errors.


ParseTree.java
  Interface to parse tree. Used in modanalyzer/ classes.

TreeNode.java
  Interface for TreeNode. Imported by a lot of classes
  in semantic/ and modanalyzer/, and by 
  parser/{SyntaxTreeNode,TLAplusParser, TLAplusParserTokenManager}
  It seems to be implemented only by SyntaxTreeNode.

==================================================================
tlasany/utilities directory
---------------------------
Assert.java
   Assertion, obsolete in java 1.5
IntWrapper.java
   Abstraction of int: value can be set, read, or incremented.
Stack.java
   Stack abstraction, pre-java Generics
Strings.java
   Add an indentation method to basic (java) strings.
Vector.java
   A generic (Object-based) java abstraction for dynamic vectors.  Can be
   resized.  supported methods:
  - int size ()
  - String toString()
  - void addElement( Obj)
  - void setElementAt( Obj, int)
  - bool contains (Obj)
  - void append( Vector)
  - void appendNoRepeats ( Vector) 
  - Enumeration elements ()
  - void removeAllElements ()
  - void removeElementAt (int)
  - void insertElementAt (Obj, int)

VectorEnumeration.java
  Support class for Vector. Creates an enumeration.
  - implements nextElement, hasMoreElements for an Enumeration on vectors
  - create a local copy of references to obj content.

==================================================================
tlasany/explorer directory
-----------------------
   This is an interface to the semantic Tree, for exploration, that is
   mainly to display the semantic tree.  It interacts with an inputStream
   for commands.  The operations are really straightforward: identifying
   a symbol and printing relevant information.

ExploreNode.java
  interface to retrieve information fron node
    methods:  String toString(int depth);
              String levelDataToString();
              void   walkGraph(Hashtable semNodesTable);


Explorer.java
  getLine 
  printNode
  lookUpAndPrintSyntaxTree( String)
  lookUpAndPrintDef( String)
  levelDataPrint( String )
  executeCommand()
  parseAndExecuteCommand()
  printSyntaxTree()
  main()

ExplorerQuitException.java
  Exception in case of Explorer problem.

==================================================================
tlasany/configuration directory
-------------------------------

ConfigConstants.java
   This file was originally generated by javacc for parsing
   defaultConfig, and then J-Ch added the definition of defaultConfig
   to it.

The following files were originally generated by javacc from a
grammar file that has vanished.  They parse the string
ConfigConstants.defaultConfig to build Operators.BuiltinTable.
--------------------
ASCII_CharStream.java
Configuration.java
ConfigurationTokenManager.java
ParseException.java
Token.java
TokenMgrError.java

==================================================================
tlasany/error directory
-----------------------

As noted below, this entire directory can be eliminated.

ErrorRegistry.java
   Doesn't appear to be used.

Log.java
   Used by BracketStack for no good purpose.  It can be removed and
   references to it eliminated.

LogCategories.java
   Used only by Log.java

Timing.java
   Appears to be unused.

ToolkitError.java
   Appears to be unused.
==================================================================
tlasany/modanalyzer directory
-----------------------------
The files in this directory are used as a interface between the driver
and the single-module parser.  It contains the mechanics to extract
which modules have been referenced, to map module names to files, and
to keep track of which modules have already been parsed.

ModuleContext.java
ModulePointer.java
ModuleRelationships.java
ModuleRelatives.java
NameToFileIStream.java
NamedInputStream.java
ParseUnit.java
  This class contains the code that walks through a module's parse 
  tree to find the names of EXTENDed or INSTANCEd modules. 
ParseUnitRelatives.java
ParseUnitsTable.java
SpecObj.java
StringToNamedInputStream.java
SyntaxTreePrinter.java

==================================================================
tlasany/semantic directory
-----------------------
ASTConstants.java
   Defines the values of the semantic nodes' `kind' field and their
   printed names.

AbortException.java
   Random exception.
SemanticsException.java
   Random exception.

ArgLevelParam.java
   Seems to be the object that contains the level information for an
   operator.

BuiltInLevel.java
   Seems to define the levels of the built-in operators.

Context.java
   A hashtable of definition and declaration nodes.

Errors.java
   Probably used to keep track of the errors found during semantic
   analysis.

ExternalModuleTable.java
   Seems to keep track of contexts and level (constant or non-constant)
   of modules that have been semantically analyzed.

FrontEnd.java
   This class contains the methods by which a tool calls the Front End
   to parse input and to create a semantic tree, and for various other
   interactions.

Generator.java
   Generates a semantic graph from a parse tree.  It also uses the list
   of modules to access contexts to instantiate or extend.

LevelConstants.java
   Trivial constants.

LevelException.java
   A random exception.

OpDefOrLabelNode.java
   An interface implemented by OpDefNode, ThmOrAssumpDefNode, and
   LabelNode.  It contains methods for accessing the set of labels
   "immediately within" this node.  [Added by LL on 23 Apr 2007]

Subst.java
   This class represents a single substitution of the form
   op <- expr such as appears in module instantiations

SetOfArgLevelConstraints.java
   Implements a map mapping arg-level parameters (ParamAndPosition) to
   levels (Integer).  An entry <pap,x> means that the argument
   pap.position of the operator pap.param must have a level >= x.

SetOfLevelConstraints.java
   Implements a map mapping parameters to levels. An entry <p,x> in
   the set means that p must have a level <= x.

SymbolTable.java
   The Symbol Table builds the stack of context tables.

SemanticNode.java
   The abstract class that is the superclass of all individual node
   classes.  These node classes are:
      ParamAndPosition.java
      LevelNode.java
         This is an abstract class that extends SemanticNode
         and is extended by:
            AssumeNode.java  
            TheoremNode.java 
               [AssumeNode and TheoremNode moved here by LL 22 Jul 2007.
                I don't know why they weren't already here.]
            ProofNode.java 
              This is abstract and is extended by 
                LeafProofNode.java
                NonLeafProofNode.java
            InstanceNode.java
            obsolete:  QEDStepNode.java  
            ExprOrOpArgNode.java
               This is abstract and is extended by 
                  ExprNode.java
                     This is an abstract node that is extended by:
                        LabelNode.java  [Added by LL 23 Apr 2007]
                        LetInNode.java
                        AtNode.java
                        DecimalNode.java
                        NumeralNode.java
                        StringNode.java
                        OpApplNode.java
                        SubstInNode.java     
                 OpArgNode.java
            AssumeProveNode.java [Moved here by LL 15 Mar 2007]
            NewSymbNode          [Added by LL 15 Mar 2007 ]
            UseOrHideNode.java   [Added by LL 29 Jul 2007]
            DefStepNode.java     [Added by LL 16 Aug 2007]
            APSubstInNode.java   [Added by LL  6 Aug 2007]
            SymbolNode.java
               This is an abstract class that extends LevelNode by
               adding the following concrete methods:
                    getName(), occur(), isParam()
               and the following abstract methods:
                   getArity(), isLocal(), and match() [for testing arity].
               It is extended by 
                  FormalParamNode.java 
                  ModuleNode.java
                  OpDefOrDeclNode.java
                     Abstract class that adds the fields
                        ModuleNode  originallyDefinedInModule 
                        SymbolTable st
                        int         arity
                     Is extended by:
                        OpDeclNode.java
                        OpDefNode.java
                  ThmOrAssumpDefNode.java [Added by LL 17 Mar 2007]

==================================================================

To add a new BuiltIn operator, search for $Nop and OP_nop in the files

  semantic/ASTConstants.java 
  semantic/BuiltInLevel.java
  configuration/ConfigConstants.java

and copy what's done there.  If the model checker needs to be able to
evaluate the operator, search for Op_nop and OPCODE_nop in

  tool/BuiltInOPs.java
  tool/Tool.java
  tool/ToolGlobals.java

==================================================================

The method getShortMessage() to be inserted into ParseException.java.

  /**
   *  * shorter variation on the following
   *
   */
  public String getShortMessage() {
    if (!specialConstructor) {
      return super.getMessage();
    }
    int maxSize = 0;
    for (int i = 0; i < expectedTokenSequences.length; i++) {
      if (maxSize < expectedTokenSequences[i].length) {
        maxSize = expectedTokenSequences[i].length;
      }
    }
    String retval = "Encountered \"";
    Token tok = currentToken.next;

    for (int i = 0; i < maxSize; i++) {
      if (i != 0) retval += " ";
      if (tok.kind == 0) {
        retval += tokenImage[0];
        break;
      }
      retval += tok.image;
      //      retval += add_escapes(tok.image);
      tok = tok.next;
    }
    retval += "\" at line " + currentToken.next.beginLine + ", column " + currentToken.next.beginColumn;
    return retval;
  }
