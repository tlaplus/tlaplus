/**
 */
package pcal;

import java.util.Vector;

/**
 * A TLA+ to PlusCal mapping is a mapping from regions of the TLA+ translation 
 * to regions of the PlusCal code.  It is used to implement a command that allows the
 * user to jump from a selected region in the TLA+ translation to the region of the
 * PlusCal code that produced that region of the translation, as well as commands
 * to jump directly from the location indicated in an error report from SANY or TLC
 * to the PlusCal code responsible for the error.
 * <p>
 * A TLA+ spec of a TLA+ to PlusCal {@link TLAtoPCalMapping#mapping}  mapping is contained 
 * in the TLAToPCal module that will be appended to the end of this file, but for now lives 
 * in the generals/docs project.
 * <p>
 * The TLAtoPCalMapping object contains a `mapping' field that is the Java implementation
 * of the mapping defined in module TLAToPCal, as well as a method to  
 * <p>
 * TODO to implement this translation:
 * 
 *   Checked calls to the old TLAToken constructor, which required handling
 *   calls from: 
 *       Tokenize.TokenOut 
 *       TLAExpr.substituteAt
 *       PcalTLAGen.SubExpr
 *       PcalTLAGen.selfAsExpr 
 *       PcalTLAGen.GenInit   [modifications deferred]
 *       PcalTLAGen.AddSubscriptsToExpr [modifications deferred]
 *       PcalParams.DefaultVarInit  [nothing done]
 *       PcalFixIDs.FixExpr
 *           
 *   Modified TLAExpr.cloneAndNormalize to preserve the origin.  
 *   Check uses of it to see if something else needs to be done.
 *   The uses are:
 *       PcalTLAGen.SubExpr [looks OK]
 *       PcalTLAGen.GenInit [modifications deferred]
 *       PcalTLAGen.AddSubscriptsToExpr  [modifications deferred]
 *       TLAExpr.substituteAt [modified]
 *       TLAExpr.SeqSubstituteForAll [looks OK]
 *       ParseAlgorithm.SubstituteInStmt  [looks OK]
 *       ParseAlgorithm.SubstituteInSingleAssign  [looks OK]
 *       
 *   Check uses of TLAToken.clone to see that they set the source region
 *   of the new token.
 *       TLAExpr.cloneAndNormalize [fixed to preserve source]
 *       Test.TokVectorToExpr  [just used for testing]
 *       PcalTranslate.TokVectorToExpr 
 *         [Creates the when expression for a pc = ... enabling condition.
 *          Need to do something only if we want the user to be able to
 *          select the label.]
 *       
 *   Check uses of new TLAToken() to see if they need to set the source
 *   region of the new token.  The uses are
 *       Test. ...  : Just for testing.
 *       PcalTranslate.AddedToken [modifications deferred]
 *       PcalTranslate.BuiltInToken [modifications deferred]
 *       PcalTranslate.IdentToken [modifications deferred]
 *       PcalTranslate.StringToken [modifications deferred]
 *   
 *   Modify methods of PcalTranslate to set the origin field of all
 *   AST objects in the parse tree.  Methods modified are:
 *   
 *      GetAssign
 *      GetEither   (++)
 *      GetGoto
 *      GetIf       (++)
 *      GetLHS
 *      GetMacro
 *      GetMacroCall
 *      GetPrintS
 *      GetProcedure 
 *      GetProcess
 *      GetReturn
 *      GetSingleAssign
 *      GetWhile     (++)
 *      getAlgorithm
 *      getAssert
 *      getCall
 *      getCallOrCallReturn
 *      getExpr
 *      GetPVarDecl
 *      getSkip
 *      getWhen 
 *      getWith      (++)
 *      GetWhile
 *      GetVarDecl
 *      SubstituteInLabeledStmt
 *      SubstituteInSingleAssign
 *      ClassifyStmSeq 
 *      SubstituteInStmt  [not really tested]
 *      
 *      todo  ,   
 *      ++ Methods marked with (++) have origin regions that do not include the
 *      "end" (P syntax) or "}" (C syntax) that they should.  See the 
 *      comments to getIf.
 *      
 *      Note: ParseAlgorithm.GetAlgToken and ParseAlgorithm.MustGobbleThis
 *      leave lastTokCol-1 and lastTokLine-1 equal to the (Java)
 *      coordinates of the beginning of the token.  Use GetLastLocationStart
 *      and GetLastLocationEnd to get the PCalLocation of the token.
 *      
 *   Check how missing labels are added, and make sure that use of
 *   GetLastLocationStart/End work properly in that case.  They should
 *   probably return null.  THIS NOW SEEMS TO WORK.
 *   
 *   Modify the PcalFixID class to make sure that origins are properly
 *   set for all the newly created AST nodes.  Have checked and the only
 *   Fix... class that needed modification was FixExpr, which was modified.
 *   
 *   Check all the Explode methods in PcalTranslate.java and modify so that
 *   the newly created AST nodes have the right origin.  Have checked the following:
 *      CopyAndExplodeLastStmt
 *      CopyAndExplodeLastStmtWithGoto
 *      Explode
 *      ExplodeCall
 *      ExplodeCallReturn
 *      ExplodeLabeledStmt
 *      ExplodeLabeledStmtSeq
 *      ExplodeLabelEither
 *      ExplodeLabelIf
 *      ExplodeMultiprocess
 *      ExplodeProcedure
 *      ExplodeProcess
 *      ExplodeReturn
 *      ExplodeUniprocess
 *      ExplodeWhile
 *      UpdatePC 
 *        Adds an assignment to pc with all origins = null.  It might be nice
 *        if the rhs had the origin the region containing the label to which
 *        control is going, but that's probably not worth the effort.
 *  All the Explode methods have been modified appropriately, but not all
 *  have been tested.
 *  
 *  All AST objects obtained by calling the constructors have been checked for
 *  proper setting of their origins.  Calls of the constructors occur only in
 *  ParseAlgorithm and PcalTranslate (in the methods called by Explode).
 *   
 *  Modify PcalTLAGen to generate the actual mapping.  Modified methods:
 *     AddSubscriptsToExpr [not modified]
 *        This adds to the expression the necessary [self] subscripts and primes.
 *        The added tokens have null source region, indicating that they were
 *        added.  For the mapping, the added tokens should be considered part of 
 *        the token that  precedes them.
 *     GenSym [++]
 *     GenUniprocess [++]
 *     GenMultiprocess [++]
 *     GenVarsAndDefs [but it won't work until GenVarDecl is modified]
 *     
 *     To Do:
 *       GenVarDecl : Note that for a multi-line declaration, the current
 *         code puts multiple lines in a single element of PcalTLAGen.tlacode.
 *  
 *
 *     [++] indicates method that's not modified because it just calls other
 *          Gen... methods to produce the translation output.
 *        
 *  Modify PcalTLAGen.getInit and PcalTLAGen.AddSubscriptsToExpr, in which 
 *  no changes have been made yet for adding source regions to constructed tokens.
 *   
 *  METHODS modified:
 *  
 *  TLAExpr.substituteAt : Added BEGIN_REPLACEMENT / END_REPLACEMENT tokens around
 *                 substituted expression.
 *                 
 *  Tokenize.TokenOut : Added the origin to the token that's seems actually to 
 *      produce a token.
 *      
 *  PcalTLAGen.SubExpr: Preserve the origin of the argument's expression in the
 *      value's expression. [Done by making TLAExpr.cloneAndNormalize() do that.]
 *      
 *  PcalTLAGen: Methods for generating AST objects that have been modified:
 *     No constructors of AST objects are called in PcalTLAGen.
 *      
 *  NOTE: NEED A METHOD TO REMOVE REDUNDANT Parens from the final MappingVector
 *  before generating the mapping array.
 *  
 * @author lamport
 *
 */
public class TLAtoPCalMapping {
  /**
   * The mapping field represents an element of TPMap in the TLAToPCal spec.
   *  
   */
  public MappingObject[][] mapping = new MappingObject[0][] ;
  
  /**
   * This is a version of {@link TLAtoPCalMapping#mapping} as a vector of vectors.
   * It is used while constructing the mapping field, and is then nulled.
   */
  public Vector mappingVector = new Vector(50) ;
  
  public TLAtoPCalMapping() {
      
  }
  
  /**
   * Sets the mapping field to an array version of mapVec, which must be a vector 
   * of vectors of MappingObjects.
   * 
   * @param mapVec
   * @return
   */
  public void  makeMapping(Vector mapVec) {
     this.mapping = new MappingObject[mapVec.size()][] ;
      for (int i = 0 ; i < this.mapping.length; i++) {
          Vector line = (Vector) mapVec.elementAt(i);
          this.mapping[i] = new MappingObject[line.size()];
          for (int j = 0; j < line.size(); j++) {
              this.mapping[i][j] = (MappingObject) line.elementAt(j);
          }
      }
      return ;
  }
  /**
   * Adds a mapping object to mappingVector.
   * 
   * NOT YET USED.  IT SEEMS UNLIKELY THAT IT WILL BE USEFUL.
   * 
   * @param mobj  The object to add.
   * @param line  The line of the translation at which the object
   *              is to be added.  This line is the position relative
   *              to tlaStartLine of the object's location.
   */
//  public void addMappingObject(MappingObject moj, int line) {
//      int nextLine = mappingVector.size() ;
//
//      if (line < nextLine-1) {
//          PcalDebug.ReportBug("Called addMappingObject with line number too small") ;
//      }
//      
//      while (line >= mappingVector.size()) {
//          mappingVector.add(new Vector()) ;
//      }
//      
//      ((Vector) mappingVector.elementAt(line)).addElement(moj) ;
//  }
  
  /**
   * Returns the PCal code location to which `mapping' maps the `selection' Region in the
   * TLA+ translation, where line numbers in `selection' are relative to tlaStartLine.
   * It returns null if the mapping does not map the selection to any PCal code. 
   * 
   * @param mapping
   * @param selection
   * @return
   */
  public static Region ApplyMapping(TLAtoPCalMapping mapping, Region selection) {
      return new Region (new PCalLocation(1, 3), new PCalLocation(3, 7)) ;
  }
  
  /**
   * The line number of the source file that, when the file was translated,
   * corresponded to line 0 of {@link TLAtoPCalMapping#mapping}.  At that
   * time, it was the line immediately after the BEGIN TRANSLATION comment.
   */
  public int tlaStartLine;
  
  /**
   * The line containing the --algorithm or --fair that begins the
   * algorithm.
   */
  public int algLine ;
  
  /**
   * Should be the column of the beginning --algorithm or --fair that
   * begins the algorithm, but it's actually the column after that
   * token--which should make any difference.
   * 
   * I don't think this is needed.
   */
  public int algColumn ;
}
