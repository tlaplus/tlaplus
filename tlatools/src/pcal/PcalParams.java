/***************************************************************************
* CLASS PcalParams                                                         *
*                                                                          *
* The fields of this class consist of all the parameters used by           *
* pcal.trans.  Some of them are set by program options.                    *
***************************************************************************/
package pcal ;
import java.util.Vector;

/**
 * Holds parameters for the PCal Translator
 * @author Keith Marzullo
 * @author Simon Zambrovski
 * @version $Id$
 */
public final class PcalParams
{ 
    /**
     * Parameters to be updated on each new release.
     */
    public static final String modDate = "2 Apr 2013";
    public static final String version = "1.8";
    /**
     * SZ Mar 9, 2009:
     * Added re-initialization method. Since PcalParams class
     * is used instead of PcalParams instance, it is required to
     * take care of parameter initialization and de-initialization
     * by explicit method. This is required in order to make PCal
     * instance reentrant. 
     * 
     * Maybe at some point in time this should be converted to an ordinary
     * configuration object, from the collection of public static variables.
     */
    public static void resetParams()
    {
        Debug = false;
        SpecOption = false;
        MyspecOption = false;
        Spec2Option = false;
        Myspec2Option = false;
        SpecFile = "";
        WriteASTFlag = false;
        LabelFlag = false;
        ReportLabelsFlag = false;
        LabelRoot = "Lbl_";
        FairnessOption = "";
        FairAlgorithm = false;
        CheckTermination = false;
        Nocfg = false;
        NoDoneDisjunct = false;
        optionsInFile = false;
        versionOption = null;
        inputVersionNumber = VersionToNumber(PcalParams.version);
        PcalTLAGen.wrapColumn = 78;
        PcalTLAGen.ssWrapColumn = 45;
        tlaPcalMapping = null ;
        
    }
    
    
  /*************************************************************************
  * Parameters related to non-file Options                                 *
  *************************************************************************/
    public static boolean Debug = false ;
    /***********************************************************************
    * True if the -debug option is chosen.                                 *
    ***********************************************************************/

    public static boolean SpecOption = false ;
    /***********************************************************************
    * True if the -spec option is chosen.                                  *
    ***********************************************************************/

    public static boolean MyspecOption = false ;
    /***********************************************************************
    * True if the -myspec option is chosen.                                *
    ***********************************************************************/

    public static boolean Spec2Option = false ;
    /***********************************************************************
    * True if the -spec2 option is chosen.                                 *
    ***********************************************************************/

    public static boolean Myspec2Option = false ;
    /***********************************************************************
    * True if the -myspec2 option is chosen.                               *
    ***********************************************************************/

    public static String SpecFile = "" ;
    /***********************************************************************
    * The file name if the -spec option is chosen.                         *
    ***********************************************************************/

    public static boolean WriteASTFlag = false ;
    /***********************************************************************
    * True if the -writeAST option is chosen.                              *
    ***********************************************************************/

    public static boolean LabelFlag = false ;
      /*********************************************************************
      * True iff the -label option is chosen.                              *
      *********************************************************************/

    public static boolean ReportLabelsFlag = false ;
      /*********************************************************************
      * True iff the -reportLabels option is chosen.                       *
      *********************************************************************/

    public static String LabelRoot = "Lbl_" ;
      /*********************************************************************
      * The root of translator-generated labels, set to its non-default    *
      * value by the -labelRoot option.                                    *
      *********************************************************************/
      
  /*************************************************************************
  * Parameters for Spec and .cfg file options.                             *
  *************************************************************************/
    public static String FairnessOption = "" ;
      /*********************************************************************
      * Should be "", "wf", "sf", "wfNext", or "sfNext".                   *
      *********************************************************************/
      
    public static boolean CheckTermination = false ;
      /*********************************************************************
      * True iff there is a -termination option.                           *
      *********************************************************************/
      
    public static boolean Nocfg = false ;
      /*********************************************************************
      * True iff there is a -nocfg option.                                 *
      *********************************************************************/
      
    public static boolean NoDoneDisjunct = false ;
     /*********************************************************************
     * True iff there is a -noDoneDisjunct option.                        *
     *********************************************************************/
    
    /**********************************************************************
     * The following parameter is set true if --fair algorithm is used.   *
     *********************************************************************/
    public static boolean FairAlgorithm = false ; 
    
  /*************************************************************************
  * Parameters related to language definition.                             *
  *************************************************************************/
    public static TLAExpr DefaultVarInit()
      /*********************************************************************
      * Returns the default initial value of a variable declared with no   *
      * value specified, which is herein defined to be "{}".               *
      *                                                                    *
      * Default initial value changed to "defaultInitValue"                *
      * by LL on 22 Aug 2007                                               *
      *********************************************************************/
      { Vector line = new Vector() ;
//        line.addElement(new TLAToken("{", 0, 0)) ;
//        line.addElement(new TLAToken("}", 0, 0)) ;
        line.addElement(new TLAToken("defaultInitValue", 0, 0));
        Vector vec = new Vector() ;
        vec.addElement(line) ;
        TLAExpr exp = new TLAExpr(vec) ;
        exp.normalize() ;
        return exp ;
      }

    /***********************************************************************
    * The strings identifying the beginning of the algorithm in the .tla   *
    * file.                                                                *
    * The strings "--fair" and "algorithm" added by LL on 6 July 2011.     *
    ***********************************************************************/
    public static final String BeginAlg = "--algorithm" ;
    public static final String BeginFairAlg = "--fair" ;
    public static final String BeginFairAlg2 = "algorithm" ;
     
    

    /***********************************************************************
    * The strings marking the beginning and end of the translated          *
    * algorithm in a .tla input file.  The translation is put immediately  *
    * after any line containing                                            *
    *                                                                      *
    *    BeginXLation1 [one or more spaces] BeginXlation2                  *
    *                                                                      *
    * It is followed by a line containing                                  *
    *                                                                      *
    *    EndXLation1 [one or more spaces] EndXlation2.                     *
    ***********************************************************************/
    public static final String BeginXlation1 = "BEGIN" ;
    public static final String BeginXlation2 = "TRANSLATION" ;

    public static final String EndXlation1 = "END" ;
    public static final String EndXlation2 = "TRANSLATION" ;

  /*************************************************************************
  * The string identifying the end of the automatically generated part of  *
  * the .cfg file and the beginning of the user-added part.                *
  *************************************************************************/
  public static String CfgFileDelimiter = 
            "\\* Add statements after this line." ;

/************ Stuff for .pcal file ***************************************/  
  
//  /***********************************************************************
//  * The string identifying the beginning of the algorithm in the .pcal   *
//  * file.                                                                *
//  ***********************************************************************/
//  public static final String PcalBeginAlg = "algorithm";
//   
//  /**
//   * The <row, col> (in Java coordinates) of the beginning of the
//   * "algorithm" token in the .pcal file.
//   */
//  public static IntPair endOfPreamble = null;
//
//  /**
//   * The <row, col> (in Java coordinates) of the beginning of the TLA+ 
//   * "code" that follows the algorithm in the input (.pcal) and output 
//   * (.tla) files.  For outputSuffixLoc, the column always equals 0.
//   */
//  public static IntPair inputSuffixLoc = null;
//  public static IntPair outputSuffixLoc = null;
//  
  /*************************************************************************
  * File parameters.                                                       *
  *************************************************************************/
  public static String TLAInputFile = "" ;
    /***********************************************************************
    * The name of the input file, with no extension.  It is set to equal   *
    * the argument with which the program is called, minus the extension.  *
    * With the introduction of pcal files, the name no longer makes sense. *
    ***********************************************************************/

  /**
   * Pcal-File Parameters
   *    The following parameters were introduced when .pcal files were 
   *    (briefly) added.  However, most of them still seem to be used.
   */

  public static boolean optionsInFile = false ;
     // Set true when an options statement has been found in the
     // module.  It is a kludgy way to pass an argument to 
     // trans.parseAndProcessStringArguments; things are done this
     // way because of the way the code evolved, and no intelligent
     // design has stepped in to fix it.
  public static String versionOption = null;
  public static int inputVersionNumber = VersionToNumber(PcalParams.version);
     // The input file's version number * 1000
//  public static boolean readOnly = false; 
     // True iff this is a .pcal input file and the .tla file should 
     // not be writable.  This is obsolete and is not used.

  /**
   * The following parameter is used to hold the TLAtoPCalMapping object
   * that is computed by the translation.  Some of that object's fields are
   * used in creating the actual mapping.  It's easier to have the methods
   * that need to use those fields access them via this parameter than to do
   * the more politically correct thing and pass the fields or the object
   * as a parameter in the method calls.
   */
  public static TLAtoPCalMapping  tlaPcalMapping ;
  
  /**
   * If str is a version number like 3.17, then this returns 1000 times
   * its numeric value--e.g., 3170.  Otherwise, it returns -1.
   * 
   */
  public static int VersionToNumber(String str) {
    boolean error = false ;
    int i = 0;
    int result = 0;
    int digitsAfterDecimal = 0;
    boolean afterDecimal = false;
    while ((!error) && i < str.length()) {
        char c = str.charAt(i);
        if (('0' <= c) && (c <= '9')) {
            result = 10 * result  +  (c - '0');
            if (afterDecimal) {
                digitsAfterDecimal++;
                if (digitsAfterDecimal > 3) {
                    error = true;
                }
            }
        } else if (c == '.') {
                afterDecimal = true;
        } else {
            error = true;
        }
        i++;
    }
    if (error) {
        return -1;
    }
    for (int j = 0; j < 3 - digitsAfterDecimal; j++) {
        result = 10 * result;
    }
    return result;
  }
  /**
   * Processes the version argument ver.  It sets versionNumber
   * and returns true if it is a legal version number; otherwise,
   * it reports the error with PcalDebug.reportError and returns false.
   */
  static boolean ProcessVersion(String ver) {
      int vnum = VersionToNumber(ver);
      if (vnum < 0) {
          PcalDebug.reportError("Illegal version " + ver + " specified."); 
          return false;
      }
      if (vnum > VersionToNumber(PcalParams.version)) {
          PcalDebug.reportError("Specified version " + ver + 
                  " later than current version " + PcalParams.version);
          return false;
      }
      inputVersionNumber = vnum;
      return true ;
  }
 }  

/* last modified on Thu 23 Aug 2007 at 10:40:25 PST by lamport */
