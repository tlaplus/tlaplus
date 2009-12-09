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
     * SZ Mar 9, 2009:
     * Added re-initialization method. Since PcalParams class
     * is used instead of PcalParams instance, it is required to
     * take care of parameter initialization and de-initialization
     * by explicit method. This is required in order to make PCal
     * instance reentrant. 
     * 
     * Maybe in some point of time this should be converted to an ordinary
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
        CheckTermination = false;
        Nocfg = false;
        fromPcalFile = false;
        versionNumber = 999999;
        versionOption = null;
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
    * The string identifying the beginning of the algorithm in the .tla    *
    * file.                                                                *
    ***********************************************************************/
    public static final String BeginAlg = "--algorithm" ;

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
   *    added.
   */

  public static boolean fromPcalFile = false ;
     // True iff the algorithm is in a .pcal file.  It is set false if
     // the file argument has the extension .tla, or if there is no
     // file named TLAInputFile + ".pcal".
  public static String versionOption = null;
  public static int versionNumber = 999999;
     // The version number * 1000
  /**
   * Processes the version argument ver.  It sets versionNumber
   * and returns true if it is a legal version number; otherwise,
   * it reports the error with PcalDebug.reportError and returns false;
   * XXXXXXXXX TODO 
   */
  static boolean ProcessVersion(String ver) {
      return true ;
  }
 }  

/* last modified on Thu 23 Aug 2007 at 10:40:25 PST by lamport */
