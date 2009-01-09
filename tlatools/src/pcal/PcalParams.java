/***************************************************************************
* CLASS PcalParams                                                         *
*                                                                          *
* The fields of this class consist of all the parameters used by           *
* pcal.trans.  Some of them are set by program options.                    *
***************************************************************************/
package pcal ;
import java.util.Vector;

public final class PcalParams
 { 
  
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
    * The string identifying the beginning of the algorithm.               *
    ***********************************************************************/
    public static final String BeginAlg = "--algorithm" ;

    /***********************************************************************
    * The strings marking the beginning and end of the translated          *
    * algorithm in the input file.  The translation is put immediately     *
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
    * the argument with which the program is called.                       *
    ***********************************************************************/
    
 }  

/* last modified on Thu 23 Aug 2007 at 10:40:25 PST by lamport */
