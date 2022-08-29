/***************************************************************************
 * CLASS PcalParams                                                         *
 *                                                                          *
 * The fields of this class consist of all the parameters used by           *
 * pcal.trans.  Some of them are set by program options.                    *
 ***************************************************************************/
package pcal;

import java.util.ArrayList;

/**
 * Holds parameters for the PCal Translator
 *
 * @author Keith Marzullo
 * @author Simon Zambrovski
 * @version $Id$
 */
public final class PcalParams {
    /**
     * Parameters to be updated on each new release.
     */
    public static final String modDate = "31 December 2020";
    // Can't increment 1.9 to 1.10 because VersionToNumber(str) calculates a lower
    // numerical value for 1.10 than it does for 1.9. This breaks the FairSeq?Test
    // tests. Until we switch from 1.xx to 2.0, increment versionWeight along with
    // version.
    public static final int versionWeight = 1902;
    public static final String version = "1.11";
    /***********************************************************************
     * The strings identifying the beginning of the algorithm in the .tla   *
     * file.                                                                *
     * The strings "--fair" and "algorithm" added by LL on 6 July 2011.     *
     ***********************************************************************/
    public static final String BeginAlg = "--algorithm";
    public static final String BeginFairAlg = "--fair";
    public static final String BeginFairAlg2 = "algorithm";
    /***********************************************************************
     * The strings marking the beginning and end of the translated          *
     * algorithm in a .tla input file.  The translation is put immediately  *
     * after any line containing                                            *
     *                                                                      *
     *    BeginXLation1 [one space] BeginXlation2 [one space] BeginXlation3 *
     *                                                                      *
     * It is followed by a line containing                                  *
     *                                                                      *
     *    EndXLation1 [one space] EndXlation2 [one space] EndXlation3       *
     ***********************************************************************/
    public static final String BeginXlation1 = "BEGIN";
    public static final String BeginXlation2 = "TRANSLATION";
    public static final String EndXlation1 = "END";
    public static final String EndXlation2 = "TRANSLATION";
    /*************************************************************************
     * The string identifying the end of the automatically generated part of  *
     * the .cfg file and the beginning of the user-added part.                *
     *************************************************************************/
    public static final String CfgFileDelimiter =
            "\\* Add statements after this line.";
    /*************************************************************************
     * Parameters related to non-file Options                                 *
     *************************************************************************/
    public boolean Debug = false;
    /***********************************************************************
     * True if the -debug option is chosen.                                 *
     ***********************************************************************/

    public boolean SpecOption = false;
    /***********************************************************************
     * True if the -spec option is chosen.                                  *
     ***********************************************************************/

    public boolean MyspecOption = false;
    /*********************************************************************
     * The root of translator-generated labels, set to its non-default    *
     * value by the -labelRoot option.                                    *
     *********************************************************************/
    /***********************************************************************
     * True if the -myspec option is chosen.                                *
     ***********************************************************************/

    public boolean Spec2Option = false;
    /***********************************************************************
     * True if the -spec2 option is chosen.                                 *
     ***********************************************************************/

    public boolean Myspec2Option = false;
    /***********************************************************************
     * True if the -myspec2 option is chosen.                               *
     ***********************************************************************/

    public String SpecFile = "";
    public boolean WriteASTFlag = false;
    /***********************************************************************
     * True if the -writeAST option is chosen.                              *
     ***********************************************************************/

    public boolean LabelFlag = false;
    /*********************************************************************
     * True iff there is a -noDoneDisjunct option.                        *
     *********************************************************************/
    /*********************************************************************
     * True iff the -label option is chosen.                              *
     *********************************************************************/

    public boolean ReportLabelsFlag = false;
    /*********************************************************************
     * True iff the -reportLabels option is chosen.                       *
     *********************************************************************/

    public String LabelRoot = "Lbl_";
    /*************************************************************************
     * Parameters for Spec and .cfg file options.                             *
     *************************************************************************/
    public String FairnessOption = "";
    /*********************************************************************
     * Should be "", "wf", "sf", "wfNext", or "sfNext".                   *
     *********************************************************************/

    public boolean CheckTermination = false;
    /*********************************************************************
     * True iff there is a -termination option.                           *
     *********************************************************************/

    public boolean NoOld = false;
    /*********************************************************************
     * True iff there is a -noold option.                                 *
     *********************************************************************/

    public boolean Nocfg = false;
    /*********************************************************************
     * True iff there is a -nocfg option.                                 *
     *********************************************************************/

    public boolean NoDoneDisjunct = false;
    /**********************************************************************
     * The following parameter is set true if --fair algorithm is used.   *
     *********************************************************************/
    public boolean FairAlgorithm = false;
    public int wrapColumn = 78;
    public int ssWrapColumn = 45;
    /*************************************************************************
     * File parameters.                                                       *
     *************************************************************************/
    public String TLAInputFile = "";
    /**
     * Pcal-File Parameters
     * The following parameters were introduced when .pcal files were
     * (briefly) added.  However, most of them still seem to be used.
     */

    public boolean optionsInFile = false;

/************ Stuff for .pcal file ***************************************/
    // Set true when an options statement has been found in the
    // module.  It is a kludgy way to pass an argument to
    // trans.parseAndProcessStringArguments; things are done this
    // way because of the way the code evolved, and no intelligent
    // design has stepped in to fix it.
    public String versionOption = null;
    /***********************************************************************
     * The name of the input file, with no extension.  It is set to equal   *
     * the argument with which the program is called, minus the extension.  *
     * With the introduction of pcal files, the name no longer makes sense. *
     ***********************************************************************/
    public int inputVersionNumber = PcalParams.versionWeight;
    /**
     * The following parameter is used to hold the TLAtoPCalMapping object
     * that is computed by the translation.  Some of that object's fields are
     * used in creating the actual mapping.  It's easier to have the methods
     * that need to use those fields access them via this parameter than to do
     * the more politically correct thing and pass the fields or the object
     * as a parameter in the method calls.
     */
    public TLAtoPCalMapping tlaPcalMapping = null;
    public PcalParams() {

    }
    // The input file's version number * 1000
//  public static boolean readOnly = false; 
    // True iff this is a .pcal input file and the .tla file should
    // not be writable.  This is obsolete and is not used.

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
    {
        final ArrayList<TLAToken> line = new ArrayList<>();
        line.add(new TLAToken("defaultInitValue", 0, 0));
        final ArrayList<ArrayList<TLAToken>> vec = new ArrayList<>();
        vec.add(line);
        final TLAExpr exp = new TLAExpr(vec);
        exp.normalize();
        return exp;
    }

    /**
     * If str is a version number like 3.17, then this returns 1000 times
     * its numeric value--e.g., 3170.  Otherwise, it returns -1.
     */
    public static int VersionToNumber(final String str) {
        boolean error = false;
        int i = 0;
        int result = 0;
        int digitsAfterDecimal = 0;
        boolean afterDecimal = false;
        while ((!error) && i < str.length()) {
            final char c = str.charAt(i);
            if (('0' <= c) && (c <= '9')) {
                result = 10 * result + (c - '0');
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

    /***********************************************************************
     * The file name if the -spec option is chosen.                         *
     ***********************************************************************/

    public boolean tlcTranslation() {
        return SpecOption || MyspecOption || Spec2Option
                || Myspec2Option;
    }

    /**
     * Processes the version argument ver.  It sets versionNumber
     * and returns true if it is a legal version number; otherwise,
     * it reports the error with PcalDebug.reportError and returns false.
     */
    boolean ProcessVersion(final String ver) {
        final int vnum = VersionToNumber(ver);
        if (vnum < 0) {
            PcalDebug.reportError("Illegal version " + ver + " specified.");
            return false;
        }
        if (vnum > PcalParams.versionWeight) {
            PcalDebug.reportError("Specified version " + ver +
                    " later than current version " + PcalParams.version);
            return false;
        }
        inputVersionNumber = vnum;
        return true;
    }
}

/* last modified on Thu 23 Aug 2007 at 10:40:25 PST by lamport */
