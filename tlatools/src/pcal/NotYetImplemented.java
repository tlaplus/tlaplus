package pcal;

import java.util.Vector;

import util.ToolIO;

public class NotYetImplemented {

    private static PcalSymTab st = null;

    public static void RemoveNameConflicts(AST ast) {
        /********************************************************************
         * Called by trans.java.  Should go in a new .java file.            *
         ********************************************************************/

        st = new PcalSymTab(ast);
        st.Disambiguate();
        if (st.disambiguateReport.size() > 0)
            ToolIO.out.println("Warning: symbols were renamed.");
        if (st.errorReport.length() > 0)
            PcalDebug.ReportError(st.errorReport);
        PcalFixIDs.Fix(ast, st);
    } 

    public static Vector Translate(AST ast) {
        /********************************************************************
         * The main translation method.  Should go in a new .java file.     *
         * Note that this requires RemoveNameConflicts to be called first   *
         * because of the grotty use of the class variable st.              *
         ********************************************************************/
        Vector result = new Vector() ;
        AST xast = null;

        for (int i = 0; i < st.disambiguateReport.size(); i++)
            result.addElement(st.disambiguateReport.elementAt(i));
        // System.out.println("Before: " + ast.toString());
        // System.out.println("After renaming: " + ast.toString());
        xast = PcalTranslate.Explode(ast, st);
        // System.out.println("After exploding: " + xast.toString());
        result.addAll(PcalTLAGen.Gen(xast,  st));
        /*******************************************************************
        * Following test added by LL on 31 Aug 2007.                       *
        *******************************************************************/
        if (ParseAlgorithm.hasDefaultInitialization) 
          { st.CheckForDefaultInitValue() ; } ;
        return result ;
    }

} 
