package pcal;

import java.util.Vector;

import pcal.exception.PcalFixIDException;
import pcal.exception.PcalSymTabException;
import pcal.exception.PcalTLAGenException;
import pcal.exception.PcalTranslateException;
import pcal.exception.RemoveNameConflictsException;
import util.ToolIO;

public class NotYetImplemented {

    private static PcalSymTab st = null;

    public static void RemoveNameConflicts(AST ast) throws RemoveNameConflictsException {
        /********************************************************************
         * Called by trans.java.  Should go in a new .java file.            *
         ********************************************************************/

        try
        {
            st = new PcalSymTab(ast);
        } catch (PcalSymTabException e)
        {
            throw new RemoveNameConflictsException(e.getMessage());
        }
        st.Disambiguate();
        if (st.disambiguateReport.size() > 0)
            ToolIO.out.println("Warning: symbols were renamed.");
        if (st.errorReport.length() > 0)
            throw new RemoveNameConflictsException(st.errorReport);
        try
        {
            PcalFixIDs.Fix(ast, st);
        } catch (PcalFixIDException e)
        {
            throw new RemoveNameConflictsException(e.getMessage());
        }
    } 

    public static Vector Translate(AST ast) throws RemoveNameConflictsException {
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
        try
        {
            xast = PcalTranslate.Explode(ast, st);
        } catch (PcalTranslateException e)
        {
            throw new RemoveNameConflictsException(e);
        }
        // System.out.println("After exploding: " + xast.toString());
        try
        {
            result.addAll(PcalTLAGen.Gen(xast,  st));
        } catch (PcalTLAGenException e)
        {
            throw new RemoveNameConflictsException(e);
        }
        /*******************************************************************
        * Following test added by LL on 31 Aug 2007.                       *
        *******************************************************************/
        try
        {
            if (ParseAlgorithm.hasDefaultInitialization) 
              { st.CheckForDefaultInitValue() ; }
        } catch (PcalSymTabException e)
        {
            throw new RemoveNameConflictsException(e.getMessage());
        } ;
        return result ;
    }

} 
