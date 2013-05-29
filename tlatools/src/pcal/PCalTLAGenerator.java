package pcal;

import java.util.Vector;

import pcal.exception.PcalFixIDException;
import pcal.exception.PcalSymTabException;
import pcal.exception.PcalTLAGenException;
import pcal.exception.PcalTranslateException;
import pcal.exception.RemoveNameConflictsException;

/**
 * Responsible for generation of TLA+ from PCal AST<br>
 * Note: this class is renamed from NotYetImplemented on 11th March 2009
 * 
 * @author Leslie Lamport, Keith Marzullo
 * @version $Id$
 */
public class PCalTLAGenerator
{

    private PcalSymTab st = null;
    private AST ast = null; 
             // This is set to the AST constructed by ParseAlgorithm.getAlgorithm

    /**
     * Constructs a working copy 
     * @param ast
     */
    public PCalTLAGenerator(AST ast)
    {
        this.ast = ast;
    }

    /********************************************************************
     * Called by trans.java.  Should go in a new .java file.            *
     ********************************************************************/
    public void removeNameConflicts() throws RemoveNameConflictsException
    {
        try
        {
            st = new PcalSymTab(ast);
        } catch (PcalSymTabException e)
        {
            throw new RemoveNameConflictsException(e.getMessage());
        }

        st.Disambiguate();
        if (st.disambiguateReport.size() > 0)
            // SZ March 11, 2009. Warning reporting moved to PCalDebug 
            PcalDebug.reportWarning("symbols were renamed.");
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

    /********************************************************************
     * The main translation method.  Should go in a new .java file.     *
     * Note that this requires RemoveNameConflicts to be called first   *
     * because of the grotty use of the class variable st.              *
     ********************************************************************/
    public Vector translate() throws RemoveNameConflictsException
    {
        Vector result = new Vector();
        AST xast = null;  // Set to the exploded AST

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
            PcalTLAGen tlaGenerator = new PcalTLAGen();
//            result.addAll(tlaGenerator.generate(xast, st));
            result = tlaGenerator.generate(xast, st, result);
        } catch (PcalTLAGenException e)
        {
            throw new RemoveNameConflictsException(e);
        }

// tla-pcal debugging
//System.out.println("After Translation:");
//System.out.println(xast.toString());
        /*******************************************************************
        * Following test added by LL on 31 Aug 2007.                       *
        *******************************************************************/
        try
        {
            if (ParseAlgorithm.hasDefaultInitialization)
            {
                st.CheckForDefaultInitValue();
            }
        } catch (PcalSymTabException e)
        {
            throw new RemoveNameConflictsException(e.getMessage());
        }
        return result;
    }
}
