package pcal;

import pcal.exception.*;

import java.util.ArrayList;

/**
 * Responsible for generation of TLA+ from PCal AST<br>
 * Note: this class is renamed from NotYetImplemented on 11th March 2009
 *
 * @author Leslie Lamport, Keith Marzullo
 * @version $Id$
 */
public class PCalTLAGenerator {

    private final AST ast;
    private final ParseAlgorithm parseAlgorithm;
    // This is set to the AST constructed by ParseAlgorithm.getAlgorithm
    private PcalSymTab st = null;

    /**
     * Constructs a working copy
     */
    public PCalTLAGenerator(final AST ast, final ParseAlgorithm parseAlgorithm) {
        this.ast = ast;
        this.parseAlgorithm = parseAlgorithm;
    }

    /********************************************************************
     * Called by trans.java.  Should go in a new .java file.            *
     ********************************************************************/
    public void removeNameConflicts() throws RemoveNameConflictsException {
        try {
            st = new PcalSymTab(ast);
        } catch (final PcalSymTabException e) {
            throw new RemoveNameConflictsException(e.getMessage());
        }

        st.Disambiguate();
        if (st.disambiguateReport.size() > 0)
            // SZ March 11, 2009. Warning reporting moved to PCalDebug 
            PcalDebug.reportWarning("symbols were renamed.");
        if (st.errorReport.length() > 0)
            throw new RemoveNameConflictsException(st.errorReport);
        try {
            PcalFixIDs.Fix(ast, st);
        } catch (final PcalFixIDException e) {
            throw new RemoveNameConflictsException(e.getMessage());
        }
    }

    /********************************************************************
     * The main translation method.  Should go in a new .java file.     *
     * Note that this requires RemoveNameConflicts to be called first   *
     * because of the grotty use of the class variable st.              *
     ********************************************************************/
    public ArrayList<String> translate() throws RemoveNameConflictsException {
        AST xast;  // Set to the exploded AST

        PcalTranslate pcalTranslate = new PcalTranslate(this.parseAlgorithm);

        ArrayList<String> result = new ArrayList<>(st.disambiguateReport);
        try {
            xast = pcalTranslate.Explode(ast, st);
        } catch (final PcalTranslateException e) {
            throw new RemoveNameConflictsException(e);
        }
        // System.out.println("After exploding: " + xast.toString());
        try {
            final PcalTLAGen tlaGenerator = new PcalTLAGen(parseAlgorithm);
//            result.addAll(tlaGenerator.generate(xast, st));
            result = tlaGenerator.generate(xast, st, result);
        } catch (final PcalTLAGenException e) {
            throw new RemoveNameConflictsException(e);
        }

// tla-pcal debugging
/*******************************************************************
 * Following test added by LL on 31 Aug 2007.                       *
 *******************************************************************/
        try {
            if (parseAlgorithm.hasDefaultInitialization) {
                st.CheckForDefaultInitValue();
            }
        } catch (final PcalSymTabException e) {
            throw new RemoveNameConflictsException(e.getMessage());
        }
        return result;
    }
}
