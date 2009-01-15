package org.lamport.tla.toolbox.spec.parser.problem;

import org.lamport.tla.toolbox.spec.parser.IParseConstants;
import org.lamport.tla.toolbox.spec.parser.IParseResultListner;
import org.lamport.tla.toolbox.ui.perspective.ProblemsPerspective;
import org.lamport.tla.toolbox.util.AdapterFactory;
import org.lamport.tla.toolbox.util.TLAMarkerHelper;
import org.lamport.tla.toolbox.util.UIHelper;
import org.lamport.tla.toolbox.util.pref.IPreferenceConstants;
import org.lamport.tla.toolbox.util.pref.PreferenceStoreHelper;

/**
 * React to re-parse 
 * @author Simon Zambrovski
 * @version $Id$
 */
public class ProblemDisplayingParseResultListener implements IParseResultListner
{

    /**
     * @see org.lamport.tla.toolbox.spec.parser.IParseResultListner#parseResultChanged(int)
     */
    public void parseResultChanged(int parseStatus)
    {
        // ignore any changes to the MODIFIED state
        if (IParseConstants.MODIFIED == parseStatus) 
        {
            return;
        }

        // look up the preference for raising windows on errors
        boolean showErrors = PreferenceStoreHelper.getInstancePreferenceStore().getBoolean(IPreferenceConstants.P_PARSER_POPUP_ERRORS);
        if (showErrors) 
        {
            UIHelper.closeWindow(ProblemsPerspective.ID);
            // there were problems -> open the problem view
            if (AdapterFactory.isProblemStatus(parseStatus))
            {
                UIHelper.openPerspectiveInWindowRight(ProblemsPerspective.ID, null, ProblemsPerspective.WIDTH);
            }
        }
        
        // update problem markers
        TLAMarkerHelper.updateProblemInformation();
    }

}
