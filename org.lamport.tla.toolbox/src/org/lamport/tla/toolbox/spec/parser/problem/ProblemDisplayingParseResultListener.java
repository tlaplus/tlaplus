package org.lamport.tla.toolbox.spec.parser.problem;

import org.lamport.tla.toolbox.spec.parser.IParseResultListner;
import org.lamport.tla.toolbox.ui.perspective.ProblemsPerspective;
import org.lamport.tla.toolbox.ui.view.ProblemMarkerView;
import org.lamport.tla.toolbox.util.AdapterFactory;
import org.lamport.tla.toolbox.util.TLAMarkerHelper;
import org.lamport.tla.toolbox.util.UIHelper;

/**
 * React to changes with UI display change 
 * @author zambrovski
 * @version $Id$
 */
public class ProblemDisplayingParseResultListener implements IParseResultListner
{

    /* (non-Javadoc)
     * @see org.lamport.tla.toolbox.spec.parser.IParseResultListner#parseResultChanged(int)
     */
    public void parseResultChanged(int parseStatus)
    {
        // SZA: moved to self window 
        // UIHelper.closeWindow(ProblemsPerspective.ID);

        // there were problems -> open the problem view
        if (AdapterFactory.isProblemStatus(parseStatus))
        {
            UIHelper.openView(ProblemMarkerView.ID);
            
            // SZA: moved to self window
            // UIHelper.openPerspectiveInNewWindow(ProblemsPerspective.ID, null);
        }

        // update problem markers
        TLAMarkerHelper.updateProblemInformation();

    }

}
