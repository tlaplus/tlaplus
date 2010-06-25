package org.lamport.tla.toolbox.editor.basic.handlers;

import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.CoreException;
import org.lamport.tla.toolbox.Activator;
import org.lamport.tla.toolbox.spec.Spec;
import org.lamport.tla.toolbox.spec.parser.IParseResultListener;
import org.lamport.tla.toolbox.spec.parser.ParseResult;
import org.lamport.tla.toolbox.tool.SpecEvent;
import org.lamport.tla.toolbox.tool.SpecLifecycleParticipant;
import org.lamport.tla.toolbox.ui.preference.EditorPreferencePage;
import org.lamport.tla.toolbox.util.ResourceHelper;

public class ShowUsesParseResultListener extends SpecLifecycleParticipant implements IParseResultListener
{

    public ShowUsesParseResultListener()
    {
        // TODO Auto-generated constructor stub
    }

    /** 
     * This method is called when the spec is parsed, as well as on other occasions
     * that don't interest us.  It deletes the Show Use markers if the user's preference
     * is to do so and if we can find any to delete.
     */
    public boolean eventOccured(SpecEvent event)
    {

        if (event.getType() != SpecEvent.TYPE_PARSE)
        {
            return true;
        }

        // Check if user preference is to remove use markers on parse.
        if (!Activator.getDefault().getPreferenceStore().getBoolean(
                EditorPreferencePage.CLEAR_DECLARATION_USE_MARKERS_ON_PARSE)) {
            return true;
        }
        
        // User wants to remove markers.  Remove them if there are any.
        Spec spec = event.getSpec();
        String moduleName = spec.getModuleToShow();
        if (moduleName == null)
        {
            return true;
        }
        IResource resource = ResourceHelper.getResourceByModuleName(moduleName);
        if (resource == null)
        {
            return true;
        }
        try
        {
            resource.deleteMarkers(ShowUsesHandler.SHOW_USE_MARKER_TYPE, false, 99);
        } catch (CoreException e)
        {
            // Nothing to be done if marker deletion fails.
        }
        
        return true;

    }

    public void newParseResult(ParseResult parseResult)
    {
        System.out.println("newParseResult called with status: " + parseResult.getStatus());
        // TODO Auto-generated method stub

    }

}
