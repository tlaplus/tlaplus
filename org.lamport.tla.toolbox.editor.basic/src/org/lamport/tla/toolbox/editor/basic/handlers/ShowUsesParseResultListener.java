package org.lamport.tla.toolbox.editor.basic.handlers;

import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.CoreException;
import org.lamport.tla.toolbox.Activator;
import org.lamport.tla.toolbox.editor.basic.TLAEditorActivator;
import org.lamport.tla.toolbox.spec.Spec;
import org.lamport.tla.toolbox.spec.parser.IParseResultListener;
import org.lamport.tla.toolbox.spec.parser.ParseResult;
import org.lamport.tla.toolbox.tool.SpecEvent;
import org.lamport.tla.toolbox.tool.SpecLifecycleParticipant;
import org.lamport.tla.toolbox.ui.preference.EditorPreferencePage;
import org.lamport.tla.toolbox.util.ResourceHelper;

/**
 * This class implements a listener that, when the module is reparsed, checks the LEAR_DECLARATION_USE_MARKERS_ON_PARSE
 * Editor preference and, if selected, should delete any Use markers.  The spec objects' getModuleToShow() value indicates
 * the module on which those markers should be, and they are retrieved from that name. 
 * 
 * @author lamport
 *
 */
public class ShowUsesParseResultListener extends SpecLifecycleParticipant implements IParseResultListener
{
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
            // I don't know why this should ever fail, but there's nothing to be done 
            // if marker deletion fails except to hope that it's because there 
            // weren't any.
        }
        
        return true;

    }
    /**
     * I have no idea when this method is supposed to be called, but I have not
     * seen it ever called.
     */
    public void newParseResult(ParseResult parseResult)
    {
    	TLAEditorActivator.getDefault().logDebug("newParseResult called with status: " + parseResult.getStatus());
    }
}
