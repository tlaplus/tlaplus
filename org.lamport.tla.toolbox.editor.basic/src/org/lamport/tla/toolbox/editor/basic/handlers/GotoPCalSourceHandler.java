/**
 *  Note: I attached this command to F10 because the F9 key on my ancient
 *  home keyboard doesn't work.  It should probably go on F9 when I'm through
 *  working on the TLA to PlusCal mapping.
 */
package org.lamport.tla.toolbox.editor.basic.handlers;

import org.eclipse.core.commands.AbstractHandler;
import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.core.commands.ExecutionException;
import org.eclipse.core.commands.IHandler;
import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.jface.text.BadLocationException;
import org.lamport.tla.toolbox.editor.basic.TLAEditor;
import org.lamport.tla.toolbox.editor.basic.util.EditorUtil;
import org.lamport.tla.toolbox.spec.Spec;
import org.lamport.tla.toolbox.tool.ToolboxHandle;
import org.lamport.tla.toolbox.util.UIHelper;

import pcal.TLAtoPCalMapping;

/**
 * @author lamport
 *
 */
public class GotoPCalSourceHandler extends AbstractHandler implements IHandler {


    /* (non-Javadoc)
     * @see org.eclipse.core.commands.IHandler#execute(org.eclipse.core.commands.ExecutionEvent)
     */
    public Object execute(ExecutionEvent event) throws ExecutionException {
        
        // Set mapping to the TLAtoPCalMapping.
        // To do that, we first get the current spec .
        Spec spec = ToolboxHandle.getCurrentSpec();
        if (spec == null)
        {
            return null;
        }

        // We need the module name for looking up the TLAtoPCalMapping.
        // We get the module name from the current editor.
        TLAEditor tlaEditor = EditorUtil.getTLAEditorWithFocus();
        if (tlaEditor == null)
        {
            return null;
        }
        String moduleName = tlaEditor.getModuleName();
       
        TLAtoPCalMapping mapping = spec.getTpMapping(moduleName + ".tla");
        
        /*
         * If mapping is null, then the last translation failed so 
         * we do nothing. This should be impossible, since the command should
         * not be enabled.
         */
        if (mapping == null) {
            return null;
        }
        
		try {
			EditorUtil.mapCurrentTLARegionToPCalRegion(mapping);
		} catch (BadLocationException e) {
			MessageDialog.openWarning(UIHelper.getShellProvider().getShell(),
					"Cannot find PCal algorithm",
					e.getMessage());
		}

		return null;
    }

    /** 
     * We disable the command if there is no translation mapping.
     * @see org.eclipse.core.commands.IHandler#isEnabled()
     */
    public boolean isEnabled() {
        Spec spec = ToolboxHandle.getCurrentSpec();
        if (spec == null)
        {
            return false;
        }
        TLAEditor tlaEditor = EditorUtil.getTLAEditorWithFocus();
        if (tlaEditor == null)
        {
            return false;
        }
        String moduleName = tlaEditor.getModuleName();
       
       return spec.getTpMapping(moduleName + ".tla") != null; 
    }

}
