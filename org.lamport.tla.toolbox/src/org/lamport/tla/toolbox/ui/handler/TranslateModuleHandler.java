package org.lamport.tla.toolbox.ui.handler;

import java.util.List;
import java.util.Vector;

import org.eclipse.core.commands.AbstractHandler;
import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.core.commands.ExecutionException;
import org.eclipse.core.commands.IHandler;
import org.eclipse.core.resources.IMarker;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.ui.IEditorInput;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.IFileEditorInput;
import org.lamport.tla.toolbox.util.ResourceHelper;
import org.lamport.tla.toolbox.util.TLAMarkerHelper;
import org.lamport.tla.toolbox.util.UIHelper;
import org.lamport.tla.toolbox.util.pref.IPreferenceConstants;

import pcal.Translator;

/**
 * Triggers the PCal translation of the module
 * @author Simon Zambrovski
 * @version $Id$
 */
public class TranslateModuleHandler extends AbstractHandler implements IHandler
{
    Translator translator = new Translator();

    public Object execute(ExecutionEvent event) throws ExecutionException
    {
        IEditorPart activeEditor = UIHelper.getActivePage().getActiveEditor();

        if (activeEditor.isDirty())
        {
            // editor is not saved
            // TODO react on this!
        }

        IEditorInput editorInput = activeEditor.getEditorInput();
        if (editorInput instanceof IFileEditorInput)
        {
            IResource fileToBuild = ((IFileEditorInput) editorInput).getFile();
            System.out.println("Translating " + fileToBuild.getLocation().toOSString());

            boolean hasPcalAlg = false;
            String[] params;

            try
            {
                hasPcalAlg = ((Boolean) fileToBuild.getSessionProperty(ResourceHelper
                        .getQName(IPreferenceConstants.CONTAINS_PCAL_ALGORITHM))).booleanValue();
                params = ((String) fileToBuild.getPersistentProperty(ResourceHelper
                        .getQName(IPreferenceConstants.PCAL_CAL_PARAMS))).split(" ");

            } catch (CoreException e1)
            {
                e1.printStackTrace();
                params = new String[0];
            }

            if (!hasPcalAlg)
            {
                // no algorithm detected
                System.out.println("No algorithm found");
            } else {
                System.out.println("Algorithm found");
            }

            // add params from the resource setting
            Vector callParams = new Vector();
            for (int i=0; i < params.length; i++)
            {
                if (params[i] != null && !params[i].equals("")) 
                {
                    callParams.add(params[i]);
                }
            }
            callParams.add(fileToBuild.getLocation().toOSString());
            

            StringBuffer buffer = new StringBuffer();
            for (int i = 0; i < callParams.size(); i++)
            {
                buffer.append(" " + callParams.elementAt(i));
            }
            System.out.println("Translator invoked with params: '" + buffer.toString()+ "'");

            translator.runTranslation((String[]) callParams.toArray(new String[callParams.size()]));

            List errors = translator.getErrorMessages();

            for (int i = 0; i < errors.size(); i++)
            {
                String errorMessage = (String) errors.get(i);

                TLAMarkerHelper.installProblemMarker(fileToBuild, fileToBuild.getName(), IMarker.SEVERITY_ERROR,
                        detectLocation(errorMessage), errorMessage, null);
            }

            // only refresh on no errors
            if (errors.size() == 0)
            {
                try
                {
                    fileToBuild.refreshLocal(IResource.DEPTH_ONE, null);
                } catch (CoreException e)
                {
                    e.printStackTrace();
                }
            }
        }
        return null;
    }

    private int[] detectLocation(String message)
    {
        int lineStarts = message.indexOf("line ");
        int lineEnds = message.indexOf(" , column ");
        if (lineStarts != -1 && lineEnds != -1)
        {
            String line = message.substring(lineStarts, lineEnds);
            int lineNumber = Integer.parseInt(line);
            return new int[] { lineNumber, -1, Integer.parseInt(line), -1 };
        }
        return new int[] { -1, -1, -1, -1 };
    }

}
