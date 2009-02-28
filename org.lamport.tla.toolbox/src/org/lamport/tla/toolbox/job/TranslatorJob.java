package org.lamport.tla.toolbox.job;

import java.util.List;
import java.util.Vector;

import org.eclipse.core.resources.IMarker;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.WorkspaceJob;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;
import org.lamport.tla.toolbox.util.ResourceHelper;
import org.lamport.tla.toolbox.util.TLAMarkerHelper;
import org.lamport.tla.toolbox.util.pref.IPreferenceConstants;

import pcal.Translator;

/**
 * Runs the PCal translator
 * @author Simon Zambrovski
 * @version $Id$
 */
public class TranslatorJob extends WorkspaceJob
{
    private Translator  translator = new Translator();
    private Vector      callParams = new Vector();
    private IResource   fileToBuild;
    
    /**
     * @param name
     */
    public TranslatorJob(IResource fileToBuild)
    {
        super("PCal Translation");
        this.fileToBuild = fileToBuild;
        
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


    }

    /**
     * @see org.eclipse.core.resources.WorkspaceJob#runInWorkspace(org.eclipse.core.runtime.IProgressMonitor)
     */
    public IStatus runInWorkspace(IProgressMonitor monitor) throws CoreException
    {
        monitor.beginTask("PCal Translation", IProgressMonitor.UNKNOWN);
        translator.runTranslation((String[]) callParams.toArray(new String[callParams.size()]));

        monitor.worked(1);
        monitor.setTaskName("Analyzing results");

        List errors = translator.getErrorMessages();

        if (errors.size() > 0)
        {
            monitor.setTaskName("Installing problem markers");
            for (int i = 0; i < errors.size(); i++)
            {
                String errorMessage = (String) errors.get(i);

                TLAMarkerHelper.installProblemMarker(fileToBuild, fileToBuild.getName(), IMarker.SEVERITY_ERROR,
                        detectLocation(errorMessage), errorMessage, null);
            }
        }

        monitor.worked(1);
        monitor.done();
        return Status.OK_STATUS;
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
