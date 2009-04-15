package org.lamport.tla.toolbox.job;

import java.lang.reflect.InvocationTargetException;
import java.util.List;
import java.util.Vector;

import org.eclipse.core.resources.IMarker;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.IResourceRuleFactory;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.resources.WorkspaceJob;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;
import org.eclipse.core.runtime.jobs.ISchedulingRule;
import org.eclipse.core.runtime.jobs.MultiRule;
import org.eclipse.jface.operation.IRunnableWithProgress;
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
    private Translator  translator;
    private Vector      callParams;
    private IResource   fileToBuild;
    
    /**
     * @param name
     */
    public TranslatorJob(IResource fileToBuild)
    {
        super("PCal Translation");
        this.translator = new Translator();
        this.fileToBuild = fileToBuild;
        this.callParams = new Vector();
        
        System.out.println("Translating " + fileToBuild.getLocation().toOSString());

        boolean hasPcalAlg = false;
        String[] params;

        try
        {
            hasPcalAlg = ((Boolean) fileToBuild.getSessionProperty(ResourceHelper
                    .getQName(IPreferenceConstants.CONTAINS_PCAL_ALGORITHM))).booleanValue();
            String paramString = ((String) fileToBuild.getPersistentProperty(ResourceHelper
                    .getQName(IPreferenceConstants.PCAL_CAL_PARAMS)));
            if (paramString != null) 
            {
                params = paramString.split(" ");
            } else {
                params = new String[0];
            }

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
        

    }

    /**
     * @see org.eclipse.core.resources.WorkspaceJob#runInWorkspace(org.eclipse.core.runtime.IProgressMonitor)
     */
    public IStatus runInWorkspace(IProgressMonitor monitor) throws CoreException
    {
        monitor.beginTask("PCal Translation", IProgressMonitor.UNKNOWN);

        // remove markers
        monitor.setTaskName("Removing problem markers");
        TLAMarkerHelper.removeProblemMarkers(fileToBuild, monitor, TLAMarkerHelper.TOOLBOX_MARKERS_TRANSLATOR_MARKER_ID);
        
        StringBuffer buffer = new StringBuffer();
        for (int i = 0; i < callParams.size(); i++)
        {
            buffer.append(" " + callParams.elementAt(i));
        }
        System.out.println("Translator invoked with params: '" + buffer.toString()+ "'");

        
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
                        detectLocation(errorMessage), errorMessage, monitor, TLAMarkerHelper.TOOLBOX_MARKERS_TRANSLATOR_MARKER_ID);
            }
        }

        monitor.worked(1);
        monitor.done();
        return Status.OK_STATUS;
    }
    
    /**
     * Return as runnable instead of the job
     * @param fileToBuild
     * @return
     */
    public static IRunnableWithProgress getAsRunnableWithProgress(final IResource fileToBuild)
    {
        final TranslatorJob job = new TranslatorJob(fileToBuild);
        return new IRunnableWithProgress()
        {
            public void run(IProgressMonitor monitor) throws InvocationTargetException, InterruptedException
            {
                try
                {
                    job.setRule(getFileModificationRule(fileToBuild));
                    job.runInWorkspace(monitor);
                } catch (CoreException e)
                {
                    throw new InvocationTargetException(e);
                }
            }
        };
    }
    
    public static ISchedulingRule getFileModificationRule(IResource file)
    {
        IResourceRuleFactory ruleFactory = ResourcesPlugin.getWorkspace().getRuleFactory();
        ISchedulingRule rule = ruleFactory.modifyRule(file);
        return rule;
    }
    


    
    private int[] detectLocation(String message)
    {
        String LINE = "line ";
        String COLUMN = ", column "; 
        
        int lineStarts = message.indexOf(LINE);
        int lineEnds = message.indexOf(COLUMN);
        if (lineStarts != -1 && lineEnds != -1)
        {
            String line = message.substring(lineStarts + LINE.length(), lineEnds);
            String column = message.substring(lineEnds + COLUMN.length());
            
            
            int lineNumber = -1;
            int columnNumber = -1;
            try 
            {
                lineNumber = Integer.parseInt(line);
            } catch (NumberFormatException e) {  }
            try 
            {
                columnNumber = Integer.parseInt(column);
            } catch (NumberFormatException e) {  }
            return new int[] { lineNumber, columnNumber, lineNumber, columnNumber + 1 };
        }
        return new int[] { -1, -1, -1, -1 };
    }

}
