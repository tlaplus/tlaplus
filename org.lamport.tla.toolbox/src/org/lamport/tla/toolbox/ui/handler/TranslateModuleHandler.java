package org.lamport.tla.toolbox.ui.handler;

import org.eclipse.core.commands.AbstractHandler;
import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.core.commands.ExecutionException;
import org.eclipse.core.commands.IHandler;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.IResourceRuleFactory;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.Status;
import org.eclipse.core.runtime.jobs.IJobChangeEvent;
import org.eclipse.core.runtime.jobs.ISchedulingRule;
import org.eclipse.core.runtime.jobs.JobChangeAdapter;
import org.eclipse.core.runtime.jobs.MultiRule;
import org.eclipse.ui.IEditorInput;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.IFileEditorInput;
import org.lamport.tla.toolbox.job.TranslatorJob;
import org.lamport.tla.toolbox.util.UIHelper;

/**
 * Triggers the PCal translation of the module
 * @author Simon Zambrovski
 * @version $Id$
 */
public class TranslateModuleHandler extends AbstractHandler implements IHandler
{

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
            final IResource fileToBuild = ((IFileEditorInput) editorInput).getFile();
            TranslatorJob job = new TranslatorJob(fileToBuild);
            job.setUser(true);
            // TODO config file is also changed
            job.setRule(getModifyRule(new IResource[]{fileToBuild}));
            
            job.addJobChangeListener(new JobChangeAdapter(){
                public void done(IJobChangeEvent event)
                {
                    if (Status.OK_STATUS.equals(event.getResult()))
                    {
                        try
                        {
                            fileToBuild.refreshLocal(IResource.DEPTH_ONE, null);
                        } catch (CoreException e)
                        {
                            // TODO
                            e.printStackTrace();
                        }
                        
                    }
                }

            });

            
            job.schedule();
        }
        return null;
    }

    
    public ISchedulingRule getModifyRule(IResource[] resources)
    {
        if (resources == null)
        {
            return null;
        }
        ISchedulingRule combinedRule = null;
        
        IResourceRuleFactory ruleFactory = ResourcesPlugin.getWorkspace().getRuleFactory();
        for (int i=0; i < resources.length; i++)
        {
           ISchedulingRule rule = ruleFactory.modifyRule(resources[i]); 
           combinedRule = MultiRule.combine(rule, combinedRule);
        }
        return combinedRule;
    }

}
