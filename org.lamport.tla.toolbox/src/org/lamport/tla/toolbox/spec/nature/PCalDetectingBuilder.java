package org.lamport.tla.toolbox.spec.nature;

import java.io.File;
import java.util.Map;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.IResourceVisitor;
import org.eclipse.core.resources.IncrementalProjectBuilder;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.QualifiedName;
import org.eclipse.jface.text.BadLocationException;
import org.eclipse.jface.text.FindReplaceDocumentAdapter;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.IRegion;
import org.eclipse.ui.editors.text.FileDocumentProvider;
import org.eclipse.ui.part.FileEditorInput;
import org.lamport.tla.toolbox.Activator;
import org.lamport.tla.toolbox.spec.Spec;
import org.lamport.tla.toolbox.util.ResourceHelper;
import org.lamport.tla.toolbox.util.pref.IPreferenceConstants;

/**
 * Detects 
 * @author Simon Zambrovski
 * @version $Id$
 */
public class PCalDetectingBuilder extends IncrementalProjectBuilder
{
    
    public static final String BUILDER_ID = "toolbox.builder.PCalAlgorithmSearchingBuilder";
    private static final String PCAL_ALGORITHM_DEFINITION = "--algorithm";
    
    private PCalDetectingVisitor visitor = new PCalDetectingVisitor();

    /* (non-Javadoc)
     * @see org.eclipse.core.resources.IncrementalProjectBuilder#build(int, java.util.Map, org.eclipse.core.runtime.IProgressMonitor)
     */
    protected IProject[] build(int kind, Map args, IProgressMonitor monitor) throws CoreException
    {
        Spec spec = Activator.getSpecManager().getSpecLoaded();
        if (spec == null) 
        {
            return null;
        }
        
        IProject project = getProject();
        
        if (project != spec.getProject())
        {
            // skip the build calls on wrong projects (which are in WS, but not a current spec)
            return null;
        }

        project.accept(visitor);
        
        // must return null
        return null;
    }

    class PCalDetectingVisitor implements IResourceVisitor
    {
        /* (non-Javadoc)
         * @see org.eclipse.core.resources.IResourceVisitor#visit(org.eclipse.core.resources.IResource)
         */
        public boolean visit(IResource resource) throws CoreException
        {
            // check for resource existence (WS in-sync or out-of-sync)
            if (!resource.exists() || !new File(resource.getLocation().toOSString()).exists()) 
            {
                return false;
            }
            if (IResource.PROJECT == resource.getType())
            {
                return true;
            } else if (IResource.FILE == resource.getType() && ResourceHelper.isModule(resource))
            {
                FileEditorInput fileEditorInput = new FileEditorInput((IFile) resource);
                FileDocumentProvider fileDocumentProvider = new FileDocumentProvider();
                fileDocumentProvider.connect(fileEditorInput);
                IDocument document = fileDocumentProvider.getDocument(fileEditorInput);
                FindReplaceDocumentAdapter searchAdapter = new FindReplaceDocumentAdapter(document);
                try
                {
                    IRegion matchRegion = searchAdapter.find(0, PCAL_ALGORITHM_DEFINITION, true, true, false, false);
                    
                    // store the session property
                    QualifiedName key = new QualifiedName(Activator.PLUGIN_ID, IPreferenceConstants.CONTAINS_PCAL_ALGORITHM);
                    if (matchRegion != null ) 
                    {
                        // found a algorithm definition
                        System.out.println("Found algorithm definition in " + resource.getName());
                        resource.setSessionProperty(key, new Boolean(true));
                        
                    } else {
                        resource.setSessionProperty(key, null);
                    }
                } catch (BadLocationException e)
                {
                    // TODO Auto-generated catch block
                    e.printStackTrace();
                }
            }
            return false;
        }

    }
}
