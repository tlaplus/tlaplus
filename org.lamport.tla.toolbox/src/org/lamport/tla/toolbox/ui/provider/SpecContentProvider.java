package org.lamport.tla.toolbox.ui.provider;

import java.util.Hashtable;
import java.util.Vector;

import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.jface.viewers.ITreeContentProvider;
import org.eclipse.jface.viewers.Viewer;
import org.lamport.tla.toolbox.Activator;
import org.lamport.tla.toolbox.job.DeleteOutOfSyncJob;
import org.lamport.tla.toolbox.spec.Module;
import org.lamport.tla.toolbox.spec.Spec;
import org.lamport.tla.toolbox.spec.manager.WorkspaceSpecManager;
import org.lamport.tla.toolbox.util.ResourceHelper;


/**
 * Content provider listing the specifications
 * @author Simon Zambrovski
 * @version $Id$
 */
public class SpecContentProvider implements ITreeContentProvider
    {
        private static final Object[] EMPTY_ARRAY = new Object[0];
        private Hashtable reverseLookup;

        
        public SpecContentProvider()
        {
            reverseLookup = new Hashtable(31);
        }

        /**
         * Retrieves the children
         */
        public Object[] getChildren(Object parentElement)
        {
            if (parentElement instanceof WorkspaceSpecManager)
            {
                return ((WorkspaceSpecManager)parentElement).getRecentlyOpened();
            } else if (parentElement instanceof Spec)
            {
                return EMPTY_ARRAY;
                /*
                Module[] modules = constructModules((Spec) parentElement);
                return modules;
                */
            } else
            {
                return EMPTY_ARRAY;
            }
        }


        public Object getParent(Object element)
        {
            if (element instanceof Spec)
            {
                return ResourcesPlugin.getWorkspace().getRoot();
            } else if (element instanceof Module)
            {
                Spec spec = (Spec) reverseLookup.get(element);
                // cheaty hack
                if (spec == null) 
                {
                    spec = Activator.getSpecManager().getSpecLoaded();
                }
                return spec;
            }
            return null;
        }

        public boolean hasChildren(Object element)
        {
            return (element instanceof WorkspaceSpecManager 
                    /* || element instanceof Spec */ );
        }

        public Object[] getElements(Object inputElement)
        {
            return getChildren(inputElement);
        }

        public void dispose()
        {
            reverseLookup = null;
        }

        public void inputChanged(Viewer viewer, Object oldInput, Object newInput)
        {
            
        }
        /**
         * @deprecated not used
         */
        private Module[] constructModules(Spec spec)
        {
            
            Vector outOfSyncResourcesToDelete = new Vector();
            Vector modules = new Vector();
            IResource[] moduleResources = spec.getModuleResources();
            for (int i = 0; i < moduleResources.length; i++)
            {
                // skip non-modules 
                if (!ResourceHelper.isModule(moduleResources[i]))
                {
                    continue;
                } 
                // skip non-existing files
                if (!moduleResources[i].isSynchronized(IResource.DEPTH_ZERO)) 
                {
                    outOfSyncResourcesToDelete.add(moduleResources[i]); 
                    continue;
                }
                Module module = new Module(moduleResources[i].getLocation().toOSString());
                modules.add(module);
                reverseLookup.put(module, spec);
            }

            DeleteOutOfSyncJob job = new DeleteOutOfSyncJob(outOfSyncResourcesToDelete);
            job.setRule(ResourceHelper.getDeleteRule((IResource[]) outOfSyncResourcesToDelete.toArray(new IResource[outOfSyncResourcesToDelete.size()])));
            job.schedule(500);

            return (Module[]) modules.toArray(new Module[modules.size()]);
        }
}
