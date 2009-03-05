package de.techjava.tla.ui.builders;

import java.util.ArrayList;
import java.util.Enumeration;
import java.util.HashMap;
import java.util.Iterator;
import java.util.Map;
import java.util.Map.Entry;

import org.eclipse.core.internal.resources.File;
import org.eclipse.core.resources.IContainer;
import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IMarker;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.IResourceVisitor;
import org.eclipse.core.resources.IncrementalProjectBuilder;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IPath;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.Path;
import org.eclipse.core.runtime.preferences.IEclipsePreferences;

import de.techjava.tla.ui.UIPlugin;
import de.techjava.tla.ui.editors.outline.TLAOutlineTreeNode;
import de.techjava.tla.ui.extensions.IProblemContainer;
import de.techjava.tla.ui.extensions.IProblemHolder;
import de.techjava.tla.ui.extensions.ITLAParserConfiguration;
import de.techjava.tla.ui.extensions.ITLAParserResult;
import de.techjava.tla.ui.extensions.ITLAParserRuntime;
import de.techjava.tla.ui.extensions.SimpleLocation;
import de.techjava.tla.ui.extensions.SimpleProblemHolder;
import de.techjava.tla.ui.markers.ITLAMarkerTypes;
import de.techjava.tla.ui.util.ExtensionManager;
import de.techjava.tla.ui.util.ITLAProjectConstants;
import de.techjava.tla.ui.util.MarkerHelper;
import de.techjava.tla.ui.util.ParserManager;
import de.techjava.tla.ui.util.ProjectUtils;

/**
 * Starts syntactic analyse
 * @author Simon Zambrovski, <a href="http://simon.zambrovski.org">http://simon.zambrovski.org</a> 
 * @version $Id: TLABuildVisitor.java,v 1.3 2007/06/27 15:34:04 dan_nguyen Exp $
 */
public class TLABuildVisitor 
	implements IResourceVisitor, TLABuilderConstants
{
    
    
    private IProgressMonitor monitor;

    public TLABuildVisitor(IProgressMonitor monitor)
    {
        this.monitor = monitor;
    }
    /**
     * @see org.eclipse.core.resources.IResourceProxyVisitor#visit(org.eclipse.core.resources.IResourceProxy)
     */
    public boolean visit(IResource resource) 
    	throws CoreException 
    {
        ParserManager parserManager = UIPlugin.getDefault().getSANYManager();
        ExtensionManager extManager = UIPlugin.getDefault().getExtensionManager();
        
        ITLAParserConfiguration configuration = extManager.getParserConfiguration(); 
        
        configuration.setSwitches(parserManager.getProperties());
        
        if (resource.getType() == IResource.PROJECT)
        {
            // clear all markers
            resource.deleteMarkers(null, true, IResource.DEPTH_INFINITE);
            
            IProject project = (IProject) resource;
            
            Path[] systemLibraries			= parserManager.getLibraries();
            IProject[] 	referencedProjects 	= project.getReferencedProjects();
            if (referencedProjects.length != 0)
            {
                Path[] 	projectLibraries		= new Path[referencedProjects.length];
	            for (int i = 0; i < referencedProjects.length; i++) 
	            {
	                if (!referencedProjects[i].isOpen()) 
	                {
	                    MarkerHelper.createMarker
	                    (
	                            IMarker.PROBLEM, 
	                            resource, 
	                            new SimpleProblemHolder(
	                                    new SimpleLocation(0,0,0,0),
	                                    "Referenced project " + referencedProjects[i].getName() + " is closed." ,
	                                    IProblemHolder.ABORT
	                            ),
	                            IMarker.SEVERITY_ERROR,
	                            IMarker.PRIORITY_HIGH
	                    );
	                    return false;
	                }
	                try 
	                {
	                    referencedProjects[i].build(IncrementalProjectBuilder.AUTO_BUILD, monitor);
	                    Path referencedProjectPath = (Path) resource.getProject().getLocation().addTrailingSeparator();
	                    
	        	        IEclipsePreferences projectNode = ProjectUtils.getProjectNode(referencedProjects[i]);
	        	        String referencedSourceProperty = projectNode.get(ITLAProjectConstants.PERSIST_PROJECT_SOURCE_FOLDER, "");
	                    if ( !referencedSourceProperty.equals("") )
	                    {
	                        referencedProjectPath = (Path) referencedProjectPath.append(referencedSourceProperty).addTrailingSeparator();
	                    }
	                    
	                    projectLibraries[i] = referencedProjectPath;
	                    
	                } catch (CoreException ce)
	                {
	                    ce.printStackTrace();
	                    return false;
	                }
	                
	            }
                Path[] allLibraries = new Path[projectLibraries.length + systemLibraries.length];
                System.arraycopy(systemLibraries, 0, allLibraries, 0, systemLibraries.length);
                System.arraycopy(projectLibraries, 0, allLibraries, systemLibraries.length, projectLibraries.length);
                configuration.setLibraryPath(allLibraries);
            } else 
            {
                configuration.setLibraryPath(systemLibraries);
            }

            IPath projectPath = resource.getProject().getLocation().addTrailingSeparator();
	        IEclipsePreferences projectNode = ProjectUtils.getProjectNode(project);
	        String sourceProperty = projectNode.get(ITLAProjectConstants.PERSIST_PROJECT_SOURCE_FOLDER, "");
            if (!sourceProperty.equals(""))
            {
                projectPath = projectPath.append(sourceProperty).addTrailingSeparator();
            }
            
            configuration.setRootDirectory(projectPath);

            // TODO: (sz9) Why is this not simply done whenever visit is invoked 
            // for the individual files anyway? If we keep this here, we should 
            // at least return false from this method so that the visitor will 
            // not decend into the project and invoke this operation for every 
            // file in the project again.
            IContainer	sourceRootResource = (IContainer) project.findMember(sourceProperty);
            IResource[] resources = sourceRootResource.members(IResource.FILE);
            ITLAParserRuntime parser = extManager.getParserRuntime();
            
            ArrayList specArr = new ArrayList();
            for (int i = 0; i < resources.length; i++)
            {
                if (resources[i] instanceof IFile ) 
                {
	                File file = (File)resources[i];
	                
	                if (file.getFileExtension() != null && file.getFileExtension().equals("tla")) 
	                {
	                	if ( file.getSessionProperty( LAST_BUILT ) != null &&
	                			((Long)file.getSessionProperty( LAST_BUILT )).longValue() ==
	                				file.getModificationStamp() )
	                    				return false; // TODO: (sz9) Why is this a return here instead of a break?

	                   ITLAParserResult[] parseResults = parser.parse(new String[]{resources[i].getName()}, file.getProject() );
	                   //dannm added	                    	                   
	                   Map tmpArr = parser.getSpecObj();
	                   Iterator iter = tmpArr.entrySet().iterator();
		           		while(iter.hasNext()){
		           			Entry entry = (Entry)iter.next();
		           			TLAOutlineTreeNode tmp =  (TLAOutlineTreeNode)entry.getValue();
		           			tmp.firePropertyChange(tmp);		           		
		           		}			           			                  	                   	                   	                

                       // We set the file's LAST_BUILT property to the 
                       // *project's* modification stamp to ensure that all 
                       // files in the project are rebuilt whenever anything in 
                       // the project is modified!
                       // TODO: (sz9) This seems fishy somehow, for the 
                       // following reasons:
                       //   1) This method will only be invoked for projects in 
                       //      need of a rebuild, so we should just rebuild 
                       //      anything in the project.
                       //   2) The file whose change led to the *previous* 
                       //      rebuild will not be rebuilt this time around 
                       //      unless it has been changed again, because its 
                       //      modification stamp will be the same as its 
                       //      LAST_BUILT property! And because it says return 
                       //      false instead of a simple break above, this may 
                       //      actually lead to a whole bunch of other modules 
                       //      not being reparsed.
	                   file.setSessionProperty( LAST_BUILT, new Long( project.getModificationStamp() ) ); 
	                   if (parseResults.length == 1) 
	                   {
	                       handleErrors(parseResults[0], file);
	                   } else 
	                   {
	                       MarkerHelper.createMarker
	                       (
	                               IMarker.PROBLEM, 
	                               resource, 
	                               new SimpleProblemHolder(
	                                       new SimpleLocation(0,0,0,0),
	                                       "Warning, the number of parse results exceeds the number of input files",
	                                       IProblemHolder.ABORT
	                               ),
	                               IMarker.SEVERITY_ERROR,
	                               IMarker.PRIORITY_HIGH
	                       );
	                       return false;
	                   }
	                }
                }
            }
            //send specMap to outline view input
//            SpecObj[] tmp = new SpecObj[specArr.size()];
//            for(int i=0; i<specArr.size(); i++)
//            	if(specArr.get(i) instanceof SpecObj)
//            		tmp[i] = specArr.get(i);
//            TLAOutlineTreeNodeFactory.setTlaOutlineTreeNode(tmp);
        }
        

        return true;
    }
    
    /**
     * Handle problems
     * @param spec
     * @throws CoreException
     */
    private void handleErrors(ITLAParserResult result, IFile resource) 
    	throws CoreException
    {
        
        IProblemContainer initProblems 		= result.getInitErrors();
        if (initProblems.hasAborts())
        {
            for(Enumeration initAborts = initProblems.getAborts();initAborts.hasMoreElements();)
            {
                IProblemHolder holder = (IProblemHolder) initAborts.nextElement();
                MarkerHelper.createMarker(ITLAMarkerTypes.MARKER_SANY_ABORT_INIT, resource, holder, IMarker.SEVERITY_ERROR, IMarker.PRIORITY_HIGH);
            }
        }
        if (initProblems.hasErrors())
        {
            for(Enumeration initErrors = initProblems.getErrors();initErrors.hasMoreElements();)
            {
                IProblemHolder holder = (IProblemHolder) initErrors.nextElement();
                MarkerHelper.createMarker(ITLAMarkerTypes.MARKER_SANY_ERROR_INIT, resource, holder, IMarker.SEVERITY_ERROR, IMarker.PRIORITY_NORMAL);
            }
        }
        if (initProblems.hasWarnings())
        {
            for(Enumeration initWarnings = initProblems.getErrors();initWarnings.hasMoreElements();)
            {
                IProblemHolder holder = (IProblemHolder) initWarnings.nextElement();
                MarkerHelper.createMarker(ITLAMarkerTypes.MARKER_SANY_WARN_INIT, resource, holder, IMarker.SEVERITY_WARNING, IMarker.PRIORITY_LOW);
            }
        }

        IProblemContainer parseProblems		= result.getParseErrors();
        if (parseProblems.hasAborts())
        {
            for(Enumeration parseAborts = parseProblems.getAborts();parseAborts.hasMoreElements();)
            {
                IProblemHolder holder = (IProblemHolder) parseAborts.nextElement();
                MarkerHelper.createMarker(ITLAMarkerTypes.MARKER_SANY_ABORT_PARSER, resource, holder, IMarker.SEVERITY_ERROR, IMarker.PRIORITY_HIGH);
            }
        }
        if (parseProblems.hasErrors())
        {
            for(Enumeration parseErrors = parseProblems.getErrors();parseErrors.hasMoreElements();)
            {
                IProblemHolder holder = (IProblemHolder) parseErrors.nextElement();
                MarkerHelper.createMarker(ITLAMarkerTypes.MARKER_SANY_ERROR_PARSER, resource, holder, IMarker.SEVERITY_ERROR, IMarker.PRIORITY_NORMAL);
            }
        }
        if (parseProblems.hasWarnings())
        {
            for(Enumeration parseWarnings = parseProblems.getErrors();parseWarnings.hasMoreElements();)
            {
                IProblemHolder holder = (IProblemHolder) parseWarnings.nextElement();
                MarkerHelper.createMarker(ITLAMarkerTypes.MARKER_SANY_WARN_PARSER, resource, holder, IMarker.SEVERITY_WARNING, IMarker.PRIORITY_LOW);
            }
        }

        IProblemContainer semanticProblems	= result.getSemanticErrors();
        if (semanticProblems.hasAborts())
        {
            for(Enumeration semanticAborts = semanticProblems.getAborts();semanticAborts.hasMoreElements();)
            {
                IProblemHolder holder = (IProblemHolder) semanticAborts.nextElement();
                MarkerHelper.createMarker(ITLAMarkerTypes.MARKER_SANY_ABORT_SEMANTIC, resource, holder, IMarker.SEVERITY_ERROR, IMarker.PRIORITY_HIGH);
            }
        }
        if (semanticProblems.hasErrors())
        {
            for(Enumeration semanticErrors = semanticProblems.getErrors();semanticErrors.hasMoreElements();)
            {
                IProblemHolder holder = (IProblemHolder) semanticErrors.nextElement();
                MarkerHelper.createMarker(ITLAMarkerTypes.MARKER_SANY_ERROR_SEMANTIC, resource, holder, IMarker.SEVERITY_ERROR, IMarker.PRIORITY_NORMAL);
            }
        }
        if (semanticProblems.hasWarnings())
        {
            for(Enumeration semanticWarnings = semanticProblems.getErrors();semanticWarnings.hasMoreElements();)
            {
                IProblemHolder holder = (IProblemHolder) semanticWarnings.nextElement();
                MarkerHelper.createMarker(ITLAMarkerTypes.MARKER_SANY_WARN_SEMANTIC, resource, holder, IMarker.SEVERITY_WARNING, IMarker.PRIORITY_LOW );
            }
        }
    }
}

/*
 * $Log: TLABuildVisitor.java,v $
 * Revision 1.3  2007/06/27 15:34:04  dan_nguyen
 * changes for tla editor outline view
 *
 * Revision 1.2  2005/09/29 08:20:00  sz9
 * Added a few comments and clarifications without actually changing the behaviour of the system. This was done in search of what causes issue #1304645. Hopefully somebody will be able to give me some feedback on these comments?
 *
 * Revision 1.1  2005/08/22 15:43:36  szambrovski
 * sf cvs init
 *
 * Revision 1.6  2004/10/25 13:54:05  sza
 * imports
 *
 * Revision 1.5  2004/10/20 17:57:39  bgr
 * incremental build functionality started
 *
 * Revision 1.4  2004/10/13 11:32:37  sza
 * persistent project props changed
 *
 * Revision 1.3  2004/10/13 09:46:02  sza
 * plugin integration
 *
 * Revision 1.2  2004/10/12 16:47:23  sza
 * removed compilation probelms
 *
 * Revision 1.1  2004/10/12 16:21:38  sza
 * initial commit
 *
 * Revision 1.1  2004/10/12 09:55:12  sza
 * additions
 *
 * Revision 1.2  2004/10/07 00:05:28  sza
 * parser bounded
 *
 * Revision 1.1  2004/10/06 01:02:29  sza
 * initial commit
 *
 * Revision 1.1  2004/10/06 00:59:05  sza
 * initial commit
 *
 *
 */