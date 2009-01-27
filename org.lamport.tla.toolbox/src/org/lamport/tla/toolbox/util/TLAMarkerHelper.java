package org.lamport.tla.toolbox.util;

import java.util.Iterator;
import java.util.List;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IMarker;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.IWorkspace;
import org.eclipse.core.resources.IWorkspaceRunnable;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.jface.text.BadLocationException;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.IRegion;
import org.eclipse.ui.editors.text.FileDocumentProvider;
import org.eclipse.ui.part.FileEditorInput;
import org.lamport.tla.toolbox.Activator;
import org.lamport.tla.toolbox.spec.Spec;
import org.lamport.tla.toolbox.spec.parser.problem.Problem;

/**
 * Takes care of problem display
 * @author Simon Zambrovski
 * @version $Id$
 */
public class TLAMarkerHelper
{
    /**
     * 
     */
    public static final String TOOLBOX_MARKERS_PROBLEM_MARKER_ID = "toolbox.markers.TLAParserProblemMarker";

    /**
     * Installs a problem marker on a resource
     * @param resource a resource, to put the problem marker on
     * @param problem a problem holder
     * @param monitor 
     */
    public static void installProblemMarkers(final IResource resource, final Problem problem,
            final IProgressMonitor monitor)
    {
        IWorkspaceRunnable runnable = new IWorkspaceRunnable() {

            public void run(IProgressMonitor monitor) throws CoreException
            {
                IMarker marker = null;
                marker = resource.createMarker(TOOLBOX_MARKERS_PROBLEM_MARKER_ID);
                // Once we have a marker object, we can set its attributes
                marker.setAttribute(IMarker.SEVERITY, AdapterFactory.getMarkerSeverityFromProblem(problem));
                marker.setAttribute(IMarker.MESSAGE, problem.message);
                marker.setAttribute(IMarker.LOCATION, problem.getFormattedLocation());

                marker.setAttribute("toolbox.location.modulename", problem.location.moduleName);
                marker.setAttribute("toolbox.location.beginline", problem.location.beginLine);
                marker.setAttribute("toolbox.location.endline", problem.location.endLine);
                marker.setAttribute("toolbox.location.begincolumn", problem.location.beginColumn);
                marker.setAttribute("toolbox.location.endcolumn", problem.location.endColumn);

                if (problem.location.beginLine == problem.location.endLine || problem.location.endLine == -1)
                {
                    marker.setAttribute(IMarker.LINE_NUMBER, problem.location.beginLine);
                }

                // retrieve the resource
                IResource problemResource = Activator.getSpecManager().getSpecLoaded().findModule(
                        problem.location.moduleName);
                IDocument document = null;
                
                // since we know that the editor uses file based editor representation
                FileEditorInput fileEditorInput = new FileEditorInput((IFile) problemResource);
                FileDocumentProvider fileDocumentProvider = new FileDocumentProvider();
                fileDocumentProvider.connect(fileEditorInput);
                document = fileDocumentProvider.getDocument(fileEditorInput);
                if (document != null)
                {
                    try
                    {
                        // find the line in the document
                        IRegion lineRegion = document.getLineInformation(problem.location.beginLine - 1);

                        // get the text representation of the line
                        String textLine = document.get(lineRegion.getOffset(), lineRegion.getLength());

                        marker.setAttribute(IMarker.CHAR_START, lineRegion.getOffset() + getRealOffset(textLine, problem.location.beginColumn - 1));
                        marker.setAttribute(IMarker.CHAR_END, lineRegion.getOffset() + getRealOffset(textLine, problem.location.endColumn));

                    } catch (BadLocationException e)
                    {
                        // TODO Auto-generated catch block
                        e.printStackTrace();
                    }
                }
            }
        };
        try
        {
            resource.getWorkspace().run(runnable, null, IWorkspace.AVOID_UPDATE, monitor);
        } catch (CoreException e)
        {
            // TODO Auto-generated catch block
            e.printStackTrace();
        }
    }

    /**
     * Delete all markers from this resource and all child resources
     * @param resource resource containing markers
     * @param monitor 
     */
    public static void removeProblemMarkers(final IResource resource, final IProgressMonitor monitor)
    {
        IWorkspaceRunnable runnable = new IWorkspaceRunnable() {

            public void run(IProgressMonitor monitor) throws CoreException
            {
                IMarker[] problems = null;
                int depth = IResource.DEPTH_INFINITE;
                problems = resource.findMarkers(IMarker.PROBLEM, true, depth);
                for (int i = 0; i < problems.length; i++)
                {
                    problems[i].delete();
                }
            }
        };

        try
        {
            resource.getWorkspace().run(runnable, monitor);
        } catch (CoreException e)
        {
            e.printStackTrace();
        }
    }

    /**
     * Updates problem information for spec currently loaded by the spec manger
     */
    public static void updateProblemInformation()
    {
        deleteMarkers(Activator.getSpecManager().getSpecLoaded(), null);
        setupProblemInformation(Activator.getSpecManager().getSpecLoaded(), null);
    }

    /**
     * Updates problem information for given spec
     * @param spec - the spec, to update information on 
     */
    public static void setupProblemInformation(final Spec spec, IProgressMonitor monitor)
    {
        if (spec != null)
        {

            // install new problem marker
            List problems = spec.getParseProblems().getProblems(Problem.ALL);
            Iterator pIterator = problems.iterator();
            // iterate over problems if any
            for (; pIterator.hasNext();)
            {
                Problem problem = (Problem) pIterator.next();
                String moduleName = problem.location.moduleName;

                if (moduleName != null && spec.getModule(moduleName) != null)
                {
                    // install problems on corresponding module
                    installProblemMarkers(spec.getModule(moduleName), problem, monitor);
                } else
                {
                    // or on spec itself
                    installProblemMarkers(spec.getProject(), problem, monitor);
                }
            }
        }
    }

    public static void deleteMarkers(Spec spec, IProgressMonitor monitor)
    {
        if (spec != null)
        {
            // delete the problems from current spec, if any
            TLAMarkerHelper.removeProblemMarkers(spec.getProject(), monitor);
        }
    }

    /**
     * 
     * @param line
     * @param offset
     * @return
     */
    public static int getRealOffset(String line, int offset)
    {
        // TODO handle this different, read from the editor settings
        if (line.indexOf("\t") == -1)
        {
            return Math.min(offset, line.length());
        } else
        {
            /*
             * TODO this is ugly.. the users should not use tabs
             * 
            int TAB_WIDTH = 8;
            int realOffset = offset;
            int modificator = 0;
            // tab is inside the line
            for (int i = 0; i != -1; i = line.indexOf("\t", i + 1))
            {
                if (i < offset)
                {

                    int tabLength = ((i + modificator) / TAB_WIDTH + 1) * TAB_WIDTH - (i + modificator);
                    modificator += (tabLength - 1);
                    realOffset = realOffset - (tabLength - 1);
                }
            }
            return realOffset;
            */
            return Math.min(offset, line.length());
        }

    }

}
