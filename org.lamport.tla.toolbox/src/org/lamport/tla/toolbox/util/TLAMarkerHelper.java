package org.lamport.tla.toolbox.util;

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
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.editors.text.FileDocumentProvider;
import org.eclipse.ui.ide.IGotoMarker;
import org.eclipse.ui.part.FileEditorInput;
import org.lamport.tla.toolbox.spec.Spec;
import org.lamport.tla.toolbox.ui.handler.OpenSpecHandler;

/**
 * Takes care of problem display
 * @author Simon Zambrovski
 * @version $Id$
 */
public class TLAMarkerHelper
{
    /**
     * End column of the error as reported by SANY
     */
    public static final String LOCATION_ENDCOLUMN = "toolbox.location.endcolumn";
    /**
     * End line of the error as reported by SANY
     */
    public static final String LOCATION_ENDLINE = "toolbox.location.endline";
    /**
     * Begin column of the error as reported by SANY
     */
    public static final String LOCATION_BEGINCOLUMN = "toolbox.location.begincolumn";
    /**
     * Begin line of the error as reported by SANY
     */
    public static final String LOCATION_BEGINLINE = "toolbox.location.beginline";
    /**
     * Module name (different from the generally use filename)
     */
    public static final String LOCATION_MODULENAME = "toolbox.location.modulename";
    /**
     * The marker ID for displaying TLA+ Parser Errors
     */
    public static final String TOOLBOX_MARKERS_PROBLEM_MARKER_ID = "toolbox.markers.TLAParserProblemMarker";

    /**
     * Installs a problem marker on a module
     */
    public static void installProblemMarkerOnModule(IFile module, final int severityError, final int[] coordinates,
            final String message, IProgressMonitor monitor)
    {
        String moduleName = ResourceHelper.getModuleNameChecked(module.getName(), false);
        installProblemMarker(module, moduleName, severityError, coordinates, message, monitor);
    }

    /**
     * Installs a problem marker on a specification 
     */
    public static void installProblemMarkerOnSpec(Spec specification, final int severityError, final int[] coordinates,
            final String message, IProgressMonitor monitor)
    {
        String moduleName = specification.getName();
        installProblemMarker(specification.getProject(), moduleName, severityError, coordinates, message, monitor);
    }
    
    
    
    /**
     * Installs a problem marker on a given resource
     */
    public static void installProblemMarker(final IResource resource, final String moduleName, final int severityError,
            final int[] coordinates, final String message, IProgressMonitor monitor)
    {
        IWorkspaceRunnable runnable = new IWorkspaceRunnable() {

            public void run(IProgressMonitor monitor) throws CoreException
            {
                System.out.println("Installing a marker on " + resource.getName() + " with error on module " + moduleName);
                
                
                IMarker marker = resource.createMarker(TOOLBOX_MARKERS_PROBLEM_MARKER_ID);
                // Once we have a marker object, we can set its attributes
                marker.setAttribute(IMarker.SEVERITY, severityError);
                marker.setAttribute(IMarker.MESSAGE, message);
                marker.setAttribute(IMarker.LOCATION, AdapterFactory.getFormattedLocation(coordinates, moduleName));

                marker.setAttribute(LOCATION_MODULENAME, moduleName);
                marker.setAttribute(LOCATION_BEGINLINE, coordinates[0]);
                marker.setAttribute(LOCATION_BEGINCOLUMN, coordinates[1]);
                marker.setAttribute(LOCATION_ENDLINE, coordinates[2]);
                marker.setAttribute(LOCATION_ENDCOLUMN, coordinates[3]);

                // important! either use line numbers (for creation of a single line marker)
                // or char_start/char_end (to create exact markers, even multi-line)
                if (coordinates[0] == coordinates[3] || coordinates[3] == -1)
                {
                    marker.setAttribute(IMarker.LINE_NUMBER, coordinates[0]);
                } else
                {
                    // retrieve the resource
                    IDocument document = null;

                    // since we know that the editor uses file based editor representation
                    FileEditorInput fileEditorInput = new FileEditorInput((IFile) resource);
                    FileDocumentProvider fileDocumentProvider = new FileDocumentProvider();
                    fileDocumentProvider.connect(fileEditorInput);
                    document = fileDocumentProvider.getDocument(fileEditorInput);
                    if (document != null)
                    {
                        try
                        {
                            // find the line in the document
                            IRegion lineRegion = document.getLineInformation(coordinates[0] - 1);

                            // get the text representation of the line
                            String textLine = document.get(lineRegion.getOffset(), lineRegion.getLength());

                            marker.setAttribute(IMarker.CHAR_START, lineRegion.getOffset()
                                    + getRealOffset(textLine, coordinates[1] - 1));
                            marker.setAttribute(IMarker.CHAR_END, lineRegion.getOffset()
                                    + getRealOffset(textLine, coordinates[3]));

                        } catch (BadLocationException e)
                        {
                            // TODO Auto-generated catch block
                            e.printStackTrace();
                        }
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
                problems = resource.findMarkers(TLAMarkerHelper.TOOLBOX_MARKERS_PROBLEM_MARKER_ID, true, depth);
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
     * Retrieves problem markers associated with given resource
     * @param resource
     * @param monitor
     * @return
     */
    public static IMarker[] getProblemMarkers(final IResource resource, final IProgressMonitor monitor)
    {
        IMarker[] problems = null;
        try
        {
            problems = resource.findMarkers(TLAMarkerHelper.TOOLBOX_MARKERS_PROBLEM_MARKER_ID, true,
                    IResource.DEPTH_INFINITE);
        } catch (CoreException e)
        {
            // TODO Auto-generated catch block
            e.printStackTrace();
            problems = new IMarker[0];
        }
        return problems;
    }

    /**
     * Calculates the offset in a particular line
     * @param line
     * @param offset
     * @return
     */
    public static int getRealOffset(String line, int offset)
    {
        if (line.indexOf("\t") != -1)
        {
            /*
             TODO this is ugly.. the users should not use tabs
             
              
             
            // TODO handle this different, read from the editor settings
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
        }

        return Math.min(offset, line.length());

    }

    /**
     * Opens the TLA+ Editor and goes to the marker
     * @param problem
     */
    public static void gotoMarker(IMarker problem)
    {
        IEditorPart part = UIHelper.openEditor(OpenSpecHandler.TLA_EDITOR, new FileEditorInput((IFile) problem
                .getResource()));
        IGotoMarker gotoMarker = null;
        if (part instanceof IGotoMarker)
        {
            gotoMarker = (IGotoMarker) part;
        } else
        {
            gotoMarker = (IGotoMarker) part.getAdapter(IGotoMarker.class);
        }
        if (gotoMarker != null)
        {
            gotoMarker.gotoMarker(problem);
        }
    }

}
