package org.lamport.tla.toolbox.util;

import java.util.Iterator;
import java.util.List;

import org.eclipse.core.resources.IMarker;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.CoreException;
import org.lamport.tla.toolbox.Activator;
import org.lamport.tla.toolbox.spec.Spec;
import org.lamport.tla.toolbox.spec.parser.problem.Problem;

/**
 * Takes care of problem display
 * @author zambrovski
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
     */
    public static void installProblemMarkers(IResource resource, Problem problem)
    {

        IMarker marker;
        try
        {
            marker = resource.createMarker(TOOLBOX_MARKERS_PROBLEM_MARKER_ID);
            // Once we have a marker object, we can set its attributes
            marker.setAttribute(IMarker.SEVERITY, AdapterFactory.getMarkerSeverityFromProblem(problem));
            marker.setAttribute(IMarker.MESSAGE, problem.message);
            marker.setAttribute(IMarker.LINE_NUMBER, problem.location.beginLine);
            if (problem.location.beginLine == problem.location.endLine) 
            {
                marker.setAttribute(IMarker.CHAR_START, problem.location.beginColumn);
                marker.setAttribute(IMarker.CHAR_START, problem.location.beginColumn);
            } else {
                // TODO react in some smart way ... create multiple markers? 
            }
            marker.setAttribute("toolbox.location.modulename", problem.location.moduleName);
            marker.setAttribute("toolbox.location.beginline", problem.location.beginLine);
            marker.setAttribute("toolbox.location.endline", problem.location.endLine);
            marker.setAttribute("toolbox.location.begincolumn", problem.location.beginColumn);
            marker.setAttribute("toolbox.location.endcolumn", problem.location.endColumn);

        } catch (CoreException e)
        {
            // TODO Auto-generated catch block
            e.printStackTrace();
        }
    }

    /**
     * Delete all markers from this resource and all child resources
     * @param resource resource containing markers
     */
    public static void removeProblemMarkers(IResource resource)
    {
        IMarker[] problems = null;
        int depth = IResource.DEPTH_INFINITE;
        try
        {
            problems = resource.findMarkers(IMarker.PROBLEM, true, depth);
            for (int i = 0; i < problems.length; i++)
            {
                problems[i].delete();
            }
        } catch (CoreException e)
        {
            // something went wrong
        }
    }
    
    /**
     * Updates problem information for spec currently loaded by the spec manger
     */
    public static void updateProblemInformation()
    {
        updateProblemInformation(Activator.getSpecManager().getSpecLoaded());
    }
    
    /**
     * Updates problem information for given spec
     * @param spec - the spec, to update information on 
     */
    public static void updateProblemInformation(Spec spec)
    {
        if (spec != null) 
        {
            // delete the problems from current spec, if any
            TLAMarkerHelper.removeProblemMarkers(spec.getProject());
            
            
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
                    installProblemMarkers(spec.getModule(moduleName), problem);
                } else {
                    // or on spec itself
                    installProblemMarkers(spec.getProject(), problem);
                }
            }
        }
    }

}
