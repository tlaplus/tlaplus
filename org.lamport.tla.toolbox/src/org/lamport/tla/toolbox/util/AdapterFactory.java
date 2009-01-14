package org.lamport.tla.toolbox.util;

import java.util.List;

import org.eclipse.core.resources.IMarker;
import org.eclipse.core.runtime.IAdapterFactory;
import org.eclipse.swt.SWT;
import org.eclipse.ui.model.IWorkbenchAdapter;
import org.eclipse.ui.model.WorkbenchAdapter;
import org.lamport.tla.toolbox.spec.Spec;
import org.lamport.tla.toolbox.spec.parser.IParseConstants;
import org.lamport.tla.toolbox.spec.parser.problem.Problem;
import org.lamport.tla.toolbox.spec.parser.problem.ProblemContainer;

/**
 * A toolkit with adapter methods
 * @author Simon Zambrovski
 * @version $Id$
 */
public class AdapterFactory implements IAdapterFactory
{
    // list of supported targets
    private static final Class[] CLASSES = new Class[] { IWorkbenchAdapter.class };

    /*
     * (non-Javadoc)
     * @see org.eclipse.core.runtime.IAdapterFactory#getAdapterList()
     */
    public Class[] getAdapterList()
    {
        return CLASSES;
    }

    /*
     * (non-Javadoc)
     * @see org.eclipse.core.runtime.IAdapterFactory#getAdapter(java.lang.Object, java.lang.Class)
     */
    public Object getAdapter(Object adaptableObject, Class adapterType)
    {
        if (adapterType == IWorkbenchAdapter.class)
        {
            if (adaptableObject instanceof Spec)
            {
                return new SpecWorkbenchAdapter();
            } else if (adaptableObject instanceof ProblemContainer)
            {
                return new ProblemContainerAdapter();
            } else if (adaptableObject instanceof Problem)
            {
                return new ProblemAdapter();
            }
        }
        return null;
    }

    /**
     * Adapts the parse problem for workbench<br>
     * Using this adapter the spec can be represented in workbench containers
     *
     * @author zambrovski
     */
    class ProblemAdapter extends WorkbenchAdapter
    {

        /*
         * (non-Javadoc)
         * @see org.eclipse.ui.model.WorkbenchAdapter#getLabel(java.lang.Object)
         */
        public String getLabel(Object object)
        {
            Problem problem = (Problem) object;
            return problem.message;
        }
    }
    
    /**
     * Adapts the parse problem container for workbench<br>
     * Using this adapter the spec can be represented in workbench containers
     * @author zambrovski
     */
    class ProblemContainerAdapter extends WorkbenchAdapter
    {

        /*
         * (non-Javadoc)
         * @see org.eclipse.ui.model.IWorkbenchAdapter#getChildren(java.lang.Object)
         */
        public Object[] getChildren(Object o)
        {
            ProblemContainer container = (ProblemContainer) o;
            List problems = container.getProblems(Problem.ABORT | Problem.ERROR | Problem.WARNING);
            return problems.toArray(new Problem[problems.size()]);
        }

        /*
         * (non-Javadoc)
         * @see org.eclipse.ui.model.IWorkbenchAdapter#getLabel(java.lang.Object)
         */
        public String getLabel(Object o)
        {
            ProblemContainer container = (ProblemContainer) o;
            if (container.isEmpty())
            {
                return "No Problems";
            } else
            {
                return "Problems (" + container.getNumberOfProblems(Problem.ABORT) + " Aborts/"
                        + container.getNumberOfProblems(Problem.ERROR) + " Errors/"
                        + container.getNumberOfProblems(Problem.WARNING) + " Warnings)";
            }
        }

    }

    /**
     * Adapts the spec object to the workbench<br>
     * Using this adapter the spec can be represented in workbench containers
     * 
     * @author zambrovski
     */
    class SpecWorkbenchAdapter extends WorkbenchAdapter
    {

        /*
         * (non-Javadoc)
         * @see org.eclipse.ui.model.WorkbenchAdapter#getLabel(java.lang.Object)
         */
        public String getLabel(Object object)
        {
            Spec spec = (Spec) object;
            return (spec == null) ? "" : spec.getName();
        }

    }
    
    /**
     * Converts a parse status to a human-readable string
     * @param spec specification holding the parse status
     * @return human readable string
     */
    public static String getStatusAsString(Spec spec)
    {
        if (spec != null)
        {
            switch (spec.getStatus()) {
                case IParseConstants.COULD_NOT_FIND_MODULE:
                    return " module not found ";
                case IParseConstants.PARSED:
                    return " parsed ";
                case IParseConstants.SEMANTIC_ERROR:
                case IParseConstants.SYNTAX_ERROR:
                case IParseConstants.UNKNOWN_ERROR:
                    return " error ";
                case IParseConstants.UNPARSED:
                    return " unparsed ";
                case IParseConstants.MODIFIED:
                    return " changed ";
                    
                default:
                    return " unknown ";
            }
        } else {
            return " unknown ";
        }
    }
    
    /**
     * Converts parse status to a color for display in the status contribution item
     * @param spec specification holding the parse status
     * @return SWT color constant
     */
    public static int getStatusAsSWTColor(Spec spec)
    {
        if (spec != null)
        {
            switch (spec.getStatus()) {
                case IParseConstants.PARSED:
                    return SWT.COLOR_DARK_GREEN;
                case IParseConstants.COULD_NOT_FIND_MODULE:
                case IParseConstants.SEMANTIC_ERROR:
                case IParseConstants.SYNTAX_ERROR:
                case IParseConstants.UNKNOWN_ERROR:
                    return SWT.COLOR_YELLOW;
                case IParseConstants.UNPARSED:
                    return SWT.COLOR_DARK_RED;
                case IParseConstants.MODIFIED:
                    return SWT.COLOR_DARK_GRAY;
                case IParseConstants.UNKNOWN:
                default:
                    return SWT.COLOR_GRAY;
            }
        } else {
            return SWT.COLOR_GRAY;
        }
    } 

    /**
     * Decides, if a parse status is a problem
     * @param status status to decide on
     * @return true if status if one of the {@link IParseConstants#COULD_NOT_FIND_MODULE}
     * {@link IParseConstants#SEMANTIC_ERROR}, {@link IParseConstants#SYNTAX_ERROR} or {@link IParseConstants#UNKNOWN_ERROR}
     */
    public static boolean isProblemStatus(int parseStatus)
    {
        switch (parseStatus) {
            // error cases
            case IParseConstants.COULD_NOT_FIND_MODULE:
            case IParseConstants.SEMANTIC_ERROR:
            case IParseConstants.SYNTAX_ERROR:
            case IParseConstants.UNKNOWN_ERROR:
                return true;
                // non-error cases
            case IParseConstants.UNPARSED:
            case IParseConstants.PARSED:
            case IParseConstants.UNKNOWN:
                return false;
            default:
                return false;
        }
        
    }
    
    /**
     * Checks if the spec holding the parse status has problems
     * @param spec specification holding the parse status
     * @return if spec is not null delegates on {@link AdapterFactory#isProblemStatus(int)} otherwise false
     */
    public static boolean hasProblemStatus(Spec spec)
    {
        if (spec != null)
        {
            return isProblemStatus(spec.getStatus());
        } else {
            return false;
        }
    }

    
    
    /**
     * Translates Problem Severity to Eclipse Marker severity
     * @param problem a problem containing the error severity
     * @return one of the {@link IMarker} constants
     */
    public static int getMarkerSeverityFromProblem(Problem problem)
    {
        switch (problem.type) 
        {
            case Problem.ERROR:
                return IMarker.SEVERITY_ERROR;
            case Problem.ABORT:
                return IMarker.SEVERITY_ERROR;
            case Problem.WARNING:
                return IMarker.SEVERITY_WARNING;
            default:
                return IMarker.SEVERITY_INFO;
        }
    }
    
    

    
}
