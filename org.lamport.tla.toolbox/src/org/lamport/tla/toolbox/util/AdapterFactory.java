package org.lamport.tla.toolbox.util;

import java.util.List;
import java.util.Vector;

import org.eclipse.core.resources.IMarker;
import org.eclipse.core.runtime.IAdapterFactory;
import org.eclipse.swt.SWT;
import org.eclipse.ui.model.IWorkbenchAdapter;
import org.eclipse.ui.model.WorkbenchAdapter;
import org.lamport.tla.toolbox.spec.Module;
import org.lamport.tla.toolbox.spec.Spec;
import org.lamport.tla.toolbox.spec.parser.IParseConstants;

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
            }
        }
        return null;
    }

    /**
     * Retrieves formated problem location
     * @param moduleName
     * @param coordinates
     * @return
     */
    public static String getFormattedLocation(int[] coordinates, String moduleName)
    {
        return "from line " + coordinates[0] + ", column " + coordinates[1] + " to line " + coordinates[2]
                + ", column " + coordinates[3] + " of module " + moduleName;
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
     * @param status the integer representing the parse status
     * @return human readable string
     */
    public static String getStatusAsString(int status)
    {
        switch (status) {
        case IParseConstants.COULD_NOT_FIND_MODULE:
            return " module not found ";
        case IParseConstants.PARSED:
            return " parsed ";
        case IParseConstants.SEMANTIC_WARNING:
            return " warning ";
        case IParseConstants.SEMANTIC_ERROR:
        case IParseConstants.SYNTAX_ERROR:
        case IParseConstants.UNKNOWN_ERROR:
            return " error ";
        case IParseConstants.UNPARSED:
            return " unparsed ";
        default:
            return " unknown " + status;
        }
    }

    /**
     * Converts a parse status of the spec to a human-readable string
     * @param spec specification holding the parse status
     * @return human readable string
     */
    public static String getStatusAsString(Spec spec)
    {
        if (spec != null)
        {
            return getStatusAsString(spec.getStatus());
        } else
        {
            return " no spec ";
        }
    }

    /**
     * Converts parse status to a background color for display in the status contribution item
     * @param spec specification holding the parse status
     * @return SWT color constant
     */
    public static int getStatusAsSWTBGColor(Spec spec)
    {
        if (spec != null)
        {
            switch (spec.getStatus()) {
            case IParseConstants.PARSED:
                return SWT.COLOR_DARK_GREEN;
            case IParseConstants.COULD_NOT_FIND_MODULE:
            case IParseConstants.SEMANTIC_WARNING:
            case IParseConstants.SEMANTIC_ERROR:
            case IParseConstants.SYNTAX_ERROR:
            case IParseConstants.UNKNOWN_ERROR:
                return SWT.COLOR_YELLOW;
            case IParseConstants.UNPARSED:
                return SWT.COLOR_DARK_RED;
            case IParseConstants.UNKNOWN:
            default:
                return SWT.COLOR_GRAY;
            }
        } else
        {
            return SWT.COLOR_GRAY;
        }
    }

    /**
     * Converts parse status to a foreground color for display in the status contribution item
     * @param spec specification holding the parse status
     * @return SWT color constant
     */
    public static int getStatusAsSWTFGColor(Spec spec)
    {
        if (spec != null)
        {
            switch (spec.getStatus()) {
            case IParseConstants.PARSED:
                return SWT.COLOR_BLACK;
            case IParseConstants.COULD_NOT_FIND_MODULE:
            case IParseConstants.SEMANTIC_WARNING:
            case IParseConstants.SEMANTIC_ERROR:
            case IParseConstants.SYNTAX_ERROR:
            case IParseConstants.UNKNOWN_ERROR:
                return SWT.COLOR_BLACK;
            case IParseConstants.UNPARSED:
                return SWT.COLOR_WHITE;
            case IParseConstants.UNKNOWN:
            default:
                return SWT.COLOR_BLACK;
            }
        } else
        {
            return SWT.COLOR_BLACK;
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
        case IParseConstants.SEMANTIC_WARNING:
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
        } else
        {
            return false;
        }
    }

    /**
     * Retrieves the text representation of the TLA+ parse problem
     * @param problem
     * @return
     */
    public static String getSeverityAsText(int severity)
    {
        switch (severity) {
        case IMarker.SEVERITY_ERROR:
            return "Error";
        case IMarker.SEVERITY_WARNING:
            return "Warning";
        case IMarker.SEVERITY_INFO:
        default:
            return "Info";
        }

    }

    /**
     * Adapts a list of modules including all dependent modules and the resource itself to the form, accepted by the dependency storage
     * @param name
     * @param userModules
     * @return
     * TODO improve the storage
     */
    public static List adaptModules(String name, Vector userModules)
    {
        Vector dependents = new Vector(userModules.size() - 1);
        for (int i = 0; i < userModules.size(); i++)
        {
            Module module = (Module) userModules.get(i);
            if (!module.getFile().getName().equals(name))
            {
                dependents.add(module.getFile().getName());
            }
        }

        return dependents;
    }

}
