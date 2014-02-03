package org.lamport.tla.toolbox.util;

import java.util.List;
import java.util.Vector;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IMarker;
import org.eclipse.core.runtime.IAdapterFactory;
import org.eclipse.jface.text.BadLocationException;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.IRegion;
import org.eclipse.jface.text.Region;
import org.eclipse.swt.SWT;
import org.eclipse.ui.model.IWorkbenchAdapter;
import org.eclipse.ui.model.WorkbenchAdapter;
import org.lamport.tla.toolbox.Activator;
import org.lamport.tla.toolbox.spec.Module;
import org.lamport.tla.toolbox.spec.Spec;
import org.lamport.tla.toolbox.spec.parser.IParseConstants;

import pcal.TLAtoPCalMapping;
import tla2sany.st.Location;

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
     * Converts four-int {@link Location} that is 1-based to a two int {@link IRegion} that is
     * 0-based.
     * 
     * TODO: unit test!
     * @param document
     * @param location
     * @return
     * @throws BadLocationException 
     */
    public static IRegion locationToRegion(IDocument document, Location location) throws BadLocationException
    {
        /* 
         * The coordinates returned by location are 1-based and the coordinates
         * for a region in a document should be 0-based to be consistent with Positions
         * in documents. Therefore, we subtract 1 from each location coordinate.
         */
        int offset = document.getLineOffset(location.beginLine() - 1) + location.beginColumn() - 1;
        /*
         * If location describes a two-character sequence beginning at column x, then it would
         * have location.endColumn() = x+1. This means that when computing the length, we add 1 to
         * the offset of the second point described by location. In other words, the offset of the
         * second point described by location is:
         * 
         * document.getLineOffset(location.endLine() - 1) + location.endColumn()-1
         * 
         * So the length is:
         * 
         * (document.getLineOffset(location.endLine() - 1) + location.endColumn()-1)+1 - offset
         * 
         * which equals:
         * 
         * document.getLineOffset(location.endLine() - 1) + location.endColumn() - offset
         */
        int length = document.getLineOffset(location.endLine() - 1) + location.endColumn() - offset;
        return new Region(offset, length);
    }

    /**
     * Converts four-int {@link Location} that is 1-based to a two int {@link IRegion} that is
     * 0-based. Different than {@link #locationToRegion(IDocument, Location)} because
     * it does not need a document as an argument but instead creates one.
     * 
     * Returns null if the location cannot be converted to a region for any reason.
     * Possible reasons are that the location points to a non-existent module or a
     * location in a module that does not exist.
     * 
     * WARNING: A module named "foo" is considered not to exist if the file containing
     * it is named "Foo.tla"--that is, if the file name and the module name don't
     * agree exactly.  This is because org.eclipse.core.internal.resources.File.exists()
     * returns false if the names disagree in the case of some letter(s).  Working
     * around this bug/feature is not trivial because it requires getting hold of
     * those two names, and this doesn't seem to be easy to do here.
     * (Added by LL on 16 Jan 2014).
     * 
     * @param location
     * @return
     */
    public static IRegion locationToRegion(Location location)
    {

        IFile module = (IFile) ResourceHelper.getResourceByModuleName(location.source());

        if (module != null && module instanceof IFile && module.exists())
        {
            try
            {
                return locationToRegion(ResourceHelper.getDocFromFile(module), location);
            } catch (BadLocationException e)
            {
                Activator.getDefault().logError("Error converting location to region for location " + location, e);
            }
        }

        return null;

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
            return " error ";
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
                return SWT.COLOR_GREEN;
            case IParseConstants.COULD_NOT_FIND_MODULE:
            case IParseConstants.SEMANTIC_WARNING:
            case IParseConstants.SEMANTIC_ERROR:
            case IParseConstants.SYNTAX_ERROR:
            case IParseConstants.UNKNOWN_ERROR:
                return SWT.COLOR_DARK_RED;
            case IParseConstants.UNPARSED:
                return SWT.COLOR_YELLOW;
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
                return SWT.COLOR_WHITE;
            case IParseConstants.UNPARSED:
                return SWT.COLOR_BLACK;
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
     * Resolves the origin of the marker 
     * @param markerType
     * @return
     */
    public static String getMarkerTypeAsText(String markerType)
    {
        if (markerType == null || "".equals(markerType))
        {
            return "";
        }
        if (TLAMarkerHelper.TOOLBOX_MARKERS_ALL_MARKER_ID.equals(markerType))
        {
            return "TLA+ Toolbox";
        } else if (TLAMarkerHelper.TOOLBOX_MARKERS_TRANSLATOR_MARKER_ID.equals(markerType))
        {
            return "PCal Translator";
        } else if (TLAMarkerHelper.TOOLBOX_MARKERS_TLAPARSER_MARKER_ID.equals(markerType))
        {
            return "TLA+ Parser";
        } else
        {
            return "";
        }
    }

    /**
     * Adapts a list of modules including all dependent modules and the
     * module itself to the form, accepted by the dependency storage.<br>
     *  
     * As of the current implementation, this means that its arguments
     * are a module name and a list of modules; it returns the list of
     * names of those modules, minus the first argument if it is the
     * name of one of those modules.<br>
     * 
     * TODO improve the storage
     *  
     * @param name A name of the module that has been parsed
     * @param userModules a list of {@link Module} objects representing the depending modules, which eventually include
     *                    one module representing the parsed module itself
     * @return a list of module names (Strings) containing all modules from the <code>userModule</code> argument, 
     *         excluding the module specified by the <code>name</code> argument    
     */
    public static List<String> adaptModules(String name, List<Module> userModules)
    {
        Vector<String> dependents = new Vector<String>(userModules.size());
        // iterate over all modules
        for (int i = 0; i < userModules.size(); i++)
        {
            Module module = userModules.get(i);
            if (!module.getFile().getName().equals(name))
            {
                // add the module name iff the name is not matching the one provided in the name argument
                dependents.add(module.getFile().getName());
            }
        }
        return dependents;
    }
    
    public static pcal.Region jumptToPCal(TLAtoPCalMapping mapping, Location location, IDocument document) throws BadLocationException {
        /*
         * Get the best guess of the line number in the
         * current contents of the editor that corresponds to what was line
         * mapping.tlaStartLine when the algorithm was translated. 
         * It is computed by assuming that neither the algorithm nor the translation
         * have changed, but they both may have been moved down by the same 
         * number delta of lines (possibly negative).  A more sophisticated approach 
         * using fingerprints of lines could be used, requiring that the necessary 
         * fingerprint information be put in TLAtoPCalMapping.
         */
        int beginAlgorithmLine = AdapterFactory.GetLineOfPCalAlgorithm(document);
        if (beginAlgorithmLine == -1) {
        	throw new BadLocationException("The algorithm is no longer in the module.");
        }

		// Translate editor location to pcal.Region
        final pcal.Region tlaRegion = location.toRegion();
		
        // Do actual mapping
        return mapping.mapTLAtoPCalRegion(tlaRegion,
				beginAlgorithmLine);
    }
    
    /**
     * Returns the line number (in Java coordinates/zero based) of the line containing the first
     * "--algorithm" or "--fair algorithm" token(s) that begin(s) a PlusCal algorithm. 
     * Returns -1 if there is none.
     * 
     * @param document
     * @return
     */
    public static int GetLineOfPCalAlgorithm(IDocument document) {
		try {
			final String moduleAsString = document.get();
			return LocationToLine(document,
					TLAtoPCalMapping.GetLineOfPCalAlgorithm(moduleAsString));
		} catch (BadLocationException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		return -1;
    }
    
    public static int GetLineOfPCalAlgorithm(final IFile module) {
		return GetLineOfPCalAlgorithm(ResourceHelper.getDocFromFile(module));
    }

    /** 
     * If location = -1, then it returns -1.  Else it returns the number of the line with
     * this location.
     * @param document
     * @param location
     * @return
     * @throws BadLocationException
     */
    private static int LocationToLine(IDocument document, int location) throws BadLocationException {
        if (location == -1) {
            return -1;
        } else {
            return document.getLineOfOffset(location);
        }
    }

}
