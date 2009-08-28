package org.lamport.tla.toolbox.tool.tlc.ui.util;

import java.util.Enumeration;
import java.util.HashSet;
import java.util.Hashtable;

import org.lamport.tla.toolbox.tool.ToolboxHandle;

import tla2sany.modanalyzer.SpecObj;
import tla2sany.semantic.Context;
import tla2sany.semantic.ExternalModuleTable;
import tla2sany.semantic.ModuleNode;
import util.UniqueString;

/**
 * A helper for resolution of objects related to the parsed specification
 * This class provides utility method for semantical checks in the forms
 * in contrast to pure syntax checks based on the pattern analysis of the input.
 * @author Simon Zambrovski
 * @version $Id$
 */
public class SemanticHelper
{

    /**
     * A constant indicating that the value is a keyword
     */
    public static final String KEYWORD = "KEYWORD";
    /**
     * Constant indicating the origin of a built-in op
     */
    public static final String TLA_BUILTIN = "--TLA+ BUILTINS--";

    private Hashtable pageStorage;
    private Context specContext;
    private HashSet keywords = ITLAReserveredWords.ALL_WORDS_SET;

    /**
     * Constructs a helper instance
     */
    public SemanticHelper()
    {
        pageStorage = new Hashtable();
        resetSpecNames();
    }

    /**
     * Reset all names used in the model
     */
    public void resetModelNames()
    {
        pageStorage = new Hashtable();
    }

    /**
     * Resets the names used in the model defined on the certain page
     * @param pageKey the key representing the page 
     * <br><br>
     * This method should be called on model re-validation
     */
    public void resetModelNames(Object pageKey)
    {
        if (pageKey != null)
        {
            pageStorage.put(pageKey, new Hashtable());
        }
    }

    /**
     * Resets the names used in the spec
     * <br><br>
     * This method should be called on spec re-parse
     */
    public void resetSpecNames()
    {
        specContext = getNewContext();
    }

    /**
     * Performs a name lookup
     * @return a status if the name is already used in the model or in the spec
     */
    protected boolean isNameUsedOnPage(String name, Object pageKey)
    {
        Hashtable pageNames = (Hashtable) pageStorage.get(pageKey);
        if (pageNames != null)
        {
            return pageNames.containsKey(name);
        } else
        {
            return false;
        }
    }

    /**
     * Performs a name lookup
     * @return a status if the name is already used in the model or in the spec
     */
    public boolean isNameUsed(String name)
    {
        // check the model
        Enumeration pages = pageStorage.keys();
        while (pages.hasMoreElements())
        {
            if (isNameUsedOnPage(name, pages.nextElement()))
            {
                return true;
            }
        }
        // finally check the reserved words and the spec
        return keywords.contains(name) || specContext.occurSymbol(UniqueString.uniqueStringOf(name));
    }

    /**
     * Get the hint where the field is used, or <code>null</code> if nowhere
     * <br><br><b>Note:</b> If the name is used on multiple pages, the method will return the first occurrence.
     * Thus, no assumption should be made about which page is the first. Just make sure to check 
     * {@link SemanticHelper#isNameUsed(String)} before putting a new name.
     *  
     *  
     * @param name name to check
     * @return either a string or a symbol 
     * the string is either {@link SemanticHelper#KEYWORD} or the description of the field the name is already used in 
     */
    public Object getUsedHint(String name)
    {
        // check the descriptions on all pages
        Enumeration pages = pageStorage.keys();
        while (pages.hasMoreElements())
        {
            Hashtable pageNames = (Hashtable) pageStorage.get(pages.nextElement());
            String description = (String) pageNames.get(name);
            if (description != null)
            {
                return description;
            }
        }
        // check keywords
        if (keywords.contains(name))
        {
            return KEYWORD;
        }
        // check the spec module
        Object specUsed = specContext.getSymbol(UniqueString.uniqueStringOf(name));
        return specUsed;
    }

    /**
     * Adds the name to the collection
     * @param name the name to add
     * @param pageKey page key indicating on what page the value is used
     * @param usageDescription the description of the field where the name is used, used for later lookups  
     */
    public void addName(String name, Object pageKey, String usageDescription)
    {
        Hashtable pageNames = (Hashtable) pageStorage.get(pageKey);
        if (pageNames == null)
        {
            pageNames = new Hashtable();
            pageStorage.put(pageKey, pageNames);
        }
        pageNames.put(name, usageDescription);
    }

    /**
     * A convenience method for access to the root module node
     * @return a module or null, if spec not parsed
     */
    public static ModuleNode getRootModuleNode()
    {
        SpecObj specObj = ToolboxHandle.getSpecObj();
        if (specObj != null)
        {
            return specObj.getExternalModuleTable().getRootModule();
        }
        return null;
    }

    /**
     * Convenience method for constructing a new context, extending the one used in the current spec
     * @return a new context
     */
    public static Context getNewContext()
    {
        SpecObj specObj = ToolboxHandle.getSpecObj();
        Context moduleContext;
        if (specObj != null)
        {
            ExternalModuleTable externalModuleTable = specObj.getExternalModuleTable();
            // duplicate
            moduleContext = externalModuleTable.getRootModule().getContext().duplicate(externalModuleTable);
        } else
        {
            // if no specification object, at least test the operators
            moduleContext = Context.getGlobalContext();
        }
        return moduleContext;
    }
}
