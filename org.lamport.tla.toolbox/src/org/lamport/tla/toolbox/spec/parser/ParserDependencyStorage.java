package org.lamport.tla.toolbox.spec.parser;

import java.util.List;
import java.util.Vector;

/**
 * This class is responsible for the storage of the dependency information between the modules.
 * It uses the DoubleHashedTable class to store the information in a rather obscure way.  My
 * guess is that Simon originally intended for this to keep the two directed graphs with "imports" and
 * "is imported by" edges.  However, a little experimentation suggests that the implementation
 * degenerated into two trivial graphs saying only that the root module imports every other module,
 * and every other module is imported by the root module.
 * 
 * @author Simon Zambrovski
 * @version $Id$
 */
public class ParserDependencyStorage
{
    
    private DoubleHashedTable moduleStore = null;

    public ParserDependencyStorage()
    {
        initialize();
    }

    /**
     * Initializes the 
     */
    public void initialize()
    {
        moduleStore = new DoubleHashedTable(101);
    }

    /**
     * Looks up a module
     * @param moduleName
     * @return true
     */
    public boolean hasModule(String moduleName) 
    {
        return moduleStore.containsKey(moduleName) || moduleStore.containsValue(moduleName); 
    }
    
    /**
     * Saves the new module dependency list, returns the old
     * list. 
     *  
     * @param parsedModule the module on which the parse has been invoked 
     * @param listOfParsedModules a list of modules, found during the parse operation, excluding the standard modules
     */
    public List put(String parsedModule, List listOfParsedModules)
    {
        if (parsedModule == null || listOfParsedModules == null)
        {
            return new Vector(0);
        }

        // cleanup the entire information that has been stored about this module
        List oldValues = parseFailed(parsedModule);

        // store the dependencies
        moduleStore.put(parsedModule, listOfParsedModules);
        
        // return the old values
        return oldValues;
        
    }

    /**
     * Parse operation failed on the specified parse module 
     * @param parseModule the module on which the parse has been invoked 
     */
    public List parseFailed(String parseModule)
    {
        // remove the key
        return moduleStore.removeKey(parseModule);
    }

    /**
     * The following documentation by Simon seems to be almost totally incorrect.
     * A little experimentation suggests that this returns a list containing only the root module
     * if changedModule is not the root Module, and an empty list otherwise.
     * 
     * Retrieves the list of modules, that should be re-parsed, because a module has changed
     * <br><b>Note:</b> The modules on the list returned EXTEND the changed module.
     * 
     *  
     * @param changedModule the name of the changed module + ".tla"
     * @return list of modules to re-parse
     */
    public List getListOfModulesToReparse(String changedModule)
    {
        Vector dependantModules = (Vector) moduleStore.getKeys(changedModule);
        if (dependantModules == null)
        {
            dependantModules = new Vector();
        }
        return dependantModules;
    }
    
    /**
     * The following documentation by Simon seems to be almost totally incorrect.
     * A little experimentation suggests that this returns the the list of all
     * imported modules if changedModule is the root module, and an empty list otherwise.

     * Retrieves the list of modules that are imported (directly
     * or indirectly) by current module
     * @param rootModule, name of the module + ".tla"
     * @return list of modules it depends (EXTEND) on
     */
    public List getListOfExtendedModules(String rootModule)
    {
        Vector dependantModules = null;
        if (rootModule == null) 
        {
            dependantModules = new Vector();
            return dependantModules;
        }
        dependantModules = (Vector) moduleStore.getValues(rootModule);
        if (dependantModules == null)
        {
            dependantModules = new Vector();
        }
        return dependantModules;
    }
}
