// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
package tla2sany.modanalyzer;

import java.util.Enumeration;
import java.util.HashSet;
import java.util.Hashtable;

import tla2sany.semantic.AbortException;
import tla2sany.semantic.Errors;
import tla2sany.semantic.ExternalModuleTable;
import tla2sany.st.TreeNode;
import tla2sany.utilities.Vector;
import util.FileUtil;
import util.FilenameToStream;
import util.NamedInputStream;
import util.ToolIO;

/**
 * This class holds the results from running the SANY on a single TLA+
 * specification.
 * @version: $Id$
 */
public class SpecObj
{

    String primaryFileName;
    // The raw file name for the root (top) module, unprocessed by adding
    // ".tla" or by prepending the full file system path to it)

    ExternalModuleTable externalModuleTable = new ExternalModuleTable();
    // This is the one ExternalModuleTable for the entire specification;
    // it includes ModuleNode's for the root module, and for all modules
    // that it depends on directly or indirectly by EXTENDS or INSTANCE

    public Vector semanticAnalysisVector = new Vector();
    // Stack of units parsed, in the order in which semantic analysis
    // must be done, i.e. if MODULE A references B, A is lower
    // on the stack. The same module name can occur multiple times.

    public Hashtable parseUnitContext = new Hashtable();
    // Holds all known ParseUnit objects, i.e external, top-level
    // modules that have so far been encountered, keyed by module
    // (parseUnit) string name

    private ModuleRelationships moduleRelationshipsSpec = new ModuleRelationships();
    // Maps ModulePointers to ModuleRelatives objects for all modules
    // in the specification, including all inner modules and all top-level
    // external modules.

    /*
     * used to translate module names to file names              
     *                                                                      
     * This field was made public by LL on 8 May 2008 in an effort to       
     * track down the full file names of included modules.  It seems safer  
     * to get the NameToFileIStream object from here in case at some later  
     * time we add a way to allow the user to specify how the parser        
     * should find a module's file from its name.  This would lead to the   
     * ability to have different NameToFileIStream objects, so it's better  
     * for a tool to do file lookup using the actual NameToFileIStream      
     * object that the parser uses.                                         
     *
     * SZA: Since there is no references to this public field, it is
     * changed to private again.
     */
    // SZ 23.02.2009: renamed according to the purpose
    private FilenameToStream resolver = null;


    ParseUnit rootParseUnit = null;
    // The ParseUnit object for the first (i.e. "root") file, roughly
    // the file that is named in the command line; null until the root
    // file is parsed

    ModulePointer rootModule = null;
    // The top level module of the rootParseUnit;
    // null until rootParseUnit is parsed

    String rootModuleName;
    // The String name of rootModule, unknown until rootParseUnit is parsed,
    // although it is supposed to be closely related to the file name

    public Errors initErrors = new Errors();
    // The Errors object for reporting errors that happen at initialization
    // time.

    public Errors parseErrors = new Errors();
    // The Errors object for reporting errors that occur during parsing,
    // including the retrieval of files (ParseUnits) for extention and
    // instantiation or the root and their extentions and instantiations, etc.

    private Errors globalContextErrors = new Errors();
    // The Errors object for reporting errors in creating the global
    // context from the file that stores it.

    public Errors semanticErrors = new Errors();
    // The Errors object for reporting errors discovered during semantic
    // analysis, including level checking.

    public int errorLevel = 0;

    /**
     * Default constructor of the SpecObj with a given primary filename and the default 
     * NameToFileIStream for its resolution 
     * @param pfn primary filename of the specification
     * @deprecated please use the {@link SpecObj#SpecObj(String, FilenameToStream)} 
     * with <code>null</code> as a second argument
     */
    public SpecObj(String pfn)
    {
        this(pfn, null);
    }

    /**
     * Constructs a SpecObj for the given filename using a specified filename resolver
     * @param pfn primary filename of the specification
     * @param ntfis string to named input stream resolver, if <code>null</code>, 
     * the default from {@link ToolIO#getDefaultResolver()} is used
     */
    public SpecObj(String pfn, FilenameToStream ntfis)
    {
        if (ntfis == null) 
        {
            ntfis = ToolIO.getDefaultResolver(); 
        }
        this.primaryFileName = pfn;
        this.resolver = ntfis;
    }

    /**
     * Any integer other than 0 returned from this method indicates a
     * fatal error while processing the TLA+ spec.  No further use
     * should be made of this object except by the maintainer.
     */
    public final int getErrorLevel()
    {
        return errorLevel;
    }

    /**
     * Returns the name of the top-level module as passed to the method
     * Specification.frontEndMain().
     */
    public final String getName()
    {
        return rootModuleName;
    }

    public final void setName(String name)
    {
        rootModuleName = name;
    }

    /**
     * Returns the raw file name of the top-level module as passed to
     * the method Specification.frontEndMain().
     */
    public final String getFileName()
    {
        return primaryFileName;
    }

    /**
     * Returns the ExternalModuleTable object that contains all of the
     * definitions for this Specification.  May be null or incomplete if
     * getErrorLevel() returns a nonzero number.
     */
    public final ExternalModuleTable getExternalModuleTable()
    {
        return externalModuleTable;
    }

    /**
     * Returns Errors object produced during initialization of the FrontEnd.
     * Should never be interesting.
     */
    public final Errors getInitErrors()
    {
        return initErrors;
    }

    /**
     * Returns Errors object containing errors found during parsing.
     */
    public final Errors getParseErrors()
    {
        return parseErrors;
    }

    /**
     * Returns Errors object containing errors found while parsing the
     * built-in operator and synonym tables.  Should never be interesting.
     * 
     * The above appears to be Simon's comment, and it is wrong.  Global
     * context errors include cases where two EXTENDed modules contain
     * conflicting definitions or declarations of the same operator.   These
     * errors probably used to get put here in Yuan's code.  They are not
     * being put there in Simon's rewriting.  As a result, they were getting
     * lost--in the sense of not being put anywhere where the Toolbox could
     * find them.  This was corrected by LL and Dan on 23 Oct 2009 by adding
     * a call of spec.setGlobalContextErrors to SANY.frontEndSemanticAnalysis.
     *  
     */
    public final Errors getGlobalContextErrors()
    {
        return globalContextErrors;
    }

    /**
     * Returns Errors object containing errors found during semantic
     * processing and level checking.
     */
    public final Errors getSemanticErrors()
    {
        return semanticErrors;
    }

    // Returns enumeration of the modules so far included in the spec.
    // As whoever wrote this documentation didn't think was worth mentioning,
    // it appears that the "modules" being returned are ModulePointer objects.
    public final Enumeration getModules()
    {
        return moduleRelationshipsSpec.getKeys();
    }

    // Returns the moduleRelationshipsSpec object
    final ModuleRelationships getModuleRelationships()
    {
        return moduleRelationshipsSpec;
    }

    // Prints the context of one ParseUnit
    public final void printParseUnitContext()
    {
        Enumeration enumerate = parseUnitContext.keys();

        ToolIO.out.println("parseUnitContext =");
        while (enumerate.hasMoreElements())
        {
            String key = (String) enumerate.nextElement();
            ToolIO.out.println("  " + key + "-->" + ((ParseUnit) parseUnitContext.get(key)).getName());
        }
    }

    // This method looks up a ParseUnit "name" in the parseUnitContext
    // table. If it is not found, then the corresponding file is looked
    // up in the file system and parsed, and a new ParseUnit is created
    // for it and an entry for it added to the parseUnitContext table.
    // The argument firstCall should be true iff this is the first call
    // to this method; it is used to determine that the name of the
    // module in the ParseUnit created is the name of the entire
    // SpecObj. Returns the ParseUnit found or created. Aborts if
    // neither happens.
    private final ParseUnit findOrCreateParsedUnit(String name, Errors errors, boolean firstCall) throws AbortException
    {
        ParseUnit parseUnit;

        // See if ParseUnit "name" is already in parseUnitContext table
        parseUnit = (ParseUnit) parseUnitContext.get(name);

        // if not, then we have to get it from the file system
        if (parseUnit == null)
        {
            // if module "name" is not already in parseUnitContext table

            // find a file derived from the name and create a
            // NamedInputStream for it if possible
            // SZ 23.02.2009: split the name resolution from the stream retrieval
            // NamedInputStream nis = this.ntfis.toNIStream(name);
            NamedInputStream nis = FileUtil.createNamedInputStream(name, this.resolver);

            if (nis != null)
            {
                // if a non-null NamedInputStream exists, create ParseUnit
                // from "nis", but don't parse it yet
                parseUnit = new ParseUnit(this, nis);

                // put "parseUnit" and its name in "parseUnitContext" table
                parseUnitContext.put(parseUnit.getName(), parseUnit);
            } else
            {
                // no such file exists---must be a missing file
                /*******************************************************************
                * At this point, nextExtenderOrInstancerModule is a ModulePointer  *
                * to the module that contains the EXTENDS or INSTANCES that        *
                * produces this error.  Hopefully, we can use this to attach a     *
                * location to the error message.                                   *
                *******************************************************************/
                errors.addAbort("Cannot find source file for module " + name +
                        ((nextExtenderOrInstancerModule == null) ? "" : " imported in module " + nextExtenderOrInstancerModule.getName()) + ".");
            }
        }

        // Actually parse the file named in "parseUnit" (or no-op if it
        // has already been parsed)
        parseUnit.parseFile(errors, firstCall);

        return parseUnit;
        // return a non-null "parseUnit" iff named module has been found,
        // either already parsed or in the file system
    }

    // Fill the Vector used to drive the semantic analysis of external
    // modules. The basic requirement is that if ParseUnit A extends or
    // instances ParseUnit B, then A must have a higher index in the
    // Vector than B.
    private void calculateDependencies(ParseUnit currentParseUnit)
    {
        Vector extendees = currentParseUnit.getExtendees();
        Vector instancees = currentParseUnit.getInstancees();

        // Make sure all extendees of currentModule are in the semanticAnalysisVector
        for (int i = 0; i < extendees.size(); i++)
        {
            calculateDependencies((ParseUnit) extendees.elementAt(i));
        }

        // And then make sure all instancees of currentModule are in the
        // semanticAnalysisVector
        for (int i = 0; i < instancees.size(); i++)
        {
            calculateDependencies((ParseUnit) instancees.elementAt(i));
        }

        // Then put self in the Vector, if not already there
        if (!semanticAnalysisVector.contains(currentParseUnit.getName()))
        {
            semanticAnalysisVector.addElement(currentParseUnit.getName());
        }
        return;
    }

    // Converts a Vector of ParseUnits to a string representing a
    // circular chain of references, for purposes of the error message
    // in nonCircularityBody method below.
    private String pathToString(Vector path)
    {
        String ret = "";
        for (int i = 0; i < path.size(); i++)
        {
            ret += ((ParseUnit) path.elementAt(i)).getFileName() + " --> ";
        }
        return ret + ((ParseUnit) path.elementAt(0)).getFileName();
    }

    // This method determines whether the there is any circularity
    // detectable this far among ParseUnits that involves the one named
    // parseUnitName. If there is, cause an abort; otherwise return.
    private void nonCircularityTest(ParseUnit parseUnit, Errors errors) throws AbortException
    {
        HashSet alreadyVisited = new HashSet();
        Vector circularPath = new Vector();

        circularPath.addElement(parseUnit);
        nonCircularityBody(parseUnit, parseUnit, errors, alreadyVisited, circularPath);
    }

    // Recursive depth-first search method to see if there is a circular
    // dependence from 'parseUnit' to 'parseUnit' through another
    // ParseUnit, candidate. If so, an abort message is posted on
    // errors, and the method aborts. The set alreadyVisited is
    // used to prevent searching paths through the same candidate
    // multiple times.
    private void nonCircularityBody(ParseUnit parseUnit, ParseUnit candidate, Errors errors, HashSet alreadyVisited,
            Vector circularPath) throws AbortException
    {
        // If we have already checked for circularities through this
        // parseUnit, just return
        if (alreadyVisited.contains(candidate))
            return;

        alreadyVisited.add(candidate);

        // Vector referencees holds ParseUnits either extended by or
        // instanced by "candidate"
        Vector referencees = candidate.getExtendees();
        referencees.appendNoRepeats(candidate.getInstancees());

        for (int i = 0; i < referencees.size(); i++)
        {
            ParseUnit referencee = (ParseUnit) referencees.elementAt(i);
            // See if our search has reached "parseUnit";
            // if so, we have a circularity
            if (referencee == parseUnit)
            {
                // Circularity detected
                errors.addAbort("Circular dependency among .tla files; " + "dependency cycle is:\n\n  "
                        + pathToString(circularPath));

            } else
            {
                circularPath.addElement(referencee);
                // See if there is a circular path continuing through this referencee
                nonCircularityBody(parseUnit, referencee, errors, alreadyVisited, circularPath);
                circularPath.removeElementAt(circularPath.size() - 1);
            } // end if
        } // end for

        return;
    }

    // The next two methods and the variables declared before them
    // traverse the tree of module relationships recursively, starting
    // at "currentModule", to find a name in an EXTENDS decl that is as
    // yet unresolved, if any, and set "nextParseUnit" to its name.
    // Return false iff there are no more unresolved EXTENDS names in
    // the entire specification.
    String nextParseUnitName = "";
    // The place where name of the next unresolved extention
    // or instance module is stored by the next methods

    ModulePointer nextExtenderOrInstancerModule = null;
    // The place where a reference to the module that extends
    // or instances the next parse unit is stored by the next method
    boolean extentionFound;
    boolean instantiationFound;

    // A wrapper for the next method, which empties the alreadyVisited
    // table calling the recursive method below
    private boolean findNextUnresolvedExtention(ModulePointer currentModule)
    {
        HashSet alreadyVisited = new HashSet();
        return findNextUnresolvedExtentionBody(currentModule, alreadyVisited);
    }

    // Traverse the tree of module relationships recursively, starting
    // at "currentModule", to find a name in an EXTENDS decl that is as
    // yet unresolved, if any, and set "nextParseUnit" to its name.
    // Return false iff there are no more unresolved EXTENDS names in
    // the entire specification.
    private boolean findNextUnresolvedExtentionBody(ModulePointer currentModule, HashSet alreadyVisited)
    {
        if (alreadyVisited.contains(currentModule))
        {
            extentionFound = false;
            return false;
        }
        alreadyVisited.add(currentModule);

        ModuleContext currentContext = currentModule.getContext();
        Vector extendees = currentModule.getNamesOfModulesExtended();
        Vector instancees = currentModule.getNamesOfModulesInstantiated();

        // for all of the modules named as extendees of the current
        // module, but which may or not be resolved yet
        for (int i = 0; i < extendees.size(); i++)
        {
            // if one of them is unresolved
            if (currentContext.resolve((String) extendees.elementAt(i)) == null)
            {
                // then it is the next unresolved extention; return it
                nextParseUnitName = (String) extendees.elementAt(i);
                nextExtenderOrInstancerModule = currentModule;
                extentionFound = true;
                return true;
            }
        } // end for

        // See if one of the already-resolved extendees has any unresolved
        // extentions
        for (int i = 0; i < extendees.size(); i++)
        {
            // by recursive invocation of this method on the extendees
            if (findNextUnresolvedExtentionBody(currentContext.resolve((String) extendees.elementAt(i)), alreadyVisited))
            {
                extentionFound = true;
                return true;
            }
        } // end for

        // See if one of the already-resolved instancees of currentModule
        // has any unresolved extentions
        for (int i = 0; i < instancees.size(); i++)
        {
            // if this instancee has been resolved
            if (currentContext.resolve((String) instancees.elementAt(i)) != null)
            {
                // check by recursive invocation of this method on the instancees
                if (findNextUnresolvedExtentionBody(currentContext.resolve((String) instancees.elementAt(i)),
                        alreadyVisited))
                {
                    extentionFound = true;
                    return true;
                } // end if
            } // end if
        } // end for

        // Finally, see if any of "currentModule"'s inner modules (or any
        // they extend or instance) have any unresolved extentions by
        // invoking this method recursively on them.
        Vector innerModules = currentModule.getDirectInnerModules();
        for (int i = 0; i < innerModules.size(); i++)
        {
            if (findNextUnresolvedExtentionBody((ModulePointer) innerModules.elementAt(i), alreadyVisited))
            {
                extentionFound = true;
                return true;
            }
        } // end for

        // Iff there are no unresolved extention module names, we return false
        extentionFound = false;
        return false;
    } // end findNextUnresolvedExtentionBody()

    // A wrapper for the next method, which empties the alreadyVisited
    // table calling the recursive method below
    private boolean findNextUnresolvedInstantiation(ModulePointer currentModule)
    {
        HashSet alreadyVisited = new HashSet();
        return findNextUnresolvedInstantiationBody(currentModule, alreadyVisited);
    }

    // Determines whether an INSTANCE statement for the module named
    // "instancee" refers to an earlier-defined internal module within
    // the same module "module". This is accomplished essentially by a
    // linear search of the declaration in the syntactic tree of
    // "module". Note: this does NOT scale when there are large numbers
    // of INSTANCE decls in a long module.
    private boolean instanceResolvesToInternalModule(ModulePointer currentModule, String instanceeName)
    {
        // Find the body part of module tree
        TreeNode body = currentModule.getBody();

        // We will be accumulating the set of names of internal modules
        // defined before the INSTANCE declaration.
        HashSet internalModulesSeen = new HashSet();

        // loop through the top level definitions in the body of the
        // module looking for embedded modules instantiations, and module
        // definitions
        for (int i = 0; i < body.heirs().length; i++)
        {
            TreeNode def = body.heirs()[i];

            // if we encounter an new (inner) module
            if (def.getImage().equals("N_Module"))
            {
                // Pick off name of inner module
                String innerModuleName = def.heirs()[0].heirs()[1].getImage();

                // Add to the set of names of inner modules seen so far
                internalModulesSeen.add(innerModuleName);
            }

            // if we encounter an INSTANCE decl
            else if (def.getImage().equals("N_Instance"))
            {
                TreeNode[] instanceHeirs = def.heirs();
                int nonLocalInstanceNodeIX;

                // The modifier "LOCAL" may or may not appear in the syntax tree;
                // if so, offset by 1
                if (instanceHeirs[0].getImage().equals("LOCAL"))
                {
                    nonLocalInstanceNodeIX = 1;
                } else
                {
                    nonLocalInstanceNodeIX = 0;
                }

                // Find the name of the module being instantiated
                String instanceModuleName = instanceHeirs[nonLocalInstanceNodeIX].heirs()[1].getImage();

                // if this is the module name we are searching for, then if it
                // corresponds to an inner module defined earlier, then return
                // true; else return false.
                if (instanceModuleName.equals(instanceeName))
                {
                    return internalModulesSeen.contains(instanceeName);
                } // end if
            } // end if

            // if we encounter a module definition (i.e. D(x,y) == INSTANCE
            // Modname WITH ...) that counts as an instance also
            else if (def.getImage().equals("N_ModuleDefinition"))
            {
                TreeNode[] instanceHeirs = def.heirs();
                int nonLocalInstanceNodeIX;

                // The modifier "LOCAL" may or may not appear in the syntax tree;
                // if so, offset by 1
                if (instanceHeirs[0].getImage().equals("LOCAL"))
                {
                    nonLocalInstanceNodeIX = 3;
                } else
                {
                    nonLocalInstanceNodeIX = 2;
                }

                // Find the name of the module being instantiated
                String instanceModuleName = instanceHeirs[nonLocalInstanceNodeIX].heirs()[1].getImage();

                // if this is the module name we are searching for, then if it
                // corresponds to an inner module defined earlier, then return
                // true; else return false.
                if (instanceModuleName.equals(instanceeName))
                {
                    return internalModulesSeen.contains(instanceeName);
                } // end if
            } // end else
        } // end for

        return false;
    } // end instanceResolvesToInternalModule()

    // Traverse the tree of module relationships recursively to find a
    // name in an INSTANCE decl that is as yet unresolved, if any, and
    // set "nextParseUnit" to its name. Return false iff there are no
    // more unresolved INSTANCES names in the entire specification.
    private boolean findNextUnresolvedInstantiationBody(ModulePointer currentModule, HashSet alreadyVisited)
    {
        if (alreadyVisited.contains(currentModule))
        {
            instantiationFound = false;
            return false;
        }
        alreadyVisited.add(currentModule);

        ModuleContext currentContext = currentModule.getContext();
        Vector extendees = currentModule.getNamesOfModulesExtended();
        Vector instancees = currentModule.getNamesOfModulesInstantiated();

        // for all of the modules named as instancees of the current
        // module, but which may or not be resolved yet.
        for (int i = 0; i < instancees.size(); i++)
        {
            // if one of them is unresolved
            if (currentContext.resolve((String) instancees.elementAt(i)) == null)
            {
                // See if it can be resolved WITHIN the module in which the
                // INSTANCE stmt occurs, i.e. does it resolve to an inner
                // module declared above this INSTANCE stmt? Nothing in the
                // logic so far covers this (most common) case, so we have to
                // insert logic here to check now.

                if (!instanceResolvesToInternalModule(currentModule, (String) instancees.elementAt(i)))
                {
                    // then it is the next unresolved instantiation; return it
                    nextParseUnitName = (String) instancees.elementAt(i);
                    nextExtenderOrInstancerModule = currentModule;
                    instantiationFound = true;
                    return true;
                }
            }
        }

        // See if one of the already-resolved extendees has any
        // unresolved instantiations
        for (int i = 0; i < extendees.size(); i++)
        {
            // by recursive invocation of this method on the extendees
            if (findNextUnresolvedInstantiationBody(currentContext.resolve((String) extendees.elementAt(i)),
                    alreadyVisited))
            {
                instantiationFound = true;
                return true;
            }
        }

        // See if one of the already-resolved instancees of currentModule
        // has any unresolved extentions.
        for (int i = 0; i < instancees.size(); i++)
        {
            // if this instancee has been resolved
            if (currentContext.resolve((String) instancees.elementAt(i)) != null)
            {
                if (findNextUnresolvedInstantiationBody(currentContext.resolve((String) instancees.elementAt(i)),
                        alreadyVisited))
                {
                    instantiationFound = true;
                    return true;
                }
            }
        }

        // Finally, see if any of "currentModule"'s inner modules (or any
        // they extend) have any unresolved instantiations by invoking
        // this method recursively on them.
        Vector innerModules = currentModule.getDirectInnerModules();
        for (int i = 0; i < innerModules.size(); i++)
        {
            if (findNextUnresolvedInstantiationBody((ModulePointer) innerModules.elementAt(i), alreadyVisited))
            {
                instantiationFound = true;
                return true;
            }
        }

        // Iff there are no unresolved Instantiation module names,
        // we return false
        instantiationFound = false;
        return false;
    }

    // Returns true iff mod1 is known to directly extend mod2
    private boolean directlyExtends(ModulePointer mod1, ModulePointer mod2)
    {
        ModuleRelatives mod1Rels = mod1.getRelatives();
        Vector extendees = mod1Rels.directlyExtendedModuleNames;
        ModuleContext mod1Context = mod1Rels.context;

        for (int i = 0; i < extendees.size(); i++)
        {
            if (mod1Context.resolve((String) extendees.elementAt(i)) == mod2)
                return true;
        }
        ;
        return false;
    }

    // Returns a Vector of all modules and submodules in the spec so far
    // that directly or indirectly extend "module", including "module"
    // itself. This method is horribly inefficient when there are a
    // large number of modules, looping as it does through ALL modules;
    // it must be rewritten recursively!!
    private Vector getModulesIndirectlyExtending(ModulePointer module)
    {
        // The Vector of Modules that equals, or directly or indirectly
        // extends, "module"
        Vector extenders = new Vector();
        extenders.addElement(module);

        // initializations for the following nested loop
        boolean additions = true;
        int lastAdditionsStart = 0;
        int lastAdditionsEnd = extenders.size();

        // while there were more additions to the Vector of modules
        // indirectly extending "module"
        while (additions)
        {
            additions = false;

            // for all newly added modules, see if there are any others that
            // extend them
            for (int i = lastAdditionsStart; i < lastAdditionsEnd; i++)
            {
                // Check ALL modules in the entire specification (!) to see if
                // they extend the i'th element of the vector
                Enumeration enumModules = getModules();
                while (enumModules.hasMoreElements())
                {
                    ModulePointer modPointer = (ModulePointer) enumModules.nextElement();

                    if (directlyExtends(modPointer, (ModulePointer) extenders.elementAt(i)))
                    {
                        if (!additions)
                            lastAdditionsStart = lastAdditionsEnd;
                        extenders.addElement(modPointer);
                        additions = true;
                    }
                }

                lastAdditionsStart = lastAdditionsEnd;
                lastAdditionsEnd = extenders.size();
            }
        }

        return extenders;
    }

    // This modules binds the name used in an INSTANCE definition in
    // module "instancer" to the top-level module in ParseUnit instancee
    private void resolveNamesBetweenSpecAndInstantiation(ModulePointer instancer, ParseUnit instancee)
    {
        // Bind the name of the instancee in the instancer's context
        ModuleContext instancerContext = instancer.getRelatives().context;
        instancerContext.bindIfNotBound(instancee.getName(), instancee.getRootModule());
    }

    // This method adds names to various module contexts (the context of
    // "extender" and any modules that extend it) that come from the
    // top-level inner modules in a ParseUnit (extendee) which is
    // extended by "extender". For any module "extender", and any
    // module xx that extends "extender", directly or indirectly, we
    // must resolve module names in xx to top level internal modules in
    // extendeeParseUnit
    private void resolveNamesBetweenSpecAndExtention(ModulePointer extender, ParseUnit extendee)
    {
        // First, bind the name of the extendee in the extender's context
        ModuleContext extenderContext = extender.getRelatives().context;
        extenderContext.bindIfNotBound(extendee.getName(), extendee.getRootModule());

        // Vextor of ModulePointers for modules that either are
        // "extender", or extend "extender" directly, of extend it
        // indirectly.
        Vector modulesIndirectlyExtending = getModulesIndirectlyExtending(extender);

        for (int i = 0; i < modulesIndirectlyExtending.size(); i++)
        {
            resolveNamesBetweenModuleAndExtention((ModulePointer) modulesIndirectlyExtending.elementAt(i), extendee);
        }
    }

    // Add all of the top level inner modules of extendeeParseUnit to
    // the contexts of extenderModule by doing appropriate bindings, and
    // do the same for all of extenderModule's submodules
    private void resolveNamesBetweenModuleAndExtention(ModulePointer extenderModule, ParseUnit extendeeParseUnit)
    {
        ModuleRelatives extenderRelatives = extenderModule.getRelatives();
        ModuleContext extenderContext = extenderRelatives.context;
        Vector instantiatedNames = extenderRelatives.directlyInstantiatedModuleNames;
        Vector extendedNames = extenderRelatives.directlyExtendedModuleNames;

        // find all unresolved names in extenderModule and its submodules
        // and see if they can be resolved in extendeeParseUnit

        // for each module name extended by extenderModule, try to resolve
        // it in the module it extends
        for (int i = 0; i < extendedNames.size(); i++)
        {
            String extendedName = (String) extendedNames.elementAt(i);

            // Pick up vector of top level inner modules of extendeeParseUnit
            Vector extendeeInnerModules = extendeeParseUnit.getRootModule().getDirectInnerModules();

            // See if the name occurs among the direct inner modules of extendee
            for (int j = 0; j < extendeeInnerModules.size(); j++)
            {
                ModulePointer extendeeInnerModule = ((ModulePointer) extendeeInnerModules.elementAt(j));
                String extendeeInnerName = extendeeInnerModule.getName();

                // if we have a match...
                if (extendedName.equals(extendeeInnerName))
                {
                    // bind the name to the inner module of extendee in the
                    // context of the extender iff it is unbound before this
                    extenderContext.bindIfNotBound(extendedName, extendeeInnerModule);

                    // and move on to the next instanceName
                    break;
                } // end if
            } // end for j
        } // end for i

        // for each module name instantiated at the top level of
        // extenderModule, try to resolve it in the module it extends
        for (int i = 0; i < instantiatedNames.size(); i++)
        {
            String instanceName = (String) instantiatedNames.elementAt(i);

            // Pick up vector of top level inner modules of extendeeParseUnit
            Vector extendeeInnerModules = extendeeParseUnit.getRootModule().getDirectInnerModules();

            // See if the name occurs among the direct inner modules of extendee
            for (int j = 0; j < extendeeInnerModules.size(); j++)
            {
                ModulePointer extendeeInnerModule = ((ModulePointer) extendeeInnerModules.elementAt(j));
                String extendeeInnerName = extendeeInnerModule.getName();

                // if we have a match...
                if (instanceName.equals(extendeeInnerName))
                {
                    // bind the name to the inner module of extendee in the
                    // context of the extender iff it is unbound before this
                    extenderContext.bindIfNotBound(instanceName, extendeeInnerModule);

                    // and move on to the next instanceName
                    break;
                } // end if
            } // end for j
        } // end for i

        // Now, for each inner module (recursively) of the extender
        // modules, try to resolve ITS unresolved module names in the same
        // extendee ParseUnit.
        Vector extenderInnerModules = extenderRelatives.directInnerModules;
        for (int i = 0; i < extenderInnerModules.size(); i++)
        {
            ModulePointer nextInner = (ModulePointer) extenderInnerModules.elementAt(i);
            resolveNamesBetweenModuleAndExtention(nextInner, extendeeParseUnit);
        }
    }

    /**
     * This method "loads" an entire specification, starting with the
     * top-level rootExternalModule and followed by all of the external
     * modules it references via EXTENDS and INSTANCE statements.
     */
    public boolean loadSpec(String rootExternalModuleName, Errors errors) throws AbortException
    {
        // If rootExternalModuleName" has *not* already been parsed, then
        // go to the file system and find the file containing it, create a
        // ParseUnit for it, and parse it. Parsing includes determining
        // module relationships. Aborts if not found in file system
        rootParseUnit = findOrCreateParsedUnit(rootExternalModuleName, errors, true /* first call */);
        rootModule = rootParseUnit.getRootModule();

        // Retrieve and parse all module extentions: As long as there is
        // another unresolved module name...
        // 0. Find the ParseUnit in corresponding to the name; go to the
        // file system to find it and parse it if necessary. Not its
        // relationship with other ParseUnits
        // 1. Verify that next unresolved module is not a circular
        // dependency among ParseUnits.
        // 2. Read, parse, and analyze module relationships for next
        // unresolved module name, and create a ParseUnit for it.
        // 3. Integrate the ModuleRelationships information from the new
        // ParseUnit into that for this entire SpecObj
        // 4. Select the next unresolved module name for processing.

        ParseUnit nextExtentionOrInstantiationParseUnit = null;

        while (findNextUnresolvedExtention(rootModule) || findNextUnresolvedInstantiation(rootModule))
        {
            // nextParseUnitName has not already been processed through some
            // other path,
            if (parseUnitContext.get(nextParseUnitName) == null)
            {
                // find it in the file system (if there) and parse and analyze it.
                nextExtentionOrInstantiationParseUnit = findOrCreateParsedUnit(nextParseUnitName, errors, false /* not first call */);
            } else
            {
                // or find it in the known parseUnitContext
                nextExtentionOrInstantiationParseUnit = (ParseUnit) parseUnitContext.get(nextParseUnitName);
            }

            // Record that extenderOrInstancerParseUnit EXTENDs or INSTANCEs
            // nextExtentionOrInstantiationParseUnit, and that
            // nextExtentionOrInstantiationParseUnit is extended or
            // instanced by extenderOrInstancerParseUnit.
            ParseUnit extenderOrInstancerParseUnit = nextExtenderOrInstancerModule.getParseUnit();

            if (extentionFound)
            {
                extenderOrInstancerParseUnit.addExtendee(nextExtentionOrInstantiationParseUnit);
                nextExtentionOrInstantiationParseUnit.addExtendedBy(extenderOrInstancerParseUnit);
            }
            if (instantiationFound)
            {
                extenderOrInstancerParseUnit.addInstancee(nextExtentionOrInstantiationParseUnit);
                nextExtentionOrInstantiationParseUnit.addInstancedBy(extenderOrInstancerParseUnit);
            }

            // Check for circular references among parseUnits; abort if found
            nonCircularityTest(nextExtentionOrInstantiationParseUnit, errors);

            // If this ParseUnit is loaded because of an EXTENDS decl, then
            // it may have inner modules that are the resolvants for
            // unresolved module names in the nextExtenderOrInstancerModule;
            // resolve the ones that are possible
            if (extentionFound)
            {
                resolveNamesBetweenSpecAndExtention(nextExtenderOrInstancerModule,
                        nextExtentionOrInstantiationParseUnit);
            }
            // If this ParseUnit is loaded because of an INSTANCE stmt, then
            // the outer module of the ParseUnit is the resolution of the
            // previously unresolved instantiation.
            if (instantiationFound)
            {
                resolveNamesBetweenSpecAndInstantiation(nextExtenderOrInstancerModule,
                        nextExtentionOrInstantiationParseUnit);
            }
        } // end while

        // Walk the moduleRelationshipsSpec graph to set up
        // semanticAnalysisVector; this vector determines the order in
        // which semantic analysis is done on parseUnits
        calculateDependencies(rootParseUnit);

        return true;
        // loadUnresolvedRelatives(moduleRelationshipsSpec, rootModule, errors);
    }

    /**
     * Getter for the name resolver used in the Spec
     * @return name resolver
     */
    public FilenameToStream getResolver()
    {
        return resolver;
    }

    /**
     * @param globalContextErrors the globalContextErrors to set
     */
    public void setGlobalContextErrors(Errors globalContextErrors)
    {
        this.globalContextErrors = globalContextErrors;
    }

}