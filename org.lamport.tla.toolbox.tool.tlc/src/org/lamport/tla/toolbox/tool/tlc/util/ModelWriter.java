package org.lamport.tla.toolbox.tool.tlc.util;

import java.util.Hashtable;
import java.util.List;
import java.util.Vector;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.debug.core.ILaunchConfiguration;
import org.eclipse.jface.text.IRegion;
import org.eclipse.jface.text.Region;
import org.lamport.tla.toolbox.tool.ToolboxHandle;
import org.lamport.tla.toolbox.tool.tlc.model.Assignment;
import org.lamport.tla.toolbox.tool.tlc.model.Formula;
import org.lamport.tla.toolbox.tool.tlc.model.TypedSet;
import org.lamport.tla.toolbox.util.ResourceHelper;

import tla2sany.modanalyzer.SpecObj;
import tla2sany.semantic.OpDefNode;

/**
 * Encapsulates two buffers and provides semantic methods to add content to the _MC file and the CFG file of the model 
 * @author Simon Zambrovski
 * @version $Id$
 */
public class ModelWriter
{
    /**
     * Counter to be able to generate unique identifiers
     */
    private static long globalCounter = 1;

    public static final String SPEC_SCHEME = "spec";
    public static final String INIT_SCHEME = "init";
    public static final String NEXT_SCHEME = "next";
    public static final String CONSTANT_SCHEME = "const";
    public static final String SYMMETRY_SCHEME = "symm";
    public static final String DEFOV_SCHEME = "def_ov";
    public static final String CONSTRAINT_SCHEME = "constr";
    public static final String ACTIONCONSTRAINT_SCHEME = "action_constr";
    public static final String INVARIANT_SCHEME = "inv";
    public static final String PROP_SCHEME = "prop";

    public static final String SPACE = " ";
    public static final String CR = "\n";
    public static final String SEP = "----";
    public static final String EQ = " = ";
    public static final String ARROW = " <- ";
    public static final String DEFINES = " == ";
    public static final String DEFINES_CR = " ==\n";
    public static final String COMMENT = "\\* ";
    public static final String ATTRIBUTE = "@";
    public static final String INDEX = ":";
    public static final String EMPTY_STRING = "";

    private StringBuffer tlaBuffer;
    private StringBuffer cfgBuffer;

    /**
     * Constructs new model writer
     */
    public ModelWriter()
    {
        this.tlaBuffer = new StringBuffer(1024);
        this.cfgBuffer = new StringBuffer(1024);
    }

    /**
     * Write the content to files
     * @param tlaFile
     * @param cfgFile
     * @param monitor
     * @throws CoreException
     */
    public void writeFiles(IFile tlaFile, IFile cfgFile, IProgressMonitor monitor) throws CoreException
    {
        tlaBuffer.append(ResourceHelper.getModuleClosingTag());
        cfgBuffer.append(ResourceHelper.getConfigClosingTag());
        ResourceHelper.replaceContent(tlaFile, tlaBuffer, monitor);
        ResourceHelper.replaceContent(cfgFile, cfgBuffer, monitor);
    }

    /**
     * Add file header
     * @param moduleFilename
     * @param extendedModuleName
     */
    public void addPrimer(String moduleFilename, String extendedModuleName)
    {
        tlaBuffer.append(ResourceHelper.getExtendingModuleContent(moduleFilename, extendedModuleName));
    }

    /**
     * Add spec definition
     * @param specDefinition
     */
    public void addSpecDefinition(String[] specDefinition, String attributeName)
    {
        cfgBuffer.append("SPECIFICATION").append(SPACE);
        cfgBuffer.append(specDefinition[0]).append(CR);

        tlaBuffer.append(COMMENT).append("Specification ").append(ATTRIBUTE).append(attributeName).append(CR);
        tlaBuffer.append(specDefinition[1]).append(CR).append(SEP).append(CR);

    }

    /**
     * Add constants declarations
     * @param constants
     * @param modelValues
     */
    public void addConstants(List constants, TypedSet modelValues, String attributeConstants, String attributeMVs)
    {
        // add model value declarations
        addMVTypedSet(modelValues, "MV CONSTANT declarations ", attributeMVs);

        Assignment constant;
        Vector symmetrySets = new Vector();

        // first run for all the declarations
        for (int i = 0; i < constants.size(); i++)
        {
            constant = (Assignment) constants.get(i);
            if (constant.isModelValue())
            {
                if (constant.isSetOfModelValues())
                {
                    // set model values
                    TypedSet setOfMVs = TypedSet.parseSet(constant.getRight());
                    addMVTypedSet(setOfMVs, "MV CONSTANT declarations", attributeConstants);
                }
            }
        }

        // now all the definitions
        for (int i = 0; i < constants.size(); i++)
        {
            constant = (Assignment) constants.get(i);
            if (constant.isModelValue())
            {
                if (constant.isSetOfModelValues())
                {
                    // set model values
                    cfgBuffer.append(COMMENT).append("MV CONSTANT definitions").append(CR);
                    tlaBuffer.append(COMMENT).append("MV CONSTANT definitions " + constant.getLeft()).append(CR);

                    String id = addArrowAssignment(constant, CONSTANT_SCHEME);
                    if (constant.isSymmetricalSet())
                    {
                        symmetrySets.add(id);
                    }
                    tlaBuffer.append(SEP).append(CR).append(CR);
                } else
                {
                    cfgBuffer.append(COMMENT).append("CONSTANT declarations").append(CR);
                    // model value assignment
                    // to .cfg : foo = foo
                    // to _MC.tla : <nothing>, since the constant is already defined in one of the spec modules
                    cfgBuffer.append("CONSTANT").append(SPACE).append(constant.getLabel()).append(EQ).append(
                            constant.getRight()).append(CR);
                }
            } else
            {
                // simple constant value assignment
                cfgBuffer.append(COMMENT).append("CONSTANT definitions").append(CR);

                tlaBuffer.append(COMMENT).append("CONSTANT definitions ").append(ATTRIBUTE).append(attributeConstants)
                        .append(INDEX).append(i).append(constant.getLeft()).append(CR);
                addArrowAssignment(constant, CONSTANT_SCHEME);
                tlaBuffer.append(SEP).append(CR).append(CR);
            }
        }

        // symmetry
        if (!symmetrySets.isEmpty())
        {
            String label = ModelWriter.getValidIdentifier(SYMMETRY_SCHEME);

            tlaBuffer.append(COMMENT).append("SYMMETRY definition").append(CR);
            cfgBuffer.append(COMMENT).append("SYMMETRY definition").append(CR);

            tlaBuffer.append(label).append(DEFINES).append(CR);
            // symmetric model value sets added
            for (int i = 0; i < symmetrySets.size(); i++)
            {
                tlaBuffer.append("Permutations(").append((String) symmetrySets.get(i)).append(")");
                if (i != symmetrySets.size() - 1)
                {
                    tlaBuffer.append(" \\union ");
                }
            }

            tlaBuffer.append(CR).append(SEP).append(CR).append(CR);
            cfgBuffer.append("SYMMETRY").append(SPACE).append(label).append(CR);
        }

    }

    /**
     * Assigns a right side to a label using an id generated from given schema
     * @param constant, constant containing the values
     * @param schema schema to generate the Id
     * @return generated id
     */
    public String addArrowAssignment(Assignment constant, String schema)
    {
        // constant instantiation
        // to .cfg : foo <- <id>
        // to _MC.tla : <id>(a, b, c)==
        // <expression>
        String id = ModelWriter.getValidIdentifier(schema);
        tlaBuffer.append(constant.getParametrizedLabel(id)).append(DEFINES).append(CR).append(constant.getRight())
                .append(CR);
        cfgBuffer.append("CONSTANT").append(CR);
        cfgBuffer.append(constant.getLabel()).append(ARROW).append(id).append(CR);
        return id;
    }

    /**
     * Creates a serial version of an MV set in both files
     * @param mvSet typed set containing the model values
     * @param comment a comment to put before the declarations, null and empty strings are OK
     */
    public void addMVTypedSet(TypedSet mvSet, String comment, String attributeName)
    {
        if (mvSet.getValueCount() != 0)
        {
            // create a declaration line
            // CONSTANTS
            // a, b, c
            if (comment != null && !comment.isEmpty())
            {
                tlaBuffer.append(COMMENT).append(comment).append(ATTRIBUTE).append(attributeName).append(CR);
            }
            tlaBuffer.append("CONSTANTS").append(CR).append(mvSet.toStringWithoutBraces());
            tlaBuffer.append(CR).append(SEP).append(CR).append(CR);

            // create MV assignments
            // a = a
            // b = b
            // c = c
            if (comment != null && !comment.isEmpty())
            {
                cfgBuffer.append(COMMENT).append(comment).append(CR);
            }
            cfgBuffer.append("CONSTANTS").append(CR);
            String mv;
            for (int i = 0; i < mvSet.getValueCount(); i++)
            {
                mv = mvSet.getValue(i);
                cfgBuffer.append(mv).append(EQ).append(mv).append(CR);
            }
        }
    }

    /**
     * Puts (String[])element[0] to CFG file and element[1] to TLA_MC file
     * 
     * @param elements a list of String[] elements
     * @param keyword the keyword to be used in the CFG file
     * @param attributeName the name of the attribute in the model file
     */
    public void addFormulaList(List elements, String keyword, String attributeName)
    {
        if (elements.isEmpty())
        {
            return;
        }
        cfgBuffer.append(COMMENT).append(keyword + " definition").append(CR);
        cfgBuffer.append(keyword).append(CR);

        for (int i = 0; i < elements.size(); i++)
        {
            String[] element = (String[]) elements.get(i);
            cfgBuffer.append(element[0]).append(CR);
            // when a definition in the root module is overriden as a model value
            // there is nothing to add to the MC.tla file so, we do not do the following
            if (!element[1].equals(EMPTY_STRING))
            {
                tlaBuffer.append(COMMENT).append(keyword + " definition ").append(ATTRIBUTE).append(attributeName)
                        .append(INDEX).append(i).append(CR);
                tlaBuffer.append(element[1]).append(CR).append(SEP).append(CR);
            }
        }
    }

    /**
     * New definitions are added to the _MC.tla file only
     * @param elements
     */
    public void addNewDefinitions(String definitions, String attributeName)
    {
        if (definitions.isEmpty())
        {
            return;
        }
        tlaBuffer.append(COMMENT).append("New definitions ").append(ATTRIBUTE).append(attributeName).append(CR);
        tlaBuffer.append(definitions).append(CR).append(SEP).append(CR);
    }

    /**
     * Create the content for a single source element
     * @return a list with at most one String[] element
     * @throws CoreException 
     */
    public static List createSourceContent(String propertyName, String labelingScheme, ILaunchConfiguration config)
            throws CoreException
    {
        Vector result = new Vector();
        String value = config.getAttribute(propertyName, EMPTY_STRING);
        if (EMPTY_STRING.equals(value))
        {
            return result;
        }
        String identifier = getValidIdentifier(labelingScheme);
        StringBuffer buffer = new StringBuffer();

        // the identifier
        buffer.append(identifier).append(DEFINES_CR);
        buffer.append(value);

        result.add(new String[] { identifier, buffer.toString() });
        return result;
    }

    /**
     * Converts formula list to a string representation
     * @param serializedFormulaList, list of strings representing formulas (with enablement flag)
     * @param labelingScheme
     * @return
     */
    public static List createFormulaListContent(List serializedFormulaList, String labelingScheme)
    {
        List formulaList = ModelHelper.deserializeFormulaList(serializedFormulaList);
        return (createListContent(formulaList, labelingScheme));
    }

    /**
     * Create a list of overrides. If the override is not in the spec's root module, then
     * the config file will have     A <- [M] id . This means that A is defined in module M,
     * and its definition is being overriden in the spec root module which is dependent upon M.
     * The following is an example from Leslie Lamport that explains what occured before changing
     * the code and what occurs now.
     * Consider the root module

    ----------------- MODULE TestA --------------------
    M(a,b) == INSTANCE TestB WITH CB <- a, CD <- b
    ==================================================

    which imports the module

    ----------------- MODULE TestB --------------------
    CONSTANTS CB, CD

    Foo(x) == <<x, CB, CD>>
    ==================================================

    If you go to definition overrides, you'll find the option of
    overriding M!Foo.  Selecting it, the toolbox asks you to define an operator
    M!Foo of 3 arguments.  If you do it and run TLC, you get the error

    The configuration file substitutes for Foo with
    def_ov_12533499062845000 of different number of arguments.

    Here's what's going on.  The INSTANCE statement imports the operator
    M!Foo into module TestA.  As you may recall, you use that operator
    in an expression by writing something like

    M(42, "a")!F(-13)

    but in the semantic tree, it looks just as if M!F were any other
    operator with three arguments.  When TLC sees the override instruction

    Foo <- [TestB]def_ov_12533495599614000

    in the .cfg file, it tries to substitute an operator def_ov_...  with
    3 arguments for the operator Foo of module TestB that has only a
    single argument.  Hence, the error.

    ------

    Here's the fix.  Instead of giving the user the option of overriding
    M!Foo, in the menu, he should simply see Foo and, if he clicks once
    it, he should see that it's in module TestB. If he chooses to override
    Foo, he should be asked to define an operator of one argument.
    
     * @param overrides
     * @param string
     * @return
     * 
     * Was throwing null-pointer exception when called with spec unparsed.
     * Hacked a fix to handle this case.  LL 20 Sep 2009
     */
    public static List createOverridesContent(List overrides, String labelingScheme)
    {
        Vector resultContent = new Vector(overrides.size());
        String[] content;
        String id;
        Assignment formula;

        // getting the opdefnodes is necessary for retrieving the correct label
        // to appear in the cfg file as explained in the documentation for this method
        SpecObj specObj = ToolboxHandle.getCurrentSpec().getValidRootModule();
        if (specObj == null)
        {
            return resultContent;
        }
        OpDefNode[] opDefNodes = specObj.getExternalModuleTable().getRootModule().getOpDefs();
        Hashtable nodeTable = new Hashtable(opDefNodes.length);

        for (int j = 0; j < opDefNodes.length; j++)
        {
            String key = opDefNodes[j].getName().toString();
            nodeTable.put(key, opDefNodes[j]);
        }

        for (int i = 0; i < overrides.size(); i++)
        {
            id = getValidIdentifier(labelingScheme);
            // formulas
            // to .cfg : <id>
            // to _MC.tla : <id> == <expression>
            formula = ((Assignment) overrides.get(i));

            OpDefNode defNode = (OpDefNode) nodeTable.get(formula.getLabel());

            if (defNode == null)
            {
                // should raise an error
                content = null;
            } else
            {
                OpDefNode source = defNode.getSource();
                if (source == defNode)
                {
                    // user is overriding a definition in the root module
                    if (formula.isModelValue() && !formula.isSetOfModelValues())
                    {
                        // model value
                        content = new String[] { formula.getLabel() + EQ + formula.getLabel(), EMPTY_STRING };
                    } else
                    {
                        // not a model value
                        content = new String[] { formula.getLabel() + ARROW + id,
                                formula.getParametrizedLabel(id) + DEFINES_CR + formula.getRight() };
                    }
                } else if (source.getSource() == source)
                {
                    // user is overriding a definition that is not in the root module
                    if (formula.isModelValue() && !formula.isSetOfModelValues())
                    {
                        // model value
                        content = new String[] {
                                source.getName().toString() + ARROW + "["
                                        + source.getOriginallyDefinedInModuleNode().getName().toString() + "]" + id
                                        + " " + id + EQ + source.getName().toString(), "CONSTANT " + id };
                    } else
                    {
                        // not a model value
                        content = new String[] {
                                source.getName().toString() + ARROW + "["
                                        + source.getOriginallyDefinedInModuleNode().getName().toString() + "]" + id,
                                formula.getParametrizedLabel(id) + DEFINES_CR + formula.getRight() };
                    }
                } else
                {
                    // should raise an error window
                    content = null;
                }
            }

            resultContent.add(content);
        }
        return resultContent;
    }

    /**
     * Converts formula list to a string representation
     * @param formulaList list of assignments
     * @param labelingScheme 
     * @return
     */
    public static List createListContent(List formulaList, String labelingScheme)
    {
        Vector resultContent = new Vector(formulaList.size());
        String[] content;
        String label;
        for (int i = 0; i < formulaList.size(); i++)
        {
            label = getValidIdentifier(labelingScheme);
            // formulas
            // to .cfg : <id>
            // to _MC.tla : <id> == <expression>
            content = new String[] { label, label + DEFINES_CR + ((Formula) formulaList.get(i)).getFormula() };
            resultContent.add(content);
        }
        return resultContent;
    }

    /**
     * A pattern to match IDs generated by the {@link ModelWriter#getValidIdentifier(String)} method
     */
    public static final Pattern ID_MATCHER = Pattern.compile("(" + SPEC_SCHEME + "|" + INIT_SCHEME + "|" + NEXT_SCHEME
            + "|" + CONSTANT_SCHEME + "|" + SYMMETRY_SCHEME + "|" + DEFOV_SCHEME + "|" + CONSTRAINT_SCHEME + "|"
            + ACTIONCONSTRAINT_SCHEME + "|" + INVARIANT_SCHEME + "|" + PROP_SCHEME + ")_[0-9]{17}");

    /**
     * Find the IDs in the given text and return the array of 
     * regions pointing to those or an empty array, if no IDs were found.
     * An ID is scheme_timestamp, created by {@link ModelWriter#getValidIdentifier(String)} e.G. next_125195338522638000
     * @param text text containing IDs (error text)
     * @return array of regions or empty array
     */
    static IRegion[] findIds(String text)
    {
        if (text == null || text.isEmpty())
        {
            return new IRegion[0];
        }

        Matcher matcher = ModelWriter.ID_MATCHER.matcher(text);
        Vector regions = new Vector();
        while (matcher.find())
        {
            regions.add(new Region(matcher.start(), matcher.end() - matcher.start()));
        }
        return (IRegion[]) regions.toArray(new IRegion[regions.size()]);
    }

    /**
     * Retrieves new valid (not used) identifier from given schema
     * @param schema a naming schema, one of the {@link ModelWriter} SCHEMA constants
     * @return a valid identifier
     */
    public static synchronized String getValidIdentifier(String schema)
    {
        try
        {
            Thread.sleep(10);
        } catch (InterruptedException e)
        {
        }
        return schema + "_" + System.currentTimeMillis() + 1000 * (++globalCounter);
    }

}
