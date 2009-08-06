package org.lamport.tla.toolbox.tool.tlc.util;

import java.util.List;
import java.util.Vector;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IProgressMonitor;
import org.lamport.tla.toolbox.tool.tlc.model.Assignment;
import org.lamport.tla.toolbox.tool.tlc.model.TypedSet;
import org.lamport.tla.toolbox.util.ResourceHelper;

/**
 * Encapsulates two buffers and provides semantic methods to add content to the _MC file and the CFG file of the model 
 * @author Simon Zambrovski
 * @version $Id$
 */
public class ModelWriter
{
    private static final String CR = "\n";
    private static final String SEP = "----";
    private static final String EQ = " = ";
    private static final String ARROW = " <- ";
    private static final String DEFINES = " == ";

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
    public void addSpecDefinition(String[] specDefinition)
    {
        cfgBuffer.append("SPECIFICATION ");
        cfgBuffer.append(specDefinition[0]).append(CR);
        
        tlaBuffer.append("\\* Specification formula").append(CR);
        tlaBuffer.append(specDefinition[1]).append(CR).append(SEP).append(CR);

    }

    /**
     * Add constants declarations
     * @param constants
     * @param modelValues
     */
    public void addConstants(List constants, TypedSet modelValues)
    {
        // add model value declarations
        addMVTypedSet(modelValues, "\\* MV CONSTANT declarations");

        Assignment constant;
        Vector symmetrySets = new Vector();

        for (int i = 0; i < constants.size(); i++)
        {
            constant = (Assignment) constants.get(i);
            if (constant.isModelValue())
            {
                if (constant.isSetOfModelValues())
                {
                    // set model values
                    TypedSet setOfMVs = TypedSet.parseSet(constant.getRight());
                    addMVTypedSet(setOfMVs, "\\* MV CONSTANT declarations");
                    cfgBuffer.append("\\* MV CONSTANT definitions" ).append(CR);
                    tlaBuffer.append("\\* MV CONSTANT definitions: " + constant.getLeft()).append(CR);
                    
                    String id = addArrowAssignment(constant, "const");
                    if (constant.isSymmetricalSet())
                    {
                        symmetrySets.add(id);
                    }
                    tlaBuffer.append(SEP).append(CR).append(CR);
                } else
                {
                    cfgBuffer.append("\\* CONSTANT declarations").append(CR);
                    // model value assignment
                    // to .cfg : foo = foo
                    // to _MC.tla : <nothing>, since the constant is already defined in one of the spec modules
                    cfgBuffer.append("CONSTANT ").append(constant.getLabel()).append(EQ).append(constant.getRight()).append(CR);
                }
            } else
            {
                // simple constant value assignment
                cfgBuffer.append("\\* CONSTANT definitions").append(CR);
                tlaBuffer.append("\\* CONSTANT definitions: " + constant.getLeft()).append(CR);
                addArrowAssignment(constant, "const");
                tlaBuffer.append(SEP).append(CR).append(CR);
            }
        }

        if (!symmetrySets.isEmpty())
        {
            String label = ModelHelper.getValidIdentifier("symm");

            tlaBuffer.append("\\* SYMMETRY definition").append(CR);
            cfgBuffer.append("\\* SYMMETRY definition").append(CR);

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
            cfgBuffer.append("SYMMETRY ").append(label).append(CR);
        }

    }

    /**
     * Assigns a right side to a label using an id generated from given schema
     * @param constant, constant containg the values
     * @param schema schema to generate the Id
     * @return generated id
     */
    public String addArrowAssignment(Assignment constant, String schema)
    {
        // constant instantiation
        // to .cfg : foo <- <id>
        // to _MC.tla : <id>(a, b, c)==
        // <expression>
        String id = ModelHelper.getValidIdentifier(schema);
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
    public void addMVTypedSet(TypedSet mvSet, String comment)
    {
        if (mvSet.getValueCount() != 0)
        {
            // create a declaration line
            // CONSTANTS
            // a, b, c
            if (comment != null && !comment.isEmpty())
            {
                tlaBuffer.append(comment).append(CR);
            }
            tlaBuffer.append("CONSTANTS").append(CR).append(mvSet.toStringWithoutBraces());
            tlaBuffer.append(CR).append(SEP).append(CR).append(CR);

            // create MV assignments
            // a = a
            // b = b
            // c = c
            if (comment != null && !comment.isEmpty())
            {
                cfgBuffer.append(comment).append(CR);
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
     */
    public void addFormulaList(List elements, String keyword)
    {
        if (elements.isEmpty())
        {
            return;
        }
        cfgBuffer.append("\\* " + keyword + " definition").append(CR);
        tlaBuffer.append("\\* " + keyword + " definition").append(CR);
        cfgBuffer.append(keyword).append(CR);

        for (int i = 0; i < elements.size(); i++)
        {
            String[] element = (String[]) elements.get(i);
            cfgBuffer.append(element[0]).append(CR);
            tlaBuffer.append(element[1]).append(CR).append(SEP).append(CR);
        }
    }

    /**
     * New definitions are added to the _MC.tla file only
     * @param elements
     */
    public void addNewDefinitions(String definitions)
    {
        if (definitions.isEmpty())
        {
            return;
        }
        tlaBuffer.append("\\* New definitions").append(CR);
        tlaBuffer.append(definitions).append(CR).append(SEP).append(CR);
    }

}
