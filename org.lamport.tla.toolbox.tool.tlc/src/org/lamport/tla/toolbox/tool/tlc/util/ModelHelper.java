/*******************************************************************************
 * Copyright (c) 2015 Microsoft Research. All rights reserved. 
 *
 * The MIT License (MIT)
 * 
 * Permission is hereby granted, free of charge, to any person obtaining a copy 
 * of this software and associated documentation files (the "Software"), to deal
 * in the Software without restriction, including without limitation the rights
 * to use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies
 * of the Software, and to permit persons to whom the Software is furnished to do
 * so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all
 * copies or substantial portions of the Software. 
 * 
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS
 * FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR
 * COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN
 * AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION
 * WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 *
 * Contributors:
 *   Simon Zambrovski - initial API and implementation
 ******************************************************************************/
package org.lamport.tla.toolbox.tool.tlc.util;

import java.io.ByteArrayInputStream;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.Comparator;
import java.util.Hashtable;
import java.util.Iterator;
import java.util.List;
import java.util.Vector;
import java.util.regex.Matcher;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IMarker;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.IWorkspace;
import org.eclipse.core.resources.IWorkspaceRunnable;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IPath;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;
import org.eclipse.core.runtime.SubProgressMonitor;
import org.eclipse.core.runtime.jobs.ISchedulingRule;
import org.eclipse.core.runtime.jobs.MultiRule;
import org.eclipse.debug.core.DebugPlugin;
import org.eclipse.debug.core.ILaunchConfiguration;
import org.eclipse.debug.core.ILaunchConfigurationWorkingCopy;
import org.eclipse.debug.core.ILaunchManager;
import org.eclipse.jface.text.BadLocationException;
import org.eclipse.jface.text.FindReplaceDocumentAdapter;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.IRegion;
import org.eclipse.jface.text.Region;
import org.lamport.tla.toolbox.tool.ToolboxHandle;
import org.lamport.tla.toolbox.tool.tlc.TLCActivator;
import org.lamport.tla.toolbox.tool.tlc.launch.IModelConfigurationConstants;
import org.lamport.tla.toolbox.tool.tlc.launch.IModelConfigurationDefaults;
import org.lamport.tla.toolbox.tool.tlc.model.Assignment;
import org.lamport.tla.toolbox.tool.tlc.model.Formula;
import org.lamport.tla.toolbox.tool.tlc.model.Model;
import org.lamport.tla.toolbox.tool.tlc.model.ModelWriter;
import org.lamport.tla.toolbox.util.ResourceHelper;

import tla2sany.modanalyzer.SpecObj;
import tla2sany.semantic.ModuleNode;
import tla2sany.semantic.OpDeclNode;
import tla2sany.semantic.OpDefNode;
import tla2sany.semantic.SymbolNode;
import tla2sany.st.Location;

/**
 * Provides utility methods for model manipulation
 */
public class ModelHelper implements IModelConfigurationConstants, IModelConfigurationDefaults
{

	/**
     * Empty location
     */
    public static final int[] EMPTY_LOCATION = new int[] { 0, 0, 0, 0 };
    /**
     * Marker indicating the TLC Errors
     */
    public static final String TLC_MODEL_ERROR_MARKER_TLC = "org.lamport.tla.toolbox.tlc.modelErrorTLC";
    public static final String TLC_MODEL_ERROR_MARKER_ATTRIBUTE_NAME = "attributeName";
    public static final String TLC_MODEL_ERROR_MARKER_ATTRIBUTE_IDX = "attributeIndex";

	/**
	 * The zero-based id of the BasicFormPage to show the error on.
	 */
	public static final String TLC_MODEL_ERROR_MARKER_ATTRIBUTE_PAGE = "basicFormPageId";

    /**
     * Delimiter used to serialize lists  
     */
    private static final String LIST_DELIMITER = ";";
    /**
     * Delimiter used to serialize parameter-value pair  
     */
    private static final String PARAM_DELIMITER = ":";

    public static final String MC_MODEL_NAME = "MC";
    public static final String FILE_TLA = MC_MODEL_NAME + ".tla";
    public static final String FILE_CFG = MC_MODEL_NAME + ".cfg";
    public static final String FILE_OUT = MC_MODEL_NAME + ".out";

    // trace explorer file names
    public static final String TE_MODEL_NAME = "TE";
    public static final String TE_FILE_TLA = TE_MODEL_NAME + ".tla";
    public static final String TE_FILE_CFG = TE_MODEL_NAME + ".cfg";
    public static final String TE_FILE_OUT = TE_MODEL_NAME + ".out";
    // the file to which TLC's output is written so
    // that the trace explorer can retrieve the trace when it is run
    public static final String TE_TRACE_SOURCE = "MC_TE.out";

    /**
     * Convenience method
     * @param modelFile file containing the model
     * @return ILaunchconfiguration
     */
    public static ILaunchConfiguration getModelByFile(IFile modelFile)
    {
        ILaunchManager launchManager = DebugPlugin.getDefault().getLaunchManager();
        return launchManager.getLaunchConfiguration(modelFile);
    }

    /**
     * Saves the config working copy
     * @param config
     */
	public static void doSaveConfigurationCopy(ILaunchConfigurationWorkingCopy config) {
	}

    /**
     * Creates a serial version of the assignment list, to be stored in the {@link ILaunchConfiguration}
     * 
     * Any assignment consist of a label, parameter list and the right side
     * These parts are serialized as a list with delimiter {@link ModelHelper#LIST_DELIMETER}
     * The parameter list is stored as a list with delimiter {@link ModelHelper#PARAM_DELIMITER}
     * 
     * If the assignment is using a model value {@link Assignment#isModelValue()} == <code>true, the right
     * side is set to the label resulting in (foo = foo) 
     * 
     *   
     */
    public static List<String> serializeAssignmentList(List<Assignment> assignments)
    {
        Iterator<Assignment> iter = assignments.iterator();
        Vector<String> result = new Vector<String>(assignments.size());

        StringBuffer buffer;
        while (iter.hasNext())
        {
            Assignment assign = (Assignment) iter.next();

            buffer = new StringBuffer();

            // label
            buffer.append(assign.getLabel()).append(LIST_DELIMITER);

            // parameters if any
            for (int j = 0; j < assign.getParams().length; j++)
            {
                String param = assign.getParams()[j];
                if (param != null)
                {
                    buffer.append(param);
                }
                buffer.append(PARAM_DELIMITER);
            }
            buffer.append(LIST_DELIMITER);

            // right side
            // encode the model value usage (if model value is set, the assignment right side is equals to the label)

            if (assign.getRight() != null)
            {
                buffer.append(assign.getRight());
            }

            // isModelValue
            buffer.append(LIST_DELIMITER).append((assign.isModelValue() ? "1" : "0"));

            // is symmetrical
            buffer.append(LIST_DELIMITER).append((assign.isSymmetricalSet() ? "1" : "0"));

            result.add(buffer.toString());
        }
        return result;
    }

    /**
     * De-serialize assignment list. 
     * @see ModelHelper#serializeAssignmentList(List)
     */
    public static List<Assignment> deserializeAssignmentList(final List<String> serializedList) {
    	return deserializeAssignmentList(serializedList, false);
    }
    
    /**
     * De-serialize assignment list. 
     * @param serializedList
     * @param stripSymmetry Strips any symmetry definitions from assignments iff true
     * @return The list of all {@link Assignment}
     * @see ModelHelper#serializeAssignmentList(List)
     */
    public static List<Assignment> deserializeAssignmentList(final List<String> serializedList, final boolean stripSymmetry)
    {
        Vector<Assignment> result = new Vector<Assignment>(serializedList.size());
        Iterator<String> iter = serializedList.iterator();
        String[] fields = new String[] { null, "", "", "0", "0" };
        while (iter.hasNext())
        {
            String[] serFields = (iter.next()).split(LIST_DELIMITER);
            System.arraycopy(serFields, 0, fields, 0, serFields.length);

            String[] params;
            if ("".equals(fields[1]))
            {
                params = new String[0];
            } else
            {
                params = fields[1].split(PARAM_DELIMITER);
            }
            // assignment with label as right side are treated as model values
            Assignment assign = new Assignment(fields[0], params, fields[2]);

            // is Model Value
            if (fields.length > 3 && fields[3].equals("1"))
            {
                assign.setModelValue(true);

                // is symmetrical
                if (!stripSymmetry && fields.length > 4 && fields[4].equals("1"))
                {
                    assign.setSymmetric(true);
                }
            }

            result.add(assign);
        }
        return result;
    }

    /**
     * De-serialize formula list, to a list of formulas, that are selected (have a leading "1")
     * 
     * The first character of the formula is used to determine if the formula is enabled in the model 
     * editor or not. This allows the user to persist formulas, which are not used in the current model 
     */
    public static List<Formula> deserializeFormulaList(List<String> serializedList)
    {
        Vector<Formula> result = new Vector<Formula>(serializedList.size());
        Iterator<String> serializedIterator = serializedList.iterator();
        while (serializedIterator.hasNext())
        {
            String entry = serializedIterator.next();
            Formula formula = new Formula(entry.substring(1));
            if ("1".equals(entry.substring(0, 1)))
            {
                result.add(formula);
            }
        }
        return result;
    }

    /**
     * Extract the constants from module node
     * @param moduleNode
     * @return a list of assignments
     */
    public static List<Assignment> createConstantsList(ModuleNode moduleNode)
    {
        OpDeclNode[] constantDecls = moduleNode.getConstantDecls();
        Vector<Assignment> constants = new Vector<Assignment>(constantDecls.length);
        for (int i = 0; i < constantDecls.length; i++)
        {
            String[] params = new String[constantDecls[i].getNumberOfArgs()];
            // pre-fill the empty array
            Arrays.fill(params, EMPTY_STRING);
            Assignment assign = new Assignment(constantDecls[i].getName().toString(), params, EMPTY_STRING);
            constants.add(assign);
        }
        return constants;
    }

    /**
     * Checks whether the constant defined by assignment is defined in the module node
     * @param assignment
     * @param node
     * @return
     */
    public static boolean hasConstant(Assignment assignment, ModuleNode moduleNode)
    {
        OpDeclNode[] constantDecls = moduleNode.getConstantDecls();
        for (int i = 0; i < constantDecls.length; i++)
        {
            if (assignment.getLabel().equals(constantDecls[i].getName().toString())
                    && assignment.getParams().length == constantDecls[i].getNumberOfArgs())
            {
                return true;
            }
        }
        return false;
    }

    /**
     * Extract the variables from module node
     * @param moduleNode
     * @return a string representation of the variables
     * 
     * This method is being called with moduleNode = null when the model is
     * saved when the spec is unparsed.  I added a hack to handle that case,
     * but I'm not positive that there are no further problems that this can
     * cause.  LL. 20 Sep 2009
     */
    public static String createVariableList(ModuleNode moduleNode)
    {
        if (moduleNode == null)
        {
            return "";
        }
        StringBuffer buffer = new StringBuffer();
        OpDeclNode[] variableDecls = moduleNode.getVariableDecls();
        for (int i = 0; i < variableDecls.length; i++)
        {
            buffer.append(variableDecls[i].getName().toString());
            if (i != variableDecls.length - 1)
            {
                buffer.append(", ");
            }
        }
        return buffer.toString();
    }

    /*
     * Returns an array of Strings containing the variables declared
     * in the module.  Added 10 Sep 2009 by LL & DR
     */
    public static String[] createVariableArray(ModuleNode moduleNode)
    {
        OpDeclNode[] variableDecls = moduleNode.getVariableDecls();
        String[] returnVal = new String[variableDecls.length];
        for (int i = 0; i < variableDecls.length; i++)
        {
            returnVal[i] = variableDecls[i].getName().toString();
        }
        return returnVal;
    }

    /*
     * Returns true iff the specified module declares
     * at least one variable.  Added 10 Sep 2009 by LL & DR
     */
    public static boolean hasVariables(ModuleNode moduleNode)
    {
        OpDeclNode[] variableDecls = moduleNode.getVariableDecls();
        return variableDecls.length > 0;
    }

    public static SymbolNode getSymbol(String name, ModuleNode moduleNode)
    {
        return moduleNode.getContext().getSymbol(name);
    }

    /**
     * Extract the operator definitions from module node
     * @param moduleNode
     * @return a list of assignments
     */
    public static List<Assignment> createDefinitionList(ModuleNode moduleNode)
    {
        OpDefNode[] operatorDefinitions = moduleNode.getOpDefs();

        Vector<Assignment> operations = new Vector<Assignment>(operatorDefinitions.length);
        for (int i = 0; i < operatorDefinitions.length; i++)
        {
            String[] params = new String[operatorDefinitions[i].getNumberOfArgs()];
            // pre-fill the empty array
            Arrays.fill(params, "");
            Assignment assign = new Assignment(operatorDefinitions[i].getName().toString(), params, "");
            operations.add(assign);
        }
        return operations;
    }

    /**
     * This method eventually changes the constants list. If the signature constants of both
     * lists are equal, the constants list is left untouched. Otherwise, all constants not present
     * in the constantsFromModule are removed, and all missing are added.
     * <br>
     * For constant comparison {@link Assignment#equalSignature(Assignment)} is used
     * 
     * @param constants the list with constants, eventually the subject of change
     * @param constantsFromModule a list of constants from the module (no right side, no params)
     */
    public static List<Assignment> mergeConstantLists(List<Assignment> constants, List<Assignment> constantsFromModule)
    {
        Vector<Assignment> constantsToAdd = new Vector<Assignment>();
        Vector<Assignment> constantsUsed = new Vector<Assignment>();
        Vector<Assignment> constantsToDelete = new Vector<Assignment>();

        // iterate over constants from module
        for (int i = 0; i < constantsFromModule.size(); i++)
        {
            Assignment fromModule = (Assignment) constantsFromModule.get(i);
            // find it in the module list
            boolean found = false;

            for (int j = 0; j < constants.size(); j++)
            {
                Assignment constant = constants.get(j);
                if (fromModule.equalSignature(constant))
                {
                    // store the information that the constant is used
                    constantsUsed.add(constant);
                    found = true;
                    break;
                }
            }
            // constant is in the module but not in the model
            if (!found)
            {
                // save the constant for adding later
                constantsToAdd.add(fromModule);
            }
        }

        // add all
        constantsToDelete.addAll(constants);
        // remove all used
        constantsToDelete.removeAll(constantsUsed);

        // at this point, all used constants are in the constantUsed list
        constants.retainAll(constantsUsed);

        // all constants to add are in constantsTo Add list
        constants.addAll(constantsToAdd);

        return constantsToDelete;
    }

    /**
     * For an given id that is used in the document retrieves the four coordinates of it's first occurrence.
     * @param document
     * @param searchAdapter
     * @param idRegion
     * @return location coordinates in the sense of {@link Location} class (bl, bc, el, ec).
     * @throws CoreException on errors
     */
    public static int[] calculateCoordinates(IDocument document, FindReplaceDocumentAdapter searchAdapter, String id)
            throws CoreException
    {
        try
        {
            IRegion foundId = searchAdapter.find(0, id, true, true, false, false);
            if (foundId == null)
            {
                return EMPTY_LOCATION;
            } else
            {
                // return the coordinates
                return regionToLocation(document, foundId, true);
            }
        } catch (BadLocationException e)
        {
            throw new CoreException(new Status(IStatus.ERROR, TLCActivator.PLUGIN_ID,
                    "Error during detection of the id position in MC.tla.", e));
        }
    }

    /**
     * Recalculate region in a document to four-int-coordinates
     * @param document
     * @param region
     * @param singleLine true, if the region covers one line only
     * @return four ints: begin line, begin column, end line, end column
     * @throws BadLocationException
     */
    public static int[] regionToLocation(IDocument document, IRegion region, boolean singleLine)
            throws BadLocationException
    {
        if (!singleLine)
        {
            throw new IllegalArgumentException("Not implemented");
        }

        int[] coordinates = new int[4];
        // location of the id found in the provided document
        int offset = region.getOffset();
        int length = region.getLength();
        // since the id is written as one word, we are in the same line
        coordinates[0] = document.getLineOfOffset(offset) + 1; // begin line
        coordinates[2] = document.getLineOfOffset(offset) + 1; // end line

        // the columns are relative to the offset of the line
        IRegion line = document.getLineInformationOfOffset(offset);
        coordinates[1] = offset - line.getOffset(); // begin column
        coordinates[3] = coordinates[1] + length; // end column

        // return the coordinates
        return coordinates;
    }

    /**
     * Create a map with marker parameters
     * @param config 
     * @param errorMessage
     * @param severityError
     * @return
     */
    public static Hashtable<String, Object> createMarkerDescription(String errorMessage, int severity)
    {
        Hashtable<String, Object> prop = new Hashtable<String, Object>();

        prop.put(IMarker.SEVERITY, new Integer(severity));
        prop.put(IMarker.MESSAGE, errorMessage);
        prop.put(TLC_MODEL_ERROR_MARKER_ATTRIBUTE_NAME, EMPTY_STRING);
        prop.put(TLC_MODEL_ERROR_MARKER_ATTRIBUTE_IDX, new Integer(0));
        prop.put(IMarker.LOCATION, EMPTY_STRING);
        prop.put(IMarker.CHAR_START, new Integer(0));
        prop.put(IMarker.CHAR_END, new Integer(0));
        return prop;
    }

    /**
     * Using the supplied findReplaceAdapter finds the name of the attribute 
     * (saved in the comment, previous to the region in which the error has been detected) 
     * 
     * @param document the document of the file containing the generated model .tla file
     * @param searchAdapter the search adapter on the document
     * @param message the error message
     * @param severity the error severity
     * @param coordinates coordinates in the document describing the area that is the id
     * 
     * @return a map object containing the information required for the marker installation:
     * <ul>
     *  <li>IMarker.SEVERITY</li>
     *  <li>IMarker.MESSAGE</li>
     *  <li>TLC_MODEL_ERROR_MARKER_ATTRIBUTE_NAME</li>
     *  <li>TLC_MODEL_ERROR_MARKER_ATTRIBUTE_IDX</li>
     *  <li>IMarker.LOCATION</li>
     *  <li>IMarker.CHAR_START</li>
     *  <li>IMarker.CHAR_END</li>
     * </ul> 
     * @throws CoreException if something goes wrong
     */
    public static Hashtable<String, Object> createMarkerDescription(IDocument document,
            FindReplaceDocumentAdapter searchAdapter, String message, int severity, int[] coordinates)
            throws CoreException
    {
        String attributeName;
        Region errorRegion = null;
        int attributeIndex = -1;
        try
        {
            // find the line in the document
            IRegion lineRegion = document.getLineInformation(coordinates[0] - 1);
            if (lineRegion != null)
            {
                int errorLineOffset = lineRegion.getOffset();

                // find the previous comment
                IRegion commentRegion = searchAdapter.find(errorLineOffset, ModelWriter.COMMENT, false, false, false,
                        false);

                // find the next separator
                IRegion separatorRegion = searchAdapter.find(errorLineOffset, ModelWriter.SEP, true, false, false,
                        false);
                if (separatorRegion != null && commentRegion != null)
                {
                    // find the first attribute inside of the
                    // comment
                    IRegion attributeRegion = searchAdapter.find(commentRegion.getOffset(), ModelWriter.ATTRIBUTE
                            + "[a-z]*[A-Z]*", true, false, false, true);
                    if (attributeRegion != null)
                    {
                        // get the attribute name without the
                        // attribute marker
                        attributeName = document.get(attributeRegion.getOffset(), attributeRegion.getLength())
                                .substring(ModelWriter.ATTRIBUTE.length());

                        // find the index
                        IRegion indexRegion = searchAdapter.find(attributeRegion.getOffset()
                                + attributeRegion.getLength(), ModelWriter.INDEX + "[0-9]+", true, false, false, true);
                        if (indexRegion != null && indexRegion.getOffset() < separatorRegion.getOffset())
                        {
                            // index value found
                            String indexString = document.get(indexRegion.getOffset(), indexRegion.getLength());
                            if (indexString != null && indexString.length() > 1)
                            {
                                try
                                {
                                    attributeIndex = Integer.parseInt(indexString.substring(1));
                                } catch (NumberFormatException e)
                                {
                                    throw new CoreException(new Status(IStatus.ERROR, TLCActivator.PLUGIN_ID,
                                            "Error during detection of the error position in MC.tla."
                                                    + "Error parsing the attribute index. " + message, e));
                                }
                            }
                        } else
                        {
                            // no index
                        }

                        // the first character of the next line
                        // after the comment

                        IRegion firstBlockLine = document.getLineInformation(document.getLineOfOffset(commentRegion
                                .getOffset()) + 1);
                        int beginBlockOffset = firstBlockLine.getOffset();
                        // get the user input
                        if (attributeName.equals(MODEL_PARAMETER_NEW_DEFINITIONS))
                        {
                            // there is no identifier in this
                            // block
                            // the user input starts directly
                            // from the first character
                        } else
                        {
                            // the id-line representing the
                            // identifier "id_number ==" comes
                            // first
                            // the user input starts only on the
                            // second line
                            // so adding the length of the
                            // id-line
                            beginBlockOffset = beginBlockOffset + firstBlockLine.getLength() + 1;
                        }

                        // calculate the error region

                        // end line coordinate
                        if (coordinates[2] == 0)
                        {
                            // not set
                            // mark one char starting from the
                            // begin column
                            errorRegion = new Region(errorLineOffset + coordinates[1] - beginBlockOffset, 1);
                        } else if (coordinates[2] == coordinates[0])
                        {
                            // equals to the begin line
                            // mark the actual error region
                            int length = coordinates[3] - coordinates[1];

                            errorRegion = new Region(errorLineOffset + coordinates[1] - beginBlockOffset,
                                    (length == 0) ? 1 : length);
                        } else
                        {
                            // the part of the first line from
                            // the begin column to the end
                            int summedLength = lineRegion.getLength() - coordinates[1];

                            // iterate over all full lines
                            for (int l = coordinates[0] + 1; l < coordinates[2]; l++)
                            {
                                IRegion line = document.getLineInformation(l - 1);
                                summedLength = summedLength + line.getLength();
                            }
                            // the part of the last line to the
                            // end column
                            summedLength += coordinates[3];

                            errorRegion = new Region(errorLineOffset + coordinates[1] - beginBlockOffset, summedLength);
                        }

                        // install the marker showing the
                        // information in the corresponding
                        // attribute (and index), at the given place

                    } else
                    {
                        // problem could not detect attribute
                        throw new CoreException(new Status(IStatus.ERROR, TLCActivator.PLUGIN_ID,
                                "Error during detection of the error position in MC.tla."
                                        + "Could not detect the attribute. " + message));
                    }
                } else
                {
                    // problem could not detect block
                    throw new CoreException(new Status(IStatus.ERROR, TLCActivator.PLUGIN_ID,
                            "Error during detection of the error position in MC.tla."
                                    + "Could not detect definition block. " + message));
                }
            } else
            {
                // problem could not detect line
                throw new CoreException(new Status(IStatus.ERROR, TLCActivator.PLUGIN_ID,
                        "Error during detection of the error position in MC.tla."
                                + "Could not data on specified location. " + message));
            }
        } catch (BadLocationException e)
        {
            throw new CoreException(new Status(IStatus.ERROR, TLCActivator.PLUGIN_ID,
                    "Error during detection of the error position in MC.tla." + "Accessing MC.tla file failed. "
                            + message, e));
        }

        // If the message refers to module MC, this should be replaced with
        // the location in the model.
        message = getMessageWithoutMC(message, attributeName, attributeIndex);

        // create the return object
        Hashtable<String, Object> props = new Hashtable<String, Object>();
        props.put(IMarker.SEVERITY, new Integer(severity));
        props.put(IMarker.MESSAGE, message);
        props.put(TLC_MODEL_ERROR_MARKER_ATTRIBUTE_NAME, attributeName);
        props.put(TLC_MODEL_ERROR_MARKER_ATTRIBUTE_IDX, new Integer(attributeIndex));
        props.put(IMarker.LOCATION, "");
        props.put(IMarker.CHAR_START, new Integer(errorRegion.getOffset()));
        props.put(IMarker.CHAR_END, new Integer(errorRegion.getOffset() + errorRegion.getLength()));

        return props;
    }

    /**
     * This method takes an error message generated by SANY for the
     * MC.tla file and attempts to remove the mention of the MC file and insert
     * the name of the model attribute and location within that attribute
     * where the parse error occured.
     * 
     * For example, the location in the message returned by SANY that says
     * "at line 25, column 2 in module MC" will be replaced with something
     * like "in Definition Overrides, line 2".
     * 
     * It is definitely possible that the set of expressions searched for by this method
     * is not exhaustive, so some messages will remain the same even if they mention the
     * MC file.
     * 
     * @param message the SANY error message for the MC file
     * @param attributeName the name of the model attribute where the error occured
     * @param attributeIndex the 0-based index of the error within the model attribute.
     * For example, if the second definition override caused an error, the attributeIndex
     * should be 1. It can be -1 if no index is found, in which case no information about
     * the location within the model attribute will be included in the message.
     * @return the message without MC location information and with model location information
     */
    private static String getMessageWithoutMC(String message, String attributeName, int attributeIndex)
    {
        if (message.indexOf("in module MC") != -1 || message.indexOf("of module MC") != -1)
        {
            // first possible expression
            String[] splitMessage = message.split("at line [0-9]{1,}, column [0-9]{1,} in module MC", 2);
            if (splitMessage.length != 2)
            {
                // split around other possibility
                splitMessage = message.split(
                        "line [0-9]{1,}, col [0-9]{1,} to line [0-9]{1,}, col [0-9]{1,} of module MC", 2);
            }
            if (splitMessage.length == 2)
            {
                String toReturn = splitMessage[0] + " in " + getSectionNameFromAttributeName(attributeName);
                if (attributeIndex != -1)
                {
                    // the exact location is known
                    toReturn = toReturn + " at line " + (attributeIndex + 1);
                }
                return toReturn + splitMessage[1];
            } else
            {
                // cannot find expression containing MC module
                // even though it is in the message
                return message;
            }
        } else
        {
            return message;
        }
    }

    /**
     * This gets the title of the section in the model editor
     * corresponding to the attributeName.
     * 
     * @param attributeName
     * @return
     */
    private static String getSectionNameFromAttributeName(String attributeName)
    {
        if (attributeName.equals(MODEL_CORRECTNESS_INVARIANTS))
        {
            return "Invariants";
        } else if (attributeName.equals(MODEL_CORRECTNESS_PROPERTIES))
        {
            return "Properties";
        } else if (attributeName.equals(MODEL_PARAMETER_ACTION_CONSTRAINT))
        {
            return "Action Contraint";
        } else if (attributeName.equals(MODEL_PARAMETER_CONSTRAINT))
        {
            return "Constraint";
        } else if (attributeName.equals(MODEL_PARAMETER_CONSTANTS))
        {
            return "What is the model?";
        } else if (attributeName.equals(MODEL_PARAMETER_DEFINITIONS))
        {
            return "Definition Override";
        } else if (attributeName.equals(MODEL_PARAMETER_NEW_DEFINITIONS))
        {
            return "Additional Definitions";
        } else if (attributeName.equals(MODEL_PARAMETER_MODEL_VALUES))
        {
            return "Model Values";
        } else if (attributeName.equals(MODEL_BEHAVIOR_CLOSED_SPECIFICATION))
        {
            return "Temporal formula";
        } else if (attributeName.equals(MODEL_BEHAVIOR_SEPARATE_SPECIFICATION_INIT))
        {
            return "Init";
        } else if (attributeName.equals(MODEL_BEHAVIOR_SEPARATE_SPECIFICATION_NEXT))
        {
            return "Next";
        } else if (attributeName.equals(MODEL_PARAMETER_VIEW))
        {
            return "View";
        } else if (attributeName.equals(Model.MODEL_EXPRESSION_EVAL))
        {
            return "Expression";
        }
        return attributeName;
    }

    /**
    /**
     * Find the IDs in the given text and return the array of 
     * regions pointing to those or an empty array, if no IDs were found.
     * An ID is scheme_timestamp, created by {@link ModelWriter#getValidIdentifier(String)} e.G. next_125195338522638000
     * @param text text containing IDs (error text)
     * @return array of regions or empty array
     */
    public static IRegion[] findIds(String text)
    {
        return ModelWriter.findIds(text);
    }

    /**
     * Finds the locations in the given text and return the array of 
     * regions pointing to those or an empty array, if no location were found.
     * A location is a pointer in the TLA file, e.G. "line 11, col 8 to line 14, col 26 of module Foo"
     * @param text text containing locations (error text)
     * @return array of regions or empty array
     */
    public static IRegion[] findLocations(String text)
    {
        if (text == null || text.length() == 0)
        {
            return new IRegion[0];
        }

        Matcher matcher = Location.LOCATION_MATCHER.matcher(text);
        Vector<IRegion> regions = new Vector<IRegion>();
        while (matcher.find())
        {
            regions.add(new Region(matcher.start(), matcher.end() - matcher.start()));
        }
        // look for this pattern also
        // this pattern appears when there
        // is an error evaluating a nested expression
        matcher = Location.LOCATION_MATCHER4.matcher(text);
        while (matcher.find())
        {
            regions.add(new Region(matcher.start(), matcher.end() - matcher.start()));
        }
        return regions.toArray(new IRegion[regions.size()]);
    }

    /**
     * Returns the OpDefNode with name equal to input string
     * Returns null if there is no such OpDefNode
     * @param name
     * @return
     */
    public static OpDefNode getOpDefNode(String name)
    {
        SpecObj specObj = ToolboxHandle.getCurrentSpec().getValidRootModule();
        /*
         * SpecObj can be null if the spec is unparsed.
         */
        if (specObj != null)
        {
            OpDefNode[] opDefNodes = specObj.getExternalModuleTable().getRootModule().getOpDefs();
            for (int j = 0; j < opDefNodes.length; j++)
            {
                if (opDefNodes[j].getName().toString().equals(name))
                {
                    return opDefNodes[j];
                }
            }
        }
        return null;
    }

    /**
     * Checks, whether a model attribute is a list 
     * @param attributeName name of the attribute, see {@link IModelConfigurationConstants}
     * @return true for invariants, properties, constants and definition overriders
     */
    public static boolean isListAttribute(String attributeName)
    {
        if (attributeName != null
                && (attributeName.equals(IModelConfigurationConstants.MODEL_CORRECTNESS_INVARIANTS)
                        || attributeName.equals(IModelConfigurationConstants.MODEL_CORRECTNESS_PROPERTIES)
                        || attributeName.equals(IModelConfigurationConstants.MODEL_PARAMETER_CONSTANTS) || attributeName
                        .equals(IModelConfigurationConstants.MODEL_PARAMETER_DEFINITIONS)))
        {
            return true;
        }
        return false;
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
     * Creates the files if they do not exist, and
     * sets the contents of each file equal to "".
     * 
     * @param files
     * @param monitor
     */
    public static void createOrClearFiles(final IFile[] files, IProgressMonitor monitor)
    {
        ISchedulingRule fileRule = MultiRule.combine(ResourceHelper.getModifyRule(files), ResourceHelper
                .getCreateRule(files));

        // create files
        try
        {
            ResourcesPlugin.getWorkspace().run(new IWorkspaceRunnable() {
                public void run(IProgressMonitor monitor) throws CoreException
                {
                    for (int i = 0; i < files.length; i++)
                    {
                        if (files[i].exists())
                        {
                            files[i].setContents(new ByteArrayInputStream("".getBytes()), IResource.DERIVED
                                    | IResource.FORCE, new SubProgressMonitor(monitor, 1));
                        } else
                        {
                            files[i].create(new ByteArrayInputStream("".getBytes()), IResource.DERIVED
                                    | IResource.FORCE, new SubProgressMonitor(monitor, 1));
                        }
                    }
                }

            }, fileRule, IWorkspace.AVOID_UPDATE, new SubProgressMonitor(monitor, 100));
        } catch (CoreException e)
        {
            TLCActivator.logError("Error creating files.", e);
        }

    }

    /**
     * Copies the module files that are extended by specRootFile into the
     * folder given by targetFolderPath.
     * @param specRootFile the file corresponding to the root module
     * @param targetFolderPath the path of the folder to which the extended modules are to be copied
     * @param monitor - the progress monitor
     * @param STEP the unit of work this corresponds to in the progress monitor 
     * @param project the project that contains the specRootFile
     * @throws CoreException
     */
    public static void copyExtendedModuleFiles(IFile specRootFile, IPath targetFolderPath, IProgressMonitor monitor,
            int STEP, IProject project) throws CoreException
    {
        // get the list of dependent modules
        List<String> extendedModules = ToolboxHandle.getExtendedModules(specRootFile.getName());

        // iterate and copy modules that are needed for the spec
        IFile moduleFile = null;
        for (int i = 0; i < extendedModules.size(); i++)
        {
            String module = extendedModules.get(i);
            // only take care of user modules
            if (ToolboxHandle.isUserModule(module))
            {
                moduleFile = ResourceHelper.getLinkedFile(project, module, false);
                if (moduleFile != null)
                {
                    moduleFile.copy(targetFolderPath.append(moduleFile.getProjectRelativePath()), IResource.DERIVED
                            | IResource.FORCE, new SubProgressMonitor(monitor, STEP / extendedModules.size()));
                }

                // TODO check the existence of copied files
            }
        }
    }

    /**
     * Determines if the spec with root module rootModuleName is dependent on a
     * module with the same name as the root module used for model checking.
     * 
     * @param rootModuleName
     * @return
     */
    public static boolean containsModelCheckingModuleConflict(String rootModuleName)
    {
        String rootModuleFileName = rootModuleName;
        if (!rootModuleName.endsWith(ResourceHelper.TLA_EXTENSION))
        {
            rootModuleFileName = ResourceHelper.getModuleFileName(rootModuleName);
        }
        List<String> extendedModuleNames = ToolboxHandle.getExtendedModules(rootModuleFileName);
        Iterator<String> it = extendedModuleNames.iterator();
        while (it.hasNext())
        {
            String moduleName = it.next();
            if (moduleName.equals(FILE_TLA))
            {
                return true;
            }
        }

        return false;
    }

    /**
     * Determines if the spec with root module rootModuleName is dependent on a
     * module with the same name as the root module used for trace exploration.
     * 
     * @param rootModuleName
     * @return
     */
    public static boolean containsTraceExplorerModuleConflict(String rootModuleName)
    {
        String rootModuleFileName = rootModuleName;
        if (!rootModuleName.endsWith(ResourceHelper.TLA_EXTENSION))
        {
            rootModuleFileName = ResourceHelper.getModuleFileName(rootModuleName);
        }
        List<String> extendedModuleNames = ToolboxHandle.getExtendedModules(rootModuleFileName);
        Iterator<String> it = extendedModuleNames.iterator();
        while (it.hasNext())
        {
            String moduleName = it.next();
            if (moduleName.equals(TE_FILE_TLA))
            {
                return true;
            }
        }

        return false;
    }
    
	public static String prettyPrintConstants(final Model model, String delim) throws CoreException {
		return prettyPrintConstants(model.getLaunchConfiguration(), delim, false);
	}

	public static String prettyPrintConstants(final ILaunchConfiguration config, String delim) throws CoreException {
		return prettyPrintConstants(config, delim, false);
	}
	
	public static String prettyPrintConstants(final Model model, String delim, boolean align) throws CoreException {
		return prettyPrintConstants(model.getLaunchConfiguration(), delim, align);
	}
	
	public static String prettyPrintConstants(final ILaunchConfiguration config, String delim, boolean align) throws CoreException {
		final List<Assignment> assignments = deserializeAssignmentList(
				config.getAttribute(IModelConfigurationConstants.MODEL_PARAMETER_CONSTANTS, new ArrayList<String>()));
		
		// Sort the assignments: Basic assignments alphabetically first, Set
		// model values including symmetric ones (alphabetically), Basic model
		// values.
		Collections.sort(assignments, new Comparator<Assignment>() {
			public int compare(Assignment a1, Assignment a2) {
				if (a1.isSimpleModelValue() && a2.isSimpleModelValue()) {
					return a1.getLeft().compareTo(a2.getLeft());
				} else if (a1.isSetOfModelValues() && a2.isSetOfModelValues()) {
					return a1.getLeft().compareTo(a2.getLeft());
				} else if (a1.isSimpleModelValue() && !a2.isModelValue()) {
					return 1;
				} else if (a1.isSimpleModelValue() && a2.isSetOfModelValues()) {
					return 1;
				} else if (a1.isSetOfModelValues() && !a2.isModelValue()) {
					return 1;
				} else if (a1.isSetOfModelValues() && a2.isSimpleModelValue()) {
					return -1;
				} else if (!a1.isModelValue() && a2.isModelValue()) {
					return -1;
				} else {
					// Basic assignments
					return a1.getLeft().compareTo(a2.getLeft());
				}
			}
		});
		
		// Determine the longest label of the assignment's left hand side.
		int longestLeft = 0;
		for (int i = 0; i < assignments.size() && align; i++) {
			final Assignment assignment = assignments.get(i);
			if (!assignment.isSimpleModelValue()) {
				longestLeft = Math.max(longestLeft, assignment.getLeft().length());
			}
		}

		final StringBuffer buf = new StringBuffer();
		for (int i = 0; i < assignments.size(); i++) {
			final Assignment assignment = assignments.get(i);
			if (assignment.isSimpleModelValue()) {
				buf.append("Model values: ");
				for (; i < assignments.size(); i++) {
					buf.append(assignments.get(i).prettyPrint());
					if (i < assignments.size() - 1) {
						buf.append(", ");
					}
				}
			} else if (align) {
				final int length = longestLeft - assignment.getLeft().length();
				final StringBuffer whitespaces = new StringBuffer(length);
				for (int j = 0; j < length; j++) {
					whitespaces.append(" ");
				}
				buf.append(assignment.prettyPrint(whitespaces.toString()));
				if (i < assignments.size() - 1) {
					buf.append(delim);
				}
			} else {
				buf.append(assignment.prettyPrint());
				if (i < assignments.size() - 1) {
					buf.append(delim);
				}
			}
		}
		return buf.toString();
	}
}
