package org.lamport.tla.toolbox.tool.tlc.ui.editor;


/**
 * Section definitions
 * @author Simon Zambrovski
 * @version $Id$
 */
public interface ISectionManager
{
    // sections of the first page
    public final static String SEC_WHAT_IS_THE_SPEC = "__what_is_the_spec";
    public final static String SEC_WHAT_TO_CHECK = "__what_to_check";
    public final static String SEC_WHAT_IS_THE_MODEL = "__what_is_the_model";
    public final static String SEC_HOW_TO_RUN = "__how_to_run";
    // section on the second page
    public final static String SEC_ADDITIONAL_DEFINITION = "__additional_definition";
    public final static String SEC_DEFINITION_OVERRIDE = "__definition_override";
    public final static String SEC_STATE_CONSTRAINT = "__state_constraints";
    public final static String SEC_ACTION_CONSTRAINT = "__action_constraints";
    public final static String SEC_MODEL_VALUES = "__model_values";
    public final static String SEC_LAUNCHING_SETUP = "__launching_setup";

    // sections of the third page
    public final static String SEC_PROGRESS = "__progress";
    public final static String SEC_OUTPUT = "__output";

}