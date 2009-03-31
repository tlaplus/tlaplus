package org.lamport.tla.toolbox.tool.tlc.launch;

/**
 * @author Simon Zambrovski
 * @version $Id$
 */
public interface IModelConfigurationConstants extends IConfigurationConstants
{
    /**
     * flag showing if one closed formula is used
     */
    public static final String MODEL_BEHAVIOR_IS_CLOSED_SPEC_USED = "modelBehaviorIsClosedFormulaUsed"; 
    /**
     * formula which points behavior specification
     */
    public static final String MODEL_BEHAVIOR_CLOSED_SPECIFICATION = "modelBehaviorSpec";
    /**
     * formula which points init part of the specification
     */
    public static final String MODEL_BEHAVIOR_SEPARATE_SPECIFICATION_INIT = "modelBehaviorInit";
    /**
     * formula which points next part of the specification
     */
    public static final String MODEL_BEHAVIOR_SEPARATE_SPECIFICATION_NEXT = "modelBehaviorNext";
    /**
     * formula which points fairness part of the specification
     */
    public static final String MODEL_BEHAVIOR_SEPARATE_SPECIFICATION_FAIRNESS = "modelBehaviorFairness";
    /**
     * flag for checking deadlock
     */
    public static final String MODEL_CORRECTNESS_CHECK_DEADLOCK = "modelCorrectnessCheckDeadlock";
    /**
     * invariants list
     */
    public static final String MODEL_CORRECTNESS_INVARIANTS = "modelCorrectnessInvariants";
    /**
     * property lists
     */
    public static final String MODEL_CORRECTNESS_PROPERTIES = "modelCorrectnessProperties";
    /**
     * init list
     */
    public static final String MODEL_CORRECTNESS_INIT = "modelCorrectnessInit";
    /**
     * action list
     */
    public static final String MODEL_CORRECTNESS_ACTIONS = "modelCorrectnessActions";
    /**
     * action constraints list
     */
    public static final String MODEL_CORRECTNESS_ACTION_CONSTRAINTS = "modelCorrectnessActionConstraints";
    /**
     * constant list 
     */
    public static final String MODEL_PARAMETER_CONSTANTS = "modelParameterConstants";
    /**
     * symmetry list
     */
    public static final String MODEL_PARAMETER_SYMMETRY = "modelParameterSymmetry";
    /**
     * definitions list
     */
    public static final String MODEL_PARAMETER_DEFINITIONS = "modelParameterDefinitions";
    /**
     * new definitions list
     */
    public static final String MODEL_PARAMETER_NEW_DEFINITIONS = "modelParameterNewDefinitions";
    /**
     * constraint 
     */
    public static final String MODEL_PARAMETER_CONTRAINT = "modelParameterContraint";
    /**
     * TODO change to another editors
     */
    public static final String MODEL_MODEL_VALUES = "modelModelValues";
}
