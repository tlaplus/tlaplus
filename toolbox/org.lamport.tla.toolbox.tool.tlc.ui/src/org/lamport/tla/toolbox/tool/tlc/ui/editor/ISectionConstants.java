package org.lamport.tla.toolbox.tool.tlc.ui.editor;


/**
 * Section definition constants
 * <br>
 * This interface contains identifiers given to sections of the three
 * Model Editor pages. An identifier is used in order to uniquely identify
 * the section. The {@link DataBindingManager} facility, provided by the editor is 
 * storing the information about "what section is located on what page" and "what 
 * attribute is displayed in what section". Using the ids the section can be expanded or collapsed.
 * This is used in case if an error is detected and the error marker is installed on the corresponding field.
 *  
 * As an example, here is how the constant SEC_WHAT_IS_THE_MODEL is used. 
 * The constant is given as an argument to the ValidateableConstantSectionPart
 * constructor in the createBodyContent method of MainModelPage, which gives it 
 * to its super, the ValidateableTableSectionPart constructor, which calls
 * page.getDataBindingManager().bindSection that puts it in the hash table
 * sectionsForPage with key the id of the page and value a vector of
 * all section ids that were registered with bindSection.  That value is e.G.
 * read by DataBindingManager.setAllSectionsEnabled which is called
 * in BasicFormPage.setEnabled, which is called by BasicFormPage.refresh,
 * which is called by:
 *  - BasicFormPage.createFormContent
 *  - a listener installed in ModelEditor by a ModelHelper.installModelModificationResourceChangeListener
 *  - MainModelPage.refresh() 
 *
 * @see {@link DataBindingManager}
 * @author Simon Zambrovski, Leslie Lamport
 * @version $Id$
 */
public interface ISectionConstants
{
    // sections of the Main page
    public final static String SEC_COMMENTS = "__what_is_the_description";

    public final static String SEC_WHAT_IS_THE_SPEC = "__what_is_the_spec";
    public final static String SEC_WHAT_TO_CHECK = "__what_to_check";
    public final static String SEC_WHAT_TO_CHECK_INVARIANTS = "__what_to_check_invariants";
    public final static String SEC_WHAT_TO_CHECK_PROPERTIES = "__what_to_check_properties";
    
    public final static String SEC_WHAT_IS_THE_MODEL = "__what_is_the_model";
    public final static String SEC_HOW_TO_RUN = "__how_to_run";
    
    
    // sections on the Spec Options page
    public final static String SEC_NEW_DEFINITION = "__additional_definition";
    public final static String SEC_DEFINITION_OVERRIDE = "__definition_override";
    public final static String SEC_STATE_CONSTRAINT = "__state_constraints";
    public final static String SEC_ACTION_CONSTRAINT = "__action_constraints";
    public final static String SEC_MODEL_VALUES = "__model_values";
    
    
    // sections on the TLC Options page
    public final static String SEC_TLCOPT_CONFIGURATION = "__tlc_opt_config";
    public final static String SEC_TLCOPT_CHECK_MODE = "__tlc_opt_check_mode";
    public final static String SEC_TLCOPT_FEATURES = "__tlc_opt_features";
    public final static String SEC_TLCOPT_PARAMS = "__tlc_opt_params";

    
    // sections of the Results page
    public final static String SEC_GENERAL = "__general"; // General Section
    public final static String SEC_OUTPUT = "__output"; // User output
    public static final String SEC_STATISTICS = "__coverage"; // Statistics
    public static final String SEC_ERRORS = "__errors"; 
    public static final String SEC_PROGRESS = "__progress"; // Progress output
    public static final String SEC_EXPRESSION = "__expression"; // Eval Constant Expressions

}