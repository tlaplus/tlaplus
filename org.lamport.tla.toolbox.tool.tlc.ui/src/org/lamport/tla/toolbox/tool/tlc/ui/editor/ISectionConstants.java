package org.lamport.tla.toolbox.tool.tlc.ui.editor;


/**
 * Section definition constants
 * <br>
 * This interface contains identifiers given to sections of the three
 * Model Editor pages. An identifier is used in order to uniquely identify
 * the section. The DataBindingManager facility, provided by the editor is 
 * storing the information about "what section is located on what page" and "what 
 * attribute is displayed in what section". Using the ids the section can be expanded or collapsed.
 * This is used in case if an error is detected and the error marker is installed on the corresponding field.
 * 
 * Note: The following was deleted by Simon Z, but re-added by LL because
 * there is no reason to throw away a comment that provides information--no
 * matter how useless that information might seem to be.
 * 
 * As an example, here is how the constant SEC_WHAT_IS_THE_MODEL is used. 
 * The constant is given as an argument to the ValidateableConstantSectionPart
 * constructor in the createBodyContent method of MainModelPage, which gives it 
 * to its super, the ValidateableTableSectionPart constructor, which calls
 * page.getDataBindingManager().bindSection that puts it in the hash table
 * sectionsForPage with key the id of the page and value a vector of
 * all section ids that were registered with bindSection.  That value is
 * read only by DataBindingManager.setAllSectionsEnabled which is called
 * in BasicFormPage.setEnabled, which is called by BasicFormPage.refresh,
 * which is called by:
 *  - BasicFormPage.createFormContent
 *  - a listener installed in ModelEditor by a ModelHelper.installModelModificationResourceChangeListener
 *  - MainModelPage.refresh() 
 * @author Simon Zambrovski
 * @version $Id$
 */
public interface ISectionConstants
{
    // sections of the first page
    public final static String SEC_WHAT_IS_THE_SPEC = "__what_is_the_spec";
    public final static String SEC_WHAT_TO_CHECK = "__what_to_check";
    public final static String SEC_WHAT_TO_CHECK_INVARIANTS = "__what_to_check_invariants";
    public final static String SEC_WHAT_TO_CHECK_PROPERTIES = "__what_to_check_properties";
    
    public final static String SEC_WHAT_IS_THE_MODEL = "__what_is_the_model";
    public final static String SEC_HOW_TO_RUN = "__how_to_run";
    // section on the second page
    public final static String SEC_NEW_DEFINITION = "__additional_definition";
    public final static String SEC_DEFINITION_OVERRIDE = "__definition_override";
    public final static String SEC_STATE_CONSTRAINT = "__state_constraints";
    public final static String SEC_ACTION_CONSTRAINT = "__action_constraints";
    public final static String SEC_MODEL_VALUES = "__model_values";
    public final static String SEC_LAUNCHING_SETUP = "__launching_setup";

    // sections of the third page
    public final static String SEC_PROGRESS = "__progress";
    public final static String SEC_OUTPUT = "__output";
    public static final String SEC_COVERAGE = "__coverage";
    public static final String SEC_ERRORS = "__errors";

}