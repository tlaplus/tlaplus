package org.lamport.tla.toolbox.tool.tlc.ui.editor.page.advanced;

import java.io.Closeable;
import java.io.IOException;
import java.util.Arrays;
import java.util.Hashtable;
import java.util.List;
import java.util.Vector;

import org.eclipse.core.runtime.CoreException;
import org.eclipse.jface.dialogs.IMessageProvider;
import org.eclipse.jface.text.Document;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.source.SourceViewer;
import org.eclipse.jface.viewers.TableViewer;
import org.eclipse.swt.SWT;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.eclipse.ui.forms.IManagedForm;
import org.eclipse.ui.forms.IMessageManager;
import org.eclipse.ui.forms.editor.FormEditor;
import org.eclipse.ui.forms.widgets.FormToolkit;
import org.eclipse.ui.forms.widgets.Section;
import org.eclipse.ui.forms.widgets.TableWrapData;
import org.eclipse.ui.forms.widgets.TableWrapLayout;
import org.lamport.tla.toolbox.tool.ToolboxHandle;
import org.lamport.tla.toolbox.tool.tlc.launch.IModelConfigurationConstants;
import org.lamport.tla.toolbox.tool.tlc.model.Assignment;
import org.lamport.tla.toolbox.tool.tlc.model.TypedSet;
import org.lamport.tla.toolbox.tool.tlc.ui.editor.DataBindingManager;
import org.lamport.tla.toolbox.tool.tlc.ui.editor.ModelEditor;
import org.lamport.tla.toolbox.tool.tlc.ui.editor.page.BasicFormPage;
import org.lamport.tla.toolbox.tool.tlc.ui.editor.page.MainModelPage;
import org.lamport.tla.toolbox.tool.tlc.ui.editor.part.ValidateableOverridesSectionPart;
import org.lamport.tla.toolbox.tool.tlc.ui.editor.part.ValidateableSectionPart;
import org.lamport.tla.toolbox.tool.tlc.ui.util.DirtyMarkingListener;
import org.lamport.tla.toolbox.tool.tlc.ui.util.FormHelper;
import org.lamport.tla.toolbox.tool.tlc.ui.util.SemanticHelper;
import org.lamport.tla.toolbox.util.IHelpConstants;
import org.lamport.tla.toolbox.util.UIHelper;

import tla2sany.modanalyzer.SpecObj;
import tla2sany.semantic.OpDefNode;

/**
 * Where we are sticking "advanced" model options, not including those related to TLC execution.
 * 
 * @author Simon Zambrovski
 */
public class AdvancedModelPage extends BasicFormPage implements Closeable {
    public static final String ID = "advancedModelPage";

    
    private SourceViewer constraintSource;
    private SourceViewer actionConstraintSource;
    private SourceViewer newDefinitionsSource;
    private SourceViewer modelValuesSource;
        
    private TableViewer definitionsTable;

    /**
     * Constructs the page
     * 
     * @param editor
     */
	public AdvancedModelPage(final FormEditor editor) {
        super(editor, ID, "Spec Options",
        		"icons/full/advanced_model_options_" + IMAGE_TEMPLATE_TOKEN + ".png");
        helpId = IHelpConstants.ADVANCED_MODEL_PAGE;
    }

    /**
     * Loads data from the model
     */
	@Override
	protected void loadData() throws CoreException {
        // definition overrides
        List<String> definitions = getModel().getAttribute(MODEL_PARAMETER_DEFINITIONS, new Vector<String>());
        FormHelper.setSerializedInput(definitionsTable, definitions);

        // new definitions
        String newDefinitions = getModel().getAttribute(MODEL_PARAMETER_NEW_DEFINITIONS, EMPTY_STRING);
        newDefinitionsSource.setDocument(new Document(newDefinitions));

        // advanced model values
        String modelValues = getModel().getAttribute(MODEL_PARAMETER_MODEL_VALUES, EMPTY_STRING);
        modelValuesSource.setDocument(new Document(modelValues));

        // constraint
        String constraint = getModel().getAttribute(MODEL_PARAMETER_CONSTRAINT, EMPTY_STRING);
        constraintSource.setDocument(new Document(constraint));

        // action constraint
        String actionConstraint = getModel().getAttribute(MODEL_PARAMETER_ACTION_CONSTRAINT, EMPTY_STRING);
        actionConstraintSource.setDocument(new Document(actionConstraint));
    }

    /**
     * Save data back to config
     */
	@Override
	public void commit(final boolean onSave) {
        // definitions
        List<String> definitions = FormHelper.getSerializedInput(definitionsTable);
        getModel().setAttribute(MODEL_PARAMETER_DEFINITIONS, definitions);

        // new definitions
        String newDefinitions = FormHelper.trimTrailingSpaces(newDefinitionsSource.getDocument().get());
        getModel().setAttribute(MODEL_PARAMETER_NEW_DEFINITIONS, newDefinitions);

        // model values
        String modelValues = FormHelper.trimTrailingSpaces(modelValuesSource.getDocument().get());
        TypedSet modelValuesSet = TypedSet.parseSet(modelValues);
        getModel().setAttribute(MODEL_PARAMETER_MODEL_VALUES, modelValuesSet.toString());

        // constraint formula
        String constraintFormula = FormHelper.trimTrailingSpaces(constraintSource.getDocument().get());
        getModel().setAttribute(MODEL_PARAMETER_CONSTRAINT, constraintFormula);

        // action constraint formula
        String actionConstraintFormula = FormHelper.trimTrailingSpaces(actionConstraintSource.getDocument().get());
        getModel().setAttribute(MODEL_PARAMETER_ACTION_CONSTRAINT, actionConstraintFormula);
      
        super.commit(onSave);
    }

    /**
     * Validate the page's state.
     */
	@Override
	public void validatePage(final boolean switchToErrorPage) {
        if (getManagedForm() == null)
        {
            return;
        }
        IMessageManager mm = getManagedForm().getMessageManager();
        mm.setAutoUpdate(false);

        ModelEditor modelEditor = (ModelEditor) getEditor();

        // clean old messages
        // this is now done in validateRunnable of
        // ModelEditor
        // mm.removeAllMessages();
        // make the run possible
        setComplete(true);

        // setup the names from the current page
        getLookupHelper().resetModelNames(this);
        
        // get data binding manager
        final DataBindingManager dm = getDataBindingManager();

        // check the model values
		final IDocument document = modelValuesSource.getDocument();
		if (document != null) {
			final TypedSet modelValuesSet = TypedSet.parseSet(FormHelper.trimTrailingSpaces(document.get()));
			if (modelValuesSet.getValueCount() > 0)
			{
				// there were values defined
				
				// check if those are numbers?
				/*
				 * if (modelValuesSet.hasANumberOnlyValue()) {
				 * mm.addMessage("modelValues1",
				 * "A model value can not be an number", modelValuesSet,
				 * IMessageProvider.ERROR, modelValuesSource.getControl());
				 * setComplete(false); }
				 */
				List<String> values = modelValuesSet.getValuesAsList();
				// check list of model values if these are already used
				validateUsage(MODEL_PARAMETER_MODEL_VALUES, values, "modelValues2_", "A model value",
						"Advanced Model Values", true);
				// check whether the model values are valid ids
				validateId(MODEL_PARAMETER_MODEL_VALUES, values, "modelValues2_", "A model value");
				
				// get widget for model values
				Control widget = UIHelper.getWidget(dm.getAttributeControl(MODEL_PARAMETER_MODEL_VALUES));
				
				// check if model values are config file keywords
				for (int j = 0; j < values.size(); j++)
				{
					String value = (String) values.get(j);
					if (SemanticHelper.isConfigFileKeyword(value))
					{
						modelEditor.addErrorMessage(value, "The toolbox cannot handle the model value " + value + ".", this
								.getId(), IMessageProvider.ERROR, widget);
						setComplete(false);
					} 
//                else {
//                   // Call of removeErrorMessage added by LL on 21 Mar 2013
//                   // However, it did nothing because the value argument is a string
					// currently in the field, which is not going to be the one that
					// caused any existing error message.
//                   modelEditor.removeErrorMessage(value, widget);
//                }
				}
				
			}
		}

        // opDefNodes necessary for determining if a definition in definition
        // overrides is still in the specification
        SpecObj specObj = ToolboxHandle.getCurrentSpec().getValidRootModule();
        OpDefNode[] opDefNodes = null;
        if (specObj != null)
        {
            opDefNodes = specObj.getExternalModuleTable().getRootModule().getOpDefs();
        }
        Hashtable<String, OpDefNode> nodeTable = new Hashtable<String, OpDefNode>();

        if (opDefNodes != null)
        {
            for (int j = 0; j < opDefNodes.length; j++)
            {
                String key = opDefNodes[j].getName().toString();
                nodeTable.put(key, opDefNodes[j]);
            }
        }

        // get widget for definition overrides
        Control widget = UIHelper.getWidget(dm.getAttributeControl(MODEL_PARAMETER_DEFINITIONS));
        mm.removeMessages(widget);
        // check the definition overrides
        @SuppressWarnings("unchecked")
		List<Assignment> definitions = (List<Assignment>) definitionsTable.getInput();
        if (definitions != null) {
            for (int i = 0; i < definitions.size(); i++)
            {
                Assignment definition = definitions.get(i);
                List<String> values = Arrays.asList(definition.getParams());
                // check list of parameters
                validateUsage(MODEL_PARAMETER_DEFINITIONS, values, "param1_", "A parameter name", "Definition Overrides",
                        false);
                // check whether the parameters are valid ids
                validateId(MODEL_PARAMETER_DEFINITIONS, values, "param1_", "A parameter name");

                // The following if test was added by LL on 11 Nov 2009 to prevent an unparsed
                // file from producing bogus error messages saying that overridden definitions
                // have been removed from the spec.
                if (opDefNodes != null)
                {
                    // Note added by LL on 21 Mar 2013:  We do not remove error messages
                    // for overridden definitions that are set by this code because doing so 
                    // may remove error messages set for these definitions by checks elsewhere
                    // in the code.

                    // check if definition still appears in root module
                    if (!nodeTable.containsKey(definition.getLabel()))
                    {
                        // the following would remove
                        // the definition override from the table
                        // right now, an error message appears instead
                        // definitions.remove(i);
                        // definitionsTable.setInput(definitions);
                        // dm.getSection(DEF_OVERRIDES_PART).markDirty();
                        modelEditor.addErrorMessage(definition.getLabel(), "The defined symbol "
                                + definition.getLabel().substring(definition.getLabel().lastIndexOf("!") + 1)
                                + " has been removed from the specification."
                                + " It must be removed from the list of definition overrides.", this.getId(),
                                IMessageProvider.ERROR, widget);
                        setComplete(false);
                    } else
                    {
                        // add error message if the number of parameters has changed
                        OpDefNode opDefNode = (OpDefNode) nodeTable.get(definition.getLabel());
                        if (opDefNode.getSource().getNumberOfArgs() != definition.getParams().length)
                        {
                            modelEditor.addErrorMessage(definition.getLabel(), "Edit the definition override for "
                                    + opDefNode.getSource().getName() + " to match the correct number of arguments.", this
                                    .getId(), IMessageProvider.ERROR, widget);
                            setComplete(false);
                        }
                    }
                }
            }
            for (int j = 0; j < definitions.size(); j++)
            {
                Assignment definition = (Assignment) definitions.get(j);
                String label = definition.getLabel();
                if (SemanticHelper.isConfigFileKeyword(label))
                {
                    modelEditor.addErrorMessage(label, "The toolbox cannot override the definition of " + label
                            + " because it is a configuration file keyword.", this.getId(), IMessageProvider.ERROR, widget);
                    setComplete(false);
                }
            }
        }
        
		final MainModelPage mmp = (MainModelPage) getModelEditor().getFormPage(MainModelPage.ID);
		if (mmp.hasLivenessProperty()) {
			if (!FormHelper.trimTrailingSpaces(constraintSource.getDocument().get()).isEmpty()) {
				modelEditor.addErrorMessage("constraintSource", "Declaring state constraints during liveness checking is dangerous: "
								+ "Please read\nsection 14.3.5 on page 247 of Specifying Systems (https://lamport.azurewebsites.net/tla/book.html)"
								+ "\nand the optionally discussion at https://discuss.tlapl.us/msg00994.html for more details.",
						this.getId(), IMessageProvider.INFORMATION,
						UIHelper.getWidget(dm.getAttributeControl(MODEL_PARAMETER_CONSTRAINT)));
				expandSection(dm.getSectionForAttribute(MODEL_PARAMETER_CONSTRAINT));
			}
			if (!FormHelper.trimTrailingSpaces(actionConstraintSource.getDocument().get()).isEmpty()) {
				modelEditor.addErrorMessage("actionConstraintSource", "Declaring action constraints during liveness checking is dangerous: "
						+ "Please read\nsection 14.3.5 on page 247 of Specifying Systems (https://lamport.azurewebsites.net/tla/book.html)"
						+ "\nand optionally the discussion at https://discuss.tlapl.us/msg00994.html for more details.",
					this.getId(), IMessageProvider.INFORMATION,
						UIHelper.getWidget(dm.getAttributeControl(MODEL_PARAMETER_ACTION_CONSTRAINT)));
				expandSection(dm.getSectionForAttribute(MODEL_PARAMETER_ACTION_CONSTRAINT));
			}
		}

        mm.setAutoUpdate(true);
        
        super.validatePage(switchToErrorPage);
    }

    /**
     * Creates the UI
     * 
     * Its helpful to know what the standard SWT widgets look like.
     * Pictures can be found at http://www.eclipse.org/swt/widgets/
     * 
     * Layouts are used throughout this method.
     * A good explanation of layouts is given in the article
     * http://www.eclipse.org/articles/article.php?file=Article-Understanding-Layouts/index.html
     */
	@Override
	protected void createBodyContent(final IManagedForm managedForm) {
        final DataBindingManager dm = getDataBindingManager();
        final int sectionFlags = Section.TITLE_BAR | Section.DESCRIPTION | Section.TREE_NODE | Section.EXPANDED;

        final FormToolkit toolkit = managedForm.getToolkit();
        final Composite body = managedForm.getForm().getBody();

        GridLayout gl;
        GridData gd;
        TableWrapData twd;

        TableWrapLayout twl = new TableWrapLayout();
        twl.leftMargin = 0;
        twl.rightMargin = 0;
        twl.numColumns = 2;
        body.setLayout(twl);

        // left
        final Composite left = toolkit.createComposite(body);
        gl = new GridLayout(1, false);
        gl.marginHeight = 0;
        gl.marginWidth = 0;
        left.setLayout(gl);
        twd = new TableWrapData(TableWrapData.FILL_GRAB);
        twd.grabHorizontal = true;
        left.setLayoutData(twd);

        // right
        final Composite right = toolkit.createComposite(body);
        gl = new GridLayout(1, false);
        gl.marginHeight = 0;
        gl.marginWidth = 0;
        right.setLayout(gl);
        twd = new TableWrapData(TableWrapData.FILL_GRAB);
        twd.grabHorizontal = true;
        right.setLayoutData(twd);

        Section section;

        // ---------------------------------------------------------------
        // new definitions

        section = FormHelper.createSectionComposite(left, "Additional Definitions",
                        "Definitions required for the model checking, in addition to the definitions in the specification modules.",
                        toolkit, sectionFlags, getExpansionListener());
        ValidateableSectionPart newDefinitionsPart = new ValidateableSectionPart(section, this, SEC_NEW_DEFINITION);
        managedForm.addPart(newDefinitionsPart);
        DirtyMarkingListener newDefinitionsListener = new DirtyMarkingListener(newDefinitionsPart, true);

        gd = new GridData();
        gd.horizontalAlignment = SWT.FILL;
        gd.grabExcessHorizontalSpace = true;
        section.setLayoutData(gd);

        Composite newDefinitionsArea = (Composite) section.getClient();
        newDefinitionsSource = FormHelper.createFormsSourceViewer(toolkit, newDefinitionsArea, SWT.V_SCROLL);
        // layout of the source viewer
        twd = new TableWrapData(TableWrapData.FILL);
        twd.heightHint = 60;
        twd.grabHorizontal = true;
        newDefinitionsSource.getTextWidget().setLayoutData(twd);
        newDefinitionsSource.addTextListener(newDefinitionsListener);
        newDefinitionsSource.getTextWidget().addFocusListener(focusListener);

        dm.bindAttribute(MODEL_PARAMETER_NEW_DEFINITIONS, newDefinitionsSource, newDefinitionsPart);

        // ---------------------------------------------------------------
        // definition overwrite
        // Change added by LL on 10 April 2011 to cause model page to be created with the 
        // definitions override section open iff there are overridden definitions.  This is
        // done so the user will be aware of automatically generated overrides.
        // 
        int expand = 0;
        try
        {
           List<String> definitions = getModel().getAttribute(MODEL_PARAMETER_DEFINITIONS, new Vector<String>());
            if ((definitions != null) && (definitions.size() != 0)) {
                expand = Section.EXPANDED;
            }
        } catch (CoreException e)
        {
            // Just ignore this since I have no idea what an exception might mean.
        }
        
        final ValidateableOverridesSectionPart definitionsPart = new ValidateableOverridesSectionPart(right,
                "Definition Override", "Directs TLC to use alternate definitions for operators.", toolkit,
                sectionFlags | expand, this);

        managedForm.addPart(definitionsPart);
        // layout
        gd = new GridData();
        gd.horizontalAlignment = SWT.FILL;
        gd.grabExcessHorizontalSpace = true;
        definitionsPart.getSection().setLayoutData(gd);
        definitionsTable = definitionsPart.getTableViewer();
        dm.bindAttribute(MODEL_PARAMETER_DEFINITIONS, definitionsTable, definitionsPart);

        // ---------------------------------------------------------------
        // modelValues
        section = FormHelper.createSectionComposite(left, "Model Values", "An additional set of model values.",
                toolkit, sectionFlags, getExpansionListener());
        ValidateableSectionPart modelValuesPart = new ValidateableSectionPart(section, this, SEC_MODEL_VALUES);
        managedForm.addPart(modelValuesPart);
        DirtyMarkingListener modelValuesListener = new DirtyMarkingListener(modelValuesPart, true);
        gd = new GridData();
        gd.horizontalAlignment = SWT.FILL;
        gd.grabExcessHorizontalSpace = true;
        section.setLayoutData(gd);

        Composite modelValueArea = (Composite) section.getClient();
        modelValuesSource = FormHelper.createFormsSourceViewer(toolkit, modelValueArea, SWT.V_SCROLL);
        // layout of the source viewer
        twd = new TableWrapData(TableWrapData.FILL);
        twd.heightHint = 60;
        twd.grabHorizontal = true;
        modelValuesSource.getTextWidget().setLayoutData(twd);
        modelValuesSource.addTextListener(modelValuesListener);
        modelValuesSource.getTextWidget().addFocusListener(focusListener);
        dm.bindAttribute(MODEL_PARAMETER_MODEL_VALUES, modelValuesSource, modelValuesPart);

        // ---------------------------------------------------------------
        // action constraint
        section = FormHelper.createSectionComposite(right, "Action Constraint",
                "A formula restricting a transition if its evaluation is not satisfied.", toolkit, sectionFlags,
                getExpansionListener());
        ValidateableSectionPart actionConstraintPart = new ValidateableSectionPart(section, this, SEC_ACTION_CONSTRAINT);
        managedForm.addPart(actionConstraintPart);
        DirtyMarkingListener actionConstraintListener = new DirtyMarkingListener(actionConstraintPart, true);

        gd = new GridData();
        gd.horizontalAlignment = SWT.FILL;
        gd.grabExcessHorizontalSpace = true;
        section.setLayoutData(gd);

        Composite actionConstraintArea = (Composite) section.getClient();
        actionConstraintSource = FormHelper.createFormsSourceViewer(toolkit, actionConstraintArea, SWT.V_SCROLL);
        // layout of the source viewer
        twd = new TableWrapData(TableWrapData.FILL);
        twd.heightHint = 60;
        twd.grabHorizontal = true;
        actionConstraintSource.getTextWidget().setLayoutData(twd);
        actionConstraintSource.addTextListener(actionConstraintListener);
        actionConstraintSource.getTextWidget().addFocusListener(focusListener);
        dm.bindAttribute(MODEL_PARAMETER_ACTION_CONSTRAINT, actionConstraintSource, actionConstraintPart);

        // ---------------------------------------------------------------
        // constraint
        section = FormHelper.createSectionComposite(body, "State Constraint",
                "A formula restricting the possible states by a state predicate.", toolkit,
                sectionFlags, getExpansionListener());
        ValidateableSectionPart constraintPart = new ValidateableSectionPart(section, this, SEC_STATE_CONSTRAINT);
        managedForm.addPart(constraintPart);
        DirtyMarkingListener constraintListener = new DirtyMarkingListener(constraintPart, true);

        twd = new TableWrapData();
        twd.colspan = 2;
        twd.grabHorizontal = true;
        twd.align = TableWrapData.FILL;
        section.setLayoutData(twd);

        Composite constraintArea = (Composite) section.getClient();
        constraintSource = FormHelper.createFormsSourceViewer(toolkit, constraintArea, SWT.V_SCROLL);
        // layout of the source viewer
        twd = new TableWrapData(TableWrapData.FILL);
        twd.heightHint = 60;
        twd.grabHorizontal = true;
        constraintSource.getTextWidget().setLayoutData(twd);
        constraintSource.addTextListener(constraintListener);
        constraintSource.getTextWidget().addFocusListener(focusListener);
        dm.bindAttribute(MODEL_PARAMETER_CONSTRAINT, constraintSource, constraintPart);

        // add section ignoring listeners
        dirtyPartListeners.add(newDefinitionsListener);
        dirtyPartListeners.add(actionConstraintListener);
        dirtyPartListeners.add(modelValuesListener);
        dirtyPartListeners.add(constraintListener);
    }

	@Override
	public void close() throws IOException {
		final int openTabState = getModel().getOpenTabsValue();
		getModelEditor().updateOpenTabsState(openTabState & ~IModelConfigurationConstants.EDITOR_OPEN_TAB_ADVANCED_MODEL);
		
        final DataBindingManager dm = getDataBindingManager();
        dm.unbindSectionAndAttribute(MODEL_PARAMETER_ACTION_CONSTRAINT);
        dm.unbindSectionAndAttribute(MODEL_PARAMETER_CONSTRAINT);
        dm.unbindSectionAndAttribute(MODEL_PARAMETER_DEFINITIONS);
        dm.unbindSectionAndAttribute(MODEL_PARAMETER_MODEL_VALUES);
        dm.unbindSectionAndAttribute(MODEL_PARAMETER_NEW_DEFINITIONS);
	}
}
