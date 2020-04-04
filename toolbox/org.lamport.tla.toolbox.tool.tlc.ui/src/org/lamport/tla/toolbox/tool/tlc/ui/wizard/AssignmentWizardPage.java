package org.lamport.tla.toolbox.tool.tlc.ui.wizard;

import org.eclipse.jface.text.Document;
import org.eclipse.jface.text.source.SourceViewer;
import org.eclipse.jface.wizard.WizardPage;
import org.eclipse.swt.SWT;
import org.eclipse.swt.custom.StyledText;
import org.eclipse.swt.events.ModifyEvent;
import org.eclipse.swt.events.ModifyListener;
import org.eclipse.swt.events.SelectionAdapter;
import org.eclipse.swt.events.SelectionEvent;
import org.eclipse.swt.events.SelectionListener;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Button;
import org.eclipse.swt.widgets.Combo;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.ui.PlatformUI;
import org.lamport.tla.toolbox.tool.tlc.ui.util.FormHelper;
import org.lamport.tla.toolbox.tool.tlc.util.ModelHelper;
import org.lamport.tla.toolbox.util.UIHelper;

import tla2sany.semantic.OpDefNode;
import tlc2.model.Assignment;
import tlc2.model.TypedSet;

/**
 * @author Simon Zambrovski
 * @version $Id$
 */
public class AssignmentWizardPage extends WizardPage
{
    public static final String CONSTANT_WIZARD_ID = "constant_assignment_wizard";
    public static final String DEF_OVERRIDE_WIZARD_ID = "definition_override_wizard";
    private LabeledListComposite paramComposite;
    private SourceViewer source;
    private final int fieldFlags;
    private final String helpId; // The id of the help context for this wizard page

    private Button optionOrdinaryValue;

    private Button optionModelValue = null;

    private Button optionSetModelValues;
    private Button flagSymmetricalSet;
    private Combo smvTypeCombo;
    private Button optionSMVUntyped;
    
    // selection adapter reacting to set of value typing radio choice
    final private SelectionListener typingOptionSelectionAdapter = new SelectionAdapter() {
        @Override
        public void widgetSelected(SelectionEvent e)
        {
            smvTypeCombo.setEnabled(optionSMVUntyped.getSelection());
        }
    };

    
    // selection adapter reacting on the choice
    final private SelectionListener optionSelectionAdapter = new SelectionAdapter() {
        @Override
		public void widgetSelected(SelectionEvent e) {
        	configureTextWidget(optionModelValue.getSelection());

            if (fieldFlags == AssignmentWizard.SHOW_OPTION)
            {
                boolean modelValueSetSelected = optionSetModelValues.getSelection();
                flagSymmetricalSet.setEnabled(modelValueSetSelected);
                smvTypeCombo.setEnabled(modelValueSetSelected);
                optionSMVUntyped.setEnabled(modelValueSetSelected);
            }
            getContainer().updateButtons();
        }
    };

    public AssignmentWizardPage(String action, String description, int fieldFlags, String helpId)
    {
        super("AssignmentWizardPage");
        this.fieldFlags = fieldFlags;
        this.helpId = helpId;
        setTitle(action);
        setDescription(description);
    }
    
    private void configureTextWidget(final boolean forModelValue) {
    	final StyledText textWidget = source.getTextWidget();
    	
		if (forModelValue) {
			textWidget.setBackground(textWidget.getParent().getBackground());
		} else {
			textWidget.setBackground(PlatformUI.getWorkbench().getDisplay().getSystemColor(SWT.COLOR_WHITE));
		}		
		textWidget.setEnabled(!forModelValue);
    }

    /* (non-Javadoc)
     * @see org.eclipse.jface.dialogs.IDialogPage#createControl(org.eclipse.swt.widgets.Composite)
     */
    public void createControl(Composite parent)
    {
        Composite container = new Composite(parent, SWT.NULL);
        container.setLayoutData(new GridData(SWT.LEFT, SWT.TOP, true, true));
        GridLayout layout = new GridLayout(2, false);
        container.setLayout(layout);
        GridData gd;

		final Assignment assignment = getAssignment();
		String localLabel = assignment.getLocalLabel();
		
        // display source name and originally defined in module
		OpDefNode node = ModelHelper.getOpDefNode(assignment.getLabel());
		if (node != null && node.getSource() != node) {
			localLabel += " [" + node.getSource().getOriginallyDefinedInModuleNode().getName().toString() + "]";
		}
		
		paramComposite = new LabeledListComposite(container, localLabel, assignment.getParams());
        gd = new GridData(SWT.LEFT, SWT.TOP, false, true);
        paramComposite.setLayoutData(gd);

        source = FormHelper.createSourceViewer(container, SWT.BORDER | SWT.MULTI | SWT.H_SCROLL | SWT.V_SCROLL);

        // set data
        source.setDocument(new Document(assignment.getRight()));
        final StyledText styledText = source.getTextWidget();
        styledText.addModifyListener(new ModifyListener() {

            public void modifyText(ModifyEvent e)
            {
                getContainer().updateButtons();
            }

        });
        styledText.setBackgroundMode(SWT.INHERIT_FORCE);
        styledText.setEditable(true);
        styledText.setFocus();

        // SWT.FILL causes the text field to expand and contract
        // with changes in size of the dialog window.
        gd = new GridData(SWT.FILL, SWT.FILL, true, true);
        gd.minimumWidth = 500;
        gd.minimumHeight = 100;
        styledText.setLayoutData(gd);

        // constant, no parameters
        if (!paramComposite.hasParameters())
        {
            // both bits set, make a radio list
            if (fieldFlags == AssignmentWizard.SHOW_OPTION)
            {
                Composite leftContainer = new Composite(container, SWT.NULL);
                gd = new GridData(SWT.LEFT, SWT.TOP, false, false);
                leftContainer.setLayoutData(gd);
                leftContainer.setLayout(new GridLayout(1, false));

                // ordinary value option
                optionOrdinaryValue = new Button(leftContainer, SWT.RADIO);
                optionOrdinaryValue.setText("Ordinary assignment");
                gd = new GridData(SWT.LEFT, SWT.TOP, false, false);
                optionOrdinaryValue.setLayoutData(gd);

                // make a model value
                optionModelValue = new Button(leftContainer, SWT.RADIO);
                optionModelValue.setText("Model value");

                gd = new GridData(SWT.LEFT, SWT.TOP, false, false);
                optionModelValue.setLayoutData(gd);

                // make a set of model values
                optionSetModelValues = new Button(leftContainer, SWT.RADIO);
                optionSetModelValues.setText("Set of model values");
                gd = new GridData(SWT.LEFT, SWT.TOP, false, false);
                optionSetModelValues.setLayoutData(gd);

                // option to make a set of model values symmetrical
                flagSymmetricalSet = new Button(leftContainer, SWT.CHECK);
                flagSymmetricalSet.setText("Symmetry set");
                gd = new GridData(SWT.LEFT, SWT.TOP, false, false);
                gd.horizontalIndent = 10;
                flagSymmetricalSet.setLayoutData(gd);

                final Composite rightContainer = new Composite(leftContainer, SWT.NONE);
                gd = new GridData(SWT.LEFT, SWT.TOP, false, false);
                rightContainer.setLayoutData(gd);
                rightContainer.setLayout(new GridLayout(2, false));

                // untyped set of model values option
                optionSMVUntyped = new Button(rightContainer, SWT.CHECK);
                optionSMVUntyped.setText("Type:");
                optionSMVUntyped.addSelectionListener(typingOptionSelectionAdapter);
                gd = new GridData(SWT.LEFT, SWT.TOP, true, false);
                gd.horizontalIndent = 5;
                optionSMVUntyped.setLayoutData(gd);

                // type combo box
                smvTypeCombo = new Combo(rightContainer, SWT.BORDER);

                // add letters (assumes A-Z...a-z)
                for (char i = 'A'; i < 'z'; i++)
                {
                    if (Character.isLetter(i))
                    {
                        smvTypeCombo.add("" + i);
                    }
                }
                gd = new GridData(SWT.LEFT, SWT.TOP, false, false);
                smvTypeCombo.setLayoutData(gd);
                smvTypeCombo.setText("A");
                smvTypeCombo.setEnabled(false);

                // install listeners
                optionOrdinaryValue.addSelectionListener(optionSelectionAdapter);
                optionModelValue.addSelectionListener(optionSelectionAdapter);
                optionSetModelValues.addSelectionListener(optionSelectionAdapter);

                // set the value from the assignment object
                configureTextWidget(assignment.isModelValue());
                if (assignment.isModelValue())
                {
                    // single model value
                    if (!assignment.isSetOfModelValues())
                    {
                        flagSymmetricalSet.setEnabled(false);
                        smvTypeCombo.setEnabled(false);
                        optionSMVUntyped.setEnabled(false);
                        optionModelValue.setSelection(assignment.isModelValue());
                        // set of model values
                    } else
                    {
                        optionSetModelValues.setSelection(assignment.isModelValue());
                        flagSymmetricalSet.setSelection(assignment.isSymmetricalSet());
                        
                        final TypedSet set = TypedSet.parseSet(this.getAssignment().getRight());
                        final boolean hasType = set.hasType();
						
						optionSMVUntyped.setSelection(hasType);
						if (hasType) {
							smvTypeCombo.setText(set.getType());
			                smvTypeCombo.setEnabled(true);
						}
						
						styledText.setBackground(PlatformUI.getWorkbench().getDisplay().getSystemColor(SWT.COLOR_WHITE));
						styledText.setEnabled(true);
                    }
                } else
                {
                    flagSymmetricalSet.setEnabled(false);
                    smvTypeCombo.setEnabled(false);
                    optionSMVUntyped.setEnabled(false);
                    optionOrdinaryValue.setSelection(true);
                }

            } else if (fieldFlags == AssignmentWizard.SHOW_MODEL_VALUE_OPTION)
            {
                // ordinary value option
                optionOrdinaryValue = new Button(container, SWT.RADIO);
                optionOrdinaryValue.setText("Ordinary assignment");
                gd = new GridData(SWT.LEFT, SWT.TOP, false, false);
                gd.horizontalSpan = 2;
                optionOrdinaryValue.setLayoutData(gd);

                // make a model value
                optionModelValue = new Button(container, SWT.RADIO);
                optionModelValue.setText("Model value");

                gd = new GridData(SWT.LEFT, SWT.TOP, false, false);
                gd.horizontalSpan = 2;
                optionModelValue.setLayoutData(gd);

                // install listeners
                optionOrdinaryValue.addSelectionListener(optionSelectionAdapter);
                optionModelValue.addSelectionListener(optionSelectionAdapter);

                configureTextWidget(assignment.isModelValue());
                // set the value from the assignment object
                if (assignment.isModelValue())
                {
                    // single model value
                    if (!assignment.isSetOfModelValues()) {
                        optionModelValue.setSelection(assignment.isModelValue());
                        source.getTextWidget().setBackground(container.getBackground());
                        // set of model values
                    } else {
						styledText.setBackground(PlatformUI.getWorkbench().getDisplay().getSystemColor(SWT.COLOR_WHITE));
						styledText.setEnabled(true);
                    }
                } else
                {
                    optionOrdinaryValue.setSelection(true);
                }
            }
        }
        // here we need to add UIHelper.setHelp(container, "assignmentHelp");
        // except Simon says that it won't work because this is also used
        // overriding definitions. Therefore, we need to add a field to the
        // class that contains the help string, and set it with the constructor.
        UIHelper.setHelp(container, helpId);

        setControl(container);
    }

    /**
     * The assignment with modified params and right part 
     * @return
     */
    public Assignment getAssignment()
    {
        return ((AssignmentWizard) getWizard()).getFormula();
    }

    // this method sets up the Assignment object when the user
    // clicks Finish or Cancel
    @Override
    public void dispose()
    {
    	// cancel should not update any model values
    	final AssignmentWizard wizard = (AssignmentWizard) getWizard();
    	if(wizard.getWizardDialogReturnCode() == org.eclipse.jface.window.Window.CANCEL) {
    		super.dispose();
    		return;
    	}
    	
        String rightSide = FormHelper.trimTrailingSpaces(source.getDocument().get());

        // if the model value(s) option exist
        if (optionModelValue != null && optionSetModelValues != null)
        {
            this.getAssignment().setModelValue(optionModelValue.getSelection() || optionSetModelValues.getSelection());

            // handling the option selected
            if (optionModelValue.getSelection())
            {
                // model value
                this.getAssignment().setRight(this.getAssignment().getLabel());
            } else if (optionSetModelValues.getSelection())
            {
                // set of model values
                // normalize the right side
                TypedSet set = TypedSet.parseSet(rightSide);
                this.getAssignment().setSymmetric(flagSymmetricalSet.getSelection());
                this.getAssignment().setRight(set.toString());
                
                // evaluate the selected option and change the MVs as appropriate
                set = TypedSet.parseSet(this.getAssignment().getRight());
                if (optionSMVUntyped.getSelection())
                {
                    // retrieve the type letter
                    final String type = smvTypeCombo.getText();
                    set.setType(type);
                } else {
                    set.unsetType();
                }
                // set the content back
                this.getAssignment().setRight(set.toString());
            } else
            {
                // ordinary assignment (with no parameters)
                this.getAssignment().setRight(rightSide);
            }

        } else if (optionModelValue != null)
        {
            // definition override with no parameters
            this.getAssignment().setModelValue(optionModelValue.getSelection());
            if (optionModelValue.getSelection())
            {
                // model value
                this.getAssignment().setRight(this.getAssignment().getLabel());
            } else
            {
                // ordinary assignment (with no parameters)
                this.getAssignment().setRight(rightSide);
            }
        } else
        {
            // no options - e.G. definition override or constant with multiple parameters
            this.getAssignment().setRight(rightSide);
        }

        // if there are parameters, set them
        if (paramComposite.hasParameters())
        {
            this.getAssignment().setParams(paramComposite.getValues());
        }
        super.dispose();
    }

    /**
     * Returns the unmodified text entered into this pages
     * source text field.
     * @return
     */
    public String getInputText()
    {
        return source.getDocument().get();
    }

    /**
     * Added by LL on 5 Nov 2009
     * Returns true iff the page has a Model Value option that is chosen.
     * @return
     */
    public boolean modelValueSelected()
    {
        // If there is no Model Value option, then optionModelValue
        // appears to be null.
        if (optionModelValue == null)
        {
            return false;
        }
        return optionModelValue.getSelection();
    }

}
