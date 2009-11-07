package org.lamport.tla.toolbox.tool.tlc.ui.wizard;

import org.eclipse.jface.text.Document;
import org.eclipse.jface.text.source.SourceViewer;
import org.eclipse.jface.wizard.IWizardPage;
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
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Display;
import org.eclipse.swt.widgets.Label;
import org.lamport.tla.toolbox.tool.tlc.model.Assignment;
import org.lamport.tla.toolbox.tool.tlc.model.TypedSet;
import org.lamport.tla.toolbox.tool.tlc.ui.util.FormHelper;
import org.lamport.tla.toolbox.tool.tlc.util.ModelHelper;
import org.lamport.tla.toolbox.util.UIHelper;

import tla2sany.semantic.OpDefNode;

/**
 * @author Simon Zambrovski
 * @version $Id$
 */
public class AssignmentWizardPage extends WizardPage
{
    public static final String CONSTANT_WIZARD_ID = "constant_assignment_wizard";
    public static final String CONSTANT_TYPING_WIZARD_ID = "constant_assignment_typing_wizard";
    public static final String DEF_OVERRIDE_WIZARD_ID = "definition_override_wizard";
    private LabeledListComposite paramComposite;
    private SourceViewer source;
    private Button optionModelValue = null;
    private final int fieldFlags;
    private final String helpId; // The id of the help context for this wizard page
    private Button optionSetModelValues;
    private Button flagSymmetricalSet;
    private Button optionOrdinaryValue;
    // selection adapter reacting on the choice
    private SelectionListener optionSelectionAdapter = new SelectionAdapter() {
        public void widgetSelected(SelectionEvent e)
        {
            boolean modelValueSelected = optionModelValue.getSelection();

            if (modelValueSelected)
            {
                source.getTextWidget().setBackground(getControl().getBackground());
            } else
            {
                source.getTextWidget().setBackground(Display.getCurrent().getSystemColor(SWT.COLOR_WHITE));
            }
            source.getControl().setEnabled(!modelValueSelected);

            if (fieldFlags == AssignmentWizard.SHOW_OPTION)
            {
                boolean modelValueSetSelected = optionSetModelValues.getSelection();
                flagSymmetricalSet.setEnabled(modelValueSetSelected);
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

        paramComposite = new LabeledListComposite(container, getAssignment().getLabel().substring(
                getAssignment().getLabel().lastIndexOf("!") + 1), getAssignment().getParams());
        gd = new GridData(SWT.LEFT, SWT.TOP, false, true);
        paramComposite.setLayoutData(gd);

        source = FormHelper.createSourceViewer(container, SWT.BORDER | SWT.MULTI | SWT.H_SCROLL | SWT.V_SCROLL);

        // set data
        source.setDocument(new Document(getAssignment().getRight()));
        StyledText styledText = source.getTextWidget();
        styledText.addModifyListener(new ModifyListener() {

            public void modifyText(ModifyEvent e)
            {
                getContainer().updateButtons();
            }

        });
        styledText.setBackgroundMode(SWT.INHERIT_FORCE);
        styledText.setEditable(true);
        styledText.setFocus();

        gd = new GridData(SWT.RIGHT, SWT.TOP, true, true);
        gd.minimumWidth = 500;
        gd.minimumHeight = 100;
        styledText.setLayoutData(gd);

        // display source name and originally defined in module
        OpDefNode node = ModelHelper.getOpDefNode(getAssignment().getLabel());
        if (node != null && node.getSource() != node)
        {
            GridData labelGridData = new GridData();
            labelGridData.horizontalSpan = 2;
            Label moduleNameLabel = new Label(container, SWT.NONE);
            moduleNameLabel.setText("From module "
                    + node.getSource().getOriginallyDefinedInModuleNode().getName().toString());
            moduleNameLabel.setLayoutData(labelGridData);
        }

        // constant, no parameters
        if (!paramComposite.hasParameters())
        {
            // both bits set, make a radio list
            if (fieldFlags == AssignmentWizard.SHOW_OPTION)
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

                // make a set of model values
                optionSetModelValues = new Button(container, SWT.RADIO);
                optionSetModelValues.setText("Set of model values");
                gd = new GridData(SWT.LEFT, SWT.TOP, false, false);
                gd.horizontalSpan = 2;
                optionSetModelValues.setLayoutData(gd);

                // option to make a set symmetrical
                flagSymmetricalSet = new Button(container, SWT.CHECK);
                flagSymmetricalSet.setText("Symmetry set");
                gd = new GridData(SWT.LEFT, SWT.TOP, false, false);
                gd.horizontalSpan = 2;
                gd.horizontalIndent = 10;
                flagSymmetricalSet.setLayoutData(gd);

                // install listeners
                optionOrdinaryValue.addSelectionListener(optionSelectionAdapter);
                optionModelValue.addSelectionListener(optionSelectionAdapter);
                optionSetModelValues.addSelectionListener(optionSelectionAdapter);

                // set the value from the assignment object
                if (getAssignment().isModelValue())
                {
                    // single model value
                    if (!getAssignment().isSetOfModelValues())
                    {
                        flagSymmetricalSet.setEnabled(false);
                        optionModelValue.setSelection(getAssignment().isModelValue());
                        source.getTextWidget().setBackground(container.getBackground());
                        // set of model values
                    } else
                    {
                        optionSetModelValues.setSelection(getAssignment().isModelValue());
                        flagSymmetricalSet.setSelection(getAssignment().isSymmetricalSet());
                    }
                } else
                {
                    flagSymmetricalSet.setEnabled(false);
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

                // set the value from the assignment object
                if (getAssignment().isModelValue())
                {
                    // single model value
                    if (!getAssignment().isSetOfModelValues())
                    {
                        optionModelValue.setSelection(getAssignment().isModelValue());
                        source.getTextWidget().setBackground(container.getBackground());
                        // set of model values
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

    public boolean finish()
    {
        return false;
    }

    // this method sets up the Assignment object when the user
    // clicks Finish
    public void dispose()
    {

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

    /*
     * Show the next page ( for typing of model values sets )
     * @see org.eclipse.jface.wizard.WizardPage#getNextPage()
     */
    public IWizardPage getNextPage()
    {
        if (isTypeInputPossible())
        {
            return super.getNextPage();
        }
        return null;
    }

    protected boolean isTypeInputPossible()
    {
        // only a set of model values can be typed
        if (optionSetModelValues == null || !optionSetModelValues.getSelection())
        {
            return false;
        }
        String set = FormHelper.trimTrailingSpaces(source.getDocument().get());
        TypedSet parsedSet = TypedSet.parseSet(set);

        return (parsedSet.getType() == null);
    }

    public boolean isCurrentPage()
    {
        return super.isCurrentPage();
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
