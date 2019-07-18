package org.lamport.tla.toolbox.tool.tlc.ui.editor.part;

import java.util.Vector;

import org.eclipse.jface.preference.IPreferenceStore;
import org.eclipse.jface.util.IPropertyChangeListener;
import org.eclipse.jface.viewers.LabelProvider;
import org.eclipse.jface.viewers.TableViewer;
import org.eclipse.jface.window.Window;
import org.eclipse.jface.wizard.WizardDialog;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Table;
import org.eclipse.ui.forms.widgets.FormToolkit;
import org.lamport.tla.toolbox.tool.ToolboxHandle;
import org.lamport.tla.toolbox.tool.tlc.model.Assignment;
import org.lamport.tla.toolbox.tool.tlc.ui.TLCUIActivator;
import org.lamport.tla.toolbox.tool.tlc.ui.dialog.FilteredDefinitionSelectionDialog;
import org.lamport.tla.toolbox.tool.tlc.ui.editor.DataBindingManager;
import org.lamport.tla.toolbox.tool.tlc.ui.editor.page.BasicFormPage;
import org.lamport.tla.toolbox.tool.tlc.ui.editor.preference.IModelEditorPreferenceConstants;
import org.lamport.tla.toolbox.tool.tlc.ui.wizard.AssignmentWizard;
import org.lamport.tla.toolbox.tool.tlc.ui.wizard.AssignmentWizardPage;
import org.lamport.tla.toolbox.tool.tlc.util.ModelHelper;

import tla2sany.semantic.OpDefNode;

/**
 * Section part for the DefinitionOverride section of the Advanced Options page
 * @author Simon Zambrovski
 */
public class ValidateableOverridesSectionPart extends ValidateableConstantSectionPart {
	private final IPropertyChangeListener m_preferenceChangeListener = (event) -> {
		if (IModelEditorPreferenceConstants.I_OVERRIDDEN_DEFINITION_STYLE.equals(event.getProperty())) {
			tableViewer.refresh(true);
		}
	};

	public ValidateableOverridesSectionPart(Composite composite, String title, String description, FormToolkit toolkit,
			int flags, BasicFormPage page) {
        super(composite, title, description, toolkit, flags, page, DataBindingManager.SEC_DEFINITION_OVERRIDE);
        
		final IPreferenceStore ips = TLCUIActivator.getDefault().getPreferenceStore();
		ips.addPropertyChangeListener(m_preferenceChangeListener);
    }
	
	@Override
	public void dispose() {
		final IPreferenceStore ips = TLCUIActivator.getDefault().getPreferenceStore();
		ips.removePropertyChangeListener(m_preferenceChangeListener);
		
		super.dispose();
	}

    @Override
    @SuppressWarnings("unchecked")  // Generic casting...
    protected Assignment doEditFormula(Assignment formula)
    {
        // add -> let the user select the definition to override
        if (formula == null)
        {
            // Set names to an array of names of definitions that have already
            // been overridden. Note that this is the name by which the operator
            // is known in the root module, which may be something like
            // "frob!bar!Id"
            String[] names = null;
            Object input = this.getTableViewer().getInput();
            // I think that input is a Vector of Assignment objects.
            // If I'm wrong, we just set names[] to a zero-length array.
            if ((input != null) && (input instanceof Vector))
            {
                Vector<Object> inputVec = (Vector<Object>) input;
                names = new String[inputVec.size()];
                for (int i = 0; i < names.length; i++)
                {
                    Object next = inputVec.elementAt(i);
                    // next should be a non-null Assignment object,
                    // but if it isn't, we just set names[i] to ""
                    if ((next != null) && (next instanceof Assignment))
                    {
                        Assignment nextAss = (Assignment) next;
                        names[i] = nextAss.getLabel();
                    } else
                    {
                        names[i] = "";
                    }
                }
            } else
            {
                names = new String[0];
            }

            FilteredDefinitionSelectionDialog definitionSelection = new FilteredDefinitionSelectionDialog(this
                    .getSection().getShell(), false, ToolboxHandle.getCurrentSpec().getValidRootModule(), names);

            definitionSelection.setTitle("Select Definition to Override");
            // It would be nice to add help to this dialog. The following command will
            // add a help button. However, I have no idea how to attach an help
            // to that button.
            //
            // definitionSelection.setHelpAvailable(true);

            definitionSelection
                    .setMessage("Type definition to override or select from the list below\n(?= any character, *= any string)");
            definitionSelection.setInitialPattern("?");
            if (Window.OK == definitionSelection.open()) // this raises the Window for selecting a definition to
                                                         // override
            {
                OpDefNode result = (OpDefNode) (definitionSelection.getResult())[0];
                formula = new Assignment(result.getName().toString(), Assignment.getArrayOfEmptyStrings(result
                        .getSource().getNumberOfArgs()), "");
            } else
            {
                return null;
            }
        }

        // check if number of params defined in modules still matches number of
        // params in definition override
        // if it does not, change number of params to match

        // The following is pretty weird. The variable result above appears to be the OpDefNode
        // that Simon is now computing.
        OpDefNode opDefNode = (OpDefNode) ModelHelper.getOpDefNode(formula.getLabel());
        if (opDefNode != null && opDefNode.getSource().getNumberOfArgs() != formula.getParams().length)
        {
            String[] newParams = new String[opDefNode.getSource().getNumberOfArgs()];
            for (int i = 0; i < newParams.length; i++)
            {
                newParams[i] = "";
            }
            formula.setParams(newParams);
        }
        // Create the wizard
        AssignmentWizard wizard = new AssignmentWizard(getSection().getText(), getSection().getDescription(),
                (Assignment) formula, AssignmentWizard.SHOW_MODEL_VALUE_OPTION,
                AssignmentWizardPage.DEF_OVERRIDE_WIZARD_ID);
        // Create the wizard dialog
        WizardDialog dialog = new WizardDialog(getTableViewer().getTable().getShell(), wizard);
        wizard.setWizardDialog(dialog);
        dialog.setHelpAvailable(true);

        // Open the wizard dialog that asks for the overriding definition
        if (Window.OK == dialog.open())
        {
            return wizard.getFormula();
        } else
        {
            return null;
        }

    }

    /**
     * create the buttons
     */
    @Override
    protected void createButtons(Composite sectionArea, FormToolkit toolkit, boolean add, boolean edit, boolean remove)
    {
        doCreateButtons(sectionArea, toolkit, true, true, true);
    }

    /**
     * Overrides the method in ValidateableConstantSectionPart in order
     * to add a label provider for displaying definition overrides properly.
     */
    @Override
    protected TableViewer createTableViewer(Table table)
    {
        TableViewer tableViewer = super.createTableViewer(table);

        // this is necessary for correctly displaying definition overrides
        // if the label is M!N!Foo, this will return Foo as the label. If ! is not used,
        // it will do nothing. If the definition override is a model value
        // then the right side will be equal to the label without any !.
        // For example if M!N!Foo is overridden as a model value,
        // the right side of the assignment used to generate the string
        // in this method will be Foo.
        tableViewer.setLabelProvider(new LabelProvider() {
            public String getText(Object element)
            {
                if (element instanceof Assignment)
                {
					final IPreferenceStore ips = TLCUIActivator.getDefault().getPreferenceStore();
					final String style = ips
							.getString(IModelEditorPreferenceConstants.I_OVERRIDDEN_DEFINITION_STYLE);
					final boolean moduleNameStyle = IModelEditorPreferenceConstants.I_OVERRIDDEN_DEFINITION_STYLE_MODULE_NAME
							.equals(style);
                    final Assignment assign = (Assignment) element;
                    final String label = assign.getLabel();
                    String noBangLabel = label.substring(label.lastIndexOf("!") + 1);
            		
					// This is upside-down because early in the call stack we had the node instance
					// but dropped it and instead serialized parts of it into Assignment. Now we
					// have to reconstruct the actual OpDefNode because need to know its module.
					// Since this is the standard idiom throughout this part of the model editor,
					// I'm not going to rewrite it.
                    final OpDefNode node = ModelHelper.getOpDefNode(label);
            		if (moduleNameStyle && (node != null) && (node.getSource() != node)) {
            			noBangLabel += " [" + node.getSource().getOriginallyDefinedInModuleNode().getName().toString() + "]";
            		}

					final boolean appendOverriddenModelValue = assign.isModelValue() && (node != null)
							&& (node.getSource() != node);
                    if (appendOverriddenModelValue && !moduleNameStyle) {
                    	return (assign.toString() + " " + noBangLabel);
                    } else {
                        final String rightSide;
    					if (assign.isModelValue()) {
    						rightSide = noBangLabel;
    					} else {
    						rightSide = assign.getRight();
    					}
    					
                        final Assignment assignNoBang = new Assignment(noBangLabel, assign.getParams(), rightSide);
                        return assignNoBang.toString() + (appendOverriddenModelValue ? (" " + noBangLabel) : "");
                    }
                }
                return super.getText(element);
            }
        });

        return tableViewer;

    }
}
