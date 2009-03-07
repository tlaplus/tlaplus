package org.lamport.tla.toolbox.tool.tlc.ui.editor;

import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Layout;
import org.eclipse.ui.forms.IManagedForm;
import org.eclipse.ui.forms.editor.FormEditor;
import org.eclipse.ui.forms.widgets.FormToolkit;
import org.lamport.tla.toolbox.tool.tlc.ui.util.FormHelper;
import org.lamport.tla.toolbox.util.IHelpConstants;

/**
 * Page for entering model values
 * @author Simon Zambrovski
 * @version $Id$
 */
public class ModelValuesPage extends BasicFormPage
{

    public static final String ID = "ModelValues";

    public ModelValuesPage(FormEditor editor)
    {
        super(editor, ModelValuesPage.ID, "Model Values");
        this.helpId = IHelpConstants.MODEL_VALUE_MODEL_PAGE;
        this.imagePath = "icons/full/args_obj.gif";
    }

    protected void createBodyContent(IManagedForm managedForm)
    {
        Composite body = managedForm.getForm().getBody();
        FormToolkit toolkit = managedForm.getToolkit();

        TableSectionPart propertiesPart = new TableSectionPart(body, "Model Values", "....", toolkit);
        managedForm.addPart(propertiesPart);

    }

    protected Layout getBodyLayout()
    {
        return FormHelper.createFormGridLayout(false, 1);
    } 
}
