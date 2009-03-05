package org.lamport.tla.toolbox.tool.tlc.ui.editor;

import org.eclipse.core.runtime.CoreException;
import org.eclipse.debug.core.ILaunchConfiguration;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Text;
import org.eclipse.ui.IEditorInput;
import org.eclipse.ui.IEditorSite;
import org.eclipse.ui.forms.editor.FormEditor;
import org.eclipse.ui.forms.widgets.FormToolkit;
import org.eclipse.ui.forms.widgets.Section;
import org.eclipse.ui.part.FileEditorInput;
import org.lamport.tla.toolbox.tool.tlc.launch.ui.IConfigurationConstants;
import org.lamport.tla.toolbox.tool.tlc.launch.ui.IConfigurationDefaultConstants;
import org.lamport.tla.toolbox.tool.tlc.ui.util.FormHelper;
import org.lamport.tla.toolbox.tool.tlc.util.ModelHelper;
import org.lamport.tla.toolbox.util.IHelpConstants;

/**
 * @author Simon Zambrovski
 * @version $Id$
 */
public class GeneralModelPage extends BasicFormPage implements IConfigurationConstants, IConfigurationDefaultConstants
{

    public static final String ID = "GeneralModelPage";
    private Text specName;
    private Text modelName;
    private ILaunchConfiguration config;
    

    public GeneralModelPage(FormEditor editor)
    {
        super(editor, GeneralModelPage.ID, "Model Overview");
        
        this.helpId = IHelpConstants.GENERAL_MODEL_PAGE;
    }




    public void init(IEditorSite site, IEditorInput input)
    {
        super.init(site, input);
        if (input instanceof FileEditorInput)
        {
            FileEditorInput finput = (FileEditorInput) input;
            if (finput != null)
            {
                config = ModelHelper.getModelByFile(finput.getFile());
            }
        }
    }




    protected void createBodyContent(FormToolkit toolkit, Composite body)
    {
        
        Section summarySection = FormHelper.createSectionComposite(body, "Model summary", "Summary about the model", toolkit);
        Composite summaryArea = (Composite) summarySection.getClient();
        summaryArea.setLayout(new GridLayout(2, false));
        
        toolkit.createLabel(summaryArea, "Spec name");
        specName = toolkit.createText(summaryArea, "");
        specName.setEditable(false);
        
        toolkit.createLabel(summaryArea, "Model name");
        modelName = toolkit.createText(summaryArea, "");
        modelName.setEditable(false);
        
        
        set();
    }

    private void set()
    {
        try
        {
            specName.setText(config.getAttribute(SPEC_NAME, SPEC_NAME_DEFAULT));
        } catch (CoreException e)
        {
            // TODO Auto-generated catch block
            e.printStackTrace();
        }
    }
    
}
