package org.lamport.tla.toolbox.tool.tlc.ui.editor;

import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Layout;
import org.eclipse.ui.forms.IManagedForm;
import org.eclipse.ui.forms.editor.FormEditor;
import org.eclipse.ui.forms.editor.FormPage;
import org.eclipse.ui.forms.events.ExpansionAdapter;
import org.eclipse.ui.forms.events.ExpansionEvent;
import org.eclipse.ui.forms.events.IExpansionListener;
import org.eclipse.ui.forms.widgets.FormToolkit;
import org.eclipse.ui.forms.widgets.ScrolledForm;
import org.eclipse.ui.forms.widgets.TableWrapLayout;
import org.lamport.tla.toolbox.tool.tlc.ui.util.FormHelper;
import org.lamport.tla.toolbox.util.UIHelper;

/**
 * Basic form page
 * @author Simon Zambrovski
 * @version $Id$
 */
public abstract class BasicFormPage extends FormPage
{

    protected String helpId;
    protected IExpansionListener formRebuildingListener = null;
    
    /**
     * @param editor
     * @param id
     * @param title
     */
    public BasicFormPage(FormEditor editor, String id, String title)
    {
        super(editor, id, title);
        
    }

    protected void createFormContent(IManagedForm managedForm)
    {
        super.createFormContent(managedForm);
    
        ScrolledForm formWidget = managedForm.getForm();
        formWidget.setText(getTitle());
    
        Composite body = formWidget.getBody();        
        UIHelper.setHelp(body, helpId);
        
        
        FormToolkit toolkit = managedForm.getToolkit();
        toolkit.decorateFormHeading(formWidget.getForm());
    
        // setup body layout
        body.setLayout(getBodyLayout());
        
        createContent(managedForm);
    }

    
    
    
    protected Layout getBodyLayout()
    {
        TableWrapLayout layout = FormHelper.createFormTableWrapLayout(false, 2);
        return layout;
    }
    
    /**
     * Is called to create the body content of the form
     * @param toolkit
     * @param body
     */
    protected void createContent(FormToolkit toolkit, Composite body)
    {
        
    }

    /**
     * Is called to create the body content of the form
     * @param toolkit
     * @param body
     */
    protected void createContent(IManagedForm managedForm)
    {
        createContent(managedForm.getToolkit(), managedForm.getForm().getBody());
    }

    /**
     * Retrieves the instance of the expansion listener, that rebuilds the form
     * @return
     */
    public IExpansionListener getExpansionListener()
    {
        if (this.formRebuildingListener == null) 
        {
            this.formRebuildingListener = new ExpansionAdapter() 
            {
                public void expansionStateChanged(ExpansionEvent e)
                {
                    
                    getManagedForm().reflow(true);
                }
            };
        }
        return this.formRebuildingListener;
    }
}