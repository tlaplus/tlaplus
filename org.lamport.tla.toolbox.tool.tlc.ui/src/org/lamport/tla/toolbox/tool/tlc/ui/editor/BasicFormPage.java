package org.lamport.tla.toolbox.tool.tlc.ui.editor;

import java.util.Enumeration;
import java.util.Hashtable;

import org.eclipse.jface.resource.ImageDescriptor;
import org.eclipse.swt.graphics.Image;
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
import org.lamport.tla.toolbox.tool.tlc.ui.TLCUIActivator;
import org.lamport.tla.toolbox.tool.tlc.ui.util.FormHelper;
import org.lamport.tla.toolbox.util.UIHelper;

/**
 * Basic form page
 * @author Simon Zambrovski
 * @version $Id$
 */
public abstract class BasicFormPage extends FormPage
{

    protected String helpId = null;
    protected String imagePath = null;
    protected IExpansionListener formRebuildingListener = null;

    // image registry
    private Hashtable images = new Hashtable();
    

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
        if (imagePath != null)
        {
            formWidget.setImage(createRegisteredImage(imagePath));
        }

        Composite body = formWidget.getBody();
        UIHelper.setHelp(body, helpId);

        FormToolkit toolkit = managedForm.getToolkit();
        toolkit.decorateFormHeading(formWidget.getForm());

        // setup body layout
        body.setLayout(getBodyLayout());

        createBodyContent(managedForm);
    }

    protected Layout getBodyLayout()
    {
        return FormHelper.createFormTableWrapLayout(false, 2);
    }

    /**
     * Is called to create the body content of the form
     * @param toolkit
     * @param body
     */
    protected void createBodyContent(FormToolkit toolkit, Composite body)
    {

    }
    
    

    /**
     * Is called to create the body content of the form
     * @param toolkit
     * @param body
     */
    protected void createBodyContent(IManagedForm managedForm)
    {
        createBodyContent(managedForm.getToolkit(), managedForm.getForm().getBody());
    }

    /**
     * Retrieves the instance of the expansion listener, that rebuilds the form
     * @return
     */
    public IExpansionListener getExpansionListener()
    {
        if (this.formRebuildingListener == null)
        {
            this.formRebuildingListener = new ExpansionAdapter() {
                public void expansionStateChanged(ExpansionEvent e)
                {

                    getManagedForm().reflow(true);
                }
            };
        }
        return this.formRebuildingListener;
    }

    /**
     * Disposes the images
     */
    public void dispose()
    {
        Enumeration elements = images.elements();
        while (elements.hasMoreElements())
        {
            ((Image)elements.nextElement()).dispose();
        }
        super.dispose();
    }
    
    /**
     * Retrieves the image and remember it for later reuse / dispose
     * @param imageName
     * @return
     */
    protected Image createRegisteredImage(String imageName)
    {
        Image image = (Image) images.get(imageName);
        if (image == null) 
        {
            ImageDescriptor descr = TLCUIActivator.imageDescriptorFromPlugin(TLCUIActivator.PLUGIN_ID, imageName);
            if (descr != null) 
            {
                image = descr.createImage();
                images.put(imageName, image);
            }
        }
        
        return image;
    }
}