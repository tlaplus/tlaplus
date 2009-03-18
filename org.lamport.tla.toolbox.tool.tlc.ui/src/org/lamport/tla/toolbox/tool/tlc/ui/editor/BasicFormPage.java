package org.lamport.tla.toolbox.tool.tlc.ui.editor;

import java.util.Enumeration;
import java.util.Hashtable;

import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.ListenerList;
import org.eclipse.debug.core.ILaunchConfigurationWorkingCopy;
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
import org.lamport.tla.toolbox.tool.tlc.ui.util.IgnoringListener;
import org.lamport.tla.toolbox.util.UIHelper;

/**
 * Basic form page for the multi-page editor
 * 
 * 
 * @author Simon Zambrovski
 * @version $Id$
 */
public abstract class BasicFormPage extends FormPage
{
    protected ListenerList ignoringListeners = new ListenerList();
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

    /**
     * Called during FormPage life cycle and delegates the form creation
     * to three methods {@link BasicFormPage#createBodyContent(IManagedForm)}, 
     * {@link BasicFormPage#loadData()}, {@link BasicFormPage#pageInitializationComplete()}
     */
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

        try
        {
            loadData();
        } catch (CoreException e)
        {
            e.printStackTrace();
        }

        pageInitializationComplete();
    }

    /**
     * Method to fill data in to the form
     * Subclasses should override this method and fill the 
     * data in to the input elements
     * @throws CoreException
     */
    protected void loadData() throws CoreException
    {

    }

    /**
     * Method finalizing the page initialization
     * Subclasses should override this method in order to activate
     * listeners  
     */
    protected void pageInitializationComplete()
    {
        Object[] listeners = ignoringListeners.getListeners();
        for (int i = 0; i < listeners.length; ++i) {
           ((IgnoringListener) listeners[i]).setIgnoreInput(false);
        }
    }

    /**
     * Is called to create the body content of the form.
     * Subclasses should override this method 
     * 
     * @param managedForm 
     */
    protected void createBodyContent(IManagedForm managedForm)
    {

    }

    /**
     * Commit the page
     */
    protected void commit(boolean onSave)
    {
        IManagedForm managedForm = getManagedForm();
        if (managedForm != null)
        {
            managedForm.commit(onSave);
        }
    }

    /**
     * Retrieves the layout of the page body
     * @return
     */
    protected Layout getBodyLayout()
    {
        return FormHelper.createFormTableWrapLayout(false, 2);
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
            ((Image) elements.nextElement()).dispose();
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

    public ILaunchConfigurationWorkingCopy getConfig()
    {
        return ((ModelEditor) getEditor()).getConfig();
    }
}