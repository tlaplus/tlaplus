package org.lamport.tla.toolbox.tool.tlc.ui.editor.page;

import java.util.Enumeration;
import java.util.Hashtable;

import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.ListenerList;
import org.eclipse.debug.core.ILaunchConfigurationWorkingCopy;
import org.eclipse.jface.action.Action;
import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.jface.resource.ImageDescriptor;
import org.eclipse.swt.graphics.Image;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Layout;
import org.eclipse.ui.forms.IManagedForm;
import org.eclipse.ui.forms.editor.FormEditor;
import org.eclipse.ui.forms.editor.FormPage;
import org.eclipse.ui.forms.events.ExpansionAdapter;
import org.eclipse.ui.forms.events.ExpansionEvent;
import org.eclipse.ui.forms.events.HyperlinkAdapter;
import org.eclipse.ui.forms.events.HyperlinkEvent;
import org.eclipse.ui.forms.events.IExpansionListener;
import org.eclipse.ui.forms.widgets.FormToolkit;
import org.eclipse.ui.forms.widgets.ScrolledForm;
import org.lamport.tla.toolbox.tool.tlc.launch.IModelConfigurationConstants;
import org.lamport.tla.toolbox.tool.tlc.launch.IModelConfigurationDefaults;
import org.lamport.tla.toolbox.tool.tlc.launch.TLCModelLaunchDelegate;
import org.lamport.tla.toolbox.tool.tlc.ui.TLCUIActivator;
import org.lamport.tla.toolbox.tool.tlc.ui.editor.ModelEditor;
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
public abstract class BasicFormPage extends FormPage implements IModelConfigurationConstants,
        IModelConfigurationDefaults
{
    public static final String MODE_RUN = "run";
    public static final String MODE_DEBUG = "debug";

    protected ListenerList dirtyPartListeners = new ListenerList();
    protected String helpId = null;
    protected String imagePath = null;
    protected IExpansionListener formRebuildingListener = null;
    protected HyperlinkAdapter runDebugAdapter = new HyperlinkAdapter() {

        public void linkActivated(HyperlinkEvent e)
        {
            doRun((String) e.getHref());
        }
    };

    // image registry
    private Hashtable images = new Hashtable();
    private boolean isComplete;

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
     * @param mode
     */
    protected void doRun(String mode)
    {
        // TODO
        IProgressMonitor monitor = null;

        if (!((ModelEditor)getEditor()).isComplete())
        {
            MessageDialog.openError(getSite().getShell(), "TLC Launch not allowed", "The model contains errors, which should be corrected before the TLC launch");
            return;
        }
        
        
        
        ILaunchConfigurationWorkingCopy config = getConfig();

        // save the editor if not saved
        if (getEditor().isDirty())
        {
            getEditor().doSave(monitor);
        }

        try
        {
            config.launch(TLCModelLaunchDelegate.MODE_MODELCHECK, monitor, false);
        } catch (CoreException e1)
        {
            e1.printStackTrace();
        }
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

        // head construction ---------------------

        // run button
        formWidget.getForm().getToolBarManager().add(new Action("Run") {
            public void run()
            {
                doRun(MODE_RUN);
            }

            public ImageDescriptor getImageDescriptor()
            {
                return TLCUIActivator.imageDescriptorFromPlugin(TLCUIActivator.PLUGIN_ID, "icons/full/lrun_obj.gif");
            }
        });

        // debug button
        formWidget.getForm().getToolBarManager().add(new Action("Debug") {
            public void run()
            {
                doRun(MODE_DEBUG);
            }

            public ImageDescriptor getImageDescriptor()
            {
                return TLCUIActivator.imageDescriptorFromPlugin(TLCUIActivator.PLUGIN_ID, "icons/full/ldebug_obj.gif");
            }
            // TODO enable on debug support
            public boolean isEnabled()
            {
                return false;
            }
            
        });

        formWidget.getForm().getToolBarManager().update(true);

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
        Object[] listeners = dirtyPartListeners.getListeners();
        for (int i = 0; i < listeners.length; ++i)
        {
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
    public void commit(boolean onSave)
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

    /**
     * Validation hook
     */
    public void validate()
    {
        
    }

    /**
     * 
     * @return
     */
    public boolean isComplete()
    {
        return isComplete;
    }

    public void setComplete(boolean isComplete)
    {
        this.isComplete = isComplete;
    }
}