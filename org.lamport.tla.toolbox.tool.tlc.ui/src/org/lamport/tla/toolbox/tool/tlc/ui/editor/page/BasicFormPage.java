package org.lamport.tla.toolbox.tool.tlc.ui.editor.page;

import java.util.Enumeration;
import java.util.Hashtable;
import java.util.List;

import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.ListenerList;
import org.eclipse.core.runtime.NullProgressMonitor;
import org.eclipse.core.runtime.jobs.Job;
import org.eclipse.debug.core.ILaunchConfiguration;
import org.eclipse.debug.core.ILaunchConfigurationWorkingCopy;
import org.eclipse.jface.action.Action;
import org.eclipse.jface.action.IToolBarManager;
import org.eclipse.jface.dialogs.IMessageProvider;
import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.jface.resource.ImageDescriptor;
import org.eclipse.swt.graphics.Image;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.eclipse.swt.widgets.Layout;
import org.eclipse.ui.forms.IManagedForm;
import org.eclipse.ui.forms.IMessageManager;
import org.eclipse.ui.forms.editor.FormEditor;
import org.eclipse.ui.forms.editor.FormPage;
import org.eclipse.ui.forms.events.ExpansionAdapter;
import org.eclipse.ui.forms.events.ExpansionEvent;
import org.eclipse.ui.forms.events.HyperlinkAdapter;
import org.eclipse.ui.forms.events.HyperlinkEvent;
import org.eclipse.ui.forms.events.IExpansionListener;
import org.eclipse.ui.forms.widgets.ExpandableComposite;
import org.eclipse.ui.forms.widgets.FormToolkit;
import org.eclipse.ui.forms.widgets.ScrolledForm;
import org.lamport.tla.toolbox.tool.tlc.launch.IModelConfigurationConstants;
import org.lamport.tla.toolbox.tool.tlc.launch.IModelConfigurationDefaults;
import org.lamport.tla.toolbox.tool.tlc.launch.TLCModelLaunchDelegate;
import org.lamport.tla.toolbox.tool.tlc.ui.TLCUIActivator;
import org.lamport.tla.toolbox.tool.tlc.ui.contribution.DynamicContributionItem;
import org.lamport.tla.toolbox.tool.tlc.ui.editor.ISectionManager;
import org.lamport.tla.toolbox.tool.tlc.ui.editor.ModelEditor;
import org.lamport.tla.toolbox.tool.tlc.ui.util.FormHelper;
import org.lamport.tla.toolbox.tool.tlc.ui.util.IgnoringListener;
import org.lamport.tla.toolbox.tool.tlc.ui.util.SemanticHelper;
import org.lamport.tla.toolbox.tool.tlc.util.ModelHelper;
import org.lamport.tla.toolbox.util.UIHelper;

import tla2sany.semantic.SymbolNode;
import tla2sany.st.Location;

/**
 * Basic form page for the multi-page editor
 * 
 * @author Simon Zambrovski
 * @version $Id$
 */
public abstract class BasicFormPage extends FormPage implements IModelConfigurationConstants,
        IModelConfigurationDefaults, ISectionManager, IDoRunContainer
{
    public static final String CRASHED_TITLE = " ( model checking has crashed )";
    public static final String RUNNING_TITLE = " ( model checking is in progress )";
    protected ListenerList dirtyPartListeners = new ListenerList();
    protected String helpId = null;
    protected String imagePath = null;
    protected boolean initialized = false;
    protected IExpansionListener formRebuildingListener = null;

    // adapter calling doRun() method
    // is reacting on clicking of Run model
    protected HyperlinkAdapter runDebugAdapter = new HyperlinkAdapter() {

        public void linkActivated(HyperlinkEvent e)
        {
            doRun((String) e.getHref());
        }
    };
    // image registry
    private Hashtable images = new Hashtable();
    // the page completion status (true by default)
    private boolean isComplete = true;

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
     * Launch TLC
     * @param mode
     */
    public void doRun(String mode)
    {
        IProgressMonitor monitor = new NullProgressMonitor();

        if (!((ModelEditor) getEditor()).isComplete())
        {
            MessageDialog.openError(getSite().getShell(), "TLC Launch not allowed",
                    "The model contains errors, which should be corrected before the TLC launch");
            return;
        }

        ILaunchConfigurationWorkingCopy config = getConfig();

        // save the editor if not saved
        if (getEditor().isDirty())
        {
            getEditor().doSave(monitor);
        }

        // launching the config
        try
        {
            config.launch(TLCModelLaunchDelegate.MODE_MODELCHECK, monitor, false);

        } catch (CoreException e)
        {
            TLCUIActivator.logError("Error launching the configuration " + config.getName(), e);
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
        IToolBarManager toolbarManager = formWidget.getForm().getToolBarManager();

        // run button
        toolbarManager.add(new DynamicContributionItem(new RunAction()));
        // stop button
        toolbarManager.add(new DynamicContributionItem(new StopAction()));

        // refresh the tool-bar
        toolbarManager.update(true);

        // setup body layout
        body.setLayout(getBodyLayout());

        // create the body of the page
        createBodyContent(managedForm);

        try
        {
            // load data from the model
            loadData();
        } catch (CoreException e)
        {
            TLCUIActivator.logError("Error loading data from the model into the form fields", e);
        }

        // check the model is-running state
        refresh();

        // finalizes the page construction
        // activates the change listeners
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

        initialized = true;
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

    /* (non-Javadoc)
     * @see org.lamport.tla.toolbox.tool.tlc.ui.editor.page.ISectionConstants#getExpansionListener()
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

    /**
     * Retrieves the configuration the editor is editing
     * @return
     */
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
     * Returns if the input is complete and the page contains no errors
     * @return
     */
    public boolean isComplete()
    {
        return isComplete;
    }

    /**
     * Sets if the page is complete and the contains no errors
     * @param isComplete
     */
    public void setComplete(boolean isComplete)
    {
        this.isComplete = isComplete;
    }

    /**
     * retrieves the helper to lookup names 
     * @return
     */
    public SemanticHelper getLookupHelper()
    {
        return ((ModelEditor) this.getEditor()).getHelper();
    }

    /**
     * Validates if the elements of the list are ids
     * @param values
     * @param listSource
     * @param errorMessagePrefix
     * @param elementType
     * @param sectionIndex the index of the section to expand   
     */
    public void validateId(List values, Control listSource, String errorMessagePrefix, String elementType,
            String sectionIndex)
    {
        if (values == null)
        {
            return;
        }
        String message;
        IMessageManager mm = getManagedForm().getMessageManager();
        for (int i = 0; i < values.size(); i++)
        {
            String value = (String) values.get(i);
            if (!FormHelper.isIdentifier(value))
            {
                message = elementType
                        + " "
                        + value
                        + " may not be used, since it is not a valid identifier.\nAn identifier is non-empty sequence of letters, digits und '_' with at least one letter.";
                mm.addMessage(errorMessagePrefix + i, message, value.toString(), IMessageProvider.ERROR, listSource);
                setComplete(false);
                expandSection(sectionIndex);
            }
        }
    }

    /**
     * Checks if the elements of the given list comply with the requirement of being not already defined in the context
     * of the current model and the specification. The method will iterate through the list and check whether every element
     * satisfies the requirement. On violation, it adds the error message to the message manager.  
     * @param values The list to check
     * @param listSource the control serving as the origin of the list, on errors a small error icon will be added next to it 
     * @param errorMessagePrefix the prefix of the error messages to be used
     * @param elementType the type of the element, used in the error message
     * @param listSourceDescription the description of the list source, used in error reporting
     * @param sectionIndex index of the section to expand 
     */
    public void validateUsage(List values, Control listSource, String errorMessagePrefix, String elementType,
            String listSourceDescription, String sectionIndex)
    {
        if (values == null)
        {
            return;
        }
        IMessageManager mm = getManagedForm().getMessageManager();
        SemanticHelper helper = getLookupHelper();
        String message;
        for (int i = 0; i < values.size(); i++)
        {
            String value = (String) values.get(i);
            Object usageHint = helper.getUsedHint(value);
            if (usageHint != null)
            {
                message = elementType + " " + value + " may not be used, since it is ";
                if (usageHint instanceof SymbolNode)
                {
                    message += "";
                    SymbolNode node = (SymbolNode) usageHint;
                    Location location = node.getLocation();
                    if (location.source().equals("--TLA+ BUILTINS--"))
                    {
                        message += "a built-in TLA+ definition.";
                    } else
                    {
                        message += "an identifier already defined at " + location.toString() + ".";
                    }
                } else if (usageHint instanceof String)
                {
                    if (SemanticHelper.KEYWORD.equals(usageHint))
                    {
                        message += "a TLA+ keyword.";
                    } else
                    {
                        message += "already used in " + usageHint;
                    }
                } else
                {
                    message = "Error during validation. This is a bug";
                }
                mm.addMessage(errorMessagePrefix + i, message, value.toString(), IMessageProvider.ERROR, listSource);
                setComplete(false);
                expandSection(sectionIndex);
            } else
            {
                // just adding the name
                helper.addName(value, this, listSourceDescription);
            }
        }
    }

    /**
     * Returns true, if the page has been initialized (loaded)
     * @return boolean flag indicating if the method pageInitializationComplete() has been called
     */
    public boolean isInitialized()
    {
        return initialized;
    }

    /**
     * Delegate to the section manager
     * @param sectionId
     */
    public void expandSection(String sectionId)
    {
        ((ModelEditor) getEditor()).getSectionManager().expandSection(sectionId);
    }

    /**
     * Enables or disables the section
     * @param sectionId
     * @param enabled
     */
    public void enableSection(String sectionId, boolean enabled)
    {
        ((ModelEditor) getEditor()).getSectionManager().enableSection(sectionId, enabled);
    }

    /**
     * Adds the section to the section manager in order to be able to expand the sections on events 
     * (like errors, hyperlinks, etc...)
     * @param sectionId
     * @param pageId
     * @param section
     */
    public void addSection(String sectionId, ExpandableComposite section)
    {
        ((ModelEditor) getEditor()).getSectionManager().addSection(section, sectionId, getId());
    }

    /**
     * Enables or disables the page
     * @param enabled, if true the page controls are enabled, otherwise disabled
     */
    public void setEnabled(boolean enabled)
    {
        setAllSectionsEnabled(enabled);
        getManagedForm().getForm().getBody().setEnabled(enabled);
    }
    
    /**
     * Enables or disables all section on the current page
     * @param enabled 
     */
    public void setAllSectionsEnabled(boolean enabled)
    {
        String[] sectionIds = ((ModelEditor) getEditor()).getSectionManager().getSectionsForPage(getId());
        for (int i = 0; i < sectionIds.length; i++)
        {
            enableSection(sectionIds[i], enabled);
        }
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
     * Forces the form refresh
     */
    public void refresh()
    {
        IManagedForm mForm = this.getManagedForm();
        if (mForm != null)
        {
            IToolBarManager toolbarManager = mForm.getForm().getToolBarManager();

            // get the usage status
            boolean modelInUse = isModelInUse();

            // refresh the title
            String title = mForm.getForm().getText();
            int titleIndex = Math.max(title.indexOf(RUNNING_TITLE), title.indexOf(CRASHED_TITLE));
            // restore the title
            if (titleIndex != -1) 
            {
                title = title.substring(0, titleIndex);
            }
            
            if (modelInUse)
            {
                if (isModelStale())
                {
                    mForm.getForm().setText(title + CRASHED_TITLE);
                    // the model crashed
                    toolbarManager.add(new DynamicContributionItem(new ModelRecoveryAction()));
                } else 
                {
                    mForm.getForm().setText(title + RUNNING_TITLE);
                }
            } else
            {
                // restore the title, only if we need
                if (titleIndex != -1)
                {
                    mForm.getForm().setText(title);
                }
            }

            // refresh the tool-bar
            toolbarManager.markDirty();
            toolbarManager.update(true);

            
            // refresh enablement status
            setEnabled(!modelInUse);
            mForm.getForm().update();
        }
    }

    /**
     * Returns true, if the model is being run, that is the attribute MODEL_IS_RUNNING is true
     * @return true if the underlying model file has attribute MODEL_IS_RUNNING set to true 
     */
    public boolean isModelInUse()
    {
        return ((ModelEditor) getEditor()).isModelInUse();
    }

    public boolean isModelStale()
    {
        return ((ModelEditor) getEditor()).isModelStale();
    }

    /**
     * The run action
     */
    class RunAction extends Action
    {
        RunAction()
        {
            super("Run", TLCUIActivator.imageDescriptorFromPlugin(TLCUIActivator.PLUGIN_ID, "icons/full/lrun_obj.gif"));
            this.setDescription("Run TLC");
            this.setToolTipText("Starts the TLC model checker");
        }

        public void run()
        {
            // System.out.println("Run");
            doRun(MODE_RUN);
        }

        /**
         * Run is only enabled if the model is not in use
         */
        public boolean isEnabled()
        {
            return !isModelInUse();
        }
    }

    /**
     * The stop action
     */
    class StopAction extends Action
    {
        StopAction()
        {
            super("Stop", TLCUIActivator.imageDescriptorFromPlugin(TLCUIActivator.PLUGIN_ID, "icons/full/progress_stop.gif"));
            this.setDescription("Stop TLC");
            this.setToolTipText("Stops the TLC model checker");
        }

        public void run()
        {
            ILaunchConfiguration config = ((ModelEditor) getEditor()).getConfig();
            try
            {
                if (ModelHelper.isModelLocked(config) && !ModelHelper.isModelStale(config))
                {
                    Job[] runningSpecJobs = Job.getJobManager().find(config);
                    for (int i = 0; i < runningSpecJobs.length; i++)
                    {
                        // send cancellations to all jobs...
                        runningSpecJobs[i].cancel();
                    }
                } 
            } catch (CoreException e)
            {
                TLCUIActivator.logError("Error stopping the model launch", e);
            }
            
        }

        /**
         * Run is only enabled if the model is not in use
         */
        public boolean isEnabled()
        {
            return isModelInUse() && !isModelStale();
        }
    }

    
    class ModelRecoveryAction extends Action
    {
        ModelRecoveryAction()
        {
            super("Restore model", TLCUIActivator.imageDescriptorFromPlugin(TLCUIActivator.PLUGIN_ID,
                    "icons/full/loop_obj.gif"));
            this.setDescription("Restore model");
            this.setToolTipText("Restore the model after the TLC crashed");
        }

        public void run()
        {
            try
            {
                ModelHelper.recoverModel(((ModelEditor) getEditor()).getConfig());
            } catch (CoreException e)
            {
                TLCUIActivator.logError("Error recovering the model", e);
            }
        }

        public boolean isEnabled()
        {
            return isModelStale();
        }
    }
}