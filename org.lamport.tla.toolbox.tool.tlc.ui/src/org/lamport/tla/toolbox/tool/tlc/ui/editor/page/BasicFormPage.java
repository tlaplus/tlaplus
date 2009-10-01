package org.lamport.tla.toolbox.tool.tlc.ui.editor.page;

import java.util.Enumeration;
import java.util.Hashtable;
import java.util.List;

import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.ListenerList;
import org.eclipse.debug.core.ILaunchConfigurationWorkingCopy;
import org.eclipse.jface.action.Action;
import org.eclipse.jface.action.IToolBarManager;
import org.eclipse.jface.dialogs.IMessageProvider;
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
import org.eclipse.ui.forms.events.IExpansionListener;
import org.eclipse.ui.forms.widgets.FormToolkit;
import org.eclipse.ui.forms.widgets.ScrolledForm;
import org.lamport.tla.toolbox.tool.tlc.launch.IModelConfigurationConstants;
import org.lamport.tla.toolbox.tool.tlc.launch.IModelConfigurationDefaults;
import org.lamport.tla.toolbox.tool.tlc.launch.TLCModelLaunchDelegate;
import org.lamport.tla.toolbox.tool.tlc.ui.TLCUIActivator;
import org.lamport.tla.toolbox.tool.tlc.ui.contribution.DynamicContributionItem;
import org.lamport.tla.toolbox.tool.tlc.ui.editor.DataBindingManager;
import org.lamport.tla.toolbox.tool.tlc.ui.editor.ISectionConstants;
import org.lamport.tla.toolbox.tool.tlc.ui.editor.ModelEditor;
import org.lamport.tla.toolbox.tool.tlc.ui.util.FormHelper;
import org.lamport.tla.toolbox.tool.tlc.ui.util.IgnoringListener;
import org.lamport.tla.toolbox.tool.tlc.ui.util.SemanticHelper;
import org.lamport.tla.toolbox.tool.tlc.util.ModelHelper;
import org.lamport.tla.toolbox.util.UIHelper;

import tla2sany.semantic.SymbolNode;
import tla2sany.st.Location;

/**
 * This is a base class for all pages used in the model editor. The model editor is a multi-page (tab) editor, and the
 * pages the subclasses of this class are pages, represented as individual tabs. 
 * The life cycle of the page is the following: the constructor of the page is called by the editor 
 * and then the added using the {@link ModelEditor#addPages}. The {@link FormPage#createPartControl} is called, which causes 
 * the method {@link BasicFormPage#createFormContent(IManagedForm)} to be called. This method creates the main UI stub of the page,
 * then calls {@link BasicFormPage#createBodyContent(IManagedForm)}, which should be overwritten by the subclasses to create the 
 * page specific UI components, then calls {@link BasicFormPage#loadData()} which should be overwritten by the subclasses in order to
 * load the data into the UI components. The initialization is finished after the execution of the {@link BasicFormPage#pageInitializationComplete()}
 * method. On changes triggered by the user, the special listeners (so called dirty part listeners) are 
 * marking the parts, containing the UI widgets as dirty and cause the page validation. This is done by calling the {@link BasicFormPage#validate()} method.
 * Finally, if the user triggers the editor to save the content, the {@link BasicFormPage#commit(boolean)} is called. If the editor 
 * is closed the {@link BasicFormEditor#dispose()} method is called.  
 * <br>
 * The abstract {@link BasicFormPage} class provides several facilities for the concrete implementations for different purposes:
 * <ul>
 *   <li>dirty part listeners: the dirty listener is a typed listener (e.G selection or text listener) that is triggered by a widget
 *   by some user activity and marks the part, the widget is contained in as "dirty". The "dirty" property is propagated further 
 *   to the page and the editor. During the construction of the page the dirty listeners installed on different widgets should be 
 *   added to the dirtyPartListeners list. The listeners are activated only after the data has been loaded, so any changes on the UI
 *   made during the execution load() will not affect the "dirty" state of the editor.</li>
 *   <li>images: a list of images used in the page, which will be disposed, after the page is disposed</li>
 * </ul>
 * 
 * @author Simon Zambrovski
 * @version $Id$
 */
public abstract class BasicFormPage extends FormPage implements IModelConfigurationConstants,
        IModelConfigurationDefaults, ISectionConstants, IModelOperationContainer
{
    public static final String CRASHED_TITLE = " ( model checking has crashed )";
    public static final String RUNNING_TITLE = " ( model checking is in progress )";

    /** 
     * a list of dirty part listeners, which marks parts as dirty on input and cause the re-validation of the input
     */
    protected ListenerList dirtyPartListeners = new ListenerList();
    /** 
     * the initialization status. Becomes true, after the {@link BasicFormPage#pageInitializationComplete()} method is executed
     */
    protected boolean initialized = false;
    /**
     * The local context id accociated with this page
     */
    protected String helpId = null;
    /**
     * Image used in the heading of the page
     */
    protected String imagePath = null;
    /**
     * Fomr rebuilding listener responsible for page reflow
     */
    protected IExpansionListener formRebuildingListener = null;

    // image registry
    private Hashtable images = new Hashtable();
    // the page completion status (true by default)
    private boolean isComplete = true;

    /**
     * Creates the main editor page
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

        ScrolledForm formWidget = managedForm.getForm();
        formWidget.setText(getTitle());
        if (imagePath != null)
        {
            formWidget.setImage(createRegisteredImage(imagePath));
        }

        Composite body = formWidget.getBody();

        FormToolkit toolkit = managedForm.getToolkit();
        toolkit.decorateFormHeading(formWidget.getForm());

        // head construction ---------------------
        IToolBarManager toolbarManager = formWidget.getForm().getToolBarManager();

        // run button
        toolbarManager.add(new DynamicContributionItem(new RunAction()));
        toolbarManager.add(new DynamicContributionItem(new GenerateAction()));
        // stop button
        toolbarManager.add(new DynamicContributionItem(new StopAction()));

        // refresh the tool-bar
        toolbarManager.update(true);

        // setup body layout
        body.setLayout(getBodyLayout());

        // create the body of the page
        createBodyContent(managedForm);

        super.createFormContent(managedForm);
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
        UIHelper.setHelp(body, helpId);
    }

    /**
     * Method to fill data in to the page from the model. This method is called as a part 
     * of the page life cycle. It is called after all the UI elements have been constructed but
     * before the completion of the page initialization.
     * 
     * Subclasses should override this method and fill the data in to the widgets
     * @throws CoreException thrown on any error during loading 
     */
    protected void loadData() throws CoreException
    {

    }

    /**
     * Method finalizing the page initialization
     * This method activates the dirty part listeners  
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
     * Validates the data entries entered in the input fields. The validate method is called 
     * on any change in the fields. For this to work, the corresponding listeners are registered 
     * on the widgets. These listeners make the parts/pages "dirty" on input and call validate on 
     * the pages. In addition, the validate is called if the relevant parts of the model are changed 
     * (that is changing the TLA files and the model file).
     * <br>
     * Another case, when this method is called, is on model change, by the validateRunnable of the ModelEditor.
     * 
     * <br>
     * Subclasses should override this method and add some page specific validation code. In doing so, it is
     * important to call <code>super.validate()</code>, since the implementation is responsible for handling
     * errors, supplied as persistent error markers on the model file.
     * 
     * @param switchToErrorPage control if on errors switching to the error page is done
     */
    public void validatePage(boolean switchToErrorPage)
    {
        // We don't want to switch to the error page just because the user
        // typed a character into some field.
        handleProblemMarkers(false);
    }

    /**
     * Handle the problem markers 
     */
    public void handleProblemMarkers(boolean switchToErrorPage)
    {
        // delegate to the editor
        ((ModelEditor) getEditor()).handleProblemMarkers(switchToErrorPage);
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
        getDataBindingManager().expandSection(sectionId);
    }

    /**
     * Enables or disables the page
     * @param enabled, if true the page controls are enabled, otherwise disabled
     */
    public void setEnabled(boolean enabled)
    {
        getDataBindingManager().setAllSectionsEnabled(getId(), enabled);
        getManagedForm().getForm().getBody().setEnabled(enabled);
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
     * Checks if the elements of the given list comply with the requirement of being not already defined in the context
     * of the current model and the specification. The method will iterate through the list and check whether every element
     * satisfies the requirement. On violation, it adds the error message to the message manager.  
     * @param values The list to check
     * @param listSource the control serving as the origin of the list, on errors a small error icon will be added next to it 
     * @param errorMessagePrefix the prefix of the error messages to be used
     * @param elementType the type of the element, used in the error message
     * @param listSourceDescription the description of the list source, used in error reporting
     * @param sectionIndex index of the section to expand
     * @param addToContext iff true, the values will be added to the context of the current model 
     */
    public void validateUsage(String attributeName, List values, String errorMessagePrefix, String elementType,
            String listSourceDescription, boolean addToContext)
    {
        if (values == null)
        {
            return;
        }

        DataBindingManager dm = getDataBindingManager();
        // find the section for the attribute
        String sectionId = dm.getSectionForAttribute(attributeName);
        if (sectionId == null)
        {
            throw new IllegalArgumentException("No section for attribute " + attributeName + " found");
        }
        // retrieve the control
        Control widget = UIHelper.getWidget(dm.getAttributeControl(attributeName));

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
                    if (location.source().equals(SemanticHelper.TLA_BUILTIN))
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
                mm.addMessage(errorMessagePrefix + i, message, value.toString(), IMessageProvider.ERROR, widget);
                setComplete(false);
                expandSection(sectionId);
            } else
            {
                // just adding the name
                if (addToContext)
                {
                    helper.addName(value, this, listSourceDescription);
                }
            }
        }
    }

    /**
     * Validates if the elements of the list are ids
     * @param attributeName name of the attribute
     * @param values
     * @param errorMessagePrefix
     * @param elementType
     */
    public void validateId(String attributeName, List values, String errorMessagePrefix, String elementType)
    {
        if (values == null)
        {
            return;
        }

        DataBindingManager dm = getDataBindingManager();
        // find the section for the attribute
        String sectionId = dm.getSectionForAttribute(attributeName);
        if (sectionId == null)
        {
            throw new IllegalArgumentException("No section for attribute " + attributeName + " found");
        }
        // retrieve the control
        Control widget = UIHelper.getWidget(dm.getAttributeControl(attributeName));

        String message;
        IMessageManager mm = getManagedForm().getMessageManager();
        for (int i = 0; i < values.size(); i++)
        {
            String value = (String) values.get(i);
            if (!FormHelper.isIdentifier(value))
            {
                message = elementType + " " + value + " may not be used, since it is not a valid identifier."
                        + "\nAn identifier is non-empty sequence of letters, digits und '_' with at least one letter.";
                mm.addMessage(errorMessagePrefix + i, message, value.toString(), IMessageProvider.ERROR, widget);
                setComplete(false);
                expandSection(sectionId);
            }
        }
    }

    /**
     * Retrieves the data binding manager
     */
    public DataBindingManager getDataBindingManager()
    {
        return ((ModelEditor) getEditor()).getDataBindingManager();
    }

    /**
     * delegate to the editor
     */
    public void doRun()
    {
        ((ModelEditor) getEditor()).launchModel(TLCModelLaunchDelegate.MODE_MODELCHECK, true);
    }

    /**
     * delegate to the editor
     */
    public void doGenerate()
    {
        ((ModelEditor) getEditor()).launchModel(TLCModelLaunchDelegate.MODE_GENERATE, true);
    }

    /**
     * delegate to the editor
     */
    public void doStop()
    {
        ((ModelEditor) getEditor()).stop();
    }

    /**
     * Deletes messages (with bubbles) from the current page
     * @param applyChange iff set to <code>true</code> makes the changes visible
     */
    public void resetAllMessages(boolean applyChange)
    {
        getManagedForm().getMessageManager().setAutoUpdate(false);
        // clean old messages
        getManagedForm().getMessageManager().removeAllMessages();
        // make the run possible
        setComplete(true);
        // make the change visible
        getManagedForm().getMessageManager().setAutoUpdate(applyChange);
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
            this.setToolTipText("Runs TLC on the model.");
        }

        public void run()
        {
            doRun();
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
     * The generate action
     */
    class GenerateAction extends Action
    {
        GenerateAction()
        {
            super("Generate", TLCUIActivator.imageDescriptorFromPlugin(TLCUIActivator.PLUGIN_ID,
                    "icons/full/debugt_obj.gif"));
            this.setDescription("Validate model");
            this.setToolTipText("Checks the model for errors but does not run TLC on it.");
        }

        public void run()
        {
            doGenerate();
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
            super("Stop", TLCUIActivator.imageDescriptorFromPlugin(TLCUIActivator.PLUGIN_ID,
                    "icons/full/progress_stop.gif"));
            this.setDescription("Stop TLC");
            this.setToolTipText("Stops the current TLC model checker run.");
        }

        public void run()
        {
            doStop();
        }

        /**
         * Run is only enabled if the model is not in use
         */
        public boolean isEnabled()
        {
            return isModelInUse() && !isModelStale();
        }
    }

    /**
     * Recovery action added to the model editor (top right corner) if the model is crashed 
     */
    class ModelRecoveryAction extends Action
    {
        ModelRecoveryAction()
        {
            super("Restore model", TLCUIActivator.imageDescriptorFromPlugin(TLCUIActivator.PLUGIN_ID,
                    "icons/full/loop_obj.gif"));
            this.setDescription("Restore model");
            this.setToolTipText("Restores the model after the TLC crashed.");
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