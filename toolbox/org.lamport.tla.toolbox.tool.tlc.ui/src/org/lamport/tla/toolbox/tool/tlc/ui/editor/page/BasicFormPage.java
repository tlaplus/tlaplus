package org.lamport.tla.toolbox.tool.tlc.ui.editor.page;

import java.util.Hashtable;
import java.util.List;
import java.util.function.Consumer;

import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.ListenerList;
import org.eclipse.jface.action.Action;
import org.eclipse.jface.action.IToolBarManager;
import org.eclipse.jface.action.ToolBarManager;
import org.eclipse.jface.dialogs.IMessageProvider;
import org.eclipse.jface.resource.ImageDescriptor;
import org.eclipse.swt.SWT;
import org.eclipse.swt.events.FocusEvent;
import org.eclipse.swt.events.FocusListener;
import org.eclipse.swt.graphics.Image;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.eclipse.swt.widgets.Layout;
import org.eclipse.swt.widgets.ToolBar;
import org.eclipse.ui.INavigationHistory;
import org.eclipse.ui.INavigationLocation;
import org.eclipse.ui.INavigationLocationProvider;
import org.eclipse.ui.forms.IManagedForm;
import org.eclipse.ui.forms.IMessage;
import org.eclipse.ui.forms.IMessageManager;
import org.eclipse.ui.forms.editor.FormEditor;
import org.eclipse.ui.forms.editor.FormPage;
import org.eclipse.ui.forms.events.ExpansionAdapter;
import org.eclipse.ui.forms.events.ExpansionEvent;
import org.eclipse.ui.forms.events.HyperlinkAdapter;
import org.eclipse.ui.forms.events.HyperlinkEvent;
import org.eclipse.ui.forms.events.IExpansionListener;
import org.eclipse.ui.forms.events.IHyperlinkListener;
import org.eclipse.ui.forms.widgets.FormToolkit;
import org.eclipse.ui.forms.widgets.ScrolledForm;
import org.eclipse.ui.forms.widgets.Section;
import org.lamport.tla.toolbox.tool.tlc.launch.IModelConfigurationConstants;
import org.lamport.tla.toolbox.tool.tlc.launch.IModelConfigurationDefaults;
import org.lamport.tla.toolbox.tool.tlc.launch.TLCModelLaunchDelegate;
import org.lamport.tla.toolbox.tool.tlc.model.Model;
import org.lamport.tla.toolbox.tool.tlc.ui.TLCUIActivator;
import org.lamport.tla.toolbox.tool.tlc.ui.contribution.DynamicContributionItem;
import org.lamport.tla.toolbox.tool.tlc.ui.editor.DataBindingManager;
import org.lamport.tla.toolbox.tool.tlc.ui.editor.ISectionConstants;
import org.lamport.tla.toolbox.tool.tlc.ui.editor.ModelEditor;
import org.lamport.tla.toolbox.tool.tlc.ui.util.DirtyMarkingListener;
import org.lamport.tla.toolbox.tool.tlc.ui.util.FormHelper;
import org.lamport.tla.toolbox.tool.tlc.ui.util.IgnoringListener;
import org.lamport.tla.toolbox.tool.tlc.ui.util.SemanticHelper;
import org.lamport.tla.toolbox.tool.tlc.ui.util.TLCUIHelper;
import org.lamport.tla.toolbox.tool.tlc.ui.view.TLCErrorView;
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
        IModelConfigurationDefaults, ISectionConstants, IModelOperationContainer, INavigationLocationProvider
{
    public static final String CRASHED_TITLE = " ( model checking has crashed )";
    public static final String RUNNING_TITLE = " ( model checking is in progress )";
    public static final String IMAGE_TEMPLATE_TOKEN = "[XXXXX]";
    
    /**
     * If a section has a data with this key, the returned object is assumed to be an implementor of Consumer<Boolean>
     * 	which will be invoked during {@link #compensateForExpandableCompositesPoorDesign(Section, boolean)} with
     *  the boolean value being true if the section is expanding.
     */
    protected static final String SECTION_EXPANSION_LISTENER = "_why_oh_why_..._sigh";
    
    private static final String TLC_ERROR_STRING = "TLC Error";
    
    /** 
     * a list of dirty part listeners, which marks parts as dirty on input and cause the re-validation of the input
     */
    protected ListenerList<DirtyMarkingListener> dirtyPartListeners = new ListenerList<DirtyMarkingListener>();
    /** 
     * the initialization status. Becomes true, after the {@link BasicFormPage#pageInitializationComplete()} method is executed
     */
    protected boolean initialized = false;
    /**
     * The local context id accociated with this page
     */
    protected String helpId = null;
    /**
     * Image path template used in the heading of the page
     */
    private String imagePathTemplate;
    
    /**
     * Fomr rebuilding listener responsible for page reflow
     */
    protected IExpansionListener formRebuildingListener = null;

    // image registry
    private Hashtable<String, Image> images = new Hashtable<String, Image>();
    // the page completion status (true by default)
    private boolean isComplete = true;

    protected ToolBarManager headClientTBM = null;

    /**
	 * A {@link FocusListener} responsible for marking a location in the
	 * navigation history whenever the current focus changes. It's the
	 * responsibility of subclasses to add this listener to their
	 * {@link Control}s in the
	 * {@link BasicFormPage#createBodyContent(IManagedForm)} method.
	 */
    protected final FocusListener focusListener = new FocusListener() {
    	/* (non-Javadoc)
    	 * @see org.eclipse.swt.events.FocusListener#focusGained(org.eclipse.swt.events.FocusEvent)
    	 */
    	public void focusGained(final FocusEvent event) {
    		final INavigationHistory navigationHistory = getSite().getPage().getNavigationHistory();
    		navigationHistory.markLocation(BasicFormPage.this);
    	}
		/* (non-Javadoc)
		 * @see org.eclipse.swt.events.FocusListener#focusLost(org.eclipse.swt.events.FocusEvent)
		 */
		public void focusLost(FocusEvent e) {
			// keeping a history does not need the focusLost event 
		}
	};
	
    // hyper link listener activated in case of errors
    protected IHyperlinkListener errorMessageHyperLinkListener = new HyperlinkAdapter() {

        public void linkActivated(HyperlinkEvent e)
        {
            IMessage[] messages = (IMessage[]) e.getHref();
            // if it is a global TLC error, it will shift focus to the error view
            if (messages.length > 0 && messages[0].getMessage().equals(TLC_ERROR_STRING))
            {
                if (getModel() != null)
                {
                    TLCErrorView.updateErrorView(getModelEditor());
                }
            } else
            {
                // will attempt to get a control
                // if there is an error on this page
                // the control will be one of the controls
                // with the error
                // if there is no error on this page
                // the control will be one of the controls
                // with an error on another page
                Control control = null;

                // for all other types of messages, determine
                // if the error is on this page
                boolean errorOnThisPage = false;
                for (int i = 0; i < messages.length; i++)
                {
                    if (messages[i].getData() instanceof String)
                    {
                        // the data should be the pageId as set in
                        // the methods handleProblemMarkers() and
                        // addErrorMessage() in ModelEditor
                        String pageId = (String) messages[i].getData();
                        if (pageId != null && pageId == getId())
                        {
                            errorOnThisPage = true;
                            control = messages[i].getControl();
                        }
                    }
                }
                if (!errorOnThisPage)
                {
                    // find the first message with a page id
                    // and switch to that page
                    for (int i = 0; i < messages.length; i++)
                    {
                        if (messages[i].getData() instanceof String)
                        {
                            // the data should be the pageId as set in
                            // the methods handleProblemMarkers() and
                            // addErrorMessage() in ModelEditor
                            String pageId = (String) messages[i].getData();
                            if (pageId != null)
                            {
                                getEditor().setActivePage(pageId);
                                control = messages[i].getControl();
                                break;
                            }
                        }
                    }
                }
                if (control != null)
                {
                    control.setFocus();
                    if (control.getParent().getParent() instanceof Section)
                    {
                        Section section = (Section) control.getParent().getParent();
                        section.setExpanded(true);
                    }
                }
            }
        }
    };

    /**
	 * Creates the main editor page
	 * 
	 * @param editor
	 * @param id
	 * @param title
	 * @param pageImagePathTemplate should contain <code>IMAGE_TEMPLATE_TOKEN</code>
	 *                              which will be replaced with 16 or 24 depending
	 *                              on the application; images of such naming are
	 *                              assumed to exist on the filesystem.
	 */
	public BasicFormPage(final FormEditor editor, final String id, final String title,
			final String pageImagePathTemplate) {
        super(editor, id, title);
        
        imagePathTemplate = pageImagePathTemplate;
    }
    
    /**
     * {@inheritDoc}
     */
	@Override
	public Image getTitleImage() {
		// Display the page's image left of the page's name on the tar bar. E.g. the
		// main model page displays three sliders left of its "Model
		// Overview" label. createFormContent below additionally sets a slightly
		// larger version of the same image on the page itself (not on the tab bar).
		return createRegisteredImage(16);
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
        if (imagePathTemplate != null)
        {
			// Show the given image left of the form page's title and beneath the tab
			// bar. E.g. the main model page displays three sliders left of its "Model
			// Overview" label.
            formWidget.setImage(createRegisteredImage(24));
        }

        Composite body = formWidget.getBody();

        FormToolkit toolkit = managedForm.getToolkit();
        toolkit.decorateFormHeading(formWidget.getForm());

        /*
         * The head client is the second row of the header section, below the title; if we don't create this
         * with 'NO_FOCUS' then the toolbar will always take focus on a form page that gains focus.
         */
        ToolBar headClientTB = new ToolBar(formWidget.getForm().getHead(), SWT.HORIZONTAL | SWT.NO_FOCUS);
        headClientTBM = new ToolBarManager(headClientTB);
        // run button
        headClientTBM.add(new DynamicContributionItem(new RunAction()));
        // validate button
        headClientTBM.add(new DynamicContributionItem(new GenerateAction()));
        // stop button
        headClientTBM.add(new DynamicContributionItem(new StopAction()));

        // refresh the head client toolbar
        headClientTBM.update(true);

        formWidget.getForm().setHeadClient(headClientTB);

        // setup body layout
        body.setLayout(getBodyLayout());

        // create the body of the page
        createBodyContent(managedForm);

        super.createFormContent(managedForm);
        try
        {
            // load data from the model
        	//TODO decouple from UI thread (causes I/O)
            loadData();
        } catch (CoreException e)
        {
            TLCUIActivator.getDefault().logError("Error loading data from the model into the form fields", e);
        }

        // check the model is-running state
        refresh();

        // finalizes the page construction
        // activates the change listeners
        pageInitializationComplete();
        TLCUIHelper.setHelp(getPartControl(), helpId);

        getManagedForm().getForm().getForm().addMessageHyperlinkListener(errorMessageHyperLinkListener);
    }

    /* (non-Javadoc)
	 * @see org.eclipse.ui.INavigationLocationProvider#createEmptyNavigationLocation()
	 */
	public INavigationLocation createEmptyNavigationLocation() {
		final NavigationLocationComposite combinedFormNav = new NavigationLocationComposite();
		
		// save the current FormPage as a navigation control
		combinedFormNav.add(new TabNavigationLocation(this));
	
		// the control selected on the current page
		final Control focusControl = getSite().getShell().getDisplay().getFocusControl();
		if (focusControl != null) {
			combinedFormNav.add(new ControlNavigationLocation(focusControl));
		}
		
		return combinedFormNav;
	}

	/* (non-Javadoc)
	 * @see org.eclipse.ui.INavigationLocationProvider#createNavigationLocation()
	 */
	public INavigationLocation createNavigationLocation() {
        return createEmptyNavigationLocation();
    }

	/**
     * Method to fill data in to the page from the model. This method is called as a part 
     * of the page life cycle. It is called after all the UI elements have been constructed but
     * before the completion of the page initialization.
     * 
     * Subclasses should override this method and fill the data in to the widgets
     * @throws CoreException thrown on any error during loading 
     */
	protected void loadData() throws CoreException { }

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
    protected abstract void createBodyContent(IManagedForm managedForm);

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
    
	// There is no way to exaggerate how poorly designed SWT and SWT-adjacent Eclipse code is... the ExpandableComposite
	//		does not fire an expansion listener notification on setExpanded and there is no way to get to the
	//		listeners to do it ourselves... i mean the whole thing is so absurdly bad.
    // .. and the only reason we have to worry about the listeners being notified is because the form page won't
    //		layout correct unless we turn the section's grid layout data's vertical grab on and off...
    // It is disabled turtles all the way down over at eclipse.org...
	@SuppressWarnings("unchecked") // generic casting
    protected void compensateForExpandableCompositesPoorDesign(final Section section, final boolean expand) {
    	section.setExpanded(expand);
    	
		if (section.getData(FormHelper.SECTION_IS_NOT_SPACE_GRABBING) == null) {
			final GridData gd = (GridData) section.getLayoutData();
			gd.grabExcessVerticalSpace = expand;
			section.setLayoutData(gd);
		}
		
		final Object o = section.getData(SECTION_EXPANSION_LISTENER);
		if (o != null) {
			((Consumer<Boolean>)o).accept(Boolean.valueOf(expand));
		}
    }

    /**
     * Retrieves the image and remember it for later reuse / dispose
     * @param size the pixel dimension of the image desired
     * @return
     */
    protected Image createRegisteredImage(final int size)
    {
    	final String imagePath = imagePathTemplate.replace(IMAGE_TEMPLATE_TOKEN, Integer.toString(size));
        Image image = (Image) images.get(imagePath);
        if (image == null)
        {
            final ImageDescriptor id = TLCUIActivator.imageDescriptorFromPlugin(TLCUIActivator.PLUGIN_ID, imagePath);
            if (id != null)
            {
                image = id.createImage();
                images.put(imagePath, image);
            }
        }

        return image;
    }

    public Model getModel() {
    	return getModelEditor().getModel();
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
    private void handleProblemMarkers(boolean switchToErrorPage)
    {
        // delegate to the editor
        getModelEditor().handleProblemMarkers(switchToErrorPage);
    }

	protected ModelEditor getModelEditor() {
		return (ModelEditor) getEditor();
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
	 * Expands the given sections.
	 */
	public void expandSections(final String[] sections) {
		for (String section : sections) {
			expandSection(section);
		}
	}

    /**
     * Enables or disables the page
     * @param enabled, if true the page controls are enabled, otherwise disabled
     */
    public void setEnabled(boolean enabled)
    {
        getDataBindingManager().setAllSectionsEnabled(getId(), enabled);
    }

    /**
     * Disposes the images
     */
    public void dispose()
    {
    	for (final Image i : images.values()) {
    		i.dispose();
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
            boolean modelRunning = getModel().isRunning();

            // refresh the title
            String title = mForm.getForm().getText();
            int titleIndex = Math.max(title.indexOf(RUNNING_TITLE), title.indexOf(CRASHED_TITLE));
            // restore the title
            if (titleIndex != -1)
            {
                title = title.substring(0, titleIndex);
            }

            if (modelRunning)
            {
                if (getModel().isStale())
                {
                    mForm.getForm().setText(title + CRASHED_TITLE);
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

            // refresh the tool-bars
            toolbarManager.markDirty();
            toolbarManager.update(true);
            if (headClientTBM != null)
            {
                headClientTBM.markDirty();
                headClientTBM.update(true);
            }

            // refresh enablement status
            setEnabled(!modelRunning);
            mForm.getForm().update();

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
     * @param addToContext iff true, the values will be added to the context of the current model 
     */
    public void validateUsage(String attributeName, List<String> values, String errorMessagePrefix, String elementType,
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
        
        validateUsage(sectionId, widget, values, errorMessagePrefix, elementType, listSourceDescription, addToContext);
    }

    public void validateUsage(final String sectionId, final Control widget, List<String> values, String errorMessagePrefix, String elementType,
             String listSourceDescription, boolean addToContext)
    {
        IMessageManager mm = getManagedForm().getMessageManager();
        SemanticHelper helper = getLookupHelper();
        String message;
        for (int i = 0; i < values.size(); i++)
        {
            String value = values.get(i);
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
    public void validateId(String attributeName, List<String> values, String errorMessagePrefix, String elementType)
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
        
        validateId(sectionId, widget, values, errorMessagePrefix, elementType);
    }

    public void validateId(final String sectionId, final Control widget, List<String> values, String errorMessagePrefix, String elementType)
    {
        String message;
        IMessageManager mm = getManagedForm().getMessageManager();
        for (int i = 0; i < values.size(); i++)
        {
            String value = values.get(i);
            if (!FormHelper.isIdentifier(value))
            {
                if (value.trim().equals(""))
                {
                    message = elementType + " has been omitted.";

                } else
                {
                    message = elementType
                            + " "
                            + value
                            + " may not be used, since it is not a valid identifier."
                            + "\nAn identifier is a non-empty sequence of letters, digits and '_' with at least one letter.";
                }

                mm.addMessage(errorMessagePrefix + i, message, value.toString(), IMessageProvider.ERROR, widget);
                setComplete(false);
                expandSection(sectionId);
            }
        }
    }

    /**
     * Subclasses may override this to be notified when model checking is about to be launched.
     */
    public void modelCheckingWillBegin() { }
    
    /**
     * Retrieves the data binding manager
     */
    public DataBindingManager getDataBindingManager()
    {
        return getModelEditor().getDataBindingManager();
    }

    /**
     * delegate to the editor
     */
    public void doRun()
    {
        getModelEditor().launchModel(TLCModelLaunchDelegate.MODE_MODELCHECK, true);
    }

    /**
     * delegate to the editor
     */
    public void doGenerate()
    {
        getModelEditor().launchModel(TLCModelLaunchDelegate.MODE_GENERATE, true);
    }

    /**
     * delegate to the editor
     */
    public void doStop()
    {
        getModelEditor().stop();
    }

    /**
     * Deletes messages (with bubbles) from the current page
     * @param applyChange iff set to <code>true</code> makes the changes visible
     * 
     * The comment above was probably written by Simon.  It seems to be false
     * because calling this method removes the error "message" at the top of the
     * page that says how many errors there are, but it doesn't remove the bubbles
     * (which I presume are the red X icons placed near the source of the error).
     * LL 15 Mar 2013
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

    public void resetMessage(final Object key) {
        getManagedForm().getMessageManager().setAutoUpdate(false);
        getManagedForm().getMessageManager().removeMessage(key);
        // make the run possible
        setComplete(true);
        // make the change visible
        getManagedForm().getMessageManager().setAutoUpdate(true);
    }
    
    /**
     * This method adds the text "TLC Error" next to the title of the page.
     * The text will appear as a hyperlink. Clicking on the link will give
     * focus to the TLC Errors view.
     * This should be called when there is a TLC error that is not bound
     * to a particular widget in the model editor. Currently it is called
     * from the method {@link ModelEditor#handleProblemMarkers(boolean)}.
     * This should not be called on the result page because there is already
     * an errors hyperlink there.
     * @param tooltipText the tooltip text to appear when the mouse is on the hyperlink
     */
    public void addGlobalTLCErrorMessage(String key)
    {
    	addGlobalTLCErrorMessage(key, TLC_ERROR_STRING);
    }
    
    public void addGlobalTLCErrorMessage(String key, String message)
    {
    	IMessageManager mm = getManagedForm().getMessageManager();
        mm.addMessage(key, message, null, IMessageProvider.WARNING);
        /*globalTLCErrorHyperLink.setText(TLC_ERROR_STRING);
        globalTLCErrorHyperLink.setToolTipText(tooltipText);
        globalTLCErrorHyperLink.setForeground(TLCUIActivator.getColor(SWT.COLOR_DARK_YELLOW));
        globalTLCErrorHyperLink.addHyperlinkListener(globalTLCErrorHyperLinkListener);*/
    }

    /**
     * The run action
     */
    class RunAction extends Action
    {
    	// TODO: HiDPI on this icon as we also have an @2x version
        RunAction() {
            super("Run", TLCUIActivator.imageDescriptorFromPlugin(TLCUIActivator.PLUGIN_ID, "icons/full/run_exc.png"));
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
            return !getModel().isRunning();
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
            return !getModel().isRunning();
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
            return getModel().isRunning() || getModel().isRunningRemotely();
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
        	((ModelEditor) getEditor()).getModel().recover();
        }

        public boolean isEnabled()
        {
            return getModel().isStale();
        }
    }

}