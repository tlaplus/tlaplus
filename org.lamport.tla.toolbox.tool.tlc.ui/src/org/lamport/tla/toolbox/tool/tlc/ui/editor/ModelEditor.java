package org.lamport.tla.toolbox.tool.tlc.ui.editor;

import java.io.ByteArrayInputStream;
import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.text.SimpleDateFormat;
import java.util.List;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IFolder;
import org.eclipse.core.resources.IMarker;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.IResourceChangeEvent;
import org.eclipse.core.resources.IResourceChangeListener;
import org.eclipse.core.resources.IResourceDelta;
import org.eclipse.core.resources.IWorkspace;
import org.eclipse.core.resources.IWorkspaceRunnable;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.resources.WorkspaceJob;
import org.eclipse.core.runtime.Assert;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.MultiStatus;
import org.eclipse.core.runtime.NullProgressMonitor;
import org.eclipse.core.runtime.Platform;
import org.eclipse.core.runtime.Status;
import org.eclipse.core.runtime.SubProgressMonitor;
import org.eclipse.core.runtime.jobs.Job;
import org.eclipse.jface.dialogs.IMessageProvider;
import org.eclipse.jface.dialogs.IPageChangedListener;
import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.jface.dialogs.PageChangedEvent;
import org.eclipse.swt.SWT;
import org.eclipse.swt.custom.CTabFolder;
import org.eclipse.swt.custom.CTabFolder2Adapter;
import org.eclipse.swt.custom.CTabFolder2Listener;
import org.eclipse.swt.custom.CTabFolderEvent;
import org.eclipse.swt.custom.CTabItem;
import org.eclipse.swt.widgets.Control;
import org.eclipse.swt.widgets.Display;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.ui.IEditorInput;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.IEditorReference;
import org.eclipse.ui.IEditorSite;
import org.eclipse.ui.INavigationHistory;
import org.eclipse.ui.IPartService;
import org.eclipse.ui.PartInitException;
import org.eclipse.ui.forms.IMessageManager;
import org.eclipse.ui.forms.editor.FormEditor;
import org.eclipse.ui.forms.editor.IFormPage;
import org.eclipse.ui.part.FileEditorInput;
import org.eclipse.ui.texteditor.ITextEditor;
import org.lamport.tla.toolbox.Activator;
import org.lamport.tla.toolbox.spec.Spec;
import org.lamport.tla.toolbox.spec.parser.IParseConstants;
import org.lamport.tla.toolbox.tool.tlc.TLCActivator;
import org.lamport.tla.toolbox.tool.tlc.launch.IModelConfigurationDefaults;
import org.lamport.tla.toolbox.tool.tlc.launch.TLCModelLaunchDelegate;
import org.lamport.tla.toolbox.tool.tlc.model.Model;
import org.lamport.tla.toolbox.tool.tlc.model.Model.StateChangeListener.ChangeEvent.State;
import org.lamport.tla.toolbox.tool.tlc.model.TLCModelFactory;
import org.lamport.tla.toolbox.tool.tlc.output.data.TLCModelLaunchDataProvider;
import org.lamport.tla.toolbox.tool.tlc.output.source.TLCOutputSourceRegistry;
import org.lamport.tla.toolbox.tool.tlc.ui.TLCUIActivator;
import org.lamport.tla.toolbox.tool.tlc.ui.editor.page.AdvancedModelPage;
import org.lamport.tla.toolbox.tool.tlc.ui.editor.page.BasicFormPage;
import org.lamport.tla.toolbox.tool.tlc.ui.editor.page.ErrorMessage;
import org.lamport.tla.toolbox.tool.tlc.ui.editor.page.MainModelPage;
import org.lamport.tla.toolbox.tool.tlc.ui.editor.page.results.ResultPage;
import org.lamport.tla.toolbox.tool.tlc.ui.preference.ITLCPreferenceConstants;
import org.lamport.tla.toolbox.tool.tlc.ui.util.ModelEditorPartListener;
import org.lamport.tla.toolbox.tool.tlc.ui.util.SemanticHelper;
import org.lamport.tla.toolbox.tool.tlc.ui.view.TLCErrorView;
import org.lamport.tla.toolbox.tool.tlc.util.ChangedSpecModulesGatheringDeltaVisitor;
import org.lamport.tla.toolbox.tool.tlc.util.ModelHelper;
import org.lamport.tla.toolbox.ui.handler.OpenSpecHandler;
import org.lamport.tla.toolbox.ui.view.PDFBrowserEditor;
import org.lamport.tla.toolbox.util.ResourceHelper;
import org.lamport.tla.toolbox.util.UIHelper;

import com.abstratt.graphviz.GraphViz;

import tla2sany.semantic.ModuleNode;

/**
 * Editor for the model
 * @author Simon Zambrovski
 */
public class ModelEditor extends FormEditor
{
	private static final SimpleDateFormat sdf = new SimpleDateFormat("MMM dd,yyyy HH:mm:ss");

	/**
     * Editor ID
     */
    public static final String ID = "org.lamport.tla.toolbox.tool.tlc.ui.editor.ModelEditor";

    /*
     * working copy of the model
     */
    // helper to resolve semantic matches of words
    private SemanticHelper helper;
    private final Model.StateChangeListener modelStateListener = new Model.StateChangeListener() {
		@Override
		public boolean handleChange(final ChangeEvent event) {
			if (event.getState().in(State.NOT_RUNNING, State.RUNNING)) {
				UIHelper.runUIAsync(new Runnable() {
					public void run() {
						for (int i = 0; i < getPageCount(); i++) {
							final Object object = pages.get(i);
							if (object instanceof BasicFormPage) {
								final BasicFormPage bfp = (BasicFormPage) object;
								bfp.refresh();
							}
						}
						if (event.getState().in(State.RUNNING)) {
							// Switch to Result Page (put on top) of model editor stack. A user wants to see
							// the status of a model run she has just started.
							ModelEditor.this.showResultPage();
						}
						if (event.getState().in(State.NOT_RUNNING)) {
							// Model checking finished, lets open state graph if any.
							if (event.getModel().hasStateGraphDump()) {
								try {
									ModelEditor.this.addOrUpdateStateGraphEditor(event.getModel().getStateGraphDump());
								} catch (CoreException e) {
									TLCUIActivator.getDefault().logError("Error initializing editor", e);
								}
							}
							
							// MAK 01/2018: Re-validate the page because running the model removes or sets
							// problem markers (Model#setMarkers) which are presented to the user by
							// ModelEditor#handleProblemMarkers. If we don't re-validate once a model is
							// done running, the user visible presentation resulting from an earlier run of
							// handleProblemMarkers gets stale.
							// This behavior can be triggered by creating a spec (note commented EXTENDS): 
							//   \* EXTENDS Integers
							//   VARIABLE s
							//   Spec == s = 0 /\ [][s'=s]_s
							// and a model that defines the invariant (s >= 0). Upon the first launch of
							// the model, the ModelEditor correctly marks the invariant due to the operator
							// >= being not defined. Uncommenting EXTENDS, saving the spec and rerunning
							// the model would incorrectly not remove the marker on the invariant.
							UIHelper.runUISync(validateRunable);
						}
					}
				});
			}
			return false;
		}
	};

    /**
     * This runnable is responsible for the validation of the pages.
     * It iterates over the pages and calls validate on them. At this point it assumes,
     * that every page is a subclass of the BasicFormPage.
     * This runnable must be called in the UI thread (using UIHelper.runUIAsync() method).
     * It is used in the workspace root listener and is called once after the input is set and after the pages 
     * are added.
     */
    private final ValidateRunnable validateRunable = new ValidateRunnable();

    private class ValidateRunnable implements Runnable
    {

        private boolean switchToErrorPage = false;

        public void run()
        {
            // Re-validate the pages, iff the model is not running.
			// Also check if the model is nulled by now which
			// happens if the ModelEditor disposed before a scheduled run gets
			// executed.
            if (model != null && !model.isRunning())
            {
                /*
                 * Note that all pages are not necessarily
                 * instances of BasicFormPage. Some are read
                 * only editors showing saved versions of
                 * modules.
                 */
                for (int i = 0; i < getPageCount(); i++)
                {
                    if (pages.get(i) instanceof BasicFormPage)
                    {
                        BasicFormPage page = (BasicFormPage) pages.get(i);
                        page.resetAllMessages(true);
                    }
                }
                for (int i = 0; i < getPageCount(); i++)
                {
                    if (pages.get(i) instanceof BasicFormPage)
                    {
                        BasicFormPage page = (BasicFormPage) pages.get(i);
                        // re-validate the model on changes of the spec
                        page.validatePage(switchToErrorPage);
                    }
                }
            }
        }
    };

    // react on spec file changes
    private IResourceChangeListener workspaceResourceChangeListener = new IResourceChangeListener() {
        public void resourceChanged(IResourceChangeEvent event)
        {
            IResourceDelta delta = event.getDelta();

            /**
             * This is a helper method that returns a new instance of ChangedModulesGatheringDeltaVisitor,
             * which gathers the changed TLA modules from a resource delta tree.
             */
            ChangedSpecModulesGatheringDeltaVisitor visitor = new ChangedSpecModulesGatheringDeltaVisitor(model) {
                public IResource getModel()
                {
                    return model.getFile();
                }
            };

            try
            {
                delta.accept(visitor);
                // one of the modules in the specification has changed
                // this means that identifiers defined in a spec might have changed
                // re-validate the editor
                if (!visitor.getModules().isEmpty() || visitor.isModelChanged() || visitor.getCheckpointChanged())
                {
                    // update the specObject of the helper
                    helper.resetSpecNames();

                    // iff the model has changed, switch to the error page after the validation
                    validateRunable.switchToErrorPage = visitor.isModelChanged();

                    // re-validate the pages
                    UIHelper.runUIAsync(validateRunable);

                    return;
                }
            } catch (CoreException e)
            {
                TLCUIActivator.getDefault().logError("Error visiting changed resource", e);
                return;
            }

        }
    };

    // data binding manager
    private DataBindingManager dataBindingManager = new DataBindingManager();

    /**
     * A listener that reacts to when editor tabs showing saved modules
     * get closed. This listener properly disposes of the editor and its contents.
     * See the class documentation for more details.
     */
    private CTabFolder2Listener listener = new CloseModuleTabListener();

    // array of pages to add
    private BasicFormPage[] pagesToAdd;

	private Model model;

    /**
     * Simple editor constructor
     */
    public ModelEditor()
    {
        helper = new SemanticHelper();
        pagesToAdd = new BasicFormPage[] { new MainModelPage(this), new AdvancedModelPage(this), new ResultPage(this) };
    }

    /**
     * Initialize the editor
     */
    public void init(IEditorSite site, IEditorInput input) throws PartInitException
    {
        // TLCUIActivator.getDefault().logDebug("entering ModelEditor#init(IEditorSite site, IEditorInput input)");
        super.init(site, input);

        // grab the input
		final FileEditorInput finput = getFileEditorInput();

		// the file might not exist anymore (e.g. manually removed by the user) 
		if (finput == null || !finput.exists()) {
			throw new PartInitException("Editor input does not exist: " + finput.getName());
		}
		
        model = TLCModelFactory.getBy(finput.getFile());
        
        // setContentDescription(path.toString());
        if (model.isSnapshot()) {
        	final String date = sdf.format(model.getSnapshotTimeStamp());
            this.setPartName(model.getSnapshotFor().getName() + " (" + date + ")");
        } else {
        	this.setPartName(model.getName());
        }
        this.setTitleToolTip(model.getFile().getLocation().toOSString());

        // add a listener that will update the tlc error view when a model editor
        // is made visible
        IPartService service = (IPartService) getSite().getService(IPartService.class);
        service.addPartListener(ModelEditorPartListener.getDefault());

        /*
         * Install resource change listener on the workspace root to react on any changes in th current spec
         */
        ResourcesPlugin.getWorkspace().addResourceChangeListener(workspaceResourceChangeListener,
                IResourceChangeEvent.POST_BUILD);

        // update the spec object of the helper
        helper.resetSpecNames();

        // initial re-validate the pages, which are already loaded
        UIHelper.runUIAsync(validateRunable);
        // TLCUIActivator.getDefault().logDebug("leaving ModelEditor#init(IEditorSite site, IEditorInput input)");

        
        // Asynchronously register a PageChangedListener to now cause cyclic part init warnings
		UIHelper.runUIAsync(new Runnable() {
			public void run() {
				addPageChangedListener(pageChangedListener);
			}
		});
		
		model.add(modelStateListener);
	}

	/**
	 * This IPageChangedListener is responsible to mark the current page in the
	 * navigation location history (stack). It is here in addition to a
	 * FocusListener in BasicFormPage which additionally track the in-page
	 * selection. However, if the user does not click into the page effectively
	 * changing the selection, the FocusListener isn't triggered.
	 */
	private final IPageChangedListener pageChangedListener = new IPageChangedListener() {
		/* (non-Javadoc)
		 * @see org.eclipse.jface.dialogs.IPageChangedListener#pageChanged(org.eclipse.jface.dialogs.PageChangedEvent)
		 */
		public void pageChanged(final PageChangedEvent event) {
			final INavigationHistory navigationHistory = getSite().getPage()
					.getNavigationHistory();
			navigationHistory.markLocation((IEditorPart) event
					.getSelectedPage());
		}
	};

	/**
	 * @see org.eclipse.ui.forms.editor.FormEditor#dispose()
	 */
	public void dispose() {
		removePageChangedListener(pageChangedListener);
        // TLCUIActivator.getDefault().logDebug("entering ModelEditor#dispose()");
        // remove the listeners
        ResourcesPlugin.getWorkspace().removeResourceChangeListener(workspaceResourceChangeListener);
		model.remove(modelStateListener);

        super.dispose();
        
        // super.dispose still needs the model instance
        model = null;
        // TLCUIActivator.getDefault().logDebug("leaving ModelEditor#dispose()");
    }
	

	public boolean isDisposed() {
		return model == null;
	}

    /**
     * This method saves the model even if the spec is not parsed.  This is probably
     * a good idea, since the user may want to quit in the middle of his work without
     * losing what he's done to the model.
     * @see org.eclipse.ui.part.EditorPart#doSave(org.eclipse.core.runtime.
     * IProgressMonitor)
     */
    public void doSave(IProgressMonitor monitor)
    {
        this.commitPages(monitor, true);
        model.save(monitor);

        // remove existing markers
        model.removeMarkers(Model.TLC_MODEL_ERROR_MARKER_SANY);

        boolean revalidate = TLCUIActivator.getDefault().getPreferenceStore().getBoolean(
                ITLCPreferenceConstants.I_TLC_REVALIDATE_ON_MODIFY);
        if (revalidate)
        {
            // run SANY
            launchModel(TLCModelLaunchDelegate.MODE_GENERATE, false, monitor /*
                                                                     * the SANY
                                                                     * will run
                                                                     * only if
                                                                     * the
                                                                     * editor is
                                                                     * valid
                                                                     */);
        }

        this.editorDirtyStateChanged();
    }

    /**
     * Commits the pages and saves the config without running validation
     * on the model.
     * 
     * @param monitor
     */
    public void doSaveWithoutValidating(IProgressMonitor monitor)
    {
        this.commitPages(monitor, true);
        model.save(monitor);

        this.editorDirtyStateChanged();
    }

    /**
     * @see org.eclipse.ui.part.EditorPart#doSaveAs()
     */
    public void doSaveAs()
    {
    }

    /**
     * Ask the view for an adapter for certain class
     */
    @SuppressWarnings("unchecked")
	public <T> T getAdapter(Class<T> required)
    {
        // ask for the launch data provider
        if (TLCModelLaunchDataProvider.class.equals(required))
        {
            // return a provider, if this can be found
            TLCModelLaunchDataProvider provider = TLCOutputSourceRegistry.getModelCheckSourceRegistry().getProvider(
            		getModel());
            if (provider != null)
            {
                return (T) provider;
            }
        }  else if (IFile.class.equals(required)) {
			// The GraphViz viewer tries to get a .dot from an editor. The
			// Toolbox's model editor is the closest thing corresponding to the
			// state graph (stored as dot).
        	final IFolder folder = model.getFolder();
			final String name = model.getName().concat(".dot");
			return (T) folder.getFile(name);
        }
        return super.getAdapter(required);
    }

    public void setFocus()
    {
        /*
         * The following commented code was causing a warning that
         * said "Prevented recursive attempt to activate part
         * toolbox.tool.tlc.view.TLCErrorView while still in the
         * middle of activating part
         * org.lamport.tla.toolbox.tool.tlc.ui.editor.ModelEditor"
         * 
         * The updating of the error view is now done by registering a
         * part listener in the init method of the modeleditor. This
         * part listener is an instance of ModelEditorPartListener()
         * whose partVisible() method does the updating of the
         * TLCErrorView.
         */
        // final TLCModelLaunchDataProvider provider = (TLCModelLaunchDataProvider) ModelEditor.this
        // .getAdapter(TLCModelLaunchDataProvider.class);
        // if (!provider.getErrors().isEmpty())
        // {
        // TLCErrorView errorView = (TLCErrorView) UIHelper.findView(TLCErrorView.ID);
        // if (errorView != null)
        // {
        // UIHelper.runUISync(new Runnable() {
        //
        // public void run()
        // {
        // TLCErrorView.updateErrorView(provider);
        // }
        // });
        // }
        // }
        // // TLCUIActivator.getDefault().logDebug("Focusing " + getConfig().getName() +
        // // " editor");

    	final IFormPage page = getActivePageInstance();
    	page.setFocus();
    }

    /*
     * @see org.eclipse.ui.part.EditorPart#isSaveAsAllowed()
     */
    public boolean isSaveAsAllowed()
    {
        return false;
    }

    /**
     * Instead of committing pages, forms and form-parts, we just commit pages 
     */
    protected synchronized void commitPages(IProgressMonitor monitor, boolean onSave)
    {
        // TLCUIActivator.getDefault().logDebug("entering ModelEditor#commitPages(IProgressMonitor monitor, boolean onSave)");
        for (int i = 0; i < getPageCount(); i++)
        {
            /*
             * Note that all pages are not necessarily
             * instances of BasicFormPage. Some are read
             * only editors showing saved versions of
             * modules.
             */
            if (pages.get(i) instanceof BasicFormPage)
            {
                BasicFormPage page = (BasicFormPage) pages.get(i);
                if (page.isInitialized())
                {
                    page.commit(onSave);
                }
            }
        }
        // TLCUIActivator.getDefault().logDebug("leaving ModelEditor#commitPages(IProgressMonitor monitor, boolean onSave)");
    }

    /*
     * @see org.eclipse.ui.forms.editor.FormEditor#addPages()
     */
    protected void addPages()
    {
        // TLCUIActivator.getDefault().logDebug("entering ModelEditor#addPages()");
        try
        {

            // This code moves the tabs to the top of the page.
            // This makes them more obvious to the user.
            if (getContainer() instanceof CTabFolder)
            {
                ((CTabFolder) getContainer()).setTabPosition(SWT.TOP);
                ((CTabFolder) getContainer()).addCTabFolder2Listener(listener);
            } else
            {
                TLCUIActivator.getDefault().logDebug("The model editor container is not a CTabFolder. This is a bug.");
            }

            for (int i = 0; i < pagesToAdd.length; i++)
            {
                addPage(pagesToAdd[i]);
                // initialize the page

                // this means the content will be created
                // the data will be loaded
                // the refresh method will update the UI state
                // the dirty listeners will be activated
                if (pagesToAdd[i].getPartControl() == null)
                {
                    pagesToAdd[i].createPartControl(getContainer());
                    setControl(i, pagesToAdd[i].getPartControl());
                    pagesToAdd[i].getPartControl().setMenu(getContainer().getMenu());
                }
            }

            // at this point everything is activated and initialized.
            // run the validation
            UIHelper.runUIAsync(validateRunable);

            
            ModuleNode rootModule = SemanticHelper.getRootModuleNode();
            if (rootModule != null && rootModule.getVariableDecls().length == 0
            		&& rootModule.getConstantDecls().length == 0)
            {
            	showResultPage();
            }
            
            if (model.hasStateGraphDump()) {
            	addOrUpdateStateGraphEditor(model.getStateGraphDump());
            }
        } catch (CoreException e)
        {
            TLCUIActivator.getDefault().logError("Error initializing editor", e);
        }

        // TLCUIActivator.getDefault().logDebug("leaving ModelEditor#addPages()");
    }
    
    /**
     * For some reason, the superclass comments out the setPageImage(...) code.
     * 
     * {@inheritDoc}
     */
    @Override
	protected void configurePage(final int index, final IFormPage page)
			throws PartInitException {
		setPageImage(index, page.getTitleImage());
    	
    	super.configurePage(index, page);
	}
    
	public void addOrUpdateStateGraphEditor(final IFile stateGraphDotDump) throws CoreException {
		// For historical reasons this preference is found in the tlatex bundle. Thus,
		// we read the value from there, but don't refer to the corresponding string
		// constants to not introduce a plugin dependency.
		// org.lamport.tla.toolbox.tool.tla2tex.TLA2TeXActivator.PLUGIN_ID
		// org.lamport.tla.toolbox.tool.tla2tex.preference.ITLA2TeXPreferenceConstants.EMBEDDED_VIEWER
		final boolean useEmbeddedViewer = Platform.getPreferencesService()
				.getBoolean("org.lamport.tla.toolbox.tool.tla2tex", "embeddedViewer", false, null);
		
		final IEditorPart findEditor;
		if (useEmbeddedViewer) {
			// Try to get hold of the editor instance without opening it yet. Opening is
			// triggered by calling addPage.
			findEditor = UIHelper.findEditor("de.vonloesch.pdf4eclipse.editors.PDFEditor");
		} else {
			findEditor = UIHelper.findEditor(PDFBrowserEditor.ID);
		}

		// Load a previously generated pdf file.
		final IFile file = model.getFolder().getFile(model.getName() + ".pdf");
		if (file.exists()) {
			addPage(findEditor, new FileEditorInput(file));
			return;
		}

		// Generating a PDF from the dot file can be a time consuming task. Thus, wrap
		// the generation inside a background job for processing. When done, the job will join the
		// main thread and update the UI (create the multipage editor page that renders
		// the pdf). Errors (IStatus) are handled by the Job framework and trigger a dialog, unless
		// errors occur inside the UI runnable. There we handle errors manually.
		final Job j = new WorkspaceJob("Generating State Graph Visualization...") {
			@Override
			public IStatus runInWorkspace(IProgressMonitor monitor) throws CoreException {
				try {
					// Generate PDF (this process runs with a timeout of one minute which is why we
					// don't provide a mechanism to cancel it.
					final byte[] load = GraphViz.load(new FileInputStream(stateGraphDotDump.getLocation().toFile()),
							"pdf", 0, 0);
					// Write byte[] into IFile file
					file.create(new ByteArrayInputStream(load), IResource.NONE, null);
					UIHelper.runUISync(new Runnable() {
						@Override
						public void run() {
							try {
								addPage(findEditor, new FileEditorInput(file));
							} catch (PartInitException e) {
								final Shell shell = Display.getDefault().getActiveShell();
								MessageDialog.openError(shell == null ? new Shell() : shell,
										"Opening state graph visualization failed.",
										"Opening state graph visualization failed: " + e.getMessage());
							} catch (OutOfMemoryError e) {
								final Shell shell = Display.getDefault().getActiveShell();
								MessageDialog.openError(shell == null ? new Shell() : shell, "Opening state graph visualization ran out of memory.",
										"Opening state graph visualization ran out of memory. The state graph is likely too large. "
										+ "Try using a standalone PDF viewer if the Toolbox is currently set to use the built-in one.");
							}
						}
					});
				} catch (CoreException e) {
					// If generation failed to generate a pdf, inform the user by raising a dialog.
					// Reason of failure can be 1) input too large 2) incorrect dot path 3) ...
					return shortenStatusMessage(e.getStatus());
				} catch (FileNotFoundException notExpectedTohappen) {
					// We don't expect this to happen, because addOrUpdateStateGraphEditor gets
					// called with a valid file.
					return new Status(IStatus.ERROR, TLCActivator.PLUGIN_ID, notExpectedTohappen.getMessage(),
							notExpectedTohappen);
				}
				return Status.OK_STATUS;
			}
		};
		j.setUser(true);
		j.setPriority(Job.LONG);
		j.schedule();
	}

	// Shorten message to 1024 chars in case GraphViz attached the complete dot
	// input which can be huge.
	// https://github.com/abstratt/eclipsegraphviz/issues/8
	private static IStatus shortenStatusMessage(IStatus status) {
		if (status.isMultiStatus()) {
			final IStatus[] convertedChildren = new Status[status.getChildren().length];
			// convert nested status objects.
			final IStatus[] children = status.getChildren();
			for (int i = 0; i < children.length; i++) {
				final IStatus child = children[i];
				convertedChildren[i] = new Status(child.getSeverity(), child.getPlugin(), child.getCode(),
						substring(child.getMessage()),
						child.getException());
			}
			return new MultiStatus(status.getPlugin(), status.getCode(), convertedChildren,
					substring(status.getMessage()),
					status.getException());
		} else {
			return new Status(status.getSeverity(), status.getPlugin(), status.getCode(),
					substring(status.getMessage()),
					status.getException());
		}
	}
	
	private static String substring(String in) {
		if (in.length() > 1024) {
			return in.substring(0, 1024) + "... (" + (in.length() - 1024) + " chars omitted)";
		}
		return in;
	}
	
    /* --------------------------------------------------------------------- */
    
	public void launchModel(final String mode, final boolean userPased) {
		launchModel(mode, userPased, new NullProgressMonitor());
	}
	
	/**
	 * Launch TLC or SANY
	 * 
	 * @param mode
	 * @param userPased
	 *            true, if the action is performed on behalf of the user action
	 *            (explicit click on the launch button)
	 * @throws CoreException
	 */
	public void launchModel(final String mode, final boolean userPased, final IProgressMonitor monitor) {
		if (userPased && model.isSnapshot()) {
			final boolean launchSnapshot = MessageDialog.openConfirm(getSite().getShell(), "Model is a snapshot",
					"The model which is about to launch is a snapshot of another model. "
					+ "Beware that no snapshots of snapshots are taken. "
					+ "Click the \"OK\" button to launch the snapshot anyway.");
			if (!launchSnapshot) {
				return;
			}
		}
		final IWorkspace workspace = ResourcesPlugin.getWorkspace();
		try {
			workspace.run(new IWorkspaceRunnable() {
				public void run(IProgressMonitor monitor) throws CoreException {

					/*
					 * The user should not be able to run the model checker or
					 * generate MC files if the spec is unparsed. Right now, the
					 * user will simply see an message dialog that has a
					 * different message depending on whether the mode is model
					 * check or generate. If the mode is generate, there will be
					 * a different message depending on whether the user
					 * explicitly clicked generate or the generation is
					 * occurring because the preference to automatically
					 * revalidate on save is selected. The messages appear
					 * below.
					 * 
					 * It would be nice to eventually add a button that allows
					 * the user to parse the spec from that dialog, and if
					 * parsing succeeds, to run TLC, but right now, that is not
					 * implemented.
					 */
					if (Activator.isSpecManagerInstantiated()) {
						Spec spec = Activator.getSpecManager().getSpecLoaded();
						if (spec == null || spec.getStatus() != IParseConstants.PARSED) {
							if (mode == TLCModelLaunchDelegate.MODE_MODELCHECK) {
								MessageDialog
										.openError(getSite().getShell(), "Model checking not allowed",
												"The spec status is not \"parsed\". The status must be \"parsed\" before model checking is allowed.");
							} else if (mode == TLCModelLaunchDelegate.MODE_GENERATE) {
								if (userPased) {
									MessageDialog
											.openError(getSite().getShell(), "Revalidation not allowed",
													"The spec status is not \"parsed\". The status must be \"parsed\" before model revalidation is allowed.");
								} else {
									MessageDialog
											.openError(getSite().getShell(), "Revalidation not allowed",
													"The model can be saved, but since the spec status is not \"parsed\" model revalidation is not allowed.");
								}
							}
							return;
						} else {
							/*
							 * The spec cannot be model checked if it contains a
							 * module named MC or a module named TE. Pop-up an
							 * error message to the user and do not run TLC.
							 */
							String rootModuleName = spec.getRootModule().getName();
							if (ModelHelper.containsModelCheckingModuleConflict(rootModuleName)) {
								MessageDialog.openError(getSite().getShell(), "Illegal module name",
										"Model validation and checking is not allowed on a spec containing a module named "
												+ ModelHelper.MC_MODEL_NAME + "."
												+ (userPased ? "" : " However, the model can still be saved."));
								return;
							}
							if (ModelHelper.containsTraceExplorerModuleConflict(rootModuleName)) {
								MessageDialog.openError(getSite().getShell(), "Illegal module name",
										"Model validation and checking is not allowed on a spec containing a module named "
												+ ModelHelper.TE_MODEL_NAME + "."
												+ (userPased ? "" : " However, the model can still be saved."));
								return;
							}
						}
					} else {
						Activator.getDefault().logDebug("The spec manager has not been instantiated. This is a bug.");
						return;
					}

					/*
					 * Ask and save _spec_ editor if it's dirty
					 */
					final IEditorReference[] editors = getSite().getPage().getEditorReferences();
					for (IEditorReference ref : editors) {
						if (OpenSpecHandler.TLA_EDITOR_CURRENT.equals(ref.getId())) {
							if (ref.isDirty()) {
								final String title = ref.getName();
								boolean save = MessageDialog.openQuestion(getSite().getShell(), "Save " + title
										+ " spec?", "The spec " + title
										+ " has not been saved, should the spec be saved prior to launching?");
								if (save) {
									// TODO decouple from ui thread
									ref.getEditor(true).doSave(monitor);
								} else {
									return;
								}
							}
						}
					}

					/*
					 * The pages should be validated one last time before TLC is
					 * run. This is currently necessary when auto-parse spec is
					 * disabled. In such cases, if the user removes a constant
					 * or a definition from the spec, saves, and then later
					 * parses the spec, the model pages will not be validated on
					 * parsing. The removed constant should cause a validation
					 * error as should the removed definition if there is an
					 * override for that definition. However, validation is not
					 * called, so no error is displayed to the user and the
					 * pages are all complete, so the toolbox attempts to run
					 * TLC. This is incorrect, so validation must occur here.
					 * This is a quick fix. A better fix would be to revalidate
					 * the pages when the spec is parsed.
					 * 
					 * This must be run synchronously so that it finishes before
					 * this method checks if the pages are complete.
					 */
					UIHelper.runUISync(validateRunable);

					// save the model editor if not saved
					if (isDirty()) {
						// TODO decouple from ui thread
						doSave(new SubProgressMonitor(monitor, 1));
					}

					if (!isComplete()) {
						// user clicked launch
						if (userPased) {
							MessageDialog.openError(getSite().getShell(), "Model processing not allowed",
									"The model contains errors, which should be corrected before further processing");
							return;
						}
					} else {
						// launching the config
						model.launch(mode, new SubProgressMonitor(monitor, 1), true);
						
						/*
						 * Close any tabs in this editor containing read-only versions of modules. They
						 * will be changed by the launch, regardless of the mode. We could do something
						 * more sophisticated like listening to resource changes and updating the
						 * editors when the underlying files change, but the doesn't seem worth the
						 * effort.
						 * 
						 * Close pages in reverse order because removing a page invalidates indices.
						 */
						for (int i = getPageCount() - 1; i >= 0; i--) {
							/*
							 * The normal form pages (main model page, advanced options, results) are remain
							 * open, all other pages get closed i.e. Saved Module Editor and State Graph
							 * editor.
							 */
							if (!(pages.get(i) instanceof BasicFormPage)) {
								removePage(i);
							}
						}

						// clear the error view when launching the model
						// checker
						// but not when validating
						if (mode.equals(TLCModelLaunchDelegate.MODE_MODELCHECK)) {
							TLCErrorView errorView = (TLCErrorView) UIHelper.findView(TLCErrorView.ID);
							if (errorView != null) {
								errorView.clear();
							}
						}
					}
				}
			}, workspace.getRoot(), IWorkspace.AVOID_UPDATE, monitor);
		} catch (CoreException e) {
			TLCUIActivator.getDefault().logError(
					"Error launching the configuration " + model.getName(), e);
			MessageDialog.openError(getSite().getShell(), "Model processing failed", e.getMessage());
		}
	}

    /**
     * Stops TLC
     */
    public void stop()
    {
        if (getModel().isRunning())
        {
            Job[] runningSpecJobs = Job.getJobManager().find(getModel().getLaunchConfiguration());
            for (int i = 0; i < runningSpecJobs.length; i++)
            {
                // send cancellations to all jobs...
                runningSpecJobs[i].cancel();
            }
        } else if (getModel().isRunningRemotely()) {
        	final Job[] remoteJobs = Job.getJobManager().find(getModel());
        	for (Job remoteJob : remoteJobs) {
				remoteJob.cancel();
			}
        }
    }

    public Model getModel()
    {
        return model;
    }

    /**
     * Checks whether the pages are complete and goes to the first (in order of addition) incomplete page if any
     * @return true if all pages are complete, false otherwise
     */
    public boolean isComplete()
    {
        for (int i = 0; i < getPageCount(); i++)
        {
            /*
             * Note that all pages are not necessarily
             * instances of BasicFormPage. Some are read
             * only editors showing saved versions of
             * modules.
             */
            if (pages.get(i) instanceof BasicFormPage)
            {
                BasicFormPage page = (BasicFormPage) pages.get(i);
                if (!page.isComplete())
                {
                    setActivePage(page.getId());
                    return false;
                }
            }
        }
        return true;
    }

    /**
     * Handles the problem markers attached to the model file. For those of them having the 
     * attribute set, the error bubbles will be attached to the corresponding field 
     * 
     * <br><b>Note</b>: has to be called from UI thread
     */
    public void handleProblemMarkers(boolean switchToErrorPage)
    {
        int errorPageIndex = -1;
        int currentPageIndex = getActivePage();
        try
        {
            IMarker[] modelProblemMarkers = model.getMarkers();
            DataBindingManager dm = getDataBindingManager();

			// The loop is going to update the page's messages for potentially
			// each marker (nested loop). Thus, turn auto update off during the
			// loop for all pages (we don't yet know which marker gets displayed
			// on which page).
            for (int i = 0; i < this.pagesToAdd.length; i++) {
				IMessageManager mm = this.pagesToAdd[i].getManagedForm().getMessageManager();
            	mm.setAutoUpdate(false);
            }
            
            for (int j = 0; j < getPageCount(); j++)
            {
                /*
                 * Note that all pages are not necessarily
                 * instances of BasicFormPage. Some are read
                 * only editors showing saved versions of
                 * modules.
                 */
                if (pages.get(j) instanceof BasicFormPage)
                {
                    // get the current page
                    BasicFormPage page = (BasicFormPage) pages.get(j);
                    Assert.isNotNull(page.getManagedForm(), "Page not initialized, this is a bug.");

                    for (int i = 0; i < modelProblemMarkers.length; i++)
                    {
                        String attributeName = modelProblemMarkers[i].getAttribute(
                                ModelHelper.TLC_MODEL_ERROR_MARKER_ATTRIBUTE_NAME,
                                IModelConfigurationDefaults.EMPTY_STRING);

                        int bubbleType = -1;
                        if (modelProblemMarkers[i].getType().equals(Model.TLC_MODEL_ERROR_MARKER_SANY))
                        {
                            // SANY markers are errors
                            bubbleType = IMessageProvider.ERROR;
                        } else if (modelProblemMarkers[i].getType().equals(ModelHelper.TLC_MODEL_ERROR_MARKER_TLC))
                        {
                            // TLC markers are warnings
                            bubbleType = IMessageProvider.WARNING;
                        } else
                        {
                            bubbleType = IMessageProvider.INFORMATION;
                        }

                        if (ModelHelper.EMPTY_STRING.equals(attributeName))
                        {
                            final String message = modelProblemMarkers[i].getAttribute(IMarker.MESSAGE,
                                    IModelConfigurationDefaults.EMPTY_STRING);
							final int pageId = modelProblemMarkers[i]
									.getAttribute(ModelHelper.TLC_MODEL_ERROR_MARKER_ATTRIBUTE_PAGE, -1);
                            // no attribute, this is a global error, not bound to a particular attribute
                            // install it on the first page
                            // if it is a global TLC error, then we call addGlobalTLCErrorMessage()
                            // to add a hyperlink to the TLC Error view
							if (pageId != -1 && bubbleType == IMessageProvider.WARNING
									&& !IModelConfigurationDefaults.EMPTY_STRING.equals(message)) {
								// Used by the ResultPage to display an error on
								// incomplete state space exploration.
								this.pagesToAdd[pageId].addGlobalTLCErrorMessage(ResultPage.RESULT_PAGE_PROBLEM, message);
							} else if (bubbleType == IMessageProvider.WARNING) {
								this.pagesToAdd[0].addGlobalTLCErrorMessage("modelProblem_" + i);
								this.pagesToAdd[1].addGlobalTLCErrorMessage("modelProblem_" + i);
							} else {
								// else install as with other messages
								IMessageManager mm = this.pagesToAdd[0].getManagedForm().getMessageManager();
								mm.addMessage("modelProblem_" + i, message, null, bubbleType);
							}
                        } else
                        {
                            // attribute found
                            String sectionId = dm.getSectionForAttribute(attributeName);
                            Assert.isNotNull(sectionId,
                                    "Page is either not initialized or attribute not bound, this is a bug.");

                            String pageId = dm.getSectionPage(sectionId);

                            // relevant, since the attribute is displayed on the current
                            // page
                            // if (page.getId().equals(pageId))
                            // {

                            // We now want the error message to be displayed on
                            // the header of every page, so the if statement that is commented
                            // out is no longer relevant
                            IMessageManager mm = page.getManagedForm().getMessageManager();
                            String message = modelProblemMarkers[i].getAttribute(IMarker.MESSAGE,
                                    IModelConfigurationDefaults.EMPTY_STRING);

                            Control widget = UIHelper.getWidget(dm.getAttributeControl(attributeName));
                            if (widget != null)
                            {
                                // we set the message's data object to the page id
                                // of the attribute with the error
                                // this makes it simple to switch to that page
                                // when the user clicks on the hyperlink because
                                // the hyperlink listener recieves that message and
                                // the message contains the data object.
                                mm.addMessage("modelProblem_" + i, message, pageId, bubbleType, widget);
                            }
                            // expand the section with an error
                            dm.expandSection(sectionId);

                            if (page.getId().equals(pageId) && errorPageIndex < j)
                            {
                                errorPageIndex = j;
                            }
                            // }
                        }
                    }
                }
            }
            
            // Once all markers have been processed, re-enable auto update again.
            for (int i = 0; i < this.pagesToAdd.length; i++) {
				final IMessageManager mm = this.pagesToAdd[i].getManagedForm().getMessageManager();
            	mm.setAutoUpdate(true);
            }
            
            if (switchToErrorPage && errorPageIndex != -1 && currentPageIndex != errorPageIndex)
            {
                // the page has a marker
                // make it active
                setActivePage(errorPageIndex);
            }

        } catch (CoreException e)
        {
            TLCUIActivator.getDefault().logError("Error retrieving model error markers", e);
        }
    }
    
    public void setActivePage(int index) {
    	if(pages != null) {
    		super.setActivePage(index);
    	}
    }

    /**
     * Current helper instance
     * @return
     */
    public SemanticHelper getHelper()
    {
        return this.helper;
    }

    /**
     * Retrieves the data binding manager for this editor
     */
    public DataBindingManager getDataBindingManager()
    {
        return this.dataBindingManager;
    }

    /**
     * Retrieve the file editor input
     * @return
     */
    public FileEditorInput getFileEditorInput()
    {
        IEditorInput input = getEditorInput();
        if (input instanceof FileEditorInput)
        {
            return (FileEditorInput) input;
        } else
        {
            throw new IllegalStateException("Something weird. The editor is designed for FileEditorInputOnly");
        }
    }

    /**
     * Returns the nested editor instance open on moduleName (without the .tla extension).
     * Returns null if no such editor is open in this model editor.
     * 
     * @param moduleName
     * @return
     */
    public ITextEditor getSavedModuleEditor(String moduleName)
    {
        for (int i = 0; i < getPageCount(); i++)
        {
            IEditorPart nestedEditor = getEditor(i);
            if (nestedEditor != null
                    && nestedEditor instanceof ITextEditor
                    && ((FileEditorInput) nestedEditor.getEditorInput()).getName().equals(
                            ResourceHelper.getModuleFileName(moduleName)))
            {
                return (ITextEditor) nestedEditor;
            }
        }
        return null;
    }

    /**
     * Show the result page of the editor    
     */
    public void showResultPage()
    {
        // goto result page
        IFormPage resultPage = setActivePage(ResultPage.ID);
        if (resultPage != null)
        {
            try
            {
                ((ResultPage) resultPage).loadData();
            } catch (CoreException e)
            {
                TLCUIActivator.getDefault().logError("Error refreshing the result page", e);
            }
        }
    }
    
	/**
	 * Expands the given sections on the model editor pages. 
	 */
	public void expandSections(final String[] sections) {
		for (int i = 0; i < pagesToAdd.length; i++) {
			final BasicFormPage basicFormPage = pagesToAdd[i];
			basicFormPage.expandSections(sections);
		}
	}
	
	public void expandSections(final String pageId, final List<String> sections) {
		final BasicFormPage formPage = getFormPage(pageId);
		formPage.expandSections(sections.toArray(new String[sections.size()]));
	}

	public BasicFormPage getFormPage(final String id) {
		for (int i = 0; i < pagesToAdd.length; i++) {
			final BasicFormPage basicFormPage = pagesToAdd[i];
			if (basicFormPage.getId().equals(id)) {
				return basicFormPage;
			}
		}
		return null;
	}
	
    // TODO remove
    public void setUpPage(BasicFormPage newPage, int index)
    {
        if (newPage.getPartControl() == null)
        {
            newPage.createPartControl(this.getContainer());
            setControl(index, newPage.getPartControl());
            newPage.getPartControl().setMenu(getContainer().getMenu());
        }
    }

    /**
     * This adds error messages to all pages for the given control.
     * If the control is null, it will do nothing.
     * 
     * @param key the unique message key
     * @param messageText the message to add
     * @param pageId the id of the page that contains the control
     * @param type the message type
     * @param control the control to associate the message with
     */
    public void addErrorMessage(Object key, String messageText, String pageId, int type, Control control)
    {
        if (control != null)
        {
            for (int i = 0; i < pagesToAdd.length; i++)
            {
                pagesToAdd[i].getManagedForm().getMessageManager().addMessage(key, messageText, pageId, type, control);
            }
        }
    }
    
	public void addErrorMessage(final ErrorMessage errorMessage) {
		addErrorMessage(errorMessage.getKey(), errorMessage.getMessage(), errorMessage.getModelEditorPageId(),
				IMessageProvider.WARNING,
				UIHelper.getWidget(getDataBindingManager().getAttributeControl(errorMessage.getViewerId())));
		expandSections(errorMessage.getModelEditorPageId(), errorMessage.getSections());
	}

    /**
     * This removes the error "message" added by the corresponding call to
     * addErrorMessage if it exists.  It does nothing if the "message  
     * does not exist.  This provides a partial fix to the problem of
     * page validation showing an error when the user has made a mistake, but
     * not removing the error when the user corrects the mistake.  Code that
     * checks for an error and calls addErrorMessage when it is found can
     * call removeErrorMessage when it's not found.  It is only a partial 
     * solution for two reasons:
     * 1. It can't be used where the same error "message" can
     *    be added in two different places in the code.  Perhaps this can be
     *    fixed by splitting such messages into separate ones with 
     *    different keys and different messages, it is added, but I haven't 
     *    tried this because I don't know where those keys might be used.  
     *    If all those places where the error is generated lie in the
     *    same call of pageValidate, then error messages generated in 
     *    the previous call of pageValidate can be remembered in a field
     *    and removed at the beginning of the call.
     * 2. Some of those keys are dynamically created when addErrorMessage is
     *    called, and it may be impossible to recompute the keys for which
     *    the error messages were previously generated.  Such cases could
     *    also be handled by adding a field that remembers what error messages 
     *    were added the last time the error was chaecked for. 
     * Added 21 Mar 2013 by LL.
     * 
     * @param key the unique message key
     * @param control the control to associate the message with
     */
    public void removeErrorMessage(Object key, Control control)
    {
        if (control != null)
        {
            for (int i = 0; i < pagesToAdd.length; i++)
            {
                pagesToAdd[i].getManagedForm().getMessageManager().removeMessage(key, control);
            }
        }
    }
    /**
     * Returns the validateRunnable so that the pages
     * can be validated by code outside of this class.
     * @return
     */
    public ValidateRunnable getValidateRunnable()
    {
        return validateRunable;
    }

    /**
     * Overrides the method in {@link FormEditor}. Calls this method in the superclass
     * and then makes some changes if the input is a tla file.
     * 
     * This is done so that when read-only editor pages are added to this model editor,
     * we can make the following changes:
     * 
     * 1.) Set the title of the tabs of those pages to the name of the module being shown.
     *    If this is not done, the title of those tabs would be the empty string.
     *    
     * 2.) Set those pages to be closeable. This makes it possible to click on the tab
     *     to close it.
     */
    public void addPage(int index, IEditorPart editor, IEditorInput input) throws PartInitException
    {
        super.addPage(index, editor, input);
        /*
         * Do stuff if the input is a tla file.
         * 
         * 1.) Set the title of the page to be the
         * name of the file.
         * 
         * 2.) Set the page to be closeable.
         */
        if (input instanceof FileEditorInput
                && ((FileEditorInput) input).getFile().getFileExtension().equals(ResourceHelper.TLA_EXTENSION))
        {
            setPageText(index, input.getName());
            /*
             * When I implemented this method, getContainer()
             * returned a CTabFolder. If this somehow stops
             * being the case, then I do not know how to set
             * the tla file pages to be closeable.
             */
            if (getContainer() instanceof CTabFolder)
            {
                ((CTabFolder) getContainer()).getItem(index).setShowClose(true);

            }
            // setPageImage(pageIndex, image);
		} else if (input instanceof FileEditorInput && "pdf".equals(((FileEditorInput) input).getFile().getFileExtension())) {
			setPageText(index, "State Graph");
		}
    }

    /**
     * A listener that reacts to when editor tabs showing saved modules
     * get closed. This listener blocks the underlying folder widget
     * from directly closing the page. Instead, it calls the
     * {@link ModelEditor#removePage(int)} method to remove the page.
     * This properly disposes of the editor. If the editor page is not
     * removed this way, bad things happen, like memory leaks and bizarre
     * problems updating the editor contents.
     * 
     * @author Daniel Ricketts
     *
     */
    private class CloseModuleTabListener extends CTabFolder2Adapter
    {

        public void close(CTabFolderEvent event)
        {
            Assert
                    .isTrue(event.item instanceof CTabItem,
                            "Something other than a CTabItem was closed in a CTabFolder.");
            CTabItem item = (CTabItem) event.item;

            // block the CTabFolder from directly removing the tab
            event.doit = false;

            // remove the page properly
            removePage(item.getParent().indexOf(item));
        }
    }
}
