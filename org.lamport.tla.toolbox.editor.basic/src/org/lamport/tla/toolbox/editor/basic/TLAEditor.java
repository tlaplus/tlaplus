package org.lamport.tla.toolbox.editor.basic;

import java.io.File;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Date;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import org.eclipse.core.commands.AbstractHandler;
import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.core.commands.ExecutionException;
import org.eclipse.core.commands.operations.IOperationHistory;
import org.eclipse.core.commands.operations.IOperationHistoryListener;
import org.eclipse.core.commands.operations.IUndoContext;
import org.eclipse.core.commands.operations.IUndoableOperation;
import org.eclipse.core.commands.operations.OperationHistoryEvent;
import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IMarker;
import org.eclipse.core.resources.IMarkerDelta;
import org.eclipse.core.resources.IResourceChangeEvent;
import org.eclipse.core.resources.IResourceChangeListener;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.Assert;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IPath;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.NullProgressMonitor;
import org.eclipse.core.runtime.Path;
import org.eclipse.e4.core.services.events.IEventBroker;
import org.eclipse.jface.action.IAction;
import org.eclipse.jface.action.IContributionItem;
import org.eclipse.jface.action.IMenuManager;
import org.eclipse.jface.action.MenuManager;
import org.eclipse.jface.action.Separator;
import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.jface.preference.IPreferenceStore;
import org.eclipse.jface.text.BadLocationException;
import org.eclipse.jface.text.Document;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.IRegion;
import org.eclipse.jface.text.ITextSelection;
import org.eclipse.jface.text.ITextViewerExtension6;
import org.eclipse.jface.text.IUndoManager;
import org.eclipse.jface.text.IUndoManagerExtension;
import org.eclipse.jface.text.Position;
import org.eclipse.jface.text.Region;
import org.eclipse.jface.text.TextSelection;
import org.eclipse.jface.text.TextViewer;
import org.eclipse.jface.text.hyperlink.IHyperlink;
import org.eclipse.jface.text.hyperlink.IHyperlinkDetector;
import org.eclipse.jface.text.source.Annotation;
import org.eclipse.jface.text.source.AnnotationModelEvent;
import org.eclipse.jface.text.source.IAnnotationModel;
import org.eclipse.jface.text.source.IAnnotationModelListener;
import org.eclipse.jface.text.source.IAnnotationModelListenerExtension;
import org.eclipse.jface.text.source.ISourceViewer;
import org.eclipse.jface.text.source.IVerticalRuler;
import org.eclipse.jface.text.source.projection.ProjectionAnnotation;
import org.eclipse.jface.text.source.projection.ProjectionAnnotationModel;
import org.eclipse.jface.text.source.projection.ProjectionSupport;
import org.eclipse.jface.text.source.projection.ProjectionViewer;
import org.eclipse.jface.viewers.ISelectionProvider;
import org.eclipse.swt.SWT;
import org.eclipse.swt.graphics.Image;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.FileDialog;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.ui.IEditorInput;
import org.eclipse.ui.IEditorSite;
import org.eclipse.ui.IFileEditorInput;
import org.eclipse.ui.IWorkbenchActionConstants;
import org.eclipse.ui.PartInitException;
import org.eclipse.ui.PlatformUI;
import org.eclipse.ui.actions.ContributionItemFactory;
import org.eclipse.ui.contexts.IContextActivation;
import org.eclipse.ui.contexts.IContextService;
import org.eclipse.ui.editors.text.EditorsUI;
import org.eclipse.ui.editors.text.IEncodingSupport;
import org.eclipse.ui.editors.text.IStorageDocumentProvider;
import org.eclipse.ui.editors.text.TextEditor;
import org.eclipse.ui.handlers.HandlerUtil;
import org.eclipse.ui.part.FileEditorInput;
import org.eclipse.ui.texteditor.ChainedPreferenceStore;
import org.eclipse.ui.texteditor.IDocumentProvider;
import org.eclipse.ui.texteditor.ITextEditorActionConstants;
import org.eclipse.ui.texteditor.ITextEditorActionDefinitionIds;
import org.eclipse.ui.texteditor.TextOperationAction;
import org.lamport.tla.toolbox.editor.basic.actions.ToggleCommentAction;
import org.lamport.tla.toolbox.editor.basic.proof.IProofFoldCommandIds;
import org.lamport.tla.toolbox.editor.basic.proof.TLAProofFoldingStructureProvider;
import org.lamport.tla.toolbox.editor.basic.util.DocumentUndoUtil;
import org.lamport.tla.toolbox.editor.basic.util.EditorUtil;
import org.lamport.tla.toolbox.editor.basic.util.ElementStateAdapter;
import org.lamport.tla.toolbox.editor.basic.util.ProgressMonitorDecorator;
import org.lamport.tla.toolbox.spec.Spec;
import org.lamport.tla.toolbox.tool.ToolboxHandle;
import org.lamport.tla.toolbox.util.ResourceHelper;
import org.lamport.tla.toolbox.util.StringHelper;
import org.lamport.tla.toolbox.util.TLAFileDocumentProvider;
import org.lamport.tla.toolbox.util.TLAUnicodeReplacer;
import org.lamport.tla.toolbox.util.TLAtoPCalMarker;
import org.lamport.tla.toolbox.util.UIHelper;
import org.osgi.service.event.Event;
import org.osgi.service.event.EventHandler;

import pcal.PCalLocation;
import pcal.TLAtoPCalMapping;
import tla2sany.st.Location;
import tla2unicode.TLAUnicode;
import tla2unicode.Unicode;

/**
 * Basic editor for TLA+
 *
 * @author Simon Zambrovski
 * @version $Id$
 */
public class TLAEditor extends TextEditor
{
	/**
	 * The IEventBroker topic identifying the event sent out when the editor is
	 * saved.
	 */
	public static final String SAVE_EVENT = "TLAEditor/save";
	
	public static final String ID = "org.lamport.tla.toolbox.editor.basic.TLAEditor";
    private IContextService contextService = null;
    private IContextActivation contextActivation = null;
    
    // projection support is required for folding
    private ProjectionSupport projectionSupport;
    // image for root module icon
    private Image rootImage = TLAEditorActivator.imageDescriptorFromPlugin(TLAEditorActivator.PLUGIN_ID,
            "/icons/root_file.gif").createImage();

    // currently installed annotations
    private Annotation[] oldAnnotations;
    // annotation model
    private ProjectionAnnotationModel annotationModel;
    // proof structure provider
    private TLAProofFoldingStructureProvider proofStructureProvider;
    
	// keeps hold of the IUndoableOperations caused by the programmatically
	// executed doc.replace changes in doSave()
    private final List<IUndoableOperation> lastUndoOperations = new ArrayList<IUndoableOperation>(2);
    /**
     * Listener to TLAPM output for adding status
     * coloring to proofs.
     * 
     * Commented out by DR. I think the coloring
     * will be done using markers in the prover
     * ui plug-in.
     */
    // private TLAPMColoringOutputListener tlapmColoring;
    /**
     * Listens to resource changes to the module.
     * 
     * In particular, reacts to read-only markers
     * being placed on the module.
     * 
     * Calls {@link TLAEditor#refresh()} when this happens.
     */
    private IResourceChangeListener moduleFileChangeListener;
	private IEventBroker service;
	private final EventHandler eventHandler;
	

    /**
     * Constructor
     */
    public TLAEditor()
    {

        super();
        
        // help id
        setHelpContextId("org.lamport.tla.toolbox.editor.basic.main_editor_window");
        
        this.eventHandler = new EventHandler() {
			@Override
			public void handleEvent(Event event) {
				if (event == null)
					return;
				final Object value = event.getProperty(IEventBroker.DATA);
				switch (event.getTopic()) {
				case TLAUnicodeReplacer.EVENTID_TOGGLE_UNICODE:
					unicodeToggleHandler((Boolean)value);
					break;
				default:		
				}
			}
		};
    }

    
    /**
     * Register the element state listener to react on the changes to the state (saved, dirty:=not saved) 
     */
    protected void setDocumentProvider(IEditorInput input)
    {
        super.setDocumentProvider(input);

        IDocumentProvider provider = getDocumentProvider();
        if (provider != null)
        {
            provider.addElementStateListener(new ElementStateAdapter() {
                public void elementDirtyStateChanged(Object element, boolean isDirty)
                {
                	if (contextService == null)
                		return;
                    if (isDirty)
                    {
                        contextService.deactivateContext(contextActivation);
                    } else
                    {
                        contextActivation = contextService.activateContext("toolbox.contexts.cleaneditor");
                    }
                }
            });
            ((IStorageDocumentProvider)provider).setEncoding(input, "UTF-8");
        }
    }

    @Override
    protected void doSetInput(IEditorInput input) throws CoreException {
    	super.doSetInput(input);
    }
    
    /*
     * (non-Javadoc)
     * @see org.eclipse.ui.texteditor.AbstractTextEditor#init(org.eclipse.ui.IEditorSite, org.eclipse.ui.IEditorInput)
     */
    public void init(IEditorSite site, IEditorInput input) throws PartInitException
    {

        super.init(site, input);

        // chain preference stores (our own, and the one for standard editor settings)
        IPreferenceStore preferenceStore = new ChainedPreferenceStore(new IPreferenceStore[] {
                TLAEditorActivator.getDefault().getPreferenceStore(), EditorsUI.getPreferenceStore() });

        // set source viewer configuration
        setSourceViewerConfiguration(new TLASourceViewerConfiguration(preferenceStore, this));

        // set preference store
        setPreferenceStore(preferenceStore);

        // setup the content description and image of spec root
        if (input instanceof FileEditorInput)
        {
            FileEditorInput finput = (FileEditorInput) input;
            if (finput != null)
            {
                IPath path = finput.getPath();
                setContentDescription(path.toString());

                if (ResourceHelper.isRoot(finput.getFile()))
                {
                    setTitleImage(rootImage);
                }
            }
        }
        // grab context service and activate the context on editor load
        this.contextService = (IContextService) getSite().getService(IContextService.class);
        Assert.isNotNull(contextService);
        this.contextActivation = contextService.activateContext("toolbox.contexts.cleaneditor");
        Assert.isNotNull(contextActivation);

        /*
         * This resource change listener listens to changes
         * to markers. If it finds a change to the read only
         * marker on the module in this editor, then it refreshes
         * the editor. See method refresh().
         */
        this.moduleFileChangeListener = new IResourceChangeListener() {

            public void resourceChanged(IResourceChangeEvent event)
            {
                IMarkerDelta[] markerChanges = event.findMarkerDeltas(EditorUtil.READ_ONLY_MODULE_MARKER, false);

                for (int i = 0; i < markerChanges.length; i++)
                {
                    if (markerChanges[i].getResource().equals(((IFileEditorInput) getEditorInput()).getFile()))
                    {
                        UIHelper.runUIAsync(new Runnable() {

                            public void run()
                            {
                                refresh();
                            }
                        });
                    }
                }
            }
        };

        ResourcesPlugin.getWorkspace().addResourceChangeListener(moduleFileChangeListener);
        
		// See end of doSave() for information.
		PlatformUI.getWorkbench().getOperationSupport()
				.getOperationHistory().addOperationHistoryListener(new IOperationHistoryListener() {
			public void historyNotification(final OperationHistoryEvent event) {
				if (event.getEventType() == OperationHistoryEvent.UNDONE) {
					final IUndoableOperation currentUndoOperation = event.getOperation();
					if (lastUndoOperations.contains(currentUndoOperation)) {
						try {
							// Undo the previous IUndoableOperation too. It is what the user actually wanted.
							PlatformUI.getWorkbench().getOperationSupport()
									.getOperationHistory().undo(getUndoContext(), new NullProgressMonitor(), null);
						} catch (final ExecutionException e) {
							lastUndoOperations.clear();
						}
					}
				}
			}
		});
		
    	setUnicode0(TLAUnicodeReplacer.isUnicode());
    }

    // @Inject
    private void unicodeToggleHandler(/*@UIEventTopic(TLAUnicodeReplacer.EVENTID_TOGGLE_UNICODE)*/ boolean value) {
    	final TLAFileDocumentProvider dp = getDocumentProvider();
		if (dp == null)
			return;
		
		TextSelection selection = (TextSelection) getSelectionProvider().getSelection();
		final int visible = getSourceViewer().getTopIndex();
		closeUndo();
		dp.setUnicode0(getEditorInput(), value);
		discardUndo(1);
    	convertUndo(TLAUnicodeReplacer.isUnicode());
    	getSourceViewer().setTopIndex(visible);
    	getSelectionProvider().setSelection(dp.converSelection1(getEditorInput(), value, selection));
		firePropertyChange(PROP_DIRTY);
    }
    
	private IUndoContext getUndoContext() {
		if (getSourceViewer() instanceof ITextViewerExtension6) {
			IUndoManager undoManager = ((ITextViewerExtension6) getSourceViewer()).getUndoManager();
			if (undoManager instanceof IUndoManagerExtension)
				return ((IUndoManagerExtension) undoManager).getUndoContext();
		}
		return null;
	}

    /*
     * @see org.eclipse.ui.texteditor.ExtendedTextEditor#createSourceViewer(org.eclipse.swt.widgets.Composite, org.eclipse.jface.text.source.IVerticalRuler, int)
     */
    protected ISourceViewer createSourceViewer(Composite parent, IVerticalRuler ruler, int styles)
    {
        ProjectionViewer viewer = new ProjectionViewer(parent, ruler, getOverviewRuler(), isOverviewRulerVisible(),
                styles);
        // ensure decoration support has been created and configured.
        // @see org.eclipse.ui.texteditor.ExtendedTextEditor#createSourceViewer
        getSourceViewerDecorationSupport(viewer);
        
        return viewer;
    }

    public void createPartControl(Composite parent)
    {
        super.createPartControl(parent);
        /*
         * Add projection support (e.G. for folding) 
         */
        ProjectionViewer viewer = (ProjectionViewer) getSourceViewer();
        projectionSupport = new ProjectionSupport(viewer, getAnnotationAccess(), getSharedColors());
        projectionSupport.addSummarizableAnnotationType("org.eclipse.ui.workbench.texteditor.error"); //$NON-NLS-1$
        projectionSupport.addSummarizableAnnotationType("org.eclipse.ui.workbench.texteditor.warning"); //$NON-NLS-1$
        projectionSupport.install();
        viewer.doOperation(ProjectionViewer.TOGGLE);

        new TLAUnicodeReplacer().init(viewer);
        
        // model for adding projections (folds)
        this.annotationModel = viewer.getProjectionAnnotationModel();
//        annotationModel.addAnnotationModel(IChangeRulerColumn.QUICK_DIFF_MODEL_ID, attachment);
        
        annotationModel.addAnnotationModelListener(new AnnotationModelListener());
        // this must be instantiated after annotationModel so that it does
        // not call methods that use annotation model when the model is still null
        this.proofStructureProvider = new TLAProofFoldingStructureProvider(this);

        // refresh the editor in case it should be
        // read only
        refresh();

        // tlapmColoring = new TLAPMColoringOutputListener(this);
        
        service = this.getSite().getService(IEventBroker.class);
        service.subscribe(TLAUnicodeReplacer.EVENTID_TOGGLE_UNICODE, eventHandler);
    }

    /**
     * Create editor actions
     */
    protected void createActions()
    {
        super.createActions();

        // content assist proposal action
        IAction a = new TextOperationAction(TLAEditorMessages.getResourceBundle(),
                "ContentAssistProposal.", this, ISourceViewer.CONTENTASSIST_PROPOSALS); //$NON-NLS-1$
        a.setActionDefinitionId(ITextEditorActionDefinitionIds.CONTENT_ASSIST_PROPOSALS);
        setAction("ContentAssistProposal", a); //$NON-NLS-1$

        // content assist tip action
        a = new TextOperationAction(TLAEditorMessages.getResourceBundle(),
                "ContentAssistTip.", this, ISourceViewer.CONTENTASSIST_CONTEXT_INFORMATION); //$NON-NLS-1$
        a.setActionDefinitionId(ITextEditorActionDefinitionIds.CONTENT_ASSIST_CONTEXT_INFORMATION);
        setAction("ContentAssistTip", a); //$NON-NLS-1$

        // define folding region action
        /*      a = new DefineFoldingRegionAction(TLAEditorMessages.getResourceBundle(), "DefineFoldingRegion.", this); //$NON-NLS-1$
                setAction("DefineFoldingRegion", a); //$NON-NLS-1$
                markAsStateDependentAction("DefineFoldingRegion", true); //$NON-NLS-1$
                markAsSelectionDependentAction("DefineFoldingRegion", true); //$NON-NLS-1$
        */

        // toggle comment
        a = new ToggleCommentAction(TLAEditorMessages.getResourceBundle(), "ToggleComment.", this); //$NON-NLS-1$
        a.setActionDefinitionId(TLAEditorActivator.PLUGIN_ID + ".ToggleCommentAction");
        setAction("ToggleComment", a); //$NON-NLS-1$
        markAsStateDependentAction("ToggleComment", true); //$NON-NLS-1$
        markAsSelectionDependentAction("ToggleComment", true);
        ((ToggleCommentAction) a).configure(getSourceViewer(), getSourceViewerConfiguration());

        // format action (only if formater available)
        if (getSourceViewerConfiguration().getContentFormatter(getSourceViewer()) != null)
        {
            a = new TextOperationAction(TLAEditorMessages.getResourceBundle(), "Format.", this, ISourceViewer.FORMAT); //$NON-NLS-1$
            a.setActionDefinitionId(TLAEditorActivator.PLUGIN_ID + ".FormatAction");
            setAction("Format", a); //$NON-NLS-1$
            markAsStateDependentAction("Format", true); //$NON-NLS-1$
            markAsSelectionDependentAction("Format", true); //$NON-NLS-1$
        }

        // createProofFoldAction(IProofFoldCommandIds.FOCUS_ON_STEP, "FoldUnusable.", "FoldUnusable");
        // createProofFoldAction(IProofFoldCommandIds.FOLD_ALL_PROOFS, "FoldAllProofs.", "FoldAllProofs");
        // createProofFoldAction(IProofFoldCommandIds.EXPAND_ALL_PROOFS, "ExpandAllProofs.", "ExpandAllProofs");
        // createProofFoldAction(IProofFoldCommandIds.EXPAND_SUBTREE, "ExpandSubtree.", "ExpandSubtree");
        // createProofFoldAction(IProofFoldCommandIds.COLLAPSE_SUBTREE, "CollapseSubtree.", "CollapseSubtree");
        // createProofFoldAction(IProofFoldCommandIds.SHOW_IMMEDIATE, "ShowImmediate.", "ShowImmediate");

        //a = new ExampleEditorAction(TLAEditorMessages.getResourceBundle(), "Example.", this, getStatusLineManager()); //$NON-NLS-1$
        // a.setActionDefinitionId("org.lamport.tla.toolbox.editor.basic.TestEditorCommand");
        // setAction("ToggleComment", a);
    }

    /**
     * Called when the context menu is about to show.
     * 
     * We use this to remove unwanted items from the menu
     * that eclipse plug-ins contribute.
     */
    protected void editorContextMenuAboutToShow(IMenuManager menuManager)
    {
        super.editorContextMenuAboutToShow(menuManager);
        // The following adds an extra section for the fold commands.
        // First, try to find the additions group.
        IContributionItem additions = menuManager.find(IWorkbenchActionConstants.MB_ADDITIONS);
        if (additions != null)
        {
            // insert fold commands after additions if found
            menuManager.insertAfter(IWorkbenchActionConstants.MB_ADDITIONS, new Separator("foldCommands"));
        } else
        {
            // else just put fold commands at the end
            menuManager.add(new Separator("foldCommands"));
        }

        /*
         * The following removes unwanted preference items.
         * 
         * The calls to the super class implementations of this method
         * add menu items that we dont want, so after they are added,
         * we remove them.
         */
        menuManager.remove(ITextEditorActionConstants.SHIFT_RIGHT);
        menuManager.remove(ITextEditorActionConstants.SHIFT_LEFT);

        /*
         * The following is a bit of a hack to remove
         * the "Show In" submenu that is contributed by
         * AbstractDecoratedTextEditor in its implementation
         * of this method. It is contributed without
         * an id, so we have to check all items in the menu
         * to check if a submenu contains an item with
         * the id viewShowIn. Then we remove this submenu.
         */
        IContributionItem[] items = menuManager.getItems();
        for (int i = 0; i < items.length; i++)
        {
            if (items[i] instanceof MenuManager)
            {
                MenuManager subMenu = (MenuManager) items[i];
                if (subMenu.find(ContributionItemFactory.VIEWS_SHOW_IN.getId()) != null)
                {
                    menuManager.remove(subMenu);
                    break;
                }
            }
        }

    }

    /*
     * We override this method to add information about who modified the file when. 
     * @see org.eclipse.ui.texteditor.AbstractTextEditor#doSave(org.eclipse.core.runtime.IProgressMonitor)
     */
    public void doSave(IProgressMonitor progressMonitor)
    {
        final IEditorInput editorInput = this.getEditorInput();
		IDocument doc = this.getDocumentProvider().getDocument(editorInput);
        

        addModificationHistory(doc);
        
		// Send out a save event through the event bus. There might be parties
		// interested in this, e.g. to regenerate the pretty printed pdf.
        // This instanceof check should always evaluate to true.
        if (editorInput instanceof FileEditorInput) {
        	final FileEditorInput fei = (FileEditorInput) editorInput;
        	final IFile spec = fei.getFile();
        	service.post(SAVE_EVENT, spec);
        }
        
        closeUndo();
		final TextSelection selection = (TextSelection) getSelectionProvider().getSelection();
		final int visible = getSourceViewer().getTopIndex();
        super.doSave(new ProgressMonitorDecorator(progressMonitor) {
        	public void done() {
        		UIHelper.runUIAsync(new Runnable() {
					@Override
					public void run() {
						if (TLAUnicodeReplacer.isUnicode())
							captureUndo(2);
						getSourceViewer().setTopIndex(visible);
						getSelectionProvider().setSelection(selection);
						firePropertyChange(PROP_DIRTY);
					}
				});
        		super.done();
        	}
        });
    }
    
    public void doRevertToSaved() {
    	Thread.dumpStack();
    	super.doRevertToSaved();
    	setUnicode(TLAUnicodeReplacer.isUnicode());
    }

	private void addModificationHistory(IDocument doc) {
		String text = doc.get();
		
		// Set historyStart to the offset at the start of the
        // modification history section, if there is one. And if there is,
        // we add the modification date and user.
        int historyStart = text.indexOf(ResourceHelper.modificationHistory);

        if (historyStart > -1)
        {

            // Set newEntryStart to the point at which the new modification
            // information is to be inserted.
            int newEntryStart = historyStart + ResourceHelper.modificationHistory.length();

            String user = System.getProperty("user.name");
            String searchString = ResourceHelper.modifiedBy + user;
            int searchStringLength = searchString.length();

            // Need to remove existing modification entry for user
            // if there is one. The following while loop sets found to true
            // iff there is an existing entry and, if so, sets nextEntry to
            // its starting offset and endOfLine to the offset at its end.
            boolean found = false;
            // In the loop, nextEntry is set to the start of the next
            // Modified entry. The next one is found by searching from
            // one character to the right of the current entry. To start
            // the loop, we initialize it to one char to the left of
            // newEntryStart, which could be pointing to the first
            // Modified entry.
            int nextEntry = newEntryStart - 1;
            int endOfLine = -1; // initialization needed to make compiler happy.
            label: while (!found)
            {
                nextEntry = text.indexOf(ResourceHelper.lastModified, nextEntry + 1);
                // It we don't find an entry, we eventually exit by
                // nextEntry becoming -1.
                if (nextEntry < 0)
                {
                    break label;
                }
                endOfLine = text.indexOf(StringHelper.newline, nextEntry + 1);
                if (endOfLine < 0)
                {
                    endOfLine = text.length();
                }
                // We want this to work even if an extra space is added at the end
                // of the user name. So, we set realEOL to the offset just to the
                // right of the last non-space character to the left of endOfLine,
                // and look for the user name ending there.
                int realEOL = endOfLine;
                while (text.charAt(realEOL - 1) == ' ')
                {
                    realEOL--;
                }

                if ((nextEntry + searchStringLength < realEOL)
                        && (searchString.equals(text.substring(realEOL - searchStringLength, realEOL))))
                {
                    found = true;
                }
            } // end while

            // Need to put the rest of the replacement code into
            // a try / catch for BadLocationExceptions.
            try
            {
                // remove old entry, if there is one.
                if (found)
                {
                    doc.replace(nextEntry, endOfLine - nextEntry, "");
                }
                doc.replace(newEntryStart, 0, ResourceHelper.lastModified + (new Date()) + searchString);
                
    			// Save the last one to two (depending on boolean "found")
    			// IUndoableOperations created by the previous two doc.replace(...)
    			// calls to the empty list of IUndoableOperations.
    			//
    			// The above stunt makes sure that a single user triggered undo does
    			// not only undo the programmatically created footer change, but the
    			// actual change made by the user.
    			captureUndo(found ? 2 : 1);
            } catch (BadLocationException e)
            { // TLAEditorActivator.getDefault().logDebug("Exception.");

            }

        } // end if (historyStart > -1)
	}

	private void captureUndo(int n) {
		// The IOperationHistoryListener in init(..) checks this list if the
		// currently undone IUndoableOp. is in the list. If yes, it also
		// undoes the operation preceding the currently undone one.
		if (lastUndoOperations.size() > 15)
			lastUndoOperations.remove(0); // no need to keep old IUndoableOps 
		final IOperationHistory operationHistory = PlatformUI.getWorkbench().getOperationSupport().getOperationHistory();
		final IUndoContext undoContext = getUndoContext();
		if (undoContext == null)
			return;
		final IUndoableOperation[] undoHistory = operationHistory.getUndoHistory(undoContext);
		for (int i = Math.max(undoHistory.length - n, 0); i < undoHistory.length; i++)
			lastUndoOperations.add(undoHistory[i]);
	}
	
	private void closeUndo() {
		final IOperationHistory operationHistory = PlatformUI.getWorkbench().getOperationSupport().getOperationHistory();
		operationHistory.closeOperation(true, true, IOperationHistory.EXECUTE);
	}
	
	private void discardUndo(int n) {
		closeUndo();
		final IOperationHistory operationHistory = PlatformUI.getWorkbench().getOperationSupport().getOperationHistory();
		final IUndoContext undoContext = getUndoContext();
		if (undoContext == null)
			return;
		final IUndoableOperation[] undoHistory = operationHistory.getUndoHistory(undoContext);
//		System.err.println("---------------------------------------------");
//		System.err.println("UUUUU: n = " + n + " undoHistory.length = " + undoHistory.length);
//		Thread.dumpStack();
//		for (int i = Math.max(undoHistory.length - 1, 0); i >= 0; i--)
//			System.err.println("WWWWW: " + i + " " + undoHistory[i]);
//		System.err.println("((((((((((((((((((((((((");
		for (int i = Math.max(undoHistory.length - n, 0); i < undoHistory.length; i++) {
//			System.err.println("UUUUU: " + i + " " + undoHistory[i]);
			operationHistory.replaceOperation(undoHistory[i], new IUndoableOperation[0]);
		}
//		System.err.println("==============================================");
	}
	
	private void convertUndo(boolean toUnicode) {
    	final TLAFileDocumentProvider dp = getDocumentProvider();
		if (dp == null)
			return;
		final IOperationHistory operationHistory = PlatformUI.getWorkbench().getOperationSupport().getOperationHistory();
		final IUndoContext undoContext = getUndoContext();
		if (undoContext == null)
			return;
		final IUndoableOperation[] undoHistory = operationHistory.getUndoHistory(undoContext);
		
		for (int i = 0; i < undoHistory.length; i++)
			convertUndo(toUnicode, undoHistory[i], dp);
			// operationHistory.replaceOperation(undoHistory[i], new IUndoableOperation[0]);
	}
	
	private IUndoableOperation convertUndo(boolean toUnicode, IUndoableOperation op, TLAFileDocumentProvider dp) {
		if (DocumentUndoUtil.isCompound(op)) {
			for (IUndoableOperation op1 : DocumentUndoUtil.getChanges(op))
				convertUndo(toUnicode, op1, dp);
		} else {
			try {
				final int start = DocumentUndoUtil.getStart(op); 
				final int end = DocumentUndoUtil.getEnd(op); 
				final String text = DocumentUndoUtil.getText(op); 
				final String preservedText = DocumentUndoUtil.getPreservedText(op); 
				
				// System.out.println("WWWWW start: " + start + " end: " + end + " text: " + text + " preserved: " + preservedText);
				DocumentUndoUtil.setStart(op, dp.convertOffset1(getEditorInput(), toUnicode, start));
				DocumentUndoUtil.setEnd(op, dp.convertOffset1(getEditorInput(), toUnicode, end));
				
				DocumentUndoUtil.setText(op, Unicode.convert(toUnicode, text));
				DocumentUndoUtil.setPreservedText(op, Unicode.convert(toUnicode, preservedText));
			} catch (Exception e) {
				e.printStackTrace();
			}
		}
		return op;
	}
	
    /**
     * Update the annotation structure in the editor.
     * 
     * This is only currently used by comment
     * folding and should be removed because it
     * is incorrect.
     * 
     * @param positions
     * @deprecated
     */
    public void updateFoldingStructure(List<Position> positions)
    {
    	if (annotationModel == null) {
    		return;
    	}

//    	List<Position> ps1 = new ArrayList<>(positions.size());
//    	for (Position p : positions)
//    		ps1.add(convertPosition(false, p));
//    	positions = ps1;
    	
        Annotation[] annotations = new Annotation[positions.size()];

         // this will hold the new annotations along
        // with their corresponding positions
        Map<ProjectionAnnotation, Position> newAnnotations = new HashMap<ProjectionAnnotation, Position>();

        for (int i = 0; i < positions.size(); i++)
        {
            ProjectionAnnotation annotation = new ProjectionAnnotation();
//            newAnnotations.put(annotation, positions.get(i));
            newAnnotations.put(annotation, convertPosition(false, positions.get(i)));
            annotations[i] = annotation;
        }
        // If this method is called too early, then annotationModel
        // can be null. This should obviously be addressed.
        this.annotationModel.modifyAnnotations(oldAnnotations, newAnnotations, null);
        oldAnnotations = annotations;
    }

    /**
     * Calls {@link ProjectionAnnotationModel#modifyAnnotations(Annotation[], Map, Annotation[])} with the
     * arguments.
     * 
     * Note that in the map additions, the keys should be instances of {@link ProjectionAnnotation} and the values
     * should be instances of the corresponding {@link Position}.
     * 
     * @param deletions
     * @param additions
     */
    public void modifyProjectionAnnotations(Annotation[] deletions, Map<ProjectionAnnotation, ? extends Position> additions)
    {
    	Map<ProjectionAnnotation, Position> as1 = new HashMap<>(additions.size());
    	for (Map.Entry<ProjectionAnnotation, ? extends Position> e : additions.entrySet())
    		as1.put(e.getKey(), convertPosition(false, e.getValue()));
    	additions = as1;
    	
        this.annotationModel.modifyAnnotations(deletions, additions, null);
    }
    
    /**
     * Calls {@link ProjectionAnnotationModel#modifyAnnotations(Annotation[], Map, Annotation[])} with the
     * arguments.
     * 
     * Note that in the map additions, the keys should be instances of {@link ProjectionAnnotation} and the values
     * should be instances of the corresponding {@link Position}.
     * 
     * @param modifications
     */
    public void modifyProjectionAnnotations(Annotation[] modifications)
    {
        this.annotationModel.modifyAnnotations(null, null, modifications);
    }
    
    /**
     * SaveAs support
     * 
     * Now that this editor is part of the multi-page editor
     * {@link TLAEditorAndPDFViewer} this method should not be called.
     * Instead, the method {@link TLAEditorAndPDFViewer#doSaveAs()} should
     * be called when the user selects Save As.
     */
    protected void performSaveAs(IProgressMonitor progressMonitor)
    {

        IFile file = ((FileEditorInput) getEditorInput()).getFile();
        Shell shell = UIHelper.getShellProvider().getShell();

        // TODO fix this?
        IPath specRootPrefix = new Path(ResourceHelper.getParentDirName(ToolboxHandle.getRootModule()));

        FileDialog saveAsDialog = null;
        while (true)
        {
            // construct the dialog
            // should this be replaced by a dialog showing the logical view of the FS?
            saveAsDialog = new FileDialog(shell, SWT.SAVE);
            saveAsDialog.setOverwrite(true);
            saveAsDialog.setText("Select the new filename...");
            saveAsDialog.setFilterExtensions(new String[] { "*.tla" });
            saveAsDialog.setFilterNames(new String[] { "TLA+ Files" });
            saveAsDialog.setFilterPath(file.getLocation().toOSString());
            String result = saveAsDialog.open();
            saveAsDialog = null;
            // no cancellation
            if (result != null)
            {
                IPath newPath = new Path(result);
                // check whether the file is in the same directory as the root module
                if (!specRootPrefix.isPrefixOf(newPath))
                {
                    MessageDialog.openError(shell, "Wrong location selected",
                            "The provided filename point to the same directory as the specification root file");
                    continue;
                }

                // fix the extension
                if (!"tla".equals(newPath.getFileExtension()))
                {
                    newPath = newPath.addFileExtension("tla");
                }

                File newFile = newPath.toFile();
                if (newFile.exists())
                {
                    boolean confirmOverwrite = MessageDialog.openQuestion(shell, "Overwrite file?",
                            "The provided filename already exists. The existing file will be overwritten.\nDo you want to overwrite the file "
                                    + newPath.toOSString() + "?");
                    if (!confirmOverwrite)
                    {
                        continue;
                    }

                    // overwriting existing file file exists
                } else
                {
                    // file does not exist
                    // create the empty file
                    boolean newFileCreated = false;
                    try
                    {
                        newFileCreated = newFile.createNewFile();
                    } catch (IOException e)
                    {
                        // do nothing, since we react on the newFileCreated being false
                    }
                    if (!newFileCreated)
                    {
                        MessageDialog.openError(shell, "Error saving a file", "File could not be created");
                        break;
                    }
                }

                // create a link to a file
                IFile newResource = ResourceHelper.getLinkedFile(file.getProject(), newPath.toOSString());

                // new editor input
                IEditorInput newInput = new FileEditorInput(newResource);

                // TLAEditorActivator.getDefault().logDebug("TODO: Save " + file.getLocation().toOSString() + " as " + newPath);

                // get the document provider
                IDocumentProvider provider = getDocumentProvider();
                boolean saveAsSuccess = false;
                try
                {
                    // notify
                    provider.aboutToChange(newInput);
                    // perform the save
                    provider.saveDocument(progressMonitor, newInput, provider.getDocument(getEditorInput()), true);
                    saveAsSuccess = true;
                } catch (CoreException x)
                {
                    MessageDialog.openError(shell, "Error saving a file", "File could not be created");
                } finally
                {
                    // notify
                    provider.changed(newInput);
                    if (saveAsSuccess)
                    {
                        // change the input
                        // alternatively, open another editor with the new resource?
                        setInput(newInput);
                    }
                }
                // break out on save
                break;
            } else
            {
                // break out on cancel of the dialog
                break;
            }
        }
    }

    public Object getAdapter(@SuppressWarnings("rawtypes") Class required)
    {
        /* adapt to projection support */
        if (projectionSupport != null)
        {
            Object adapter = projectionSupport.getAdapter(getSourceViewer(), required);
            if (adapter != null)
                return adapter;
        }

        if (ISelectionProvider.class.equals(required))
        {
            return getSelectionProvider();
        }
        
        if (IEncodingSupport.class.equals(required)) {
        	return new IEncodingSupport() {
				
				@Override
				public void setEncoding(String encoding) {
				}
				
				@Override
				public String getEncoding() {
					return "UTF-8";
				}
				
				@Override
				public String getDefaultEncoding() {
					return "UTF-8";
				}
			};
        }

        return super.getAdapter(required);
    }

    public void dispose()
    {
        // tlapmColoring.dispose();
        proofStructureProvider.dispose();
        rootImage.dispose();
        ResourcesPlugin.getWorkspace().removeResourceChangeListener(moduleFileChangeListener);
        service.unsubscribe(eventHandler);
        super.dispose();
    }

    /* (non-Javadoc)
	 * @see org.eclipse.ui.texteditor.AbstractTextEditor#selectAndReveal(int, int)
	 */
	public void selectAndReveal(final pcal.Region aRegion) throws BadLocationException {
		final IDocument document = getDocumentProvider().getDocument(
				getEditorInput());

		// Translate pcal.Region coordinates into Java IDocument coordinates
		final PCalLocation begin = aRegion.getBegin();
		final int startLineOffset = document.getLineOffset(begin.getLine());
		final int startOffset = startLineOffset + begin.getColumn();
		
		final PCalLocation end = aRegion.getEnd();
		final int endLineOffset = document.getLineOffset(end.getLine());
		final int endOffset = endLineOffset + end.getColumn();

		final int length = endOffset - startOffset;
		
		selectAndReveal(startOffset, length);
	}
	
	/**
	 * @return The {@link TLAtoPCalMapping} for the current editor's content or
	 *         <code>null</code> if none
	 */
	public TLAtoPCalMapping getTpMapping() {
        final Spec spec = ToolboxHandle.getCurrentSpec();
        return spec.getTpMapping(getModuleName() + ".tla");
	}
	
	/* (non-Javadoc)
	 * @see org.eclipse.ui.texteditor.AbstractDecoratedTextEditor#gotoMarker(org.eclipse.core.resources.IMarker)
	 */
	public void gotoMarker(final IMarker marker) {
		// if the given marker happens to be of instance TLAtoPCalMarker, it
		// indicates that the user wants to go to the PCal equivalent of the
		// current TLA+ marker
		if (marker instanceof TLAtoPCalMarker) {
			final TLAtoPCalMarker tlaToPCalMarker = (TLAtoPCalMarker) marker;
			try {
				final pcal.Region region = tlaToPCalMarker.getRegion();
				if (region != null) {
					selectAndReveal(region);
					return;
				} else {
					UIHelper.setStatusLineMessage("No valid TLA to PCal mapping found for current selection");
				}
			} catch (BadLocationException e) {
				// not expected to happen
				e.printStackTrace();
			}
		}
		
		// fall back to original marker if the TLAtoPCalMarker didn't work or no
		// TLAtoPCalMarker
		super.gotoMarker(marker);
	}

	/**
     * Gets the module name from the name of the file that
     * this editor is editing.
     *  
     * @return
     */
	public String getModuleName() {
		IFile moduleFile = ((FileEditorInput) this.getEditorInput()).getFile();
		return ResourceHelper.getModuleName(moduleFile);
	}

	public TextViewer getViewer() {
		return (TextViewer) getSourceViewer();
	}

	public void setStatusMessage(String message) {
		getStatusLineManager().setMessage(message);
	}

    /**
     * Runs the fold operation represented by commandId. This
     * should be an id from {@link IProofFoldCommandIds}.
     * @param commandId
     */
    public void runFoldOperation(String commandId)
    {
        // the current selection
        if (getSelectionProvider().getSelection() instanceof ITextSelection)
        {
            ITextSelection selection = (ITextSelection) getSelectionProvider().getSelection();

            proofStructureProvider.runFoldOperation(commandId, selection);
        }
    }

    public TLAProofFoldingStructureProvider getProofStructureProvider()
    {
        return proofStructureProvider;
    }

    /**
     * Refreshes the editor.
     * 
     * This currently just involves checking if the resource
     * has been marked read-only by {@link EditorUtil#setReadOnly(org.eclipse.core.resources.IResource, boolean)}.
     * If it is, the editor is set to be read only. If it isn't, the editor
     * is set to be editable.
     */
    private void refresh()
    {
        if (getSourceViewer() != null)
        {
        	if (getEditorInput() instanceof IFileEditorInput) {
        		final IFileEditorInput fileEditorInput = (IFileEditorInput) getEditorInput();
        		getSourceViewer().setEditable(!EditorUtil.isReadOnly(fileEditorInput.getFile()));
        	} else {
        		getSourceViewer().setEditable(false);
        	}
        }
    }
    
    /**
     * Simon put OpenDeclarationHandler as a subclass of TLAEditor because
     * that handler needed to use AbstractTextEditor's getSourceViewer
     * method, inherited by TLAEditor, but that's a private method.  To
     * avoid having to put ShowUsesHandler and all other classes that
     * might want to use getSourceViewer() in TLAEditor, LL defined 
     * the following method that provides it to the public at large.
     * 
     * @return
     */
    public ISourceViewer publicGetSourceViewer() {
        return this.getSourceViewer();
    }
    
    /**
     * Simon's comments, explaining exactly what this class is doing:
     * The class is located here, because editor does not expose the source viewer (method protected)
     * 
     * What LL has discovered by experimentation and from Dan:
     * This is the handler for the OpenDeclaration (F3) command that finds 
     * the definition or declaration of the currently selected string.  
     * Here's how that command is implemented.  
     * 
     * This class is the handler for  the OpenDeclaration command.
     * Executing the command causes the execute method to be called.   
     * That method calls the getHyperlinkDetectors method of the editor,
     * which will return an array IHyperLinkDetector objects, that
     * currently contains only a single TLAHyperlinkDetector object.  
     * (This is apparently controlled by the extension of
     * org.eclipse.ui.workbench.texteditor.hyperlinkDetectors
     * in org.lamport.tla.toolbox.editor.basic.plugin.xml.)
     * It then calls that detector, which will return an array of 
     * 0 or 1 OpenDeclarationAction objects (the hyperlinks).  
     * If one such object is returned, its open method is called to
     * jump to the definition or declaration.  
     */
    public static final class OpenDeclarationHandler extends AbstractHandler
    {
        public OpenDeclarationHandler()
        {
        }

        public Object execute(ExecutionEvent event) throws ExecutionException
        {

            TLAEditorAndPDFViewer editor = (TLAEditorAndPDFViewer) HandlerUtil.getActiveEditor(event);
            ISourceViewer internalSourceViewer = editor.getTLAEditor().getSourceViewer();

            ITextSelection selection = (ITextSelection) editor.getTLAEditor().getSelectionProvider().getSelection();
            IRegion region = new Region(selection.getOffset(), selection.getLength());

            // get the detectors
            IHyperlinkDetector[] hyperlinkDetectors = editor.getTLAEditor().getSourceViewerConfiguration()
                    .getHyperlinkDetectors(internalSourceViewer);
            if (hyperlinkDetectors != null)
            {
                for (int i = 0; i < hyperlinkDetectors.length; i++)
                {
                    // detect
                    IHyperlink[] hyperlinks = hyperlinkDetectors[i].detectHyperlinks(internalSourceViewer, region,
                            false);
                    if (hyperlinks != null && hyperlinks.length > 0)
                    {
                        // open
                        IHyperlink hyperlink = hyperlinks[0];
                        hyperlink.open();
                        break;
                    }
                }
            }
            return null;
        }
    }
    
    public TLAFileDocumentProvider getDocumentProvider() {
    	return (TLAFileDocumentProvider) super.getDocumentProvider();
    }
    
    private void setUnicode(final boolean unicode) {
    	UIHelper.runUIAsync(new Runnable() {
			@Override
			public void run() {
        		setUnicode0(unicode);
			}
		});
    }
    
	private void setUnicode0(boolean unicode) {
		if (TLAUnicodeReplacer.isUnicode())
			discardUndo(1);
	}
    
    public IDocument getAsciiDocument() {
    	return getDocumentProvider().getAsciiDocument(getEditorInput());
    }
    
 // screen: is the given location in editor coordinates
    public Location convertLocation(boolean screen, Location location) {
		final TLAFileDocumentProvider dp = getDocumentProvider();
		if (dp == null)
			return null;
		return dp.convertLocationIfUnicode(getEditorInput(), screen, location);
    }
    
    public Position convertPosition(boolean screen, Position position) {
    	final TLAFileDocumentProvider dp = getDocumentProvider();
		if (dp == null)
			return null;
		return dp.convertPositionIfUnicode(getEditorInput(), screen, position);
    }
    
    private class AnnotationModelListener implements IAnnotationModelListener, IAnnotationModelListenerExtension {
    	private boolean recursive;
    	
		@Override
		public void modelChanged(AnnotationModelEvent event) {
			if (recursive)
				return;
			recursive = true;
			try {
//				final AnnotationModel am = (AnnotationModel)event.getAnnotationModel(); 
//				for (Annotation ann : event.getAddedAnnotations())
//					am.modifyAnnotationPosition(ann, convertPosition(false, am.getPosition(ann)));
			} finally {
				recursive = false;
			}
		}

		@Override
		public void modelChanged(IAnnotationModel model) {
			throw new AssertionError("Shouldn't be called");	
		}
    }
    
 // screen: is the given offset in editor coordinates
    public int convertOffsetIfUnicode(boolean screen, int offset) {
    	final TLAFileDocumentProvider dp = getDocumentProvider();
		if (dp == null)
			return -1;
		return dp.convertOffsetIfUnicode(getEditorInput(), screen, offset);
    }
    
    public IRegion convertRegionIfUnicode(boolean screen, IRegion region) {
		final TLAFileDocumentProvider dp = getDocumentProvider();
		if (dp == null)
			return null;
		return dp.convertRegionIfUnicode(getEditorInput(), screen, region);
    }
    
	private void setDirty(boolean dirty) {
		final IEditorInput editorInput = getEditorInput();
		final IDocumentProvider dp = getDocumentProvider();
		if (dp == null)
			return;
		((TLAFileDocumentProvider)dp).setDirty(editorInput, dirty);
    	firePropertyChange(PROP_DIRTY);
	}
}
