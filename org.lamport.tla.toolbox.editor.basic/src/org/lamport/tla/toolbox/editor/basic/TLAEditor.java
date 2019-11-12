package org.lamport.tla.toolbox.editor.basic;

import java.io.File;
import java.io.IOException;
import java.net.URI;
import java.util.ArrayList;
import java.util.Date;
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
import org.eclipse.core.filesystem.URIUtil;
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
import org.eclipse.jface.action.ContributionManager;
import org.eclipse.jface.action.IAction;
import org.eclipse.jface.action.IContributionItem;
import org.eclipse.jface.action.IMenuManager;
import org.eclipse.jface.action.MenuManager;
import org.eclipse.jface.action.Separator;
import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.jface.preference.IPreferenceStore;
import org.eclipse.jface.text.BadLocationException;
import org.eclipse.jface.text.FindReplaceDocumentAdapter;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.IRegion;
import org.eclipse.jface.text.ITextSelection;
import org.eclipse.jface.text.ITextViewerExtension6;
import org.eclipse.jface.text.IUndoManager;
import org.eclipse.jface.text.IUndoManagerExtension;
import org.eclipse.jface.text.Position;
import org.eclipse.jface.text.Region;
import org.eclipse.jface.text.TextViewer;
import org.eclipse.jface.text.hyperlink.IHyperlink;
import org.eclipse.jface.text.hyperlink.IHyperlinkDetector;
import org.eclipse.jface.text.source.Annotation;
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
import org.eclipse.swt.widgets.Display;
import org.eclipse.swt.widgets.FileDialog;
import org.eclipse.swt.widgets.Menu;
import org.eclipse.swt.widgets.MenuItem;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.ui.IEditorInput;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.IEditorSite;
import org.eclipse.ui.IFileEditorInput;
import org.eclipse.ui.IURIEditorInput;
import org.eclipse.ui.IWorkbenchActionConstants;
import org.eclipse.ui.PartInitException;
import org.eclipse.ui.PlatformUI;
import org.eclipse.ui.contexts.IContextActivation;
import org.eclipse.ui.contexts.IContextService;
import org.eclipse.ui.editors.text.EditorsUI;
import org.eclipse.ui.editors.text.TextEditor;
import org.eclipse.ui.handlers.HandlerUtil;
import org.eclipse.ui.ide.IGotoMarker;
import org.eclipse.ui.part.FileEditorInput;
import org.eclipse.ui.texteditor.ChainedPreferenceStore;
import org.eclipse.ui.texteditor.IDocumentProvider;
import org.eclipse.ui.texteditor.ITextEditorActionConstants;
import org.eclipse.ui.texteditor.ITextEditorActionDefinitionIds;
import org.eclipse.ui.texteditor.TextOperationAction;
import org.lamport.tla.toolbox.editor.basic.actions.ToggleCommentAction;
import org.lamport.tla.toolbox.editor.basic.pcal.IPCalReservedWords;
import org.lamport.tla.toolbox.editor.basic.proof.IProofFoldCommandIds;
import org.lamport.tla.toolbox.editor.basic.proof.TLAProofFoldingStructureProvider;
import org.lamport.tla.toolbox.editor.basic.util.EditorUtil;
import org.lamport.tla.toolbox.editor.basic.util.ElementStateAdapter;
import org.lamport.tla.toolbox.spec.Spec;
import org.lamport.tla.toolbox.tool.ToolboxHandle;
import org.lamport.tla.toolbox.util.ResourceHelper;
import org.lamport.tla.toolbox.util.StringHelper;
import org.lamport.tla.toolbox.util.TLAtoPCalMarker;
import org.lamport.tla.toolbox.util.UIHelper;

import pcal.PCalLocation;
import pcal.TLAtoPCalMapping;

/**
 * Basic editor for TLA+
 *
 * @author Simon Zambrovski
 */
public class TLAEditor extends TextEditor
{
	/**
	 * The IEventBroker topic identifying the event sent out when the editor is
	 * saved.
	 */
	public static final String SAVE_EVENT = "TLAEditor/save";
	/**
	 * The IEventBroker topic identifying the event sent out while the editor is
	 * being saved.
	 */
	public static final String PRE_SAVE_EVENT = "TLAEditor/presave";
	
	public static final String ID = "org.lamport.tla.toolbox.editor.basic.TLAEditor";
    private IContextService contextService = null;
    private IContextActivation contextActivation = null;

    // projection support is required for folding
    private ProjectionSupport projectionSupport;
    // image for root module icon
    private Image rootImage = TLAEditorActivator.imageDescriptorFromPlugin(TLAEditorActivator.PLUGIN_ID,
            "/icons/root_file.gif").createImage();

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

    /**
     * Constructor
     */
    public TLAEditor()
    {

        super();

        // help id
        setHelpContextId("org.lamport.tla.toolbox.editor.basic.main_editor_window");
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
                    if (isDirty)
                    {
                        contextService.deactivateContext(contextActivation);
                    } else
                    {
                        contextActivation = contextService.activateContext("toolbox.contexts.cleaneditor");
                    }
                }
            });
        }
    }

    protected TLASourceViewerConfiguration getTLASourceViewerConfiguration(final IPreferenceStore preferenceStore) {
    	return new TLASourceViewerConfiguration(preferenceStore, this);
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
        setSourceViewerConfiguration(getTLASourceViewerConfiguration(preferenceStore));

        // set preference store
        setPreferenceStore(preferenceStore);

        initEditorNameAndDescription(input);
        
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
    }

	protected void initEditorNameAndDescription(final IEditorInput input) {
        // setup the content description and image of spec root
        if (input instanceof FileEditorInput)
        {
            final FileEditorInput finput = (FileEditorInput) input;
            if (finput != null)
            {
                final IPath path = finput.getPath();
                setContentDescription(path.toString());

                if (ResourceHelper.isRoot(finput.getFile()))
                {
                    setTitleImage(rootImage);
                }
            }
        }
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

    @Override
    public void createPartControl(final Composite parent)
    {
        super.createPartControl(parent);
        /*
         * Add projection support (i.e. for folding) 
         */
        final ProjectionViewer viewer = (ProjectionViewer) getSourceViewer();
        projectionSupport = new ProjectionSupport(viewer, getAnnotationAccess(), getSharedColors());
        projectionSupport.addSummarizableAnnotationType("org.eclipse.ui.workbench.texteditor.error"); //$NON-NLS-1$
        projectionSupport.addSummarizableAnnotationType("org.eclipse.ui.workbench.texteditor.warning"); //$NON-NLS-1$
        projectionSupport.install();
        
		if (viewer.canDoOperation(ProjectionViewer.TOGGLE)) {
			viewer.doOperation(ProjectionViewer.TOGGLE);
		}

        // model for adding projections (folds)
        annotationModel = viewer.getProjectionAnnotationModel();

        // this must be instantiated after annotationModel so that it does
        // not call methods that use annotation model when the model is still null
        proofStructureProvider = new TLAProofFoldingStructureProvider(this);
        
        // refresh the editor in case it should be
        // read only
        refresh();

        // tlapmColoring = new TLAPMColoringOutputListener(this);
        
        service = this.getSite().getService(IEventBroker.class);
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
    @Override
	protected void editorContextMenuAboutToShow(final IMenuManager menuManager) {
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

        // It would be nice if we had all of that "Run As", etc nonsense populated by the time we get here,
        //		but that gets added later, after us.. so, we will do something fairly hacky below.
        if (menuManager instanceof ContributionManager) {
        	final ContributionManager cm = (ContributionManager)menuManager;
        	
        	removeTopLevelMenuWithDisplayText("Open W&ith", cm);
        	removeTopLevelMenuWithDisplayText("Sho&w In", cm);

        	if (menuManager instanceof MenuManager) {
        		
        	}
        	final Runnable r = () -> {
        		final MenuManager mm = (MenuManager)cm;
        		final ArrayList<Integer> menuCountFerry = new ArrayList<>();
        		final Display d = PlatformUI.getWorkbench().getDisplay();
        		
        		d.syncExec(() -> {
        			menuCountFerry.clear();
        			
        			final Menu m = mm.getMenu();
        			menuCountFerry.add(Integer.valueOf((m != null) ? m.getItemCount() : 0));
        		});
        		while (menuCountFerry.get(0).intValue() == 0) {
            		try {
            			Thread.sleep(40);
            		} catch (final Exception e) { }
            		
            		d.syncExec(() -> {
            			menuCountFerry.clear();
            			
            			final Menu m = mm.getMenu();
            			menuCountFerry.add(Integer.valueOf((m != null) ? m.getItemCount() : 0));
            		});
        		}
        		
        		PlatformUI.getWorkbench().getDisplay().asyncExec(() -> {
        			final Menu menu = mm.getMenu();
        			
                	removeMenuItemWithDisplayText("&Run As", menu);
                	removeMenuItemWithDisplayText("&Debug As", menu);
                	removeMenuItemWithDisplayText("Import SWTBot", menu);
                	removeMenuItemWithDisplayText("T&eam", menu);
                	removeMenuItemWithDisplayText("Rep&lace With", menu);
                	removeMenuItemWithDisplayText("Comp&are With", menu);
        		});
        	};
        	(new Thread(r)).start();
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
    }
    
    // Were there ever more than one menu with the same display text beginning, this would produce unexpected results.
    private void removeMenuItemWithDisplayText(final String text, final Menu menu) {
    	final MenuItem[] items = menu.getItems();
    	
    	for (final MenuItem item : items) {
    		final String menuItemText = item.getText();
    		
    		if ((menuItemText != null) && menuItemText.startsWith(text)) {
    			item.dispose();
    			
    			return;
    		}
    	}
    }
    
    // Were there ever more than one menu with the same display text beginning, this would produce unexpected results.
    private void removeTopLevelMenuWithDisplayText(final String text, final ContributionManager cm) {
        final IContributionItem[] items = cm.getItems();
    	
        for (final IContributionItem item : items) {
        	if (item instanceof MenuManager) {
        		final MenuManager mm = (MenuManager)item;
        		final String menuText = mm.getMenuText();
        		
        		if ((menuText != null) && menuText.startsWith(text)) {
        			cm.remove(item);
        			return;
        		}
        	}
        }
    }

    /*
     * We override this method to add information about who modified the file when. 
     * @see org.eclipse.ui.texteditor.AbstractTextEditor#doSave(org.eclipse.core.runtime.IProgressMonitor)
     */
    @Override
    public void doSave(IProgressMonitor progressMonitor)
    {
        service.send(PRE_SAVE_EVENT, this);
        
        final IEditorInput editorInput = this.getEditorInput();
		IDocument doc = this.getDocumentProvider().getDocument(editorInput);
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
    			// calls to the empty list of IUndoableOperations. The
    			// IOperationHistoryListener in init(..) checks this list if the
    			// currently undone IUndoableOp. is in the list. If yes, it also
    			// undoes the operation preceding the currently undone one.
    			//
    			// The above stunt makes sure that a single user triggered undo does
    			// not only undo the programmatically created footer change, but the
    			// actual change made by the user.
    			lastUndoOperations.clear(); // no need to keep old IUndoableOps created by earlier footer changes
    			final IOperationHistory operationHistory = PlatformUI.getWorkbench().getOperationSupport()
    					.getOperationHistory();
    			final IUndoableOperation[] undoHistory = operationHistory.getUndoHistory(getUndoContext());
    			if (found) {
    				lastUndoOperations.add(undoHistory[undoHistory.length - 2]);
    			}
    			lastUndoOperations.add(undoHistory[undoHistory.length - 1]);
            } catch (BadLocationException e)
            { // TLAEditorActivator.getDefault().logDebug("Exception.");

            }

        } // end if (historyStart > -1)
        
        super.doSave(progressMonitor);
        
		// Send out a save event through the event bus. There might be parties
		// interested in this, e.g. to regenerate the pretty printed pdf.
        // This instanceof check should always evaluate to true.
        if (editorInput instanceof FileEditorInput) {
        	final FileEditorInput fei = (FileEditorInput) editorInput;
        	final IFile spec = fei.getFile();
        	service.post(SAVE_EVENT, spec);
        }
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
	public void modifyProjectionAnnotations(final Annotation[] deletions,
			final Map<? extends ProjectionAnnotation, ? extends Position> additions) {
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

    @SuppressWarnings("unchecked")
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

        return super.getAdapter(required);
    }

    public void dispose()
    {
        // tlapmColoring.dispose();
        proofStructureProvider.dispose();
        rootImage.dispose();
		final TLAReconcilingStrategy reconciler = (TLAReconcilingStrategy) getViewer()
				.getData(TLAReconcilingStrategy.class.toString());
		if (reconciler != null) {
			reconciler.dispose();
		}
        ResourcesPlugin.getWorkspace().removeResourceChangeListener(moduleFileChangeListener);
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
		
		// fall back to original marker if the TLAtoPCalMarker didn't work or no TLAtoPCalMarker
		//  N.B even though this is marked deprecated, the recommended replacement of: 
		//					((IGotoMarker)getAdapter(IGotoMarker.class)).gotoMarker(marker);
		//	causes a stack overflow.
		//		See: https://github.com/tlaplus/tlaplus/commit/28f6e2cf6328b84027762e828fb2f741b1a25377#r35904992
		super.gotoMarker(marker);
	}

	/**
     * Gets the module name from the name of the file that
     * this editor is editing.
     *  
     * @return
     */
	public String getModuleName() {
		final IEditorInput iei = this.getEditorInput();
		if (iei instanceof FileEditorInput) {
			final IFile moduleFile = ((FileEditorInput) iei).getFile();
			return ResourceHelper.getModuleName(moduleFile);
		} else if (iei instanceof IURIEditorInput) {
			final URI uri = ((IURIEditorInput) iei).getURI();
			if (uri != null) {
				final IPath path = URIUtil.toPath(uri);
				if (path != null) {
					final IFile moduleFile = ResourcesPlugin.getWorkspace().getRoot().getFile(path);
					return ResourceHelper.getModuleName(moduleFile);
				}
			}
		}
		return "";
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
    
    
	public boolean hasPlusCal() {
		try {
			// Search the document for the string "--algorithm" or "--fair".
	        final IDocument doc = this.getDocumentProvider().getDocument(this.getEditorInput());
			final FindReplaceDocumentAdapter search = new FindReplaceDocumentAdapter(doc);
			IRegion find = search.find(0, IPCalReservedWords.ALGORITHM, true, true, false, false);
			if (find != null) {
				return true;
			}
			find = search.find(0, "--" + IPCalReservedWords.FAIR, true, true, false, false);
			if (find != null) {
				return true;
			}
		} catch (BadLocationException e) {
		}
		return false;
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
        public Object execute(ExecutionEvent event) throws ExecutionException
        {
            final IEditorPart activeEditor = HandlerUtil.getActiveEditor(event);
            final TLAEditor tlaEditor = activeEditor.getAdapter(TLAEditor.class);

            final ITextSelection selection = (ITextSelection) tlaEditor.getSelectionProvider().getSelection();
            final IRegion region = new Region(selection.getOffset(), selection.getLength());

            // get the detectors
            final ISourceViewer internalSourceViewer = tlaEditor.getSourceViewer();
            final IHyperlinkDetector[] hyperlinkDetectors = tlaEditor.getSourceViewerConfiguration()
                    .getHyperlinkDetectors(internalSourceViewer);
            if (hyperlinkDetectors != null)
            {
                for (int i = 0; i < hyperlinkDetectors.length; i++)
                {
                    // detect
                    final IHyperlink[] hyperlinks = hyperlinkDetectors[i].detectHyperlinks(internalSourceViewer, region,
                            false);
                    if (hyperlinks != null && hyperlinks.length > 0)
                    {
                        // open
                        final IHyperlink hyperlink = hyperlinks[0];
                        hyperlink.open();
                        break;
                    }
                }
            }
            return null;
        }
    }
}
