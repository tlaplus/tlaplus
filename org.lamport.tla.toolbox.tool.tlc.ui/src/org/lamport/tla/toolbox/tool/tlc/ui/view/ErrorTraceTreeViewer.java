package org.lamport.tla.toolbox.tool.tlc.ui.view;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.concurrent.ConcurrentHashMap;

import org.eclipse.core.runtime.CoreException;
import org.eclipse.jface.action.Action;
import org.eclipse.jface.action.IMenuListener;
import org.eclipse.jface.action.IMenuManager;
import org.eclipse.jface.action.MenuManager;
import org.eclipse.jface.dialogs.IDialogSettings;
import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.jface.resource.FontRegistry;
import org.eclipse.jface.resource.JFaceResources;
import org.eclipse.jface.util.IPropertyChangeListener;
import org.eclipse.jface.viewers.CellLabelProvider;
import org.eclipse.jface.viewers.ColumnViewerToolTipSupport;
import org.eclipse.jface.viewers.ILazyTreeContentProvider;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.jface.viewers.TreeViewer;
import org.eclipse.jface.viewers.TreeViewerColumn;
import org.eclipse.jface.viewers.Viewer;
import org.eclipse.jface.viewers.ViewerCell;
import org.eclipse.swt.SWT;
import org.eclipse.swt.events.ControlAdapter;
import org.eclipse.swt.events.ControlEvent;
import org.eclipse.swt.events.SelectionAdapter;
import org.eclipse.swt.events.SelectionEvent;
import org.eclipse.swt.graphics.Color;
import org.eclipse.swt.graphics.Font;
import org.eclipse.swt.graphics.Image;
import org.eclipse.swt.widgets.Control;
import org.eclipse.swt.widgets.Event;
import org.eclipse.swt.widgets.Listener;
import org.eclipse.swt.widgets.Menu;
import org.eclipse.swt.widgets.ScrollBar;
import org.eclipse.swt.widgets.Scrollable;
import org.eclipse.swt.widgets.Tree;
import org.eclipse.swt.widgets.TreeColumn;
import org.eclipse.ui.PlatformUI;
import org.lamport.tla.toolbox.Activator;
import org.lamport.tla.toolbox.tool.tlc.TLCActivator;
import org.lamport.tla.toolbox.tool.tlc.launch.IModelConfigurationConstants;
import org.lamport.tla.toolbox.tool.tlc.launch.IModelConfigurationDefaults;
import org.lamport.tla.toolbox.tool.tlc.launch.TLCModelLaunchDelegate;
import org.lamport.tla.toolbox.tool.tlc.model.Model;
import org.lamport.tla.toolbox.tool.tlc.output.data.TLCError;
import org.lamport.tla.toolbox.tool.tlc.output.data.TLCFcnElementVariableValue;
import org.lamport.tla.toolbox.tool.tlc.output.data.TLCFunctionVariableValue;
import org.lamport.tla.toolbox.tool.tlc.output.data.TLCModelLaunchDataProvider;
import org.lamport.tla.toolbox.tool.tlc.output.data.TLCMultiVariableValue;
import org.lamport.tla.toolbox.tool.tlc.output.data.TLCNamedVariableValue;
import org.lamport.tla.toolbox.tool.tlc.output.data.TLCRecordVariableValue;
import org.lamport.tla.toolbox.tool.tlc.output.data.TLCSequenceVariableValue;
import org.lamport.tla.toolbox.tool.tlc.output.data.TLCSetVariableValue;
import org.lamport.tla.toolbox.tool.tlc.output.data.TLCSimpleVariableValue;
import org.lamport.tla.toolbox.tool.tlc.output.data.TLCState;
import org.lamport.tla.toolbox.tool.tlc.output.data.TLCVariable;
import org.lamport.tla.toolbox.tool.tlc.output.data.TLCVariableValue;
import org.lamport.tla.toolbox.tool.tlc.ui.TLCUIActivator;
import org.lamport.tla.toolbox.tool.tlc.ui.editor.ModelEditor;
import org.lamport.tla.toolbox.tool.tlc.ui.preference.ITLCPreferenceConstants;
import org.lamport.tla.toolbox.tool.tlc.ui.util.RecordToSourceCoupler;
import org.lamport.tla.toolbox.tool.tlc.ui.util.RecordToSourceCoupler.LoaderTLCState;

import tla2sany.st.Location;

/**
 * {@link TLCErrorView} was becoming a bit of a behemoth, so we're spinning out this chunk into its own class and inner
 * 	classes.
 */
class ErrorTraceTreeViewer {
    private static final int[] COLUMN_WIDTH = { 200, 200 };
    private static final String[] COLUMN_TEXTS = { "Name", "Value" };

	private static final String LOADER_TOOL_TIP
			= "Double-click to load more states.\nIf the number of states is large, this might take a few seconds.";

    
	private final TreeViewer treeViewer;
	
    // listener on changes to the error trace font preference
    private final IPropertyChangeListener errorTraceFontChangeListener;
    
    private ModelEditor modelEditor;
	
	ErrorTraceTreeViewer(final Tree parent, final ModelEditor associatedModelEditor) {
		treeViewer = new TreeViewer(parent);
		treeViewer.setUseHashlookup(true);
		treeViewer.setContentProvider(new StateContentProvider());
		ColumnViewerToolTipSupport.enableFor(treeViewer);

		final TraceDisplayResizer resizer = new TraceDisplayResizer(parent);
		final StateLabelProvider labelProvider = new StateLabelProvider();
		for (int i = 0; i < COLUMN_TEXTS.length; i++) {
			final TreeViewerColumn column = new TreeViewerColumn(treeViewer, i);
			column.getColumn().setText(COLUMN_TEXTS[i]);
			column.getColumn().setWidth(COLUMN_WIDTH[i]);
			column.setLabelProvider(labelProvider);
			resizer.setColumnForIndex(column, i);
			column.getColumn().addSelectionListener(new SelectionAdapter() {
				public void widgetSelected(final SelectionEvent e) {
					// reverse the current trace
					final TLCError error = (TLCError) treeViewer.getInput();
					error.reverseTrace();
					// Reset the viewer's selection to the empty selection. With empty
					// selection, the subsequent refresh call does *not* invalidate the
					// StateContentProvider's lazy policy.
					// We know that the user clicked on the tree's column header
					// and the real selection is of little importance.
					treeViewer.setSelection(new ISelection() {
						public boolean isEmpty() {
							return true;
						}
					});
					treeViewer.refresh(false);
					
					// remember the order for next trace shown
					final IDialogSettings dialogSettings = Activator.getDefault().getDialogSettings();
					dialogSettings.put(TLCModelLaunchDataProvider.STATESORTORDER,
							!dialogSettings.getBoolean(TLCModelLaunchDataProvider.STATESORTORDER));
				}
			});
		}
		
        parent.addControlListener(resizer);
		
		errorTraceFontChangeListener = (event) -> {
			if ((event == null) || event.getProperty().equals(ITLCPreferenceConstants.I_TLC_ERROR_TRACE_FONT)) {
				final Font f = JFaceResources.getFont(ITLCPreferenceConstants.I_TLC_ERROR_TRACE_FONT);
				
				JFaceResources.getFontRegistry().put(TLCErrorView.JFACE_ERROR_TRACE_ID, f.getFontData());

				if (treeViewer != null) {
					treeViewer.refresh(true);
				}
			}
		};
		errorTraceFontChangeListener.propertyChange(null);
        JFaceResources.getFontRegistry().addListener(errorTraceFontChangeListener);
        
        createContextMenu();
        
        setModelEditor(associatedModelEditor);
	}
	
	void dispose() {
		final FontRegistry fr = JFaceResources.getFontRegistry();
		
        fr.removeListener(errorTraceFontChangeListener);
	}
	
	void setModelEditor(final ModelEditor associatedModelEditor) {
		modelEditor = associatedModelEditor;
	}
	
	/**
	 * @return the {@link TreeViewer} instance wrapped by this class
	 */
	TreeViewer getTreeViewer() {
		return treeViewer;
	}
	
	TLCError getCurrentTrace() {
		return (TLCError)treeViewer.getInput();
	}
	
	private void createContextMenu() {
	    final MenuManager contextMenu = new MenuManager("#ViewerMenu"); //$NON-NLS-1$
	    contextMenu.setRemoveAllWhenShown(true);
	    contextMenu.addMenuListener(new IMenuListener() {
	        @Override
	        public void menuAboutToShow(final IMenuManager menuManager) {
				final Object selection = ((IStructuredSelection)treeViewer.getSelection()).getFirstElement();
				if (selection instanceof TLCState) {
		        	menuManager.add(new Action("Run model from this point") {
		    	        @Override
		    	        public void run() {
		    	        	if (modelEditor != null) {
		    	        		final Model m = modelEditor.getModel();
		    	        		
		    	        		if (m != null) {
									try {
										final int specType = m.getAttribute(
												IModelConfigurationConstants.MODEL_BEHAVIOR_SPEC_TYPE,
												IModelConfigurationDefaults.MODEL_BEHAVIOR_TYPE_DEFAULT);

										if (specType == IModelConfigurationDefaults.MODEL_BEHAVIOR_TYPE_NO_SPEC) {
											return;
										}
										
										final StringBuilder constraint = new StringBuilder();
										final String attributeKey;
										if (specType == IModelConfigurationDefaults.MODEL_BEHAVIOR_TYPE_SPEC_INIT_NEXT) {
											attributeKey = IModelConfigurationConstants.MODEL_BEHAVIOR_SEPARATE_SPECIFICATION_INIT;
										} else {
											attributeKey = IModelConfigurationConstants.MODEL_BEHAVIOR_CLOSED_SPECIFICATION;
											final String temporalSpecification = m.getAttribute(attributeKey, "");
											constraint.append(temporalSpecification).append('\n');
										}
										
										constraint.append(((TLCState) selection).getConjunctiveDescription(false));

										m.setAttribute(attributeKey, constraint.toString());
										m.save(null);

										modelEditor.launchModel(TLCModelLaunchDelegate.MODE_MODELCHECK, true);
		    	        			} catch (final CoreException e) {
		    	        				TLCActivator.logError("Problem encountered attempting to launch checker.", e);
		    	        			}
		    	        		}
		    	        	} else {
		    	        		TLCActivator.logInfo(
		    	        				"Were not able to launch ammended model because we have no model editor.");
		    	        	}
		    	        }
		    	    });
				}
	        	/*
	        	  In earlier versions of the Toolbox, we also provided:
	        	  		Collapse All (treeViewer.collapseAll())
	        	  		Expand to default level (treeViewer.collapseAll(); treeViewer.expandToLevel(2);)
	        	  		Expand All (treeViewer.expandAll())
	        	  But we now provide expand and collapse through the parent section's toolbar
	        	 */
	        }
	    });

	    final Control c = treeViewer.getControl();
	    final Menu menu = contextMenu.createContextMenu(c);
	    c.setMenu(menu);
	}

	
    private class StateContentProvider implements ILazyTreeContentProvider {
		private List<TLCState> states;
		private final int numberOfStatesToShow;

		StateContentProvider() {
			states = new ArrayList<>(0);
			
			numberOfStatesToShow = TLCUIActivator.getDefault().getPreferenceStore()
					.getInt(ITLCPreferenceConstants.I_TLC_TRACE_MAX_SHOW_ERRORS);
    	}

		@Override
		public void inputChanged(final Viewer viewer, final Object oldInput, final Object newInput) {
			// Eagerly cache the list of states as it can be a sublist of the
			// complete trace. Getting the sublist in the updateElement method
			// means we obtain it over and over again for each top-level tree
			// item.
			if (newInput instanceof TLCError) {
				this.states = ((TLCError) newInput).getStates();
			} else if (newInput == null) {
				this.states = new ArrayList<TLCState>(0);
			} else {
				throw new IllegalArgumentException();
			}
		}

		@Override
		public void updateElement(final Object parent, final int viewerIndex) {
			if (parent instanceof TLCError) {
				final TLCError error = (TLCError) parent;
				if (error.isTraceRestricted() && (viewerIndex == 0)) {
					// If only a subset of the trace is shown, show a dummy item
					// at the top which can be double-clicked to load more.
					treeViewer.replace(parent, viewerIndex, new RecordToSourceCoupler.LoaderTLCState(treeViewer,
							Math.min(numberOfStatesToShow, error.getNumberOfRestrictedTraceStates()), error));
					return;
				}
				
				// decrease index into states by one if the viewers first element is a dummy item
				final int statesIndex = viewerIndex - (error.isTraceRestricted() ? 1 : 0);
				final TLCState child = states.get(statesIndex);
				// Diffing is supposed to be lazy and thus is done here when
				// the state is first used by the viewer. The reason why it
				// has to be lazy is to be able to efficiently handle traces
				// with hundreds or thousands of states where it would be a
				// waste to diff all state pairs even if the user is never
				// going to look at all states anyway.
				// TODO If ever comes up as a performance problem again, the
				// nested TLCVariableValues could also be diffed lazily.
           		if (statesIndex > 0) {
           			final TLCState predecessor = states.get(statesIndex - 1);
           			predecessor.diff(child);
           		}
				treeViewer.replace(parent, viewerIndex, child);
				// Always setHashChildren even if child has no children: This is
				// a virtual table here meaning that it reduces the number of
				// table items at the OS level by recycling them (the OS only
				// creates a many items that fit into the visible area). If an
				// item showing a regular state, is later recycled by a "back to
				// state" or "stuttering" indicator (neither has children),
				// the OS still incorrectly assumes the item has children. This
				// crashes hard on Linux and results in erratic behavior on
				// Windows and Mac.
				treeViewer.setHasChildren(child, child.getVariablesAsList().size() > 0);
				// Lazily expand the children
				if (child.isExpandable()){
					treeViewer.expandToLevel(child, 1);
				}
			} else if (parent instanceof TLCState) {
				final TLCState state = (TLCState) parent;
                if ((state.isStuttering() || state.isBackToState())) {
                	treeViewer.setChildCount(state, 0);
                } else {
                	final List<TLCVariable> variablesAsList = state.getVariablesAsList();
                	if (variablesAsList.size() > viewerIndex) {
                		final TLCVariable child = variablesAsList.get(viewerIndex);
                		treeViewer.replace(parent, viewerIndex, child);
                		treeViewer.setHasChildren(child, child.getChildCount() > 0);
                	}
                }
			} else if (parent instanceof TLCVariable
					&& ((TLCVariable) parent).getValue() instanceof TLCMultiVariableValue) {
				final TLCMultiVariableValue multiValue = (TLCMultiVariableValue) ((TLCVariable) parent).getValue();
				final TLCVariableValue child = multiValue.asList().get(viewerIndex);
				treeViewer.replace(parent, viewerIndex, child);
				treeViewer.setHasChildren(child, child.getChildCount() > 0);
			} else if (parent instanceof TLCVariable) {
				final TLCVariable variable = (TLCVariable) parent;
				final TLCVariableValue child = variable.getValue();
				treeViewer.replace(parent, viewerIndex, child);
				treeViewer.setChildCount(child, child.getChildCount());
			} else if (parent instanceof TLCMultiVariableValue) {
				final TLCMultiVariableValue multiValue = (TLCMultiVariableValue) parent;
				final TLCVariableValue child = multiValue.asList().get(viewerIndex);
				treeViewer.replace(parent, viewerIndex, child);
				treeViewer.setHasChildren(child, child.getChildCount() > 0);
			} else if (parent instanceof TLCVariableValue
					&& ((TLCVariableValue) parent).getValue() instanceof TLCMultiVariableValue) {
				final TLCMultiVariableValue multiValue = (TLCMultiVariableValue) ((TLCVariableValue) parent).getValue();
				final TLCVariableValue child = multiValue.asList().get(viewerIndex);
				treeViewer.replace(parent, viewerIndex, child);
				treeViewer.setHasChildren(child, child.getChildCount() > 0);
			} else {
				throw new IllegalArgumentException();
			}
		}

		@Override
		public void updateChildCount(Object element, int currentChildCount) {
			if (element instanceof TLCError) {
				final TLCError error = (TLCError) element;
				int traceSize = error.getTraceSize();
				if (traceSize != currentChildCount) {
					if (error.isTraceRestricted()) {
						treeViewer.setChildCount(element, traceSize + 1);
					} else {
						treeViewer.setChildCount(element, traceSize);
					}
				}
			} else if (element instanceof TLCState) {
				final TLCState state = (TLCState) element;
				if (((state.isStuttering() || state.isBackToState()) && currentChildCount != 0)) {
					treeViewer.setChildCount(element, 0);
				} else if (currentChildCount != state.getVariablesAsList().size()) {
					treeViewer.setChildCount(element, state.getVariablesAsList().size());
				}
			} else if (element instanceof TLCVariable) {
				final TLCVariable variable = (TLCVariable) element;
				if (currentChildCount != variable.getChildCount()) {
					treeViewer.setChildCount(element, variable.getChildCount());
				}
			} else if (element instanceof TLCVariableValue) {
				final TLCVariableValue value = (TLCVariableValue) element;
				if (currentChildCount != value.getChildCount()) {
					treeViewer.setChildCount(element, value.getChildCount());
				}
			} else {
				throw new IllegalArgumentException();
			}
		}

		@Override
		public Object getParent(Object element) {
			return null;
		}
    }
    
    /**
	 * Label provider for the tree table. Modified on 30 Aug 2009 by LL to implement
	 * ITableColorProvider instead of IColorProvider. This allows coloring of
	 * individual columns, not just of entire rows.
	 */
	static class StateLabelProvider extends CellLabelProvider {
        private static final int NAME_COLUMN_INDEX = 0;
        private static final int VALUE_COLUMN_INDEX = 1;

		private static final Map<String, Color> LOCATION_COLOR_MAP = new ConcurrentHashMap<String, Color>();
		//TODO Convert to Toolbox preference once this features proves useful.
		private static final boolean COLORING_SYSTEM_PROPERTY = Boolean.getBoolean(TLCErrorView.class.getName() + ".coloring");

    	
        private final Image stateImage;
        private final Image varImage;
        private final Image recordImage;
        private final Image setImage;
        private final Image loadMoreImage;
        
		public StateLabelProvider() {
            stateImage = TLCUIActivator.getImageDescriptor("/icons/full/default_co.gif").createImage();
            varImage = TLCUIActivator.getImageDescriptor("/icons/full/private_co.gif").createImage();
            recordImage = TLCUIActivator.getImageDescriptor("/icons/full/brkpi_obj.gif").createImage();
            // setImage = TLCUIActivator.getImageDescriptor("/icons/full/over_co.gif").createImage();
            setImage = TLCUIActivator.getImageDescriptor("/icons/full/compare_method.gif").createImage();
            loadMoreImage = TLCUIActivator.getImageDescriptor("/icons/full/add.gif").createImage();
            // other candidates are newstream_wiz.gif, nav_go.gif, debugt_obj.gif
        }

		@Override
		public void dispose() {
			stateImage.dispose();
			varImage.dispose();
			recordImage.dispose();
			setImage.dispose();
			loadMoreImage.dispose();
			
			super.dispose();
		}

		@Override
		public String getToolTipText(final Object element) {
			if (element instanceof LoaderTLCState) {
				return LOADER_TOOL_TIP;
			}
			
			return null;
		}

		@Override
		public void update(final ViewerCell cell) {
			// labels
			cell.setText(getColumnText(cell.getElement(), cell.getColumnIndex()));
			
			// images
			cell.setImage(getColumnImage(cell.getElement(), cell.getColumnIndex()));
			
			// font
			cell.setFont(getFont(cell.getElement(), cell.getColumnIndex()));
			
			// colors - we were previously (pre-201909) calling a method to set foreground whose return was always null
			cell.setBackground(getBackground(cell.getElement(), cell.getColumnIndex()));
		}

		private Image getColumnImage(Object element, int columnIndex) {
			if (columnIndex == NAME_COLUMN_INDEX) {
				if (element instanceof LoaderTLCState) {
					return loadMoreImage;
				}
				if (element instanceof TLCState) {
					return stateImage;
				} else if (element instanceof TLCVariable) {
					return varImage;
				} else if (element instanceof TLCNamedVariableValue) {
					return recordImage;
				} else if (element instanceof TLCFcnElementVariableValue) {
					return recordImage;
				}
				return setImage; // other things appear in unordered collections
			}
			return null;
		}

		private String getColumnText(final Object element, final int columnIndex) {
			if (element instanceof TLCState) {
				final TLCState state = (TLCState) element;

				switch (columnIndex) {
					case NAME_COLUMN_INDEX:
						if (state.isStuttering()) {
							return "<Stuttering>";
						} else if (state.isBackToState()) {
							return "<Back to state " + state.getStateNumber() + ">";
						}
						return state.getLabel();
					case VALUE_COLUMN_INDEX:
						if (state instanceof RecordToSourceCoupler.LoaderTLCState) {
							return "";
						} else {
							return "State (num = " + state.getStateNumber() + ")";
						}
						// state.toString();
					default:
						break;
				}
			} else if (element instanceof TLCVariable) {
				final TLCVariable var = (TLCVariable) element;
				switch (columnIndex) {
					case NAME_COLUMN_INDEX:
						if (var.isTraceExplorerVar()) {
							return var.getSingleLineName();
						} else {
							return var.getName();
						}
					case VALUE_COLUMN_INDEX:
						return var.getValue().toSimpleString();
					// Changed from toString by LL on 30 Aug 2009
					default:
						break;
				}
			} else if ((element instanceof TLCSetVariableValue)
						|| (element instanceof TLCSequenceVariableValue)
						|| (element instanceof TLCSimpleVariableValue)) {
				final TLCVariableValue varValue = (TLCVariableValue) element;
				switch (columnIndex) {
					case VALUE_COLUMN_INDEX:
						return varValue.toString();
					case NAME_COLUMN_INDEX:
						return ""; // added by LL on 5 Nov 2009
					default:
						break;
				}
			} else if (element instanceof TLCNamedVariableValue) {
				final TLCNamedVariableValue namedValue = (TLCNamedVariableValue) element;
				switch (columnIndex) {
					case NAME_COLUMN_INDEX:
						return namedValue.getName();
					case VALUE_COLUMN_INDEX:
						return ((TLCVariableValue) namedValue.getValue()).toSimpleString();
					// Changed from toString by LL on 30 Aug 2009
					default:
						break;
				}
			} else if (element instanceof TLCFcnElementVariableValue) {
				final TLCFcnElementVariableValue fcnElementValue = (TLCFcnElementVariableValue) element;
				switch (columnIndex) {
					case NAME_COLUMN_INDEX:
						return fcnElementValue.getFrom().toSimpleString();
					// Changed from toString by LL on 30 Aug 2009
					case VALUE_COLUMN_INDEX:
						return ((TLCVariableValue) fcnElementValue.getValue()).toSimpleString();
					// Changed from toString by LL on 30 Aug 2009
					default:
						break;
				}
			} else if (element instanceof TLCRecordVariableValue) {
				final TLCRecordVariableValue recordValue = (TLCRecordVariableValue) element;
				switch (columnIndex) {
					case NAME_COLUMN_INDEX:
						return "";
					case VALUE_COLUMN_INDEX:
						return recordValue.toSimpleString();
					default:
						break;
				}
			} else if (element instanceof TLCFunctionVariableValue) {
				final TLCFunctionVariableValue fcnValue = (TLCFunctionVariableValue) element;
				switch (columnIndex) {
					case NAME_COLUMN_INDEX:
						return "";
					case VALUE_COLUMN_INDEX:
						return fcnValue.toSimpleString();
					default:
						break;
				}
			}

			return null;
		}

        /**
         * The following method sets the background color of a row or column of
         * the table. It highlights the entire row for an added or deleted item.
         * For a changed value, only the value is highlighted.
         */
		private Color getBackground(final Object element, final int column) {
            if (element instanceof TLCVariable) {
				final TLCVariable var = (TLCVariable) element;
				if (var.isChanged() && (column == VALUE_COLUMN_INDEX)) {
					return TLCUIActivator.getDefault().getChangedColor();
				}
			} else if (element instanceof TLCVariableValue) {
				final TLCVariableValue value = (TLCVariableValue) element;
				if (value.isChanged()) {
					if (column == VALUE_COLUMN_INDEX) {
						return TLCUIActivator.getDefault().getChangedColor();
					}
				} else if (value.isAdded()) {
					// Added takes precedence over deleted. E.g. a value can be
					// added to a set in this state and be removed in the next
					// state.
					return TLCUIActivator.getDefault().getAddedColor();
				} else if (value.isDeleted()) {
					return TLCUIActivator.getDefault().getDeletedColor();
				}
			} else if (COLORING_SYSTEM_PROPERTY && (element instanceof TLCState)) {
				// Assign a color to each location to make actions in the error
				// viewer more easily distinguishable.
				final TLCState state = (TLCState) element;
				final Location moduleLocation = state.getModuleLocation();
				if (moduleLocation == null) {
					return null;
				}
				Color c = LOCATION_COLOR_MAP.get(moduleLocation.toString());
				if (c == null) {
					final int color = SWT.COLOR_WHITE + (2 * LOCATION_COLOR_MAP.size());
					c = TLCUIActivator.getColor(color);
					LOCATION_COLOR_MAP.put(state.getModuleLocation().toString(), c);
				}
				return c;
			}
			return null;
		}

		private Font getFont(final Object element, final int columnIndex) {
			boolean returnBoldVersion = false;
			
			if (element instanceof TLCVariable) {
				if (((TLCVariable) element).isTraceExplorerVar()) {
					returnBoldVersion = true;
				}
			} else if (element instanceof RecordToSourceCoupler.LoaderTLCState) {
				returnBoldVersion = true;
			}

			final FontRegistry fr = JFaceResources.getFontRegistry();
			return returnBoldVersion ? fr.getBold(TLCErrorView.JFACE_ERROR_TRACE_ID)
									 : fr.get(TLCErrorView.JFACE_ERROR_TRACE_ID);
		}
    }
	
	
    /**
     * A control listener for the Provides method for resizing the columns of
     * the error trace viewer. This is to solve the problem of a bogus
     * "third column" being displayed when the window is made wider than the two
     * real columns.
     * 
     * There are two listener methods in this class: controlResized - called
     * when the tree is resized. handleEvent - called when column[0] is resized.
     * The controlResized command can change the size of column[0], which
     * triggers the calling of the handleEvent. Experimentation indicates that
     * this call of handleEvent occurs in the middle of executing the call of
     * controlResized. The boolean flag inControlResized is used to tell the
     * handleEvent method whether it was called this way or by the user resizing
     * the colulmn.
     * 
     * Note: I [N.B. no idea who "I" is] am assuming that the call of handleEvent that happens when
     * controlResized is resizing column[0] happens during the execution of
     * column[0].setWidth, and no funny races are possible.
     * 
     * Note that all the code here assumes that there are two columns. It needs
     * to be modified if the number of columns is changed.
     */
	private static class TraceDisplayResizer extends ControlAdapter implements Listener {
        private double firstColumnPercentageWidth = 0.5;

        // See comments above for meaning of the following flag.
        private boolean inControlResized = false;
        
        private final Tree tree;
        private final TreeColumn[] columns;
        private final Scrollable treeParentComponent;

        TraceDisplayResizer(final Tree resizingTree) {
        	tree = resizingTree;
        	treeParentComponent = (Scrollable)tree.getParent();
        	columns = new TreeColumn[COLUMN_TEXTS.length];
        }
        
        @Override
		public void controlResized(final ControlEvent e) {
            inControlResized = true;

            final int treeWidth = computeMaximumWidthOfAllColumns();
            final int firstColWidth = Math.round(Math.round(firstColumnPercentageWidth * treeWidth));
            final int secondColWidth = treeWidth - firstColWidth;
            columns[0].setWidth(firstColWidth);
            columns[1].setWidth(secondColWidth);
            
            inControlResized = false;
        }

        @Override
		public void handleEvent(final Event event) {
			if (inControlResized) {
				return;
			}

			final int treeWidth = computeMaximumWidthOfAllColumns();
			if (treeWidth == 0) {
				return;
			}

			// the percentage that the first column will occupy
			// until controlResized is called
			// We do not want the width of either column
			// to be less than 10% of the total width
			// of the tree. Currently, the user
			// can make a column smaller than 10%, but
			// when controlResized is called, the column
			// will be enlarged to 10%. It is not very nice
			// to do the enlarging in this method. It creates
			// very choppy performance.
			int firstColWidth = columns[0].getWidth();
			final double tentativefirstColPercentageWidth = (double) firstColWidth / (double) treeWidth;
			if ((tentativefirstColPercentageWidth > 0.1) && (tentativefirstColPercentageWidth < 0.9)) {
				firstColumnPercentageWidth = (double) firstColWidth / (double) treeWidth;
			} else if (tentativefirstColPercentageWidth <= .1) {
				firstColumnPercentageWidth = 0.1;
			} else {
				firstColumnPercentageWidth = 0.9;
			}
			firstColWidth = Math.round(Math.round(tentativefirstColPercentageWidth * treeWidth));
			columns[1].setWidth(treeWidth - firstColWidth);
		}
        
        void setColumnForIndex(final TreeViewerColumn column, final int index) {
        	columns[index] = column.getColumn();
        	
        	if (index == 0) {
                // I [N.B. no idea who "I" is] need to add a listener for size changes to column[0] to
                // detect when the user has tried to resize the individual columns. The following might work,
        		// if I can figure out the real event type to use.
                columns[0].addListener(SWT.Resize, this);
        	}
        }

        /*
         * Computes the maximum width that columns of the tree can occupy
         * without having a horizontal scrollbar.
         * 
         * This is not equal to the sash form's client area. From the client
         * area we must subtract the tree's border width. We must also subtract
         * the width of the grid lines used in the tree times the number of
         * columns because there is one grid line per column. We must subtract
         * the width of the vertical scroll bar if it is visible.
         */
		private int computeMaximumWidthOfAllColumns() {
			final ScrollBar vBar = tree.getVerticalBar();
			final boolean scrollBarShown = vBar.isVisible();
			
			return treeParentComponent.getClientArea().width
							- tree.getBorderWidth()
							- (tree.getColumnCount() * tree.getGridLineWidth())
							- ((scrollBarShown) ? vBar.getSize().x : 0);
		}
    }
}
