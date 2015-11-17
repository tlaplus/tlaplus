/*******************************************************************************
 * Copyright (c) 2015 Microsoft Research. All rights reserved. 
 *
 * The MIT License (MIT)
 * 
 * Permission is hereby granted, free of charge, to any person obtaining a copy 
 * of this software and associated documentation files (the "Software"), to deal
 * in the Software without restriction, including without limitation the rights
 * to use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies
 * of the Software, and to permit persons to whom the Software is furnished to do
 * so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all
 * copies or substantial portions of the Software. 
 * 
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS
 * FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR
 * COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN
 * AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION
 * WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 *
 * Contributors:
 *   Markus Alexander Kuppe - initial API and implementation
 ******************************************************************************/

package org.lamport.tla.toolbox.tool.tlc.ui.dialog;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Comparator;
import java.util.List;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;
import org.eclipse.debug.core.ILaunchConfiguration;
import org.eclipse.jface.action.Action;
import org.eclipse.jface.action.IAction;
import org.eclipse.jface.action.IMenuManager;
import org.eclipse.jface.dialogs.IDialogSettings;
import org.eclipse.jface.text.Document;
import org.eclipse.jface.text.source.SourceViewer;
import org.eclipse.jface.viewers.DelegatingStyledCellLabelProvider.IStyledLabelProvider;
import org.eclipse.jface.viewers.LabelProvider;
import org.eclipse.jface.viewers.StructuredSelection;
import org.eclipse.jface.viewers.StyledString;
import org.eclipse.swt.SWT;
import org.eclipse.swt.graphics.Image;
import org.eclipse.swt.graphics.Point;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.ui.ISharedImages;
import org.eclipse.ui.PlatformUI;
import org.eclipse.ui.dialogs.FilteredItemsSelectionDialog;
import org.eclipse.ui.ide.IDE.SharedImages;
import org.eclipse.ui.navigator.IDescriptionProvider;
import org.lamport.tla.toolbox.Activator;
import org.lamport.tla.toolbox.spec.Module;
import org.lamport.tla.toolbox.spec.Spec;
import org.lamport.tla.toolbox.tool.tlc.launch.IModelConfigurationConstants;
import org.lamport.tla.toolbox.tool.tlc.ui.TLCUIActivator;
import org.lamport.tla.toolbox.tool.tlc.util.ModelHelper;

public class TLAFilteredItemsSelectionDialog extends FilteredItemsSelectionDialog {
	
	private static final String SHOW_CONSTANTS = "ShowConstants"; //$NON-NLS-1$
	
	private static final String SHOW_CLOSED_SPECS = "ShowClosedSpecs"; //$NON-NLS-1$
	
	private static final String EMPTY_STRING = ""; //$NON-NLS-1$

	private static final Image ModelImage = TLCUIActivator.getImageDescriptor("/icons/full/choice_sc_obj.gif")
			.createImage();

	private final ToggleShowAction toggleShowConstantsAction  = new ToggleShowAction("Show spec constants", getDialogSettings().getBoolean(SHOW_CONSTANTS));
	
	private final ToggleShowAction toggleShowSpecAction = new ToggleShowAction("Show closed specs", getDialogSettings().getBoolean(SHOW_CLOSED_SPECS));
	
	private SourceViewer sourceViewer;

	public TLAFilteredItemsSelectionDialog(final Shell shell) {
		super(shell, false);
		setInitialPattern("?"); // https://bugs.eclipse.org/308689
		setListLabelProvider(new TableLabelProvider());
		setDetailsLabelProvider(new DetailsLabelProvider());
	}
	
	/* (non-Javadoc)
	 * @see org.eclipse.jface.dialogs.Dialog#getInitialSize()
	 */
	protected Point getInitialSize() {
		final Point defaultSize = super.getInitialSize();
		if (defaultSize.x == 500 && defaultSize.y == 600) {
			// Increase the parents default size
			defaultSize.x = (int) Math.round(defaultSize.x * 1.9); // x has room to align with the default spec line-wrapping
			defaultSize.y = (int) Math.round(defaultSize.y * 1.75);
		}
		return defaultSize;
	}
	
	/* (non-Javadoc)
	 * @see org.eclipse.ui.dialogs.SelectionDialog#isResizable()
	 */
	protected boolean isResizable() {
		return true;
	}

	/* (non-Javadoc)
	 * @see org.eclipse.ui.dialogs.FilteredItemsSelectionDialog#createExtendedContentArea(org.eclipse.swt.widgets.Composite)
	 */
	protected Control createExtendedContentArea(final Composite parent) {
		final Composite content = new Composite(parent, SWT.BORDER);
		
		final GridData layoutData = new GridData(GridData.FILL_HORIZONTAL);
		layoutData.heightHint = 200;
		content.setLayoutData(layoutData);

		final GridLayout layout = new GridLayout();
		layout.numColumns = 1;
		layout.marginWidth = 0;
		layout.marginHeight = 0;
		content.setLayout(layout);
		
		sourceViewer = new SourceViewer(content, null, SWT.WRAP | SWT.V_SCROLL);
		sourceViewer.getTextWidget().setLayoutData(new GridData(GridData.FILL_BOTH));
		sourceViewer.getTextWidget().setWordWrap(true);
		sourceViewer.getTextWidget().setEditable(false);
		sourceViewer.getTextWidget().setFont(TLCUIActivator.getDefault().getCourierFont());
		return content;
	}

	/* (non-Javadoc)
	 * @see org.eclipse.ui.dialogs.FilteredItemsSelectionDialog#getDialogSettings()
	 */
	protected IDialogSettings getDialogSettings() {
		return Activator.getDefault().getDialogSettings();
	}

	/* (non-Javadoc)
	 * @see org.eclipse.ui.dialogs.FilteredItemsSelectionDialog#storeDialog(org.eclipse.jface.dialogs.IDialogSettings)
	 */
	protected void storeDialog(IDialogSettings settings) {
		settings.put(SHOW_CONSTANTS, toggleShowConstantsAction.isChecked());
		settings.put(SHOW_CLOSED_SPECS, toggleShowSpecAction.isChecked());
		super.storeDialog(settings);
	}
	
	/* (non-Javadoc)
	 * @see org.eclipse.ui.dialogs.FilteredItemsSelectionDialog#fillViewMenu(org.eclipse.jface.action.IMenuManager)
	 */
	protected void fillViewMenu(IMenuManager menuManager) {
		menuManager.add(toggleShowConstantsAction);
		menuManager.add(toggleShowSpecAction);
		super.fillViewMenu(menuManager);
	}
	
	/* (non-Javadoc)
	 * @see org.eclipse.ui.dialogs.FilteredItemsSelectionDialog#validateItem(java.lang.Object)
	 */
	protected IStatus validateItem(final Object item) {
		// Nothing to validate so far
		return Status.OK_STATUS;
	}

	/* (non-Javadoc)
	 * @see org.eclipse.ui.dialogs.FilteredItemsSelectionDialog#handleSelected(org.eclipse.jface.viewers.StructuredSelection)
	 */
	protected void handleSelected(StructuredSelection selection) {
		if (selection != null && selection.size() == 0) {
			// unset the sourceviewer when the filter turned the search results
			// empty
			sourceViewer.setDocument(new Document(EMPTY_STRING));
		} else if (selection != null && selection.getFirstElement() instanceof Module) {
			final Module module = (Module) selection.getFirstElement();
			try {
				sourceViewer.setDocument(new Document(new String(Files.readAllBytes(module.getFile().toPath()))));
			} catch (IOException e) {
				sourceViewer.setDocument(new Document(EMPTY_STRING));
			}
		} else if (selection != null && selection.getFirstElement() instanceof ILaunchConfiguration) {
			final ILaunchConfiguration config = (ILaunchConfiguration) selection.getFirstElement();
			try {
				// By default, show the model's comment/description and fall-back
				// to its constants. If there are no constants, the last fall-back
				// is the model's name.
				final List<String> fallbacksFallback = new ArrayList<String>();
				fallbacksFallback.add(ModelHelper.getModelName(config));
				
				final String fallback = ModelHelper.prettyPrintConstants(config, "\n");

				final String attribute = config.getAttribute(IModelConfigurationConstants.MODEL_COMMENTS, fallback);
				if (!EMPTY_STRING.equals(attribute)) {
					sourceViewer.setDocument(new Document(attribute));
				} else {
					sourceViewer.setDocument(new Document(fallback));
				}
			} catch (final CoreException ignored) {
				sourceViewer.setDocument(new Document(EMPTY_STRING));
			}
		} else if (selection != null && selection.getFirstElement() instanceof Spec) {
			final Spec spec = (Spec) selection.getFirstElement();
			final Path path = spec.getRootFile().getLocation().makeAbsolute().toFile().toPath();
			try {
				sourceViewer.setDocument(new Document(new String(Files.readAllBytes(path))));
			} catch (IOException e) {
				sourceViewer.setDocument(new Document(EMPTY_STRING));
			}
		} else if (selection != null && selection.getFirstElement() instanceof ItemsListSeparator) {
			sourceViewer.setDocument(new Document(EMPTY_STRING));
		}
		super.handleSelected(selection);
	}

	/* (non-Javadoc)
	 * @see org.eclipse.ui.dialogs.FilteredItemsSelectionDialog#createFilter()
	 */
	protected ItemsFilter createFilter() {
		return new TLCItemFilter();
	}

	/* (non-Javadoc)
	 * @see org.eclipse.ui.dialogs.FilteredItemsSelectionDialog#getItemsComparator()
	 */
	protected Comparator<Object> getItemsComparator() {
		return new Comparator<Object>() {

			public int compare(final Object o1, final Object o2) {
				if (o1 instanceof ILaunchConfiguration && o2 instanceof ILaunchConfiguration) {
					final ILaunchConfiguration c1 = (ILaunchConfiguration) o1;
					final ILaunchConfiguration c2 = (ILaunchConfiguration) o2;
					return ModelHelper.getModelName(c1.getFile()).compareTo(ModelHelper.getModelName(c2.getFile()));
				} else if (o1 instanceof Module && o2 instanceof Module) {
					final Module m1 = (Module) o1;
					final Module m2 = (Module) o2;
					return m1.getModuleName().compareTo(m2.getModuleName());
				} else if (o1 instanceof Spec && o2 instanceof Spec) {
					return ((Spec) o1).getName().compareTo(((Spec) o2).getName());
				} else if (o1 instanceof ILaunchConfiguration && o2 instanceof Module) {
					return -1;
				} else if (o1 instanceof ILaunchConfiguration && o2 instanceof Spec) {
					return -1;
				} else if (o1 instanceof ILaunchConfiguration && o2 instanceof ItemsListSeparator) {
					return -1;
				} else if (o1 instanceof Module && o2 instanceof ILaunchConfiguration) {
					return 1;
				} else if (o1 instanceof Module && o2 instanceof Spec) {
					return -1;
				} else if (o1 instanceof Module && o2 instanceof ItemsListSeparator) {
					return -1;
				} else if (o1 instanceof Spec && o2 instanceof ILaunchConfiguration) {
					return 1;
				} else if (o1 instanceof Spec && o2 instanceof Module) {
					return 1;
				} else if (o1 instanceof Spec && o2 instanceof ItemsListSeparator) {
					return 1;
				} else if (o1 instanceof ItemsListSeparator && o2 instanceof ILaunchConfiguration) {
					return 1;
				} else if (o1 instanceof ItemsListSeparator && o2 instanceof Module) {
					return 1;
				} else if (o1 instanceof ItemsListSeparator && o2 instanceof Spec) {
					return -1;
				} else {
					return 1;
				}
			}
		};
	}

	/* (non-Javadoc)
	 * @see org.eclipse.ui.dialogs.FilteredItemsSelectionDialog#fillContentProvider(org.eclipse.ui.dialogs.FilteredItemsSelectionDialog.AbstractContentProvider, org.eclipse.ui.dialogs.FilteredItemsSelectionDialog.ItemsFilter, org.eclipse.core.runtime.IProgressMonitor)
	 */
	protected void fillContentProvider(final AbstractContentProvider contentProvider, final ItemsFilter itemsFilter,
			final IProgressMonitor progressMonitor) throws CoreException {
		final Spec spec = Activator.getSpecManager().getSpecLoaded();
		
		// Models
		final List<ILaunchConfiguration> models = ModelHelper.getModelsBySpec(spec);
		for (final ILaunchConfiguration model : models) {
			if (itemsFilter.isConsistentItem(model)) {
				contentProvider.add(model, itemsFilter);
			}
		}

		// Modules
		final List<Module> modules = spec.getModules();
		for (Module module : modules) {
			if (itemsFilter.isConsistentItem(module)) {
				contentProvider.add(module, itemsFilter);
			}
		}
		
		// All closed specs
		if (toggleShowSpecAction.isChecked()) {
			final Spec[] specs = Activator.getSpecManager().getRecentlyOpened();
			if (specs.length > 0) {
				contentProvider.add(new ItemsListSeparator("Closed specifications"), itemsFilter);
				for (int i = 0; i < specs.length; i++) {
					final Spec aSpec = specs[i];
					if (!spec.equals(aSpec) && itemsFilter.isConsistentItem(aSpec)) {
						contentProvider.add(aSpec, itemsFilter);
					}
				}
			}
		}
	}

	/* (non-Javadoc)
	 * @see org.eclipse.ui.dialogs.FilteredItemsSelectionDialog#getElementName(java.lang.Object)
	 */
	public String getElementName(final Object item) {
		return EMPTY_STRING;
	}

	public class TLCItemFilter extends ItemsFilter {

		private final TableLabelProvider labelProvider = new TableLabelProvider();
		
		/* (non-Javadoc)
		 * @see org.eclipse.ui.dialogs.FilteredItemsSelectionDialog.ItemsFilter#isConsistentItem(java.lang.Object)
		 */
		public boolean isConsistentItem(final Object item) {
			return true;
		}

		/* (non-Javadoc)
		 * @see org.eclipse.ui.dialogs.FilteredItemsSelectionDialog.ItemsFilter#matchItem(java.lang.Object)
		 */
		public boolean matchItem(final Object item) {
			if (getPattern() == null || getPattern().length() == 0) {
				return true;
			}
			// Use the text shown by the label provider. The user definitely
			// wants to search inside what is actually shown.
			return patternMatcher.matches(labelProvider.getText(item));
		}
	}

	private class DetailsLabelProvider extends LabelProvider {

		/* (non-Javadoc)
		 * @see org.eclipse.jface.viewers.LabelProvider#getText(java.lang.Object)
		 */
		public String getText(final Object element) {
			if (element instanceof Module) {
				final Module module = (Module) element;
				return module.getModuleName();
			} else if (element instanceof ILaunchConfiguration) {
				final ILaunchConfiguration config = (ILaunchConfiguration) element;
				return ModelHelper.getModelName(config.getFile());
			} else if (element instanceof Spec) {
				final Spec spec = (Spec) element;
				return spec.getName();
			} else if (element instanceof ItemsListSeparator) {
				return EMPTY_STRING;
			}
			return super.getText(element);
		}
	}
	
	private class ItemsListSeparator {
		private final String label;
		
		public ItemsListSeparator(String label) {
			this.label = label;
		}

		public String getLabel() {
			return label;
		}
	}

	private class TableLabelProvider extends LabelProvider implements IDescriptionProvider, IStyledLabelProvider {

		private static final String DELIM = ":";

		public String getText(final Object element) {
			if (element == null) {
				return null;
			}
			if (element instanceof Spec) {
				final Spec spec = (Spec) element;
				final IFile root = spec.getRootFile();
				if (root == null) {
					return null;
				}
				return spec.getName() + " [ " + root.getName() + " ]";
			} else if (element instanceof Module) {
				return ((Module) element).getModuleName();
			} else if (element instanceof ILaunchConfiguration) {
				final ILaunchConfiguration config = (ILaunchConfiguration) element;
				try {
					String attribute = config.getAttribute(IModelConfigurationConstants.MODEL_COMMENTS,
							toggleShowConstantsAction.isChecked()
									? ModelHelper.prettyPrintConstants(config, DELIM + " ")
									: EMPTY_STRING);
					if (!EMPTY_STRING.equals(attribute)) {
						if (attribute.contains("\n")) {
							attribute = attribute.split("\n")[0];
						}
						return ModelHelper.getModelName(config) + DELIM + " " + attribute;
					}
				} catch (CoreException e) {
				}
				return ModelHelper.getModelName(config);
			} else if (element instanceof ItemsListSeparator) {
				final ItemsListSeparator ils = (ItemsListSeparator) element;
				return "-------------- " + ils.getLabel() + " --------------";
			}
			return null;
		}

		public String getDescription(final Object element) {
			return super.getText(element);
		}

		public Image getImage(final Object element) {
			if (element == null) {
				return null;
			}
			if (element instanceof Spec) {
				if (Activator.getSpecManager().isSpecLoaded((Spec) element)) {
					return PlatformUI.getWorkbench().getSharedImages().getImage(SharedImages.IMG_OBJ_PROJECT);
				}
				return PlatformUI.getWorkbench().getSharedImages().getImage(SharedImages.IMG_OBJ_PROJECT_CLOSED);
			} else if (element instanceof Module) {
				return PlatformUI.getWorkbench().getSharedImages().getImage(ISharedImages.IMG_OBJ_FILE);
			} else if (element instanceof ILaunchConfiguration) {
				return ModelImage;
			}
			return null;
		}

		public StyledString getStyledText(Object element) {
			final String text = getText(element);
			if (text == null || EMPTY_STRING.equals(text)) {
				return new StyledString();
			}
			
			final StyledString string = new StyledString(text);
			
			if (element instanceof Spec) {
				string.setStyle(0, string.length(), StyledString.QUALIFIER_STYLER);
			} else if (element instanceof ILaunchConfiguration && text.indexOf(DELIM) != -1) {
				final int index = text.indexOf(DELIM);
				string.setStyle(index, text.length() - index, StyledString.DECORATIONS_STYLER);
			} else if (element instanceof ItemsListSeparator) {
				string.setStyle(0, string.length(), StyledString.QUALIFIER_STYLER);
			}
			return string;
		}
	}
	
	private class ToggleShowAction extends Action {

		public ToggleShowAction(final String label, final boolean checked) {
			super(label, IAction.AS_CHECK_BOX);
			setChecked(checked);
		}

		public void run() {
			// Doesn't do anything. The dialog has to be re-opened to see its effect.
		}
	}
}