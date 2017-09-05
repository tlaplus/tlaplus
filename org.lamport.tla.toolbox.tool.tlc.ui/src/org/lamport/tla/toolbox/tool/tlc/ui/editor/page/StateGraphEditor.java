package org.lamport.tla.toolbox.tool.tlc.ui.editor.page;

import java.io.File;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.content.IContentDescription;
import org.eclipse.swt.SWT;
import org.eclipse.swt.layout.FillLayout;
import org.eclipse.swt.widgets.Canvas;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.ui.IEditorInput;
import org.eclipse.ui.IEditorSite;
import org.eclipse.ui.IFileEditorInput;
import org.eclipse.ui.PartInitException;
import org.eclipse.ui.part.EditorPart;

public class StateGraphEditor extends EditorPart {

	private com.abstratt.imageviewer.GraphicalViewer viewer;
	
	@Override
	public void init(IEditorSite site, IEditorInput input) throws PartInitException {
		setSite(site);
		setInput(input);
		setPartName("State Graph");
	}

	@Override
	public void createPartControl(Composite parent) {
		parent.setLayout(new FillLayout());
		final Canvas canvas = new Canvas(parent, SWT.NONE);
		viewer = new com.abstratt.imageviewer.GraphicalViewer(canvas);
		
		if (getEditorInput() instanceof IFileEditorInput) {
			setFileEditorInput((IFileEditorInput) getEditorInput());
		}
	}

	public void setFileEditorInput(IFileEditorInput fileEditorInput) {
		final IFile file = fileEditorInput.getFile();
		IContentDescription contentDescription = null;
		try {
			contentDescription = file.getContentDescription();
		} catch (final CoreException e) {
			e.printStackTrace();
		}
		if (contentDescription == null || contentDescription.getContentType() == null) {
			return;
		}
		final com.abstratt.content.IContentProviderRegistry.IProviderDescription providerDefinition = com.abstratt.content.ContentSupport
				.getContentProviderRegistry().findContentProvider(contentDescription.getContentType(),
						com.abstratt.imageviewer.IGraphicalContentProvider.class);
		if (providerDefinition == null) {
			return;
		}
		final com.abstratt.imageviewer.IGraphicalContentProvider provider = (com.abstratt.imageviewer.IGraphicalContentProvider) providerDefinition
				.getProvider();
		viewer.setContentProvider(provider);
		
		// Handle a too large file by refusing to open it. Instead print a dummy graph
		// with a single node as an error message.
		final File f = file.getLocation().toFile();
		if (f.length() > 100000) {
			viewer.setInput(
					"strict digraph DiskGraph {123 [shape=plaintext] [label=\"State Graph too large to visualize.\nReduce the number of distinct states and rerun TLC.\"]}"
							.getBytes());
		} else {
			viewer.setInput(providerDefinition.read(file));
		}
	}

	@Override
	public void setFocus() {
		viewer.getControl().setFocus();
	}

	@Override
	public void doSave(IProgressMonitor monitor) {
	}

	@Override
	public void doSaveAs() {
	}

	@Override
	public boolean isDirty() {
		return false;
	}

	@Override
	public boolean isSaveAsAllowed() {
		return false;
	}
}
