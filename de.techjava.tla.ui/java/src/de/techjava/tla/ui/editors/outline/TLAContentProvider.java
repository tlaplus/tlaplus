package de.techjava.tla.ui.editors.outline;

import java.util.ArrayList;

import org.eclipse.jface.util.IPropertyChangeListener;
import org.eclipse.jface.util.PropertyChangeEvent;
import org.eclipse.jface.viewers.ITreeContentProvider;
import org.eclipse.jface.viewers.TreeViewer;
import org.eclipse.jface.viewers.Viewer;
import org.eclipse.swt.widgets.Control;


/**
 * TLA's outline content provider
 *
 * @author Boris Gruschko ( Lufthansa Systems Business Solutions GmbH )
 * @version $Id: TLAContentProvider.java,v 1.3 2007/07/04 08:59:10 dan_nguyen Exp $
 */
public class TLAContentProvider
		implements ITreeContentProvider, IPropertyChangeListener
{
	
	private TreeViewer viewer;


	
	/**
	 * @see org.eclipse.jface.viewers.IContentProvider#dispose()
	 */
	public void dispose()
	{
		// TODO Auto-generated method stub
	}

	/**
	 * @see org.eclipse.jface.viewers.IContentProvider#inputChanged(org.eclipse.jface.viewers.Viewer, java.lang.Object, java.lang.Object)
	 */
	public void inputChanged(Viewer viewer, Object oldInput, Object newInput)
	{
		System.out.println("Input changed");
		if(this.viewer == null)
			this.viewer = (TreeViewer) viewer;
		if (oldInput != newInput) { // if not the same

		      if (newInput != null) { // add listener to new - fires even if old is null
		        ((TLAOutlineTreeNode) newInput).addPropertyChangeListener(this);
		      }

		      if (oldInput != null) { // remove from old - fires even if new is null
		        ((TLAOutlineTreeNode) oldInput).removePropertyChangeListener(this);
		      }
		    }

	}
	
	

	/**
	 * @param event
	 */
	
	public void propertyChange(final PropertyChangeEvent event) {
		Control ctrl = viewer.getControl();
	    if (ctrl != null && !ctrl.isDisposed()) {

	      ctrl.getDisplay().asyncExec(new Runnable() {

	        public void run() {
	        	viewer.setInput(event.getNewValue());
	        	viewer.refresh();
	        	
	        }
	      });
	    }
		
	}

	/**
	 * @see org.eclipse.jface.viewers.IStructuredContentProvider#getElements(java.lang.Object)
	 */
	public Object[] getElements(Object inputElement)
	{
		if (inputElement instanceof TLAOutlineTreeNode)
			return getChildren(inputElement);
		return new Object[0];
	}

	/**
	 * @see org.eclipse.jface.viewers.ITreeContentProvider#getChildren(java.lang.Object)
	 */
	public Object[] getChildren(Object parentElement)
	{
		if(parentElement instanceof TLAOutlineTreeNode) {
			ArrayList arrayList = new ArrayList();
			TLAOutlineTreeNode[] children = ((TLAOutlineTreeNode) parentElement).getChildren();
			for(int i=0; i < children.length; i++)
				arrayList.add(children[i]);
			return arrayList.toArray();
		}
		return new Object[0];
			
	}

	/**
	 * @see org.eclipse.jface.viewers.ITreeContentProvider#getParent(java.lang.Object)
	 */
	public Object getParent(Object element)
	{
		
		return null;
	}

	/**
	 * @see org.eclipse.jface.viewers.ITreeContentProvider#hasChildren(java.lang.Object)
	 */
	public boolean hasChildren(Object element)
	{
		if(element instanceof TLAOutlineTreeNode)
			return ((TLAOutlineTreeNode)element).getChildren() != null || 
					((TLAOutlineTreeNode)element).getChildren().length == 0 ;
		return false;
	}

}

/*-
 * $Log: TLAContentProvider.java,v $
 * Revision 1.3  2007/07/04 08:59:10  dan_nguyen
 * remove unused comments
 *
 * Revision 1.2  2007/06/27 15:34:19  dan_nguyen
 * changes for tla editor outline view
 *
 * Revision 1.1  2005/08/22 15:43:35  szambrovski
 * sf cvs init
 *
 * Revision 1.1  2004/10/20 11:56:14  bgr
 * first outline added
 *
 */