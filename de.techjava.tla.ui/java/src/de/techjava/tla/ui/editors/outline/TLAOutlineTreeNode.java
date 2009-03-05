package de.techjava.tla.ui.editors.outline;

import java.util.ArrayList;

import org.eclipse.core.runtime.ListenerList;
import org.eclipse.jface.util.IPropertyChangeListener;
import org.eclipse.jface.util.PropertyChangeEvent;



public class TLAOutlineTreeNode {
	
	private String name;
	private int kind;
	private TLAOutlineTreeNode[] children;
	private int startCol = 0;
	private int startRow = 0;
	private int endCol = 0;
	private int endRow = 0;
	private String rootModuleName;
		
	ListenerList propertyChangeListeners = null;
	
	
	public TLAOutlineTreeNode() {
		
	}
	

	
	public TLAOutlineTreeNode(String name, int kind, String root) {
		this.name = name;
		this.kind = kind;		
		this.startCol = 0;
		this.startRow = 0;
		this.endCol = 0;
		this.endRow = 0;
		this.rootModuleName = root;
	}
	
	
	
	public TLAOutlineTreeNode(String name, int kind, 
			int startCol, int startRow,
			int endCol, int endRow, String root) {
		
		this.name = name;
		this.kind = kind;		
		this.startCol = startCol;
		this.startRow = startRow;
		this.endCol = endCol;
		this.endRow = endRow;
		this.rootModuleName = root;
		
	}
	
	
	public String getRootModuleName(){
		return this.rootModuleName;
	}
	


	public int getEndCol() {
		return endCol;
	}

	public int getEndRow() {
		return endRow;
	}



	public int getStartCol() {
		return startCol;
	}

	public int getStartRow() {
		return startRow;
	}

	/**
	 * @return the children
	 */
	public TLAOutlineTreeNode[] getChildren() {
		return children;
	}




	/**
	 * @param children the children to set
	 */
	public void setChildren(ArrayList children) {
		this.children = new TLAOutlineTreeNode[children.size()];
		for(int i=0; i<children.size(); i++)
			this.children[i] = (TLAOutlineTreeNode)children.get(i); 		
	}
	
	public void setChildren(TLAOutlineTreeNode[] children) {
		this.children = children; 		
	}

	/**
	 * @return the name
	 */
	public String getName() {
		return name;
	}

	/**
	 * @param name the name to set
	 */
	public void setName(String name) {
		this.name = name;
	}

	/**
	 * @return the type
	 */
	public int getKind() {
		return kind;
	}

	/**
	 * @param type the type to set
	 */
	public void setKind(int kind) {
		this.kind = kind;
	}
		
	public void addPropertyChangeListener(IPropertyChangeListener listener) {
		getPropertyChangeListeners().add(listener);
	}

	public void removePropertyChangeListener(IPropertyChangeListener listener) {
		getPropertyChangeListeners().remove(listener);
	}
	
	public Object[] retrievePropertyChangeListener() {
		return getPropertyChangeListeners().getListeners();
	}

	public void firePropertyChange(Object newValue) {
		final PropertyChangeEvent event = new PropertyChangeEvent(this, "", null, newValue);	
		Object[] listeners = getPropertyChangeListeners().getListeners();
		for (int i = 0; i < listeners.length; i++) {
			((IPropertyChangeListener) listeners[i]).propertyChange(event);
		}
	}

	private ListenerList getPropertyChangeListeners() {
		if (propertyChangeListeners == null)
			propertyChangeListeners = new ListenerList();
		return propertyChangeListeners;
	}
	
	
	
}
