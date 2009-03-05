package de.techjava.tla.ui.editors.outline;

import java.util.ArrayList;
import java.util.Map;

import org.eclipse.core.runtime.CoreException;
import org.eclipse.jface.viewers.ISelectionChangedListener;
import org.eclipse.jface.viewers.SelectionChangedEvent;
import org.eclipse.jface.viewers.TreeSelection;
import org.eclipse.jface.viewers.TreeViewer;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.ui.views.contentoutline.ContentOutlinePage;

import de.techjava.tla.ui.UIPlugin;
import de.techjava.tla.ui.editors.TLAEditor;
import de.techjava.tla.ui.extensions.ITLAParserRuntime;




/**
 * TLA's outline page
 *
 * @author Boris Gruschko ( Lufthansa Systems Business Solutions GmbH )
 * @version $Id: TLAOutlinePage.java,v 1.3 2007/07/04 08:59:10 dan_nguyen Exp $
 */
public class TLAOutlinePage
		extends ContentOutlinePage
		implements ISelectionChangedListener

{
	private TLAEditor editor;
	private TLAOutlineTreeNode moduleRootNode;
	private String moduleName;
	TreeViewer view;
	private int[] endColArr; 
	ArrayList tmpArr;
	
	
	public TLAOutlinePage( TLAEditor editor ) {
		this.editor = editor;
		init();			
	}
	
	private void init() {
		try {
			ITLAParserRuntime parser = UIPlugin.getDefault().getExtensionManager().getParserRuntime();
			this.moduleName = editor.getTitle(); //name.tla
			if(moduleName.indexOf(".tla") != -1)
				moduleName = moduleName.substring(0, moduleName.indexOf(".tla"));
			//get the Module corresponding to this tla file
			Map outlineNode = parser.getSpecObj();
			if(outlineNode != null && outlineNode.get(moduleName) != null) {
				this.moduleRootNode = (TLAOutlineTreeNode)outlineNode.get(moduleName);
				int maxRow = 0;						
				TLAOutlineTreeNode[] tmpChildren = moduleRootNode.getChildren();
				maxRow = calculateMaxRow(tmpChildren[tmpChildren.length - 1], maxRow);
//				System.out.println("Row number: " + maxRow);
				
				tmpArr = new ArrayList(maxRow);
				for(int i=0; i<maxRow; i++)
					tmpArr.add(new Integer(0));
				tmpArr = createEndColArr(tmpChildren[tmpChildren.length - 1]); //the right treenode representing the current editor's content is always the last node in tree
				this.endColArr = new int[tmpArr.size()];
				for(int i=0; i<tmpArr.size(); i++) {
					Integer tmpInt = (Integer)tmpArr.get(i);
					endColArr[i] = tmpInt.intValue();
				}
//				System.out.println(tmpArr.toString());
			}							
		} catch (CoreException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		} catch(Exception e) {
			e.printStackTrace();
		}
	}
	
	private int calculateMaxRow(TLAOutlineTreeNode node, int max){
		TLAOutlineTreeNode[] children = node.getChildren();
		for(int i=0; i< children.length; i++) {
			TLAOutlineTreeNode tmpNode = children[i];
			if(tmpNode.getEndRow() > max)
				max = tmpNode.getEndRow();
			
			calculateMaxRow(tmpNode, max);
		}
		return max;
	}
	
	private ArrayList createEndColArr(TLAOutlineTreeNode node) {
				
		TLAOutlineTreeNode[] children = node.getChildren();
		for(int i=0; i< children.length; i++) {
			TLAOutlineTreeNode tmpNode = children[i];
			int index = ((tmpNode.getStartRow() - 1) > 0) ? (tmpNode.getStartRow() - 1) : 0;
			
			try {						
				if(tmpArr.get(index) == null)
					tmpArr.add(index, new Integer(tmpNode.getEndCol()));
				else {
					Integer oldMax = (Integer)tmpArr.get(index);
					int newMax = tmpNode.getEndCol();
					if(tmpNode.getStartRow() == tmpNode.getEndRow() && oldMax.intValue() < newMax) 
						tmpArr.set(index, new Integer(newMax));				
				}				
				
			} catch(java.lang.IndexOutOfBoundsException e) {
				tmpArr.add(index, new Integer(tmpNode.getEndCol()));
			}
			createEndColArr(tmpNode);
		}
		return tmpArr;						
	}

	/**
	 * @see org.eclipse.ui.part.IPage#createControl(org.eclipse.swt.widgets.Composite)
	 */
	public void createControl(Composite parent)
	{
		super.createControl(parent);
		view = getTreeViewer();			
		view.setContentProvider(new TLAContentProvider());
		view.setLabelProvider( new TLALabelProvider() );
		view.setInput(moduleRootNode);		
		view.addSelectionChangedListener(this);

	}


	
	public void selectionChanged(SelectionChangedEvent event){
		
		 TreeSelection selection = (TreeSelection) event.getSelection();
		 if(selection != null && selection.size() > 0){
			 TLAOutlineTreeNode selectedNode = (TLAOutlineTreeNode)selection.getFirstElement();
			 if(selectedNode.getRootModuleName() != "" && !selectedNode.getRootModuleName().equals(this.moduleName))
				 return;
			 
//			 System.out.println(selectedNode.getName() + " Location: " + selectedNode.getStartCol() + " " + selectedNode.getStartRow() + " " 
//					 + selectedNode.getEndCol() + " " + selectedNode.getEndRow());
			 if(selectedNode.getStartCol() != 0 || selectedNode.getStartRow() != 0){
				 int start = 0;
				 int length = 0;
				 if(selectedNode.getStartRow() < 2){
					 start = selectedNode.getStartCol();					 					
				 }
				 else {					 
					 for(int i=0; i < selectedNode.getStartRow() - 1; i++){
						 start += this.endColArr[i] + 1 ;					
					 }
					 start += selectedNode.getStartCol();
				 }
				 for(int i = selectedNode.getStartRow(); i < selectedNode.getEndRow(); i++) {
					 length += this.endColArr[i];
				 }
				 if(selectedNode.getStartRow() == selectedNode.getEndRow())
					 length += selectedNode.getEndCol() - selectedNode.getStartCol() + 1;
				 else
					 length += endColArr[0] - selectedNode.getStartCol() + 1 + selectedNode.getEndCol();
				 
//				 System.out.println("Start: " + start + " Length: " + length);
				 
				 editor.selectAndReveal(start - 1, length);
			 }
		 }		 
	}
	

	
	
}

/*-
 * $Log: TLAOutlinePage.java,v $
 * Revision 1.3  2007/07/04 08:59:10  dan_nguyen
 * remove unused comments
 *
 * Revision 1.2  2007/06/27 15:34:19  dan_nguyen
 * changes for tla editor outline view
 *
 * Revision 1.1  2005/08/22 15:43:35  szambrovski
 * sf cvs init
 *
 * Revision 1.2  2004/10/20 16:30:26  sza
 * warnings killed
 *
 * Revision 1.1  2004/10/20 11:56:14  bgr
 * first outline added
 *
 */