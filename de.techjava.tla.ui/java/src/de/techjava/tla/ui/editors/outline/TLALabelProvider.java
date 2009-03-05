package de.techjava.tla.ui.editors.outline;

import org.eclipse.jface.viewers.ILabelProvider;
import org.eclipse.jface.viewers.ILabelProviderListener;
import org.eclipse.swt.graphics.Image;


/**
 * DOCME 
 *
 * @author Boris Gruschko ( http://gruschko.org, boris at gruschko.org )
 * @version $Id: TLALabelProvider.java,v 1.2 2007/06/27 15:34:19 dan_nguyen Exp $
 */
public class TLALabelProvider
		implements ILabelProvider
{

	/**
	 * @see org.eclipse.jface.viewers.IBaseLabelProvider#addListener(org.eclipse.jface.viewers.ILabelProviderListener)
	 */
	public void addListener(ILabelProviderListener listener)
	{
		// TODO Auto-generated method stub

	}

	/**
	 * @see org.eclipse.jface.viewers.IBaseLabelProvider#dispose()
	 */
	public void dispose()
	{
		// TODO Auto-generated method stub

	}

	/**
	 * @see org.eclipse.jface.viewers.IBaseLabelProvider#isLabelProperty(java.lang.Object, java.lang.String)
	 */
	public boolean isLabelProperty(Object element, String property)
	{
		// TODO Auto-generated method stub
		return false;
	}

	/**
	 * @see org.eclipse.jface.viewers.IBaseLabelProvider#removeListener(org.eclipse.jface.viewers.ILabelProviderListener)
	 */
	public void removeListener(ILabelProviderListener listener)
	{
		// TODO Auto-generated method stub

	}

	/**
	 * @see org.eclipse.jface.viewers.ILabelProvider#getImage(java.lang.Object)
	 */
	public Image getImage(Object element)
	{
		// TODO Auto-generated method stub
		return null;
	}

	/**
	 * @see org.eclipse.jface.viewers.ILabelProvider#getText(java.lang.Object)
	 */
	public String getText(Object element)
	{
		if (element instanceof TLAOutlineTreeNode) {
			TLAOutlineTreeNode tmp = (TLAOutlineTreeNode) element;
			String tmpStr = tmp.getName() + " (kind=" + tmp.getKind() + ")";
			switch(tmp.getKind()){
			case 282: //module node
				return tmpStr + " " + getModuleName(tmp);
			case 289: //operation node
				return tmpStr + " " + getOperationDefinitionName(tmp);
			default:
				return tmpStr;
			}
			
			
		}
		return "";
			
	}
	
	private String getModuleName(TLAOutlineTreeNode n_module) {
		TLAOutlineTreeNode n_beginModule = n_module.getChildren()[0];
		if(n_beginModule != null) {
			String moduleName = "";
			if(n_beginModule.getChildren().length > 1 && n_beginModule.getChildren()[1] != null) {
				moduleName = n_beginModule.getChildren()[1].getName();
				return moduleName;
			}
		}
		return "";			
	}
	
	private String getOperationDefinitionName(TLAOutlineTreeNode n_operationDefinition) {
		TLAOutlineTreeNode n_identLHS = n_operationDefinition.getChildren()[0];
		if(n_identLHS != null) {
			String operationName = "";
			TLAOutlineTreeNode[] tmpArr = n_identLHS.getChildren();
			if( tmpArr!= null) {
				for(int i=0; i<tmpArr.length; i++) {
					String tmpStr = tmpArr[i].getName();
					if(tmpArr[i].getKind() == 263)
						tmpStr = tmpArr[i].getChildren()[0].getName();
					operationName += tmpStr;
				}				
				return operationName;
			}
		}
		return "";			
	}

}

/*-
 * $Log: TLALabelProvider.java,v $
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