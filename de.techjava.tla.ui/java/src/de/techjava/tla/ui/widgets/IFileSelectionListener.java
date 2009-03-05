package de.techjava.tla.ui.widgets;

import org.eclipse.core.resources.IFile;


/**
 * marks a selection of a file
 *
 * @author Boris Gruschko ( http://gruschko.org, boris at gruschko.org )
 * @version $Id: IFileSelectionListener.java,v 1.1 2005/08/22 15:43:33 szambrovski Exp $
 */
public interface IFileSelectionListener
{
	/**
	 * will be called every time a file has been selected
	 * 
	 * @param file resource which has been selected
	 */
	public void fileSelected( IFile file );
}

/*-
 * $Log: IFileSelectionListener.java,v $
 * Revision 1.1  2005/08/22 15:43:33  szambrovski
 * sf cvs init
 *
 * Revision 1.1  2004/10/25 10:09:10  bgr
 * apply button handling added
 *
 */