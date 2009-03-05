package de.techjava.tla.ui.editors.detector;

import org.eclipse.jface.text.rules.IWhitespaceDetector;

public class TLAWhitespaceDetector 
	implements IWhitespaceDetector 
{
	public boolean isWhitespace(char c) 
	{
	    return Character.isWhitespace(c);
	}
}
