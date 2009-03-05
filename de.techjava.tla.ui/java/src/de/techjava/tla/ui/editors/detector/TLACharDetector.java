package de.techjava.tla.ui.editors.detector;

import java.util.Hashtable;

import org.eclipse.jface.text.rules.IWordDetector;

public class TLACharDetector 
	implements IWordDetector
{
    public final static char[] WORD_STARTING_CHARS = new char[] 
    {
      '!', '#', '$', '%', '&', '(', '*', '+', '-', '.', '/', ':', '<', '=', '>', '?', '@', '\\', '^', '|', '~', '\'', '[',
      ',', '\n', '\t',         ')',                                                                                   ']'       
    };
    
    public final static Hashtable startingMap = new Hashtable(WORD_STARTING_CHARS.length, 0.75f);
    /**
     * Constructor for operation char detector
     */
    public TLACharDetector()
    {
        for (int i=0;i<WORD_STARTING_CHARS.length;i++)
        {
            startingMap.put(new String(new char[]{WORD_STARTING_CHARS[i]}), "");
        }
    }
    
    /**
     * @see org.eclipse.jface.text.rules.IWordDetector#isWordStart(char)
     */
    public boolean isWordStart(char c) 
    {
        if ( startingMap.get(new String(new char[]{c})) != null ) 
        {
            return true;
        } else {
            return false;
        }
    }

    /**
     * @see org.eclipse.jface.text.rules.IWordDetector#isWordPart(char)
     */
    public boolean isWordPart(char c) 
    {
        return !Character.isWhitespace(c); 
    }
}
