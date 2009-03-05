package de.techjava.tla.ui.editors.detector;

import java.util.Hashtable;

import org.eclipse.jface.text.rules.IWordDetector;

/**
 * Detects language separators
 * @author Simon Zambrovski, <a href="http://simon.zambrovski.org">http://simon.zambrovski.org</a> 
 * @version $Id: TLASeparatorDetector.java,v 1.1 2005/08/22 15:43:37 szambrovski Exp $
 */
public class TLASeparatorDetector 
	implements IWordDetector 
{
    public final static char[] WORD_STARTING_CHARS = new char[] 
  {
    '(', ',', '{', '['      
  };
                                                              
  public final static Hashtable startingMap = new Hashtable(WORD_STARTING_CHARS.length, 0.75f);
  /**
   * Constructor for operation char detector
   */
  public TLASeparatorDetector()
  {
      for ( int i=0; i < WORD_STARTING_CHARS.length; i++ )
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
      if ( !Character.isWhitespace(c) ) 
      {
          return true;
      } else {
          return false;
      }
  }

}

/*
 * $Log: TLASeparatorDetector.java,v $
 * Revision 1.1  2005/08/22 15:43:37  szambrovski
 * sf cvs init
 *
 * Revision 1.1  2004/10/20 22:42:31  sza
 * editor improvements
 *
 *
 */