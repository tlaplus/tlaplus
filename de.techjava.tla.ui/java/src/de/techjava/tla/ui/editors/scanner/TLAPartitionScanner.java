package de.techjava.tla.ui.editors.scanner;

import java.util.ArrayList;
import java.util.List;

import org.eclipse.jface.text.rules.EndOfLineRule;
import org.eclipse.jface.text.rules.ICharacterScanner;
import org.eclipse.jface.text.rules.IPredicateRule;
import org.eclipse.jface.text.rules.IToken;
import org.eclipse.jface.text.rules.IWordDetector;
import org.eclipse.jface.text.rules.MultiLineRule;
import org.eclipse.jface.text.rules.RuleBasedPartitionScanner;
import org.eclipse.jface.text.rules.Token;
import org.eclipse.jface.text.rules.WordRule;

/**
 * A scanner for identifying partitions in TLA source
 * @author Simon Zambrovski, <a href="http://simon.zambrovski.org">http://simon.zambrovski.org</a> 
 * @version $Id: TLAPartitionScanner.java,v 1.1 2005/08/22 15:43:37 szambrovski Exp $
 */
public class TLAPartitionScanner 
	extends RuleBasedPartitionScanner 
{
    public final static String TLA_DEFAULT 			= "__tla_default";
    public final static String TLA_COMMENT 			= "__tla_comment";
    public final static String TLA_COMMENT_MULTI	= "__tla_comment_multi";
	public final static String TLA_RESERVED_WORD 	= "__tla_reserved";
	public final static String TLA_OPERATOR 		= "__tla_operator";
    public static final String TLA_PARTITIONING 	= "__tla_partitioning";
    
    public final static String[] TLA_PARTITION_TYPES = new String[]{TLA_COMMENT_MULTI, TLA_COMMENT};  
    
        
    /**
     * Default constructor
     */
    public TLAPartitionScanner()
    {
        super();
		IToken comment 		= new Token(TLA_COMMENT);
		IToken commentMulti = new Token(TLA_COMMENT_MULTI);

		List rules= new ArrayList();

		// Add rule for single line comments.
		rules.add(new EndOfLineRule("\\*", comment)); 

		// Add rule for strings and character constants.
		// rules.add(new SingleLineRule("\"", "\"", Token.UNDEFINED, '\\')); 
		// rules.add(new SingleLineRule("'", "'", Token.UNDEFINED, '\\')); 

		// Add special case word rule.
		rules.add(new WordPredicateRule(comment));

		// Add rules for multi-line comments
		rules.add(new MultiLineRule("(*", "*)", commentMulti, (char) 0, false));

		IPredicateRule[] result= new IPredicateRule[rules.size()];
		rules.toArray(result);
		setPredicateRules(result);

    }
    
    /**
	 * Detector for empty comments.
	 */
	static class EmptyCommentDetector 
		implements IWordDetector 
	{

	    /**
	     * @see org.eclipse.jface.text.rules.IWordDetector#isWordStart(char)
	     */
		public boolean isWordStart(char c) 
		{
			return (c == '(' || c == '\\');
		}
		/**
		 * @see org.eclipse.jface.text.rules.IWordDetector#isWordPart(char)
		 */
		public boolean isWordPart(char c) {
			return (c == '*' || c == ')');
		}
	}
	
	/**
	 * 
	 */
	static class WordPredicateRule 
		extends WordRule 
		implements IPredicateRule 
	{
		
		private IToken fSuccessToken;
		
		public WordPredicateRule(IToken successToken) 
		{
			super(new EmptyCommentDetector());
			fSuccessToken= successToken;
			addWord("(**)", fSuccessToken);
		}
		
		/**
		 * @see org.eclipse.jface.text.rules.IPredicateRule#evaluate(ICharacterScanner, boolean)
		 */
		public IToken evaluate(ICharacterScanner scanner, boolean resume) {
			return super.evaluate(scanner);
		}

		/**
		 * @see org.eclipse.jface.text.rules.IPredicateRule#getSuccessToken()
		 */
		public IToken getSuccessToken() {
			return fSuccessToken;
		}
	}

}

/*
 * $Log: TLAPartitionScanner.java,v $
 * Revision 1.1  2005/08/22 15:43:37  szambrovski
 * sf cvs init
 *
 * Revision 1.5  2004/10/20 22:42:31  sza
 * editor improvements
 *
 * Revision 1.4  2004/10/13 19:29:06  sza
 * old code removed
 *
 * Revision 1.3  2004/10/13 19:28:36  sza
 * refactrored
 *
 * Revision 1.2  2004/10/13 14:45:00  sza
 * operators added
 *
 * Revision 1.1  2004/10/12 16:21:38  sza
 * initial commit
 *
 * Revision 1.1  2004/10/12 09:55:12  sza
 * additions
 *
 * Revision 1.1  2004/10/06 01:02:29  sza
 * initial commit
 *
 * Revision 1.1  2004/10/06 00:59:04  sza
 * initial commit
 *
 *
 */