package org.lamport.tla.toolbox.editor.basic;

import org.eclipse.jface.text.BadLocationException;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.rules.ICharacterScanner;
import org.eclipse.jface.text.rules.IPartitionTokenScanner;
import org.eclipse.jface.text.rules.IToken;
import org.eclipse.jface.text.rules.Token;
import org.lamport.tla.toolbox.editor.basic.util.BufferedDocumentScanner;

/**
 * Partition token scanner
 *  
 * @author Simon Zambrovski
 * @version $Id$
 */
public class TLAPartitionScanner implements IPartitionTokenScanner
{

    public static final String TLA_PARTITIONING = "__tla_partitioning"; //$NON-NLS-1$

    public final static String TLA_MULTI_LINE_COMMENT = "__tla_multiline_comment"; //$NON-NLS-1$
    public final static String TLA_SINGLE_LINE_COMMENT = "__tla_singleline_comment"; //$NON-NLS-1$
    public final static String TLA_PCAL = "__tla_pcal"; //$NON-NLS-1$
    public final static String TLA_STRING = "__tla_string"; //$NON-NLS-1$
    /**
     * supported partition types
     */
    public static final String[] TLA_PARTITION_TYPES = new String[] { TLA_MULTI_LINE_COMMENT, TLA_SINGLE_LINE_COMMENT,
            TLA_STRING };

    // states
    private static final int TLA = 0;
    private static final int SINGLE_LINE_COMMENT = 1;
    private static final int MULTI_LINE_COMMENT = 2;
    private static final int PCAL = 3;
    private static final int STRING = 4;

    private final IToken[] fTokens = new IToken[] { new Token(null), new Token(TLA_SINGLE_LINE_COMMENT),
            new Token(TLA_MULTI_LINE_COMMENT), new Token(TLA_PCAL), new Token(TLA_STRING) };

    // pre-fixes and post-fixes
    private static final int NONE = 0;
    private static final int BACKSLASH = 1;
    private static final int O_BRACKET = 2;
    private static final int C_BRACKET = 3;
    private static final int STAR = 4;
    private static final int CARRIAGE_RETURN = 5;
    private static final int C_BRACKET_STAR = 6;
    private static final int O_BRACKET_STAR = 7;

    private final BufferedDocumentScanner fScanner = new BufferedDocumentScanner(1000); // faster implementation

    private int fTokenOffset;
    private int fTokenLength;

    private int fPrefixLength;
    private int fLast;
    private int fState;

    private boolean fEmulate = false;
    private int fTLAOffset;
    private int fTLALength;

    private int fCommentDepth;

    /**
     * Constructor
     */
    public TLAPartitionScanner()
    {
    }

    /* (non-Javadoc)
     * @see org.eclipse.jface.text.rules.ITokenScanner#nextToken()
     */
    public IToken nextToken()
    {
        // emulate TLAPartitionScanner
        if (fEmulate) {
            if (fTLAOffset != -1 && fTokenOffset + fTokenLength != fTLAOffset + fTLALength) {
                fTokenOffset += fTokenLength;
                return fTokens[TLA];
            } else {
                fTLAOffset= -1;
                fTLALength= 0;
            }
        }

        
        fTokenOffset += fTokenLength;
        fTokenLength = fPrefixLength;

        while (true)
        {
            final int ch = fScanner.read();

            // characters
            switch (ch) {
            case ICharacterScanner.EOF:
                if (fTokenLength > 0)
                {
                    fLast = NONE; // ignore last
                    return preFix(fState, TLA, NONE, 0);
                } else
                {
                    fLast = NONE;
                    fPrefixLength = 0;
                    return Token.EOF;
                }
            case '\r':
             // emulate TLAPartitionScanner
                if (!fEmulate && fLast != CARRIAGE_RETURN)
                {
                    fLast = CARRIAGE_RETURN;
                    fTokenLength++;
                    continue;
                } else
                {
                    switch (fState) {
                    case SINGLE_LINE_COMMENT:
                    case STRING:
                        if (fTokenLength > 0)
                        {
                            IToken token = fTokens[fState];

                            // emulate TLAPartitionScanner
                            if (fEmulate) {
                                fTokenLength++;
                                fLast= NONE;
                                fPrefixLength= 0;
                            } else {
                                fLast= CARRIAGE_RETURN;
                                fPrefixLength= 1;
                            }
                            
                            fState = TLA;
                            return token;

                        } else
                        {
                            consume();
                            continue;
                        }

                    default:
                        consume();
                        continue;
                    }
                }

            case '\n':
                switch (fState) {
                case SINGLE_LINE_COMMENT:
                case STRING:
                    return postFix(fState);

                default:
                    consume();
                    continue;
                }

            default:
                if (!fEmulate && fLast == CARRIAGE_RETURN)
                {
                    switch (fState) {
                    case SINGLE_LINE_COMMENT:
                    case STRING:

                        int last;
                        int newState;
                        switch (ch) {

                        case '(':
                            last = O_BRACKET;
                            newState = TLA;
                            break;

                        case ')':
                            last = C_BRACKET;
                            newState = TLA;
                            break;

                        case '*':
                            last = STAR;
                            newState = TLA;
                            break;

                        case '"':
                            last = NONE;
                            newState = STRING;
                            break;

                        case '\r':
                            last = CARRIAGE_RETURN;
                            newState = TLA;
                            break;

                        case '\\':
                            last = BACKSLASH;
                            newState = TLA;
                            break;

                        default:
                            last = NONE;
                            newState = TLA;
                            break;
                        }

                        fLast = NONE; // ignore fLast
                        return preFix(fState, newState, last, 1);

                    default:
                        break;
                    }
                }
            }

            // states
            switch (fState) {

            case TLA:
                switch (ch) {

                case '\\':
                    fLast = BACKSLASH;
                    fTokenLength++;
                    break;

                case '(':
                    fLast = O_BRACKET;
                    fTokenLength++;
                    break;

                case '*':
                    if (fLast == BACKSLASH)
                    {
                        if (fTokenLength - getLastLength() > 0)
                        {
                            // return single line comment
                            return preFix(TLA, SINGLE_LINE_COMMENT, NONE, 2);
                        } else
                        {
                            preFix(TLA, SINGLE_LINE_COMMENT, NONE, 2);
                            fTokenOffset += fTokenLength;
                            fTokenLength = fPrefixLength;
                            break;
                        }
                    } else if (fLast == O_BRACKET)
                    {
                        fCommentDepth++;
                        if (fTokenLength - getLastLength() > 0) {
                            return preFix(TLA, MULTI_LINE_COMMENT, O_BRACKET_STAR, 2);
                        }
                        else
                        {
                            preFix(TLA, MULTI_LINE_COMMENT, O_BRACKET_STAR, 2);
                            fTokenOffset += fTokenLength;
                            fTokenLength = fPrefixLength;
                            break;
                        }

                    } else
                    {
                        fTokenLength++;
                        fLast = STAR;
                        break;
                    }

                case '"':
                    fLast = NONE; // ignore fLast
                    if (fTokenLength > 0)
                        return preFix(TLA, STRING, NONE, 1);
                    else
                    {
                        preFix(TLA, STRING, NONE, 1);
                        fTokenOffset += fTokenLength;
                        fTokenLength = fPrefixLength;
                        break;
                    }

                default:
                    consume();
                    break;
                }
                break;

            case SINGLE_LINE_COMMENT:
                consume();
                break;

            case MULTI_LINE_COMMENT:
                switch (ch) {
                case '*':
                    if (fLast == O_BRACKET) 
                    {
                        fCommentDepth++;
                        consume();
                        break;
                    } else {
                        fTokenLength++;
                        fLast = STAR;
                        break;
                    }

                case ')':
                    if (fLast == STAR)
                    {
                        fCommentDepth--;
                        if (fCommentDepth == 0) 
                        {
                            // return multi-line comment
                            return postFix(MULTI_LINE_COMMENT);
                        } else {
                            consume();
                            break;
                        }
                    } else
                    {
                        consume();
                        break;
                    }
                case '(':
                    fLast = O_BRACKET;
                    fTokenLength++;
                    break;

                default:
                    consume();
                    break;
                }
                break;

            case STRING:
                switch (ch) {
                case '\"':
                    if (fLast != BACKSLASH)
                    {
                        // return String
                        return postFix(STRING);

                    } else
                    {
                        consume();
                        break;
                    }

                default:
                    consume();
                    break;
                }
                break;
            }
        }
    }

    /* (non-Javadoc)
     * @see org.eclipse.jface.text.rules.ITokenScanner#setRange(org.eclipse.jface.text.IDocument, int, int)
     */
    public void setRange(IDocument document, int offset, int length)
    {
        fScanner.setRange(document, offset, length);
        fTokenOffset = offset;
        fTokenLength = 0;
        fPrefixLength = 0;
        fCommentDepth = 0;
        fLast = NONE;
        fState = TLA;

        // emulate TLAPartitionScanner
        if (fEmulate)
        {
            fTLAOffset = -1;
            fTLALength = 0;
        }

    }

    /* (non-Javadoc)
     * @see org.eclipse.jface.text.rules.IPartitionTokenScanner#setPartialRange(org.eclipse.jface.text.IDocument, int, int, java.lang.String, int)
     */
    public void setPartialRange(IDocument document, int offset, int length, String contentType, int partitionOffset)
    {
        fScanner.setRange(document, offset, length);
        fTokenOffset = partitionOffset;
        fTokenLength = 0;
        fPrefixLength = offset - partitionOffset;
        
        fLast = NONE;

        if (offset == partitionOffset)
        {
            // restart at beginning of partition
            fState = TLA;
        } else
        {
            fState = getState(contentType);
        }
        
        if (fState == MULTI_LINE_COMMENT) 
        {
            fCommentDepth = getCommentDepth(document, partitionOffset, fPrefixLength);
        } else {
            fCommentDepth = 0;    
        }

        // emulate TLAPartitionScanner
        if (fEmulate)
        {
            fTLAOffset = -1;
            fTLALength = 0;
        }
    }

    /**
     * If the scanner starts inside of the multi-line partition, the depth of comment nesting need to be determined. This is performed by this method.
     * @param document the document
     * @param offset start of the partition
     * @param length number of characters between the start of partition and the offset from which the scanner will continue
     * @return comment depth
     */
    private int getCommentDepth(IDocument document, int offset, int length)
    {
        try
        {
            String partitionText = document.get(offset, length);
            // regex for (* and *) needs escaping
            return partitionText.split("\\(\\*").length - partitionText.split("\\*\\)").length;
            
        } catch (BadLocationException e)
        {
            e.printStackTrace();
            return 1;
        }
    }

    /*
     * @see ITokenScanner#getTokenLength()
     */
    public int getTokenLength()
    {
        return fTokenLength;
    }

    /*
     * @see ITokenScanner#getTokenOffset()
     */
    public int getTokenOffset()
    {
        return fTokenOffset;
    }

    /**
     * Map content types to internal states 
     * @param contentType
     * @return
     */
    private static int getState(String contentType)
    {
        if (contentType == null)
            return TLA;
        else if (contentType.equals(TLA_MULTI_LINE_COMMENT))
            return MULTI_LINE_COMMENT;
        else if (contentType.equals(TLA_SINGLE_LINE_COMMENT))
            return SINGLE_LINE_COMMENT;
        else if (contentType.equals(TLA_PCAL))
            return PCAL;
        else if (contentType.equals(TLA_STRING))
            return STRING;
        else
            return TLA;
    }

    /**
     * Consume a character from the scanner
     */
    private final void consume()
    {
        fTokenLength++;
        fLast = NONE;
    }

    /**
     * 
     * @param state
     * @return
     */
    private final IToken postFix(int state)
    {
        fTokenLength++;
        fLast = NONE;
        fState = TLA;
        fPrefixLength = 0;
        return fTokens[state];
    }

    /**
     * 
     * @param state
     * @param newState
     * @param last
     * @param prefixLength
     * @return
     */
    private final IToken preFix(int state, int newState, int last, int prefixLength)
    {
        if (fEmulate && state == TLA && (fTokenLength - getLastLength() > 0))
        {
            fTokenLength -= getLastLength();
            fLast = last;
            fTLAOffset= fTokenOffset;
            fTLALength= fTokenLength;
            fPrefixLength = prefixLength;
            fTokenLength = 1;
            fState = newState;
            return fTokens[state];

        } else
        {
            fTokenLength -= getLastLength();
            fLast = last;
            fPrefixLength = prefixLength;
            IToken token = fTokens[state];
            fState = newState;
            return token;
        }
    }

    /**
     * Return the length of the last significant characters read 
     * @return
     */
    private int getLastLength()
    {
        switch (fLast) {
        default:
            return -1;
        case NONE:
            return 0;
        case CARRIAGE_RETURN:
        case BACKSLASH:
        case STAR:
        case C_BRACKET:
        case O_BRACKET:
            return 1;
        case C_BRACKET_STAR:
        case O_BRACKET_STAR:
            return 2;
        }
    }

}
