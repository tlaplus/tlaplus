package org.lamport.tla.toolbox.tool.tlc.output.source;

import java.util.Vector;

import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.rules.IPredicateRule;
import org.eclipse.jface.text.rules.IRule;
import org.eclipse.jface.text.rules.IToken;
import org.eclipse.jface.text.rules.RuleBasedPartitionScanner;
import org.eclipse.jface.text.rules.SingleLineRule;
import org.eclipse.jface.text.rules.Token;

/**
 * Partitioning of the TLC output
 * @author Simon Zambrovski
 * @version $Id$
 */
public class TagBasedTLCOutputTokenScanner extends RuleBasedPartitionScanner
{
    private final static String HEAD_DELIM = "@!@!@";
    private final static String TAIL_DELIM = "";
    private final static String RULE_START = HEAD_DELIM + "STARTMSG";
    private final static String RULE_END = HEAD_DELIM + "ENDMSG";

    public static final String TAG_OPEN = "__tlc_tag_open";
    public static final String TAG_CLOSED = "__tlc_tag_closed";
    public static final String DEFAULT_CONTENT_TYPE = "__tlc_output";

    public static final String[] CONTENT_TYPES = new String[] { TAG_OPEN, TAG_CLOSED, DEFAULT_CONTENT_TYPE };

    public TagBasedTLCOutputTokenScanner()
    {
        Vector rules = new Vector();

        rules.add(new SingleLineRule(RULE_START, TAIL_DELIM + "\n", new Token(TAG_OPEN)));
        rules.add(new SingleLineRule(RULE_END, TAIL_DELIM + "\n", new Token(TAG_CLOSED)));

        // add the rules
        setPredicateRules((IPredicateRule[]) rules.toArray(new IPredicateRule[rules.size()]));

        // output is default
        setDefaultReturnToken(new Token(DEFAULT_CONTENT_TYPE));
    }

    public IToken nextToken()
    {
        reportEnter("nextToken");
        IToken result = super.nextToken();
        reportExit("nextToken");
        return result;
    }

    public int getColumn()
    {
        reportEnter("getColumn");
        int result = super.getColumn();
        reportExit("getColumn");
        return result;
    }

    public char[][] getLegalLineDelimiters()
    {
        reportEnter("getLegalLineDelimiters");
        char[][] result = super.getLegalLineDelimiters();
        reportExit("getLegalLineDelimiters");
        return result;
    }

    public int getTokenLength()
    {
        reportEnter("getTokenLength");
        int result = super.getTokenLength();
        reportExit("getTokenLength");
        return result;
    }

    public int getTokenOffset()
    {
        reportEnter("getTokenOffset");
        int result = super.getTokenOffset();
        reportExit("getTokenOffset");
        return result;
    }

    public int read()
    {
        // reportEnter("read");
        int result = super.read();
        // reportExit("read");
        return result;
    }

    public void setDefaultReturnToken(IToken defaultReturnToken)
    {
        reportEnter("setDefaultReturnToken");
        super.setDefaultReturnToken(defaultReturnToken);
        reportExit("setDefaultReturnToken");
    }

    public void setPartialRange(IDocument document, int offset, int length, String contentType, int partitionOffset)
    {
        reportEnter("setPartialRange");
        super.setPartialRange(document, offset, length, contentType, partitionOffset);
        reportExit("setPartialRange");
    }

    public void setPredicateRules(IPredicateRule[] rules)
    {
        reportEnter("setPredicateRules");
        super.setPredicateRules(rules);
        reportExit("setPredicateRules");
    }

    public void setRange(IDocument document, int offset, int length)
    {
        reportEnter("setRange");
        super.setRange(document, offset, length);
        reportExit("setRange");
    }

    public void setRules(IRule[] rules)
    {
        reportEnter("setRules");
        super.setRules(rules);
        reportExit("setRules");
    }

    public void unread()
    {
        reportEnter("unread");
        super.unread();
        reportExit("unread");
    }

    private void reportEnter(String string)
    {
        // TLCUIActivator.logDebug(">>> Entering " + string);
    }

    private void reportExit(String string)
    {
        // TLCUIActivator.logDebug(">>> Exiting " + string);
    }

}
