/***************************************************************************
 * CLASS TLAToken                                                           *
 *                                                                          *
 * A TLAToken object represents a single token of a TLA+ expression.        *
 *                                                                          *
 * A TLAToken object has the following fields:                              *
 *                                                                          *
 *   String string : The actual input.                                      *
 *   int column    : The column in the input line of its first              *
 *                   character (counting from 0).                           *
 *   int type      : The type of the token.  Possibilities are:             *
 *                      BUILTIN, NUMBER, STRING, IDENT, ADDED               *
 *                                                                          *
 * The constructors are TLAToken() and TLAToken(string, column, type).      *
 *                                                                          *
 * The methods are                                                          *
 *                                                                          *
 *   getWidth() : returns width of token in input.                          *
 *   toString() : for debugging                                             *
 ***************************************************************************/
package pcal;

import java.util.ArrayList;

public class TLAToken
        /*************************************************************************
         * This class defines the TLAToken object, which is an element of a       *
         * tokenized expression.                                                  *
         *************************************************************************/
{
    /********************************************************************
     * The region in the file occupied by the token in the PlusCal       *
     * code.  Added 6 Dec 2011 for TLA to PlusCal mapping.               *
     ********************************************************************/

    public static final int BUILTIN = 1;
    /******************************************************************
     * A built-in token.                                               *
     ******************************************************************/

    public static final int NUMBER = 2;
    /******************************************************************
     * A number like "2" or "\O777".                                   *
     ******************************************************************/

    public static final int STRING = 3;
    /******************************************************************
     * A string like "foo".  In this type, the string field does not   *
     * contain the enclosing quotes.                                   *
     ******************************************************************/

    public static final int IDENT = 4;
    /******************************************************************
     * An identifier, such as foo_Bar.                                 *
     ******************************************************************/

    public static final int ADDED = 5;
    public String string;
    /*********************************************************************
     * The string of the token.  This is usually what the user has        *
     * typed, but it may also be something else.                          *
     *********************************************************************/

    public int column;
    /*********************************************************************
     * The column in which the first character of the token appears in    *
     * the expression.                                                    *
     *********************************************************************/

    public int type;
    /********************************************************************
     * The type of the token.  Here are the possibilities:               *
     ********************************************************************/

    public Region source;
    /******************************************************************
     * A token "pc" or "stack" has this type when it has been added    *
     * by the translator, and so it should be given a subscript if     *
     * this is a multiprocess algorithm.  It doesn't matter whether    *
     * or not the translator uses this type for other tokens it        *
     * creates.                                                        *
     ******************************************************************/

    /**
     * A BEGIN/END_REPLACEMENT token is a zero-width token, with
     * string "", that marks the beginning/end of a region of an
     * expression obtained by substituting an expression for a token.
     * The beginning and end  of the region of the BEGIN_REPLACEMENT
     * token both equal the begin location of the replaced token; the
     * beginning and end of the region of the END_REPLACEMENT token
     * both equal the end region of the replaced token.
     */
    /**
     * The beginSubst and endSubst fields represent sequences of Paren objects in a TPMap,
     * as described in module TLAtoPCal.  This means that they indicate the beginning
     * and ending of substitutions that created the expression containing the token.
     * Here is an example.
     * <p>
     * macro foo(a) {
     * x := a + 1
     * }
     * macro bar(b) {
     * foo(b)
     * }
     * ...
     * bar(3+2) ;
     * <p>
     * After macro expansion, the call of foo in macro bar is replaced by
     * <p>
     * x := b + 1
     * <p>
     * and the call of bar is replaced by
     * <p>
     * x := (3+2)+1
     * <p>
     * The token "b" in "x := b" will have
     * <p>
     * beginSubst = <<beginLoc(a)>> and endSubst = <<endLoc(a)>>
     * <p>
     * where beginLoc(a) and endLoc(a) are the beginning and end locations of the
     * token "a" in expression "x := a + 1" of macro foo.  The token "(" in
     * "x := (3+2)+1" will have
     * <p>
     * beginSubst = << beginLoc(a), beginLoc(b) >> and  endSubst = << >>
     * <p>
     * and the ")" token would have
     * <p>
     * beginSubst =  << >> and endSubst = << endLoc(a), endLoc(b) >>
     * <p>
     * (It was an arbitrary choice to add the begin/endLoc(b) elements to the
     * beginning of the begin/endSubst sequences rather than to the end.)
     * <p>
     * Note that there's no need for the TPMap to have the extra Parens corresponding
     * to the location of "b".  It wouldn't be needed if  substituting an expression containing
     * more than one token for a token always adds parentheses around the substituted
     * expression.  This would imply that if some token has beginSubst equal to a sequence
     * of beginLoc locations, then some token (perhaps the same one) has a its
     * endSubst equal to the corresponding sequence of endLoc locations.  As in the,
     * example, there would be no need to keep anything but the first element of the
     * sequence, which is what is done.  However, since the {@link TLAExpr#substituteAt}
     * method is sometimes called with an argument telling it not to  add
     * parentheses when substituting multiple tokens, I'm letting beginSubst and endSubst
     * be sequences (Vectors) of PCalLocation objects.  It would be a good idea to
     * remove redundant pairs of matching parens (the ones for "b" in the example), and
     * perhaps I'll do that.
     */
    private ArrayList<PCalLocation> beginSubst = new ArrayList<>(2); // of PCalLocation
    private ArrayList<PCalLocation> endSubst = new ArrayList<>(2);    // of PCalLocation
    /**
     * The isAppended flag is true iff this token is a prime ("'")
     * or one of the tokens in the "[self]" that is effectively added
     * to an expression immediately after an IDENT token by the
     * {@link PcalTLAGen#AddSubscriptsToExpr} method.
     */
    private boolean isAppended = false;

    /**
     * This is the old constructor, used before the addition of the TLA-PCal
     * mapping.  It should be used only to construct tokens that do not come
     * from a corresponding token in the PCal code.
     */
    public TLAToken(final String str, final int col, final int typ)
    /*********************************************************************
     * A TLAToken constructor                                             *
     *********************************************************************/
    {
        string = str;
        column = col;
        type = typ;
        source = null;
    }

    /**
     * The following constructor added for TLA-PCal mapping.  It
     * sets the source field.
     */
    public TLAToken(final String str, final int col, final int typ, final int line)
    /*********************************************************************
     * A TLAToken constructor                                             *
     *********************************************************************/
    {
        string = str;
        column = col;
        type = typ;
        source = new Region(line, col, str.length());
    }

    /**
     * A constructor for cases in which the source region is known.
     */
    public TLAToken(final String str, final int col, final int typ, final Region src) {
        string = str;
        column = col;
        type = typ;
        source = src;
    }


    /**
     * A constructor used only in {@link PcalTLAGen#AddSubscriptsToExpr}
     * or in Gen... methods that use it to construct tokens for the
     * TLAExpr argument of a call AddSubscriptsToExpr
     * to create a token with isAppended = true.
     */
    public TLAToken(final String str, final int col, final int typ, final boolean appended) {
        string = str;
        column = col;
        type = typ;
        source = null;
        isAppended = true;
    }

    public TLAToken()
    /*********************************************************************
     * A default Token constructor, apparently needed for subclasses.     *
     *********************************************************************/
    {
        string = "";
        column = 0;
        type = 0;
    }


    /***********************************************************************
     * Below are the methods for this object class, including the           *
     * constructors.                                                        *
     ***********************************************************************/

    public ArrayList<PCalLocation> getBeginSubst() {
        return beginSubst;
    }

    public void setBeginSubst(final ArrayList<PCalLocation> beginSubst) {
        this.beginSubst = beginSubst;
    }

    public ArrayList<PCalLocation> getEndSubst() {
        return endSubst;
    }

    public void setEndSubst(final ArrayList<PCalLocation> endSubst) {
        this.endSubst = endSubst;
    }

    public boolean isAppended() {
        return isAppended;
    }

    public int getWidth()
    /*********************************************************************
     * Returns a width, which is the number of columns the token spans    *
     * in the original input stream.                                      *
     *********************************************************************/
    {
        if (string == null) {
            return 0;
        } else if (type == STRING) {/****************************************************************
         * Have to compensate for the removal of the quotes.             *
         ****************************************************************/
            return string.length() + 2;
        } else {
            return string.length();
        }
    }

    public String toString()
    /*********************************************************************
     * This is used to print a TLAToken for debugging.                    *
     *********************************************************************/
    {
        String typeName = switch (type) {
            case BUILTIN -> "BUILTIN";
            case NUMBER -> "NUMBER";
            case STRING -> "STRING";
            case IDENT -> "IDENT";
            default -> "";
        };
        String str = "\"" + string + "\"";
        if (string == null) {
            str = "null";
        }

        final String result = "[str |-> " + str
                + ", type |-> " + typeName
                + ", col |-> " + column
                + ", source |->" +
                ((source == null) ? "null" : source.toString())
                + ", beginSub |-> " + beginSubst.toString()
                + ", endSub |-> " + endSubst.toString() + "]";

        return result;
    }


    /**
     * Modified by LL on 6 Dec 2011 to set the source field too.
     * And on 14 Dec 2011 to set the beginSubst and endSubst fields.
     */
    @SuppressWarnings("unchecked")
    public TLAToken Clone() {
        final TLAToken result = new TLAToken(this.string, this.column, this.type);
        result.source = this.source;
        result.beginSubst = (ArrayList<PCalLocation>) this.beginSubst.clone();
        result.endSubst = (ArrayList<PCalLocation>) this.endSubst.clone();
        result.isAppended = this.isAppended;
        return result;
    }

}

/* last modified on Tue 26 Jul 2005 at  0:03:08 UT by lamport */
