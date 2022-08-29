/***************************************************************************
 * CLASS TLAExpr                                                            *
 *                                                                          *
 * A TLAExpr is a representation of any part of a TLA+ specification.  It   *
 * usually represents an expression, but can be used to represent           *
 * sequences of declarations and definitions--including the complete        *
 * translation.                                                             *
 *                                                                          *
 * A TLAExpr expr contains the following fields and methods:                *
 *                                                                          *
 *    tokens       : A vector of lines, where a line is a vector of tokens. *
 *                   We say that expr is NORMALIZED iff expr.tokens has     *
 *                   no non-empty line, or it has a non-empty line whose    *
 *                   first token is in column 0.                            *
 *                                                                          *
 *    anchorTokens : An array of TLAToken's of the same length as           *
 *                   expr.tokens, where expr.anchorTokens[i] is the anchor  *
 *                   of line i.  (The definition of an anchor token is in   *
 *                   the rule for preserving formatting in the comments at  *
 *                   the end of this file.)                                 *
 *                                                                          *
 *    anchorTokCol : An array of int's, of the same length as expr.tokens,  *
 *                   where if expr.anchorTokens[i] is non-null, then        *
 *                   expr.anchorTokCol[i] was the value of                  *
 *                   (expr.anchorTokens[i]).column when the normalize       *
 *                   method was called.                                     *
 *                                                                          *
 * If expr comes from an expression taken directly from the algorithm,      *
 * then it evolves as follows.  First, expr is built up token by token,     *
 * using the methods expr.addToken and expr.addLine methods.  It is then    *
 * normalized and expr.anchorTokCol and expr.anchorTokens are computed by   *
 * calling expr.normalize().  Additional tokens may then be added.  Adding  *
 * a token modifies the columns of the tokens to the right, but it does     *
 * not modify expr.anchorTokens or expr.anchorTokCol.  The renormalize      *
 * method should be called after adding a sequence of tokens (such as by    *
 * substituting an expression for a token) to adjust the anchorTokens and   *
 * anchorTokCol fields before any more tokens are added to the expression.  *
 *                                                                          *
 * Here are the methods.                                                    *
 *                                                                          *
 *    addToken(tok) : Adds the TLAToken tok to the end of the last line.    *
 *                    Note that tok.column must have the proper value       *
 *                    for the expression produced by the method to be       *
 *                    sensible.                                             *
 *                                                                          *
 *    addTokenOffset(tok, offset) :                                         *
 *                    Adds the TLAToken tok to the end of the last line,    *
 *                    setting tok's column so the token appears offset      *
 *                    characters to the right of the last token on the      *
 *                    line.  (Added 30 Aug 2007.)                           *
 *                                                                          *
 *    addLine()     : Adds an empty line to the end.  (Must be called       *
 *                    before the first call of addToken.)                   *
 *                                                                          *
 *    normalize()   : Removes empty lines at the end of the expression      *
 *                    and computes anchorTokens and anchorTokCol as         *
 *                    explained above.                                      *
 *                                                                          *
 *    renormalize() : Recomputes anchorTokens and anchorTokCol as           *
 *                    explained above.                                      *
 *                                                                          *
 *    toStringVector() :                                                    *
 *      Equals a ArrayList of strings, each being the ASCII representation     *
 *      of the corresponding line of expr.  If expr.anchorTokens[i] is      *
 *      non-null, then an extra                                             *
 *                                                                          *
 *         (expr.anchorTokens[i]).column - expr.anchorTokCol[i]             *
 *                                                                          *
 *      spaces are added to the beginning of line i to maintain the         *
 *      original indentation.                                               *
 *                                                                          *
 *    toString() :                                                          *
 *       This converts an expr into a string that is its TLA+               *
 *       representation in the AST module.  It is used for                  *
 *       the -spec option, and for debugging.                               *
 *                                                                          *
 *    cloneAndNormalize() :                                                 *
 *       Used to create a clone of the current expression.                  *
 *                                                                          *
 *    prepend(expr, spaces) :                                               *
 *       Prepends the expression expr to the current expression,            *
 *       leaving `spaces' spaces between the end of expr and the            *
 *       first token of the original expression.                            *
 *                                                                          *
 *    substituteForAll(exprs, strs, parenthesize) :                         *
 *       Substitutes the expressions in the vector exprs of TLAExpr         *
 *       objects for the identifiers in the vector strs of strings.         *
 *       If parenthesize = true, then put parentheses around the            *
 *       substituted expression unless it or the current expression         *
 *       consists of just one token.                                        *
 *                                                                          *
 *    substituteForAll(exprs, strs) :                                       *
 *       Same as substituteForAll(exprs, strs, true).  (Kept for            *
 *       compatibility after the third argument was added.)                 *
 *                                                                          *
 *    SeqSubstituteForAll(expVec, exprs, strs) :                            *
 *       A vector of expressions obtained from the vector expVec of         *
 *       expressions by cloning each of them and then                       *
 *       substituting the expressions in the vector exprs of TLAExpr        *
 *       objects for the identifiers in the vector strs of strings.         *
 *                                                                          *
 * There are quite a few other methods used to implement these that might   *
 * be of use for manipulating expressions.  Search below for "SUBSTITUTING  *
 * IN EXPRESSIONS" to find them.                                            *
 ***************************************************************************/
package pcal;

import pcal.exception.TLAExprException;
import tla2tex.Debug;

import java.util.ArrayList;
import java.util.Objects;

public class TLAExpr {

    /**
     * A TLAExpr object represents a TLA+ expression.  The tokens vector is
     * a vector of vectors of TLAToken objects.  Each
     * subvector contains the tokens in one line of the expression.
     */
    public ArrayList<ArrayList<TLAToken>> tokens = new ArrayList<>(4);
    public TLAToken[] anchorTokens = null;
    public int[] anchorTokCol = null;

    /**
     * If this object represents an expression in the PCal code, then
     * origin is the region from the beginning of the first token to the
     * end of the last token.
     * <p>
     * If this object is an expression substituted for a token, then
     * origin is the region is the source region of that token.
     */
    private Region origin = null;

    TLAExpr()
    /*********************************************************************
     * A constructor for an empty object of class TLAExpr.                *
     *********************************************************************/
    {
    }

    TLAExpr(final ArrayList<ArrayList<TLAToken>> t)
    /*********************************************************************
     * A constructur that builds a new, unnormalized TLAExpr with a       *
     * given tokens ArrayList.                                               *
     *********************************************************************/
    {
        tokens = t;
        anchorTokens = null;
        anchorTokCol = null;
    }

    public static ArrayList<TLAExpr> SeqSubstituteForAll(final ArrayList<TLAExpr> expVec, // of TLAExpr
                                                         final ArrayList<TLAExpr> exprs,  // of TLAExpr
                                                         final ArrayList<String> strs) throws TLAExprException   // of String
    /*********************************************************************
     * Produces a vector of new expressions obtained by cloning each      *
     * expression in expVec and then applying substituteForAll(exprs,     *
     * strs) to the clone.                                                *
     *********************************************************************/
    {
        final ArrayList<TLAExpr> result = new ArrayList<>();
        int i = 0;
        while (i < expVec.size()) {
            final TLAExpr e = expVec.get(i).cloneAndNormalize();
            e.substituteForAll(exprs, strs);
            result.add(e);
            i = i + 1;
        }
        return result;
    }

    /***************** private and debugging methods *********************/

    private static String SpacesString(final int n)
    /***********************************************************************
     * A string of n spaces.                                                *
     ***********************************************************************/
    {
        int i = 0;
        final StringBuilder result = new StringBuilder();
        if (i < 0) {
            PcalDebug.ReportBug(
                    "SpacesString called with negative argument");
        }
        while (i < n) {
            result.append(" ");
            i = i + 1;
        }
        return result.toString();
    }

    public Region getOrigin() {
        return origin;
    }

    public void setOrigin(final Region origin) {
        this.origin = origin;
    }

    public void addToken(final TLAToken tok) {
        tokens.get(tokens.size() - 1).add(tok);
    }

    /***********************************************************************
     * The addTokenOffset method was added by LL on 30 Aug 2007 to fix the  *
     * following bug.  When a prime or "[self]" is appended to a variable   *
     * v, the sustituteForAll() method is called to replace the token "v"   *
     * with an expression consisting of a line having the sequence of       *
     * tokens                                                               *
     *                                                                      *
     *    "v"  "'"   or   "v" "[" "self" "]"                                *
     *                                                                      *
     * However, every token in this expression had column 0, which caused   *
     * the renormalize() method to mess up alignment and even halt with     *
     * the error                                                            *
     *                                                                      *
     *   "TLAExpr.renormalize() found anchor has moved to left."            *
     *                                                                      *
     * To fix this, the calls in PcalTLAGen.java to addToken() that were    *
     * used to create the new expression were replaced by calls to          *
     * addTokenOffset.                                                      *
     ***********************************************************************/
    public void addTokenOffset(final TLAToken tok, final int offset) {
        final ArrayList<TLAToken> lastLine = tokens.get(tokens.size() - 1);
        int newCol = offset;
        if (lastLine.size() > 0) {
            final TLAToken lastTok =
                    lastLine.get(lastLine.size() - 1);
            newCol = newCol + lastTok.column + lastTok.string.length();
        }
        tok.column = newCol;
        lastLine.add(tok);
    }

    public void addLine() { /*******************************************************************
     * The new line is set to an empty vector.                          *
     *******************************************************************/
        tokens.add(new ArrayList<>());
    }

    public void normalize() { /*******************************************************************
     * Remove empty lines at beginning and end of tokens.               *
     *******************************************************************/
        while ((tokens.size() > 0)
                /********************************************************
                 * I don't think we should ever get an empty             *
                 * expression, but we'll check just in case.             *
                 ********************************************************/
                && (tokens.get(0).size() == 0)
        ) {
            tokens.remove(0);
        }

        while ((tokens.size() > 0)
                /********************************************************
                 * I don't think we should ever get an empty             *
                 * expression, but we'll check just in case.             *
                 ********************************************************/
                && (tokens.get(tokens.size() - 1).size() == 0)
        ) {
            tokens.remove(tokens.size() - 1);
        }

        /*******************************************************************
         * Set minCol to minimum column number.                             *
         *******************************************************************/
        int minCol = 999999;
        int i = 0;

        while (i < tokens.size()) {
            if (tokens.get(i).size() > 0) {
                final TLAToken tok =
                        tokens.get(i).get(0);
                if (tok.column < minCol) {
                    minCol = tok.column;
                }
            }
            i = i + 1;
        }

        /*******************************************************************
         * Subtract minCol from tok.column for all tokens tok.              *
         *******************************************************************/
        i = 0;
        while (i < tokens.size()) {
            int j = 0;
            final ArrayList<TLAToken> curLine = tokens.get(i);
            while (j < curLine.size()) {
                final TLAToken tok = curLine.get(j);
                tok.column = tok.column - minCol;
                j = j + 1;
            }
            i = i + 1;
        }

        /*******************************************************************
         * Compute anchorTokens and anchorTokCol.                           *
         *                                                                  *
         * Loop with index i through all lines.                             *
         *******************************************************************/
        anchorTokens = new TLAToken[tokens.size()];
        anchorTokCol = new int[tokens.size()];
        i = 0;
        while (i < tokens.size()) {
            final ArrayList<TLAToken> curLine = tokens.get(i);
            if (curLine.size() > 0) {
                final int curLineFirstCol =
                        curLine.get(0).column;
                /***********************************************************
                 * Loop backwards with loop index j through lines (i-1) ->  *
                 * 0, exiting when anchor line found.                       *
                 ***********************************************************/
                int j = i - 1;
                boolean lineNotFound = true;
                while ((j >= 0) && lineNotFound) {
                    final ArrayList<TLAToken> ancLine = tokens.get(j);
                    if ((ancLine.size() > 0)
                            && (ancLine.get(0).column
                            <= curLineFirstCol
                    )) { /***************************************************
                     * This line contains the anchor token.             *
                     ***************************************************/
                        lineNotFound = false;

                        /***************************************************
                         * Loop indexed by k starting at 1 through tokens   *
                         * on ancLine until reaching end or a token to the  *
                         * right of curLineFirstCol.                        *
                         ***************************************************/
                        int k = 0;
                        while ((k + 1 < ancLine.size())
                                && (ancLine.get(k + 1).column
                                <= curLineFirstCol)
                        ) {
                            k = k + 1;
                        }

                        final TLAToken tok = ancLine.get(k);
                        anchorTokens[i] = tok;
                        anchorTokCol[i] = tok.column;
                    }//END if
                    j = j - 1;
                }//END while j
            }
            i = i + 1;
        }//END while i
    } //END normalize

    public void renormalize() throws TLAExprException
    /*********************************************************************
     * Used to renormalize the expression so anchorTokCol[i] equals the   *
     * actual column of the anchorTokens[i].  It should be called every   *
     * time new tokens have been inserted into the expression.            *
     *                                                                    *
     * This is done as follows.  For each i from 0 to the maximum line    *
     * number, if the anchor token of line i has moved k tokens to the    *
     * right, then anchorTokCol[i] and the columns of every token in      *
     * line i are incremented by k.                                       *
     *********************************************************************/
    {
        int i = 0;
        while (i < tokens.size()) {
            if (anchorTokens[i] != null) {
                final ArrayList<TLAToken> line = tokens.get(i);
                final int k = anchorTokens[i].column - anchorTokCol[i];
                anchorTokCol[i] = anchorTokens[i].column;
                if (k < 0) {
                    throw new TLAExprException(
                            "TLAExpr.renormalize() found anchor has moved to left.");
                }
                int j = 0;
                while (j < line.size()) {
                    final TLAToken tok = line.get(j);
                    tok.column = tok.column + k;
                    j = j + 1;
                }
            }
            i = i + 1;
        }
    }

    public ArrayList<String> toStringVector() {
        final ArrayList<String> result = new ArrayList<>(tokens.size());
        int i = 0;
        while (i < tokens.size()) {
            final ArrayList<TLAToken> curTokLine = tokens.get(i);
            StringBuilder curString = new StringBuilder();
            final TLAToken curAncTok = anchorTokens[i];
            final int curAncCol = anchorTokCol[i];
            if (curAncTok != null) {
                curString = new StringBuilder(SpacesString(curAncTok.column - curAncCol));
            }

            TLAToken curTok;
            TLAToken lastTok = null;
            int j = 0;
            while (j < curTokLine.size()) {
                curTok = curTokLine.get(j);
                if (j == 0) {
                    curString.append(SpacesString(curTok.column));
                } else {
                    curString.append(SpacesString(curTok.column - lastTok.column
                            - lastTok.getWidth()));
                }
                /***********************************************************
                 * Need to add the quotes for a string token.               *
                 ***********************************************************/
                if (curTok.type == TLAToken.STRING) {
                    curString.append("\"").append(curTok.string).append("\"");
                } else {
                    curString.append(curTok.string);
                }
                lastTok = curTok;
                j = j + 1;
            }
            result.add(curString.toString());
            i = i + 1;
        }
        return result;
    }

    /**
     * Returns a ArrayList of Vectors of {@link MappingObject} objects, which
     * represents the TLA+ to PlusCal mapping for the expression as if that
     * expression were the complete spec.  That is, the returned value contains
     * the same number of lines as the expression has, and the columns of
     * Begin/EndTlaToken and SourceToken objects are obtained directly from
     * the columns of the tokens.  The returned value does NOT contain LeftParen
     * and RightParen MappingObjects enclosing the entire expression.
     */
    public ArrayList<ArrayList<MappingObject>> toMappingVector() {
        final ArrayList<ArrayList<MappingObject>> result = new ArrayList<>(4);
        for (ArrayList<TLAToken> token : this.tokens) {
            final ArrayList<MappingObject> mapLine = new ArrayList<>();
            final ArrayList<TLAToken> expLine = token;
            MappingObject.SourceToken sourceTok = null;
            for (final TLAToken tok : expLine) {
                final int tokEndCol = tok.column + tok.string.length();
                for (int k = 0; k < tok.getBeginSubst().size(); k++) {
                    mapLine.add(new MappingObject.LeftParen(
                            tok.getBeginSubst().get(k)));
                }
                if (tok.source == null) {
                    if (sourceTok == null || !tok.isAppended()) {
                        mapLine.add(new MappingObject.BeginTLAToken(tok.column));
                        mapLine.add(
                                new MappingObject.EndTLAToken(tokEndCol));
                        sourceTok = null;
                    } else {
                        /* {
                         *
                         * Make this TLA token part of sourceTok
                         */
                        sourceTok.setEndColumn(tokEndCol);
                    }
                } else {

                    sourceTok = new MappingObject.SourceToken(
                            tok.column, tokEndCol, tok.source);
                    mapLine.add(sourceTok);
                }
                for (int k = tok.getEndSubst().size() - 1; k >= 0; k--) {
                    mapLine.add(new MappingObject.RightParen(
                            tok.getEndSubst().get(k)));
                }
            }
            result.add(mapLine);
        }
        return result;
    }

    public String toString() {
        final StringBuilder result = new StringBuilder("<< ");
        int i = 0;
        boolean nonempty = false;
        while (i < tokens.size()) {
            if (i > 0) {
                result.append("\n");
            }
            final ArrayList<TLAToken> curLine = tokens.get(i);
            int j = 0;
            while (j < curLine.size()) {
                if (nonempty) {
                    result.append(", ");
                }
                nonempty = true;
                final TLAToken tok = curLine.get(j);

                if (tok.type == TLAToken.STRING) {
                    result.append("\"\\\"\", \"").append(tok.string).append("\", \"\\\"\"");
                }
//               else if (tok.type == TLAToken.BEGIN_REPLACEMENT) {
//            	   result = result + "(map" ;
//               }
//               else if (tok.type == TLAToken.END_REPLACEMENT) {
//            	   result = result + "map)" ;
//               }
                else if (tok.string.equals("\\/")) {
                    result.append(String.format("\"(col%s) \\\\/\"", tok.column));
                } else if (tok.string.charAt(0) == '\\') {
                    result.append("\"\\").append(tok.string).append("\"");
                } else if (tok.string.equals("/\\")) {
                    result.append(String.format("\"(col%s) /\\\\\"", tok.column));
                } else {
                    result.append("\"").append(tok.string).append("\"");
                }
                j = j + 1;
            }
            i = i + 1;
        }
        return result + " >>";
    }

    /*
     * The following method does not seem to be called from anywhere, so LL
     * deleted it on 6 Dec 2011.
     */

    /***************************************************************************
     *        METHODS FOR SEARCHING AND SUBSTITUTING IN EXPRESSIONS             *
     *                                                                          *
     * The tokens field of a TLAExpr is a vector of lines, where a line is a    *
     * vector of tokens.  The "Java coordinates" of a token in the expression   *
     * is a pair (ln, itm) such that the token is item number itm in line       *
     * number ln, where the numbering of lines and items starts at 0.  Note     *
     * that the first token of an expression always has coordinates (0, 0).     *
     * Java coordinates are passed as arguments and returned as values as       *
     * IntPair objects.                                                         *
     ***************************************************************************/
    public TLAExpr cloneAndNormalize()
    /*********************************************************************
     * Creates a clone of the current TLAExpr by cloning all the tokens   *
     * and then calling normalize to compute anchorTokens and             *
     * anchorTokCol.   Sets the origin region of the clone to that of the *
     * original.                                                          *
     *********************************************************************/
    {
        final TLAExpr result = new TLAExpr();
        result.tokens = new ArrayList<>();
        int i = 0;
        while (i < this.tokens.size()) {
            final ArrayList<TLAToken> newline = new ArrayList<>();
            final ArrayList<TLAToken> line = this.tokens.get(i);
            int j = 0;
            while (j < line.size()) {
                newline.add(line.get(j).Clone());
                j = j + 1;
            }
            result.tokens.add(newline);
            i = i + 1;
        }
        result.setOrigin(this.getOrigin());
        result.normalize();
        return result;
    }

    public void prepend(final TLAExpr expr, final int spaces) throws TLAExprException
    /*********************************************************************
     * Prepends the expression expr to the front of the current           *
     * expression, leaving `spaces' number of spaces between the last     *
     * token of expr and the first token of the current expression.       *
     *********************************************************************/
    { /*******************************************************************
     * Prepend all but the last line of expr to the current expression. *
     *******************************************************************/
        int i = 0;
        while (i < expr.tokens.size() - 1) {
            this.tokens.add(i, expr.tokens.get(i));
            i = i + 1;
        }
        /*******************************************************************
         * Set exprLine to the last line of expr and thisLine to what was   *
         * the first line of the current expression.                        *
         *******************************************************************/
        final ArrayList<TLAToken> exprLine = expr.tokens.get(i);
        final ArrayList<TLAToken> thisLine = this.tokens.get(i);

        /*******************************************************************
         * Increment the columns of the tokens in thisLine.                 *
         *******************************************************************/
        // Last element
        TLAToken tok = exprLine.get(exprLine.size() - 1);
        final int incr = tok.column + tok.getWidth() + spaces;
        int j = 0;
        while (j < thisLine.size()) {
            tok = thisLine.get(j);
            tok.column = tok.column + incr;
            j = j + 1;
        }

        /*******************************************************************
         * Prepend the last line of expr to the first line of this          *
         * expression.                                                      *
         *******************************************************************/
        j = 0;
        while (j < exprLine.size()) {
            thisLine.add(j, exprLine.get(j));
            j = j + 1;
        }

        /*******************************************************************
         * Modify anchorTokens and anchorTokCol.                            *
         *******************************************************************/
        final TLAToken[] newAToks = new TLAToken[this.tokens.size()];
        final int[] newATCol = new int[this.tokens.size()];

        j = 0;
        while (j < expr.tokens.size()) {
            newAToks[j] = expr.anchorTokens[j];
            newATCol[j] = expr.anchorTokCol[j];
            j = j + 1;
        }

        while (j < this.tokens.size()) {
            newAToks[j] = this.anchorTokens[j - expr.tokens.size() + 1];
            newATCol[j] = this.anchorTokCol[j - expr.tokens.size() + 1];
            j = j + 1;
        }
        this.anchorTokens = newAToks;
        this.anchorTokCol = newATCol;

        this.renormalize();
    }

    /**
     * Substitutes clones of the expressions in exprs for the corresponding
     * strings of strs in the current expression.
     * <p>
     * This is called with parenthesize = true only during the initial parsing
     * phase (the execution of ParseAlgorithm.getAlgorithm).  It is called with
     * parenthesize = false by:
     * <p>
     * PcalFixIDs.FixExpr : replaces the string of an IDENT token with a
     * new one to perform renaming in case of name conflicts.
     * <p>
     * PcalTLAGen.AddSubscriptsToExpr: adds the primes and "[self]" subscripts
     * to variables when needed.
     * <p>
     * This method was modified by LL on 10 August 2012 to do the substitutions
     * "simultaneously" rather than one after the other.  The original code
     * first did all the substitutions for the first string, then all the
     * substitutions for the second string, etc.  This yielded a bug if the
     * expression substituted for the first string contained the second
     * string.  For example, the substitutions
     * <p>
     * a <- F(b), b <- c
     * <p>
     * in  a + b  produced  F(c) + c  instead of the correct  F(b) + c .
     *
     * @param exprs A vector of TLAExpr objects
     * @param strs  A vector of strings
     */
    public void substituteForAll(final ArrayList<TLAExpr> exprs, // of TLAExpr
                                 final ArrayList<String> strs    // of String
    ) throws TLAExprException {
        substituteForAll(exprs, strs, true);
    }

    /**
     *
     */
    public void substituteForAll(final ArrayList<TLAExpr> exprs, // of TLAExpr
                                 final ArrayList<String> strs,  // of String
                                 final boolean parenthesize
    ) throws TLAExprException {
        final TLAExpr[] expArray = new TLAExpr[exprs.size()];
        final String[] strArray = new String[strs.size()];
        final IntPair[] nextArray = new IntPair[expArray.length];

        // Set expArray and strArray to array versions of exprs and strs.
        // Initialize nextArray with the  positions of the first
        // instances of all the strings in strs.
        for (int i = 0; i < nextArray.length; i++) {
            expArray[i] = exprs.get(i);
            strArray[i] = strs.get(i);
            nextArray[i] = findNextInstanceIn(strArray[i], new IntPair(0, 0));
        }

        boolean notDone = true;
        while (notDone) {
            IntPair nextPos = null;
            int nextIdx = -1;

            // Set nextPos to the smallest non-null IntPair in nextArray, and
            // nextIdx to its index in nextArray.  The value of nextPos
            // is set to null if all the elements of nextArray are null;
            for (int i = 0; i < nextArray.length; i++) {
                final IntPair pos = nextArray[i];
                if (pos != null) {
                    if (nextPos == null) {
                        nextPos = pos;
                        nextIdx = i;
                    } else if ((pos.one < nextPos.one)
                            || ((pos.one == nextPos.one)
                            && (pos.two < nextPos.two))) {
                        nextPos = pos;
                        nextIdx = i;
                    }
                }
            }

            if (nextPos == null) {
                notDone = false;
            } else {
                final IntPair afterNextPos = stepCoord(nextPos, 1);
                // This is the next token after nextPos, which will

                final IntPair newPos = substituteAt(expArray[nextIdx], nextPos, parenthesize);


                nextArray[nextIdx] = (newPos == null) ?
                        null :
                        findNextInstanceIn(strArray[nextIdx], newPos);

                // The values of nextArray[i] for all i # nextIdx need to be adjusted
                // if the substitution replaced parameter number nextIdx by an
                // expression consisting of more than a single token-- which is the
                // case iff newPos # afterNextPos.  We now move those positions
                // accordingly.  Note that if newPos is null, then there are no tokens
                // in any position after the replaced token, so nextArray[i] should
                // be null for all i.
                for (int i = 0; i < nextArray.length; i++) {
                    if ((i != nextIdx) && (nextArray[i] != null)) {
                        Debug.Assert(newPos != null, "Doing substitutions in wrong order.");

                        if (afterNextPos.one == Objects.requireNonNull(newPos).one) {
                            // The substituted expression occupies a single line.
                            // Must move nextArray[i] to the right iff it is on the
                            // same line as nextPos
                            if (nextArray[i].one == nextPos.one) {
                                nextArray[i].two = nextArray[i].two + (newPos.two - afterNextPos.two);
                                Debug.Assert(nextArray[i].two > nextPos.two, "Wrong substitution order.");
                            }
                        } else {
                            // The substituted expression occupies more than one line.  We have
                            // to increment the line number, but do it separately in the
                            // following two cases.
                            //
                            // Have to change nextArray[i] iff it was pointing at the same line as nextPos
                            if (nextArray[i].one == nextPos.one) {
                                nextArray[i].one = nextArray[i].one + (newPos.one - afterNextPos.one);
                                Debug.Assert(nextArray[i].two > nextPos.two, "Wrong substitution order.");
                                nextArray[i].two = nextArray[i].two + (newPos.two - afterNextPos.two);
                                // Note: nextArray[i] comes after nextPos implies that, since they
                                // are on the same line, nextArray[i].two should be >= afterNextPos.two,
                                // so this sets nextArray[i].two to a non-negative number
                            } else {
                                nextArray[i].one = nextArray[i].one + (newPos.one - afterNextPos.one);
                            }
                        }
                    }
                }
            }
        }
    }

    public void substituteFor(final TLAExpr expr, final String id, final boolean parenthesize) throws TLAExprException
    /*********************************************************************
     * Substitutes expression expr for all tokens in the current          *
     * expression representing the identifier id -- that is, instances    *
     * in which id does not represent the name of a record field.         *
     * If parenthesize = true, then parentheses are put around the        *
     * substituted string unless it or the current expression consists    *
     * of just one token.                                                 *
     *********************************************************************/
    {
        IntPair next = new IntPair(0, 0);
        while (next != null) {
            next = this.findNextInstanceIn(id, next);
            if (next != null) {
                next = this.substituteAt(expr, next, parenthesize);
            }
        }
    }

    public IntPair substituteAt(final TLAExpr expr, final IntPair coord, final boolean par) throws TLAExprException
    /*********************************************************************
     * Replaces the token tok with coordinates coord in the current       *
     * expression with the expression expr (adding parentheses when       *
     * needed if par = true), and return the coordinates of the token     *
     * immediately past the substituted expression (or null if the        *
     * substitution was for the last token).  The trick is to do this is  *
     * a way that preserves the alignment information.  In particular,    *
     * we have to be concerned with the possibility that token tok might  *
     * be an anchor token.  If the current expression consists of a       *
     * single token, then we just replace its fields the fields obtained  *
     * by cloning expr.  Otherwise, there are two cases.                  *
     *                                                                    *
     * Case 1: expr consists of a single token etok.                      *
     *    In this case, the `string' and `type' fields of tok are         *
     *    set to the corresponding fields of etok, and the                *
     *    remainder tokens on the current line are shifted                *
     *    to the right if the new string has more characters than the     *
     *    original.                                                       *
     *                                                                    *
     * Case 2: expr consists of multiple tokens.                          *
     *    In this case, tok is changed to "(", and copies of the tokens   *
     *    of expr followed by a ")" token are inserted into the current   *
     *    expression, creating one new line for every line of expr other  *
     *    than the first.  The column of each token from expr is          *
     *    incremented by 1 plus the column number of tok.  The tokens     *
     *    from the current expression that follow on the same line as the *
     *    last line of the newly inserted tokens are incremented by the   *
     *    appropriate amount to shift them to the right of the inserted   *
     *    tokens.                                                         *
     *                                                                    *
     *    Note: if you want to change this method so it doesn't always    *
     *    put parentheses around multi-token expressions, then see the    *
     *    comments preceding TLAToken.beginSubst before doing anything.   *
     *********************************************************************/
    { /*******************************************************************
     * First handle of the case when current expression has a single    *
     * token.                                                           *
     *******************************************************************/
        /*
         * Note that in this case, the origin field of this TLAExpr object
         * should be unchanged.
         */
        final TLAToken tok = this.tokenAt(coord);
        final Region tokSource = tok.source;
        if (this.isOneToken()) {
            final TLAExpr cloned = expr.cloneAndNormalize();
            if (tokSource != null) {
                cloned.firstToken().getBeginSubst().addAll(tok.getBeginSubst());
                cloned.firstToken().getBeginSubst().add(tokSource.getBegin());
                cloned.lastToken().getEndSubst().addAll(tok.getEndSubst());
                cloned.lastToken().getEndSubst().add(tokSource.getEnd());
            }
            this.tokens = cloned.tokens;
            this.anchorTokens = cloned.anchorTokens;
            this.anchorTokCol = cloned.anchorTokCol;

// The approach of adding dummy tokens to an expression to indicate
// substitution produced an error when normalizing the expression.  Rather
// than risking any further bugs appearing because of it, I'm backing out
// of that and doing something else that cannot make any changes to the
// existing translation.

            return null;
        }

        /*******************************************************************
         * Set                                                              *
         *                                                                  *
         *    tok = the token being substituted for,                        *
         *    spaces = number of spaces between tok and token to its right, *
         *             or 0 if tok at end of line.                          *
         *    restOfLine = a vector of the tokens to the right of tok,      *
         *                                                                  *
         * and delete tokens to right of tok from expr.                     *
         *******************************************************************/
        final ArrayList<TLAToken> tokLine = this.tokens.get(coord.one);
        int spaces = 0;
        if (coord.two + 1 < tokLine.size()) {
            final TLAToken nextTok = tokLine.get(coord.two + 1);
            spaces = nextTok.column - (tok.column + tok.getWidth());
        }
        final ArrayList<TLAToken> restOfLine = new ArrayList<>();

        while (coord.two + 1 < tokLine.size()) {
            restOfLine.add(tokLine.get(coord.two + 1));
            tokLine.remove(coord.two + 1);
        }

        /*******************************************************************
         * curLine will be set to the line number and line to the line at   *
         * the end of which the tokens in restOfLine will be appended.      *
         *******************************************************************/
        int curLine = coord.one;
        ArrayList<TLAToken> line = this.tokens.get(curLine);
        /*******************************************************************
         * Insert the new tokens into the expression.                       *
         *******************************************************************/
        if ((expr.tokens.size() == 1)
                && ((expr.tokens.get(0)).size() == 1)
        ) { /***************************************************************
         * There is a single token etok.                                *
         ***************************************************************/
            final TLAToken etok =
                    (expr.tokens.get(0)).get(0);
            tok.string = etok.string;
            tok.type = etok.type;
            tok.source = etok.source;
            /*
             * Set tok.begin/endSubst to the sequence
             *
             *   tok.begin/EndSubst \o << tok.source.begin/end >>
             *      \o etok.begin/EndSubst
             */
            if (tokSource != null) {
                tok.getBeginSubst().add(tokSource.getBegin());
                tok.getEndSubst().add(tokSource.getEnd());
            }
            tok.getBeginSubst().addAll(etok.getBeginSubst());
            tok.getEndSubst().addAll(etok.getEndSubst());
        } else { /***************************************************************
         * Replace tok by "(" token if par = true, and set indent to    *
         * the amount to indent the first line of inserted tokens.      *
         ***************************************************************/
            int indent = ((par) ? 1 : 0) + tok.column;

            /***************************************************************
             * Set doInsert to true iff the token being substituted for     *
             * must be replaced with the first token of the expression,     *
             * otherwise set it to false and substitute a "(" for it.       *
             ***************************************************************/
            boolean doInsert = true;
            if (par) {
                /*
                 * Turn tok into a new "(" token.  Must reset its
                 * source, beginSubst, and endSubst fields, and add its
                 * original source begin/end to the begin/endSubst vectors
                 * if it's not null.
                 */
                tok.string = "(";
                tok.type = TLAToken.BUILTIN;
                doInsert = false;
                tok.source = null;
                /*
                 * Append tokSource to tok.beginSubst.
                 * We need to set tok.endSubst to << >>, but we
                 * do that when we add the ")" token, because we
                 * need to set its endSubst to tok.endSubst \o tokSource.
                 */
                if (tokSource != null) {
                    tok.getBeginSubst().add(tokSource.getBegin());
                }
            }
            int i = 0;
            final TLAExpr newExpr = expr.cloneAndNormalize();
            /**
             * If we're not going to insert a parenthesis and tok has a source,
             * then add its beginning to the first token's beginSubst vector and
             * its end to the last token's endSubst vector.
             */
            if ((!par) && (tokSource != null)) {
                newExpr.firstToken().getBeginSubst().add(tokSource.getBegin());
                newExpr.lastToken().getEndSubst().add(tokSource.getEnd());
            }
            while (i < newExpr.tokens.size()) {
                final ArrayList<TLAToken> eline = newExpr.tokens.get(i);
                int j = 0;
                while (j < eline.size()) {
                    final TLAToken nextTok =
                            eline.get(j);
                    nextTok.column = nextTok.column + indent;
                    if (doInsert) {
                        tok.string = nextTok.string;
                        tok.type = nextTok.type;

                        /*
                         * We need to merge the begin/end subst information of tok
                         * with that of the substituted expression newExpr.  The
                         * parens represented by the substitution information of newExpr
                         * should go inside those represented by the substitution
                         * information of tok.  The left parens represented by
                         * the beginSubst entries of a token go in the same order as
                         * in the beginSubst vector, and the inverse is true of right parens.
                         * Hence, the beginSubst entries of the first token of newExpr
                         * should go after those of tok, and the endSubst entries
                         * of tok should go after those of the last token of newExpr.
                         *
                         * We also have to set tok.endSubst to nextTok.endSubst
                         * so we don't lose those substitutions.
                         */
                        tok.getBeginSubst().addAll(nextTok.getBeginSubst());
                        newExpr.lastToken().getEndSubst().addAll(tok.getEndSubst());
                        tok.setEndSubst(nextTok.getEndSubst());

                        doInsert = false;
                    } else line.add(nextTok);
                    j = j + 1;
                }
                i = i + 1;
                if (i < newExpr.tokens.size()) { /*******************************************************
                 * Increment curLine, insert a new empty line into      *
                 * expr at this position, insert                        *
                 * newExpr.anchorTokens[curLine] into                   *
                 * this.anchorTokens as item i, and similarly for       *
                 * anchorTokCol.                                        *
                 *******************************************************/
                    indent = 0;
                    curLine = curLine + 1;
                    this.tokens.add(curLine, new ArrayList<>());
                    line = this.tokens.get(curLine);
                    final TLAToken[] aTok = new TLAToken[this.tokens.size()];
                    final int[] aTCol = new int[this.tokens.size()];
                    int k = 0;
                    while (k < this.tokens.size()) {
                        if (k < curLine) {
                            aTok[k] = this.anchorTokens[k];
                            aTCol[k] = this.anchorTokCol[k];
                        } else if (k == curLine) {
                            aTok[k] = newExpr.anchorTokens[i];
                            aTCol[k] = newExpr.anchorTokCol[i];
                        } else {
                            aTok[k] = this.anchorTokens[k - 1];
                            aTCol[k] = this.anchorTokCol[k - 1];
                        }
                        k = k + 1;
                    }
                    this.anchorTokens = aTok;
                    this.anchorTokCol = aTCol;
                }
            }
            final TLAToken lastTok = line.get(line.size() - 1);
            if (par) {
                /**
                 * Create the new ")" token, and add if the replaced token's
                 * source is not null, then add its right endpoint location to
                 * the ")" token's endSubst vector.
                 */
                final TLAToken rParen =
                        new TLAToken(")",
                                lastTok.column + lastTok.getWidth(),
                                TLAToken.BUILTIN);
                rParen.setEndSubst(tok.getEndSubst());
                if (tokSource != null) {
                    rParen.getEndSubst().add(tokSource.getEnd());
                }
                /*
                 * Can now reset tok.endSubst.
                 */
                tok.setEndSubst(new ArrayList<>(2));
                line.add(rParen);
            }

// Removing the replacement tokens because putting them in was apparently
// not a safe thing to do.
            /*
             * Add the BEGIN_ and END_REPLACEMENT tokens to the expression,
             * first adding the END_REPLACEMENT.
             *
             * Note: the REPLACEMENT tokens are simply stuck into the
             * expression rather than inserted by calling insertNewToken.
             * I think this is safe to do for a zero-width token.
             */
        }

        final IntPair result = new IntPair(curLine, line.size() - 1);
        /*******************************************************************
         * Put the tokens from restOfLine back into the expression.         *
         *******************************************************************/
        if (restOfLine.size() > 0) {
            final TLAToken prevTok = line.get(line.size() - 1);
            final TLAToken firstTok = restOfLine.get(0);
            final int indent = prevTok.column + prevTok.getWidth()
                    + spaces - firstTok.column;
            int i = 0;
            while (i < restOfLine.size()) {
                final TLAToken oldTok = restOfLine.get(i);
// Correction made 25 Aug 2005.
// For some reason I no longer understand, I was replacing the original
// tokens with new ones.  This was wrong because any anchorToken that
// pointed to one of those tokens was now pointing to the wrong
// TLAToken object.  Here's the bad code:
                oldTok.column = oldTok.column + indent;
                line.add(oldTok);
                i = i + 1;
            }
        }
        this.renormalize();
        return this.stepCoord(result, 1);
    }

    public IntPair findNextInstanceIn(final String id,
                                      final IntPair start)
    /*********************************************************************
     * If expr is a TLAExpr, then expr.findNextInstanceIn(id, start)      *
     * returns the Java coordinates of the first token with Java          *
     * coordinates at or after "start" with string id that represents an  *
     * identifier.  It ignores tokens with string id that represent       *
     * record labels.  However, in certain exceptional cases, it will     *
     * ignore an instance that binds the identifier id in a quantified    *
     * expression--for example, in the expression "\E x, id : ...".       *
     * This method should therefore not be used in the case when id       *
     * could legally be a bound identifier of a quantified expression.    *
     *                                                                    *
     * The search is performed as if the first token of the expression    *
     * were the one with Java coordinates `start'.  This means that the   *
     * method will mistakenly return `start' if it is the Java            *
     * coordinates of a record label.  For example, if the method is      *
     * invoked for the expression "[id |-> 17]" with `start' equal to     *
     * the coordinates of the token id, then the method will return       *
     * `start', even though id does not represent an identifier in the    *
     * whole expression.                                                  *
     *                                                                    *
     * The method regards an id to be a record label iff it appears in    *
     * the following contexts:                                            *
     *                                                                    *
     *    . id                                                            *
     *    [ id :                                                          *
     *    , id :                                                          *
     *    [ id |->                                                        *
     *    , id :                                                          *
     *                                                                    *
     * I believe this works except that it misidentifies id as a record   *
     * label when it appears as a bound identifier in an unbounded        *
     * quantifier expression such as                                      *
     *                                                                    *
     *    \E x, id : ...                                                  *
     *********************************************************************/
    {
        IntPair result = new IntPair(start.one, start.two);
        if (this.isEmpty()) {
            result = null;
        }
        while (result != null) {
            final TLAToken tok = this.tokenAt(result);
            if (tok.type == TLAToken.STRING) {
                result = this.stepCoord(result, 1);
            } else if (tok.string.equals(".")) {
                result = this.stepCoord(result, 2);
            } else if ((tok.string.equals("[")
                    || tok.string.equals(",")
            )
                    && (this.stepCoord(result, 2) != null)
                    && (this.tokenAt(this.stepCoord
                    (result, 2)).type != TLAToken.STRING)
                    && (this.tokenAt(this.stepCoord
                    (result, 2)).string.equals(":")
                    || this.tokenAt(this.stepCoord
                    (result, 2)).string.equals("|->")
            )
            ) {
                result = this.stepCoord(result, 3);
            } else if (tok.string.equals(id)) {
                return result;
            } else {
                result = this.stepCoord(result, 1);
            }

        }
        return null;
    }

    public TLAToken tokenAt(final IntPair coord)
    /**********************************************************************
     * exp.tokenAt(coord) is the TLAToken in TLAExpr exp with Java         *
     * coordinates coord.                                                  *
     **********************************************************************/
    {
        return this.tokens.get(coord.one).get(coord.two);
    }

    public IntPair stepCoord(final IntPair coord, final int incr)
    /**********************************************************************
     * exp.stepCoord(coord, incr) returns the Java coordinates of the      *
     * token in exp that is incr tokens past the one with Java             *
     * coordinates coord.  If there is no such token, then it returns      *
     * null.                                                               *
     **********************************************************************/
    { /********************************************************************
     * Check that coord is a valid coordinate pair.                      *
     ********************************************************************/
        if (tokens.size() <= coord.one) {
            PcalDebug.ReportBug(
                    "TLAExpr.StepCoord called with line too big");
        }
        ArrayList<TLAToken> line = tokens.get(coord.one);
        if (line.size() <= coord.two) {
            PcalDebug.ReportBug(
                    "TLAExpr.StepCoord called with col too big");
        }

        final IntPair result = new IntPair(coord.one, coord.two);
        int i = 0;
        while (i < incr) {
            result.two = result.two + 1;
            if (line.size() == result.two) {
                result.two = 0;
                result.one = result.one + 1;
                while ((result.one < tokens.size())
                        && (tokens.get(result.one).size()
                        == 0)) {
                    result.one = result.one + 1;
                }
                if (result.one == tokens.size()) {
                    return null;
                }
                line = tokens.get(result.one);
            }
            i = i + 1;
        }
        return result;
    }

    public boolean isEmpty() {
        return (tokens == null)
                || (tokens.size() == 0);
    }

    public boolean isOneToken() {
        return (!this.isEmpty())
                && (tokens.size() == 1)
                && (tokens.get(0).size() == 1);
    }

    public TLAToken firstToken() {
        final ArrayList<TLAToken> line = this.tokens.get(0);
        return line.get(0);
    }

    public TLAToken lastToken() {
        final ArrayList<TLAToken> line = this.tokens.get(this.tokens.size() - 1);
        return line.get(line.size() - 1);
    }

    /************************************************************************
     * For debugging, the following prints a TLAExpr with an indicated name. *
     ************************************************************************/
    public void print(final String name) {
        PcalDebug.print2DVector(tokens, name + ".tokens");
        PcalDebug.printObjectArray(anchorTokens, name + ".anchorTokens");
        PcalDebug.printIntArray(anchorTokCol, name + ".anchorTokCol");
    }

/***************************************************************************
 * Appending Vectors:                                                       *
 *                                                                          *
 * For any distinct vectors v and v2, the method v.addAll(v2)               *
 * apparently appends v2 to the end of v, and returns true iff this v2 is   *
 * non-empty, so this changes v.                                            *
 ***************************************************************************/

}
/***************************************************************************
 * RULE FOR PRESERVING THE FORMATTING WHEN REWRITING AN EXPRESSION.         *
 *                                                                          *
 * I first define some terminology for describing an expression.  A TOKEN   *
 * t consists of a symbol t.symbol and a column t.column that is a          *
 * positive integer.  For example, in                                       *
 *                                                                          *
 *    (a = 0) => /\ B                                                       *
 *               /\ C                                                       *
 *                                                                          *
 * the => is represented by a token t with t.symbol = => and t.column =     *
 * 9, since the = of => occurs in the 9th column of the expression.  (I     *
 * assume that column numbers are normalized so the left-most token of an   *
 * expression occurs in column 1.)  A LINE is a sequence <<t_{1}, \ldots,   *
 * t_{n}>> of tokens, where t_{i}.column < t_{i+1}.column for               *
 * i=1,\ldots,n-1.  An EXPRESSION is a sequence of one or more lines        *
 * beginning and ending with a nonempty line.                               *
 *                                                                          *
 * If line number n is nonempty, define column(n) to be the column of       *
 * its first (left-most) token.  I say that line m COVERS line              *
 * n iff lines m and n are nonempty, m < n, and column(m) \leq column(n).   *
 * The covering line of line number n is the largest line number m such     *
 * that m covers n, if such an m exists.                                    *
 *                                                                          *
 * If line n has a covering line m, then the ANCHOR of line                 *
 * n is defined as follows.  Let T be the set of all tokens t in            *
 * line m such that t.column \leq column(n) and t.symbol equals             *
 * /\ or \/.  If T is nonempty, then the anchor of n is                     *
 * the token t in T with the largest value of t.column.  Otherwise,         *
 * the anchor of n is the first token of line m.  If n has no               *
 * covering line, then it is defined to have no anchor.  The first line     *
 * of any expression has no anchor.  In the example above, the anchor of    *
 * line 2 is the /\ token in line 1.                                        *
 *                                                                          *
 * The rule for preserving indentation is: (1) if a line has an anchor,     *
 * then its indentation from its anchor must be preserved in the            *
 * rewriting, and (2) if a line has no anchor, then its indentation from    *
 * the left margin is preserved.  I now state this rule more precisely.     *
 *                                                                          *
 * The rewriting of an expression exp by the compiler consists of           *
 * inserting additional tokens into lines and modifying the column          *
 * numbers of some existing tokens to form a new expression newExp.         *
 * For any token t of exp, let f(t) be the same token in                    *
 * newExp---in other words, the token in newExp that corresponds to         *
 * token t in exp.  The mapping f satisfies:                                *
 *                                                                          *
 * - If token t occurs in line n of exp, then f(t) occurs in                *
 *   line n of newExp.                                                      *
 *                                                                          *
 * - If token t is the first token on its line in exp, then                 *
 *   f(t) is the first token on its line in newExp.                         *
 *   The following is the rule for formatting the expression newExp         *
 *   obtained by rewriting expression exp.                                  *
 *                                                                          *
 * For any nonempty line n of exp with first token s:                       *
 *                                                                          *
 *     If n has an anchor t, then                                           *
 *        f(s).column - f(t).column = s.column - t.column                   *
 *                                                                          *
 *     If n has no anchor, then s.column = f(s).column                      *
 *                                                                          *
 * This rule is actually stronger than necessary.  In case (1), it is       *
 * only necessary that                                                      *
 *                                                                          *
 *    (i) s.column = t.column implies f(s).column = f(t).column and         *
 *   (ii) s.column > t.column implies f(s).column > f(t).column.            *
 *                                                                          *
 * In other words, only the relations "in the same column" and "to the      *
 * right of" between a column and its anchor must be preserved.  However,   *
 * the stronger rule seems better because it should produce a rewritten     *
 * expression that looks as much as possible like the original.             *
 *                                                                          *
 ***************************************************************************/


/* last modified on Fri 31 Aug 2007 at 14:03:38 PST by lamport */
