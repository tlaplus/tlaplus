// Copyright (c) 2003 Compaq Corporation.  All rights reserved.

/***************************************************************************
 * CLASS WriteTLAFile                                                       *
 *                                                                          *
 * Contains the method Write for writing out a tokenized spec as a TLA      *
 * file, deleting the "`^ ... ^'" parts of comments, and replacing "`~",    *
 * "~'", "`.", and ".'" by spaces.                                          *
 ***************************************************************************/
package tla2tex;

public class WriteTLAFile {
    public static void Write(final Token[][] spec, final String fileName) {
        final OutputFileWriter writer = new OutputFileWriter(fileName);
        int line = 0;

        boolean deleting = false;
        /*******************************************************************
         * true if we have processed a line from a multi-line comment with  *
         * a "`^", but have not yet encountered the matching "^'".          *
         *******************************************************************/

        int multiBelow = 0;
        /*******************************************************************
         * When, after deleting characters inside a "`^" in a multi-line    *
         * comment, we wind up with nothing but space characters on the     *
         * line, we don't print out that line.  Instead, we print in its    *
         * place the next line of the comment that has something that's     *
         * not deleted.  The value of multiBelow is the number of lines     *
         * below that we have to look for the current line of the comment.  *
         * In other words, when we get to a line of a multi-line comment    *
         * on line ln, we process the comment-line at line ln +             *
         * multiBelow.                                                      *
         *******************************************************************/

        while (line < spec.length) {
            final StringBuilder outLine = new StringBuilder();
            int item = 0;
            boolean nullComment = false;
            /*****************************************************************
             * True iff produced no output for a multi-line comment line      *
             * because of deletions.                                          *
             *****************************************************************/
            while (item < spec[line].length) {
                final Token tok = spec[line][item];
                if (item > 0) {
                    outLine.append(SpacesString(tok.column
                            - spec[line][item - 1].column
                            - spec[line][item - 1].getWidth()));
                } else {
                    outLine.append(SpacesString(tok.column));
                }
                switch (tok.type) {
                    case Token.BUILTIN, Token.NUMBER, Token.IDENT, Token.PCAL_LABEL, Token.DASHES, Token.END_MODULE, Token.PROLOG, Token.EPILOG, Token.PF_STEP ->
                            outLine.append(tok.string);
                    case Token.STRING -> outLine.append("\"").append(tok.string).append("\"");
                    case Token.COMMENT -> {
                        /*************************************************************
                         * Set ctok to the current comment token we are processing.   *
                         *************************************************************/
                        CommentToken ctok = (CommentToken) tok;
                        if (ctok.subtype == CommentToken.BEGIN_MULTI)
                        /***********************************************************
                         * Reset deleting and multiBelow when beginning a           *
                         * mult-line comment.                                       *
                         ***********************************************************/ {
                            deleting = false;
                            multiBelow = 0;
                        }
                        String commentString = "";
                        /***********************************************************
                         * Will set commentString to the current comment line       *
                         * minus the deleted characters.                            *
                         ***********************************************************/
                        if ((ctok.subtype == CommentToken.MULTI)
                                || (ctok.subtype == CommentToken.NULL))
                        /***********************************************************
                         * Set ctok to the token multiBelow lines below this one,   *
                         * following the belowAlign pointers, or null if this       *
                         * takes us past the end of the comment--which means we've  *
                         * output the entire comment already.                       *
                         ***********************************************************/ {
                            int i = 0;
                            while ((ctok != null)
                                    && (i < multiBelow)) {
                                final Position bpos = ctok.belowAlign;
                                ctok = null;
                                if (bpos.line != -1) {
                                    final Token btok = bpos.toToken(spec);
                                    if (btok.type == Token.COMMENT) {
                                        final CommentToken bctok = (CommentToken) btok;
                                        if ((bctok.subtype == CommentToken.MULTI)
                                                || (bctok.subtype == CommentToken.NULL)) {
                                            ctok = bctok;
                                        }
                                    }
                                }
                                i = i + 1;
                            }

                            if (ctok != null) {
                                commentString = ctok.string;
                                if (deleting) {
                                    commentString = "`^" + commentString;
                                }
                                deleting = UnmatchedDelete(commentString);
                                commentString = RemoveDeletions(commentString);
                                while (deleting
                                        && (ctok != null)
                                        && Misc.isBlank(commentString)) {
                                    final Position bpos = ctok.belowAlign;
                                    ctok = null;
                                    if (bpos.line != -1) {
                                        final Token btok = bpos.toToken(spec);
                                        if (btok.type == Token.COMMENT) {
                                            final CommentToken bctok = (CommentToken) btok;
                                            if ((bctok.subtype == CommentToken.MULTI)
                                                    || (bctok.subtype == CommentToken.NULL)) {
                                                ctok = bctok;
                                                multiBelow = multiBelow + 1;
                                                commentString = ctok.string;
                                                deleting =
                                                        UnmatchedDelete("`^" + commentString);
                                                commentString =
                                                        RemoveDeletions("`^" + commentString);
                                            }
                                        }
                                    }
                                } // END while ( deleting ... )
                            }
                            if ((ctok != null)
                                    && Misc.isBlank(commentString)) {
                                commentString = SpacesString(ctok.string.length());
                            }
                        } else { /*********************************************************
                         * This is not a MULTI or NULL comment token.             *
                         *********************************************************/
                            commentString = RemoveDeletions(ctok.string);
                            commentString = commentString +
                                    SpacesString(ctok.string.length() -
                                            commentString.length());
                        }
                        if (ctok != null) {
                            commentString = ReplaceQuoteTildes(commentString);
                            switch (ctok.rsubtype) {
                                case CommentToken.NORMAL -> outLine.append("(*").append(commentString).append("*)");
                                case CommentToken.LINE -> outLine.append("\\*").append(commentString);
                                case CommentToken.BEGIN_OVERRUN -> outLine.append("(*").append(commentString);
                                case CommentToken.END_OVERRUN -> outLine.append(commentString).append("*)");
                                case CommentToken.OVERRUN -> outLine.append(commentString);
                                default -> Debug.ReportBug("Bad CommentToken subtype found.");
                            }
                        } else {
                            nullComment = true;
                        }
                    }
                    default -> Debug.ReportBug("Bad token type found.");
                }
                item = item + 1;
            }
            if (!(nullComment
                    && (spec[line].length == 1))) {
                writer.putLine(outLine.toString());
            }
            line = line + 1;
        }
        writer.close();
    }

    private static String SpacesString(final int n)
    /***********************************************************************
     * A string of n spaces.                                                *
     ***********************************************************************/
    {
        int i = 0;
        final StringBuilder result = new StringBuilder();
        while (i < n) {
            result.append(" ");
            i = i + 1;
        }
        return result.toString();
    }

    private static boolean UnmatchedDelete(final String str)
    /***********************************************************************
     * True iff the last "`^" string comes after the last "^'" string.      *
     ***********************************************************************/
    {
        return (str.lastIndexOf("^'") < str.lastIndexOf("`^"));
    }

    private static String RemoveDeletions(final String str)
    /***********************************************************************
     * The string obtained by removing everything from each "`^" through    *
     * the next "^'" (if there is one).                                     *
     ***********************************************************************/
    {
        String rest = str;
        final StringBuilder start = new StringBuilder();
        int nextDel = rest.indexOf("`^");
        while (nextDel != -1) {
            start.append(rest, 0, nextDel);
            rest = rest.substring(nextDel);
            final int nextEnd = rest.indexOf("^'");
            if (nextEnd == -1) {
                nextDel = -1;
                rest = "";
            } else {
                rest = rest.substring(nextEnd + 2);
                nextDel = rest.indexOf("`^");
            }
        }
        return start + rest;
    }

    private static String ReplaceQuoteTildes(final String str)
    /***********************************************************************
     * The string obtained by replacing each "`~", "~'", "`.", and ".'" by  *
     * spaces.                                                              *
     ***********************************************************************/
    {
        String result = str;
        int nextRepl = result.indexOf("`~");
        while (nextRepl != -1) {
            result = result.substring(0, nextRepl)
                    + "  " + result.substring(nextRepl + 2);
            nextRepl = result.indexOf("`~");
        }
        nextRepl = result.indexOf("~'");
        while (nextRepl != -1) {
            result = result.substring(0, nextRepl)
                    + "  " + result.substring(nextRepl + 2);
            nextRepl = result.indexOf("~'");
        }
        nextRepl = result.indexOf("`.");
        while (nextRepl != -1) {
            result = result.substring(0, nextRepl)
                    + "  " + result.substring(nextRepl + 2);
            nextRepl = result.indexOf("`.");
        }
        nextRepl = result.indexOf(".'");
        while (nextRepl != -1) {
            result = result.substring(0, nextRepl)
                    + "  " + result.substring(nextRepl + 2);
            nextRepl = result.indexOf(".'");
        }
        return result;
    }
}