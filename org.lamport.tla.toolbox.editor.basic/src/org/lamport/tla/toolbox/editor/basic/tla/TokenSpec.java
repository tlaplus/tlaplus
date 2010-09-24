/**
 * 
 */
package org.lamport.tla.toolbox.editor.basic.tla;

import org.eclipse.jface.text.BadLocationException;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.IRegion;
import org.eclipse.jface.text.ITextSelection;
import org.eclipse.jface.text.Region;
import org.eclipse.jface.text.source.ISourceViewer;
import org.lamport.tla.toolbox.editor.basic.TLAEditor;
import org.lamport.tla.toolbox.editor.basic.util.EditorUtil;
import org.lamport.tla.toolbox.util.ResourceHelper;

import tla2sany.semantic.ModuleNode;
import tla2sany.semantic.SymbolNode;
import tla2sany.st.Location;
import util.UniqueString;

/**
 * A TokenSpec object represents a possible TLA+ symbol name together
 * with the position of that symbol.  Note that the
 * expression Foo(a, b)!Bar(c) may be an occurrence of the symbol
 * named "Foo!Bar", whose left position is at the "F" and whose right
 * position is just after the "r" (and hence, at the following ")").
 * 
 * The main method is findTokenSpecs.
 *  
 * @author lamport
 *
 */
public class TokenSpec
{
    /*
     * The following are the fields of the object.  They are accessed
     * directly, without any of this set...() and get...() Java 
     * nonsense.
     */
    public String token;
    public int leftPos;
    public int rightPos;
    public SymbolNode resolvedSymbol = null;

    public TokenSpec(String tok, int left, int right)
    {
        this.token = tok;
        this.leftPos = left;
        this.rightPos = right;
    }

    /**
     * This method returns the TokenSpec of the symbol at the cursor position 
     * of the TLAEditor with the current focus.  If it cannot find the definition
     * or declaration of such a symbol, it returns a TokenSpec for the token
     * being pointed to with a null resolvedSymbol field.  This will be the
     * case if that token is a module name.
     * 
     * @return
     */
    public static TokenSpec findCurrentTokenSpec()
    {
        // We first get the editor with focus and find its module and
        // its document, returning null if we get any nulls.
        TLAEditor editor = EditorUtil.getTLAEditorWithFocus();
        if (editor == null)
        {
            return null;
        }
        String moduleName = editor.getModuleName();
        ModuleNode moduleNode = ResourceHelper.getModuleNode(moduleName);
        if (moduleNode == null)
        {
            return null;
        }
        ISourceViewer internalSourceViewer = editor.publicGetSourceViewer();
        IDocument document = internalSourceViewer.getDocument();
        ITextSelection selection = (ITextSelection) editor.getSelectionProvider().getSelection();
        IRegion region = new Region(selection.getOffset(), selection.getLength());

        // Sets currentLine to the line of text of the module containing the beginning of the
        // current region, and sets currentPos to the position of the beginning of the
        // current region in that line. The Document.getLineLength method seems to include
        // the length of the line's delimeter, which should not be included in currentLine.
        String currentLine;
        int currentPos;
        int offsetOfLine;
        try
        {
            int lineNumber = document.getLineOfOffset(region.getOffset());
            int lineDelimLength = 0;
            String delim = document.getLineDelimiter(lineNumber);
            if (delim != null)
            {
                lineDelimLength = delim.length();
            }
            ;
            offsetOfLine = document.getLineOffset(lineNumber);
            currentLine = document.get(offsetOfLine, document.getLineLength(lineNumber) - lineDelimLength);
            currentPos = region.getOffset() - offsetOfLine;
            // System.out.println("`" + currentLine + "'");
            // System.out.println(currentLine.substring(currentPos));
            // for (int j = 0; j < currentLine.length(); j++)
            // {
            // System.out.println("curPos = " + j);
            // TokenSpec[] ts = TokenSpec.findTokenSpecs(currentLine, j); // currentPos);
            // if (ts.length == 0)
            // {
            // System.out.println("empty");
            // } else
            // {
            // for (int i = 0; i < ts.length; i++)
            // {
            // System.out.println("  " + i + ": " + ts[i].toString() + " `"
            // + currentLine.substring(ts[i].leftPos, ts[i].rightPos) + "'");
            // }
            // }
            // }
        } catch (BadLocationException e)
        {
            System.out.println("Exception thrown");
            return null;
        }

        // Call findTokenSpecs to find the array of candidate TokenSpec
        // objects. Note that this may return an array of length 0, but
        // does not return null.
        TokenSpec[] tokenSpecs = findTokenSpecs(currentLine, currentPos);

        // We update the positions to be offsets within the document,
        // and look for resolvedSymbol, setting goodIndex to the index
        // in tokenSpecs of the first element that resolves.
        int goodIndex = -1;
        SymbolNode symbol = null;
        for (int i = 0; i < tokenSpecs.length; i++)
        {

            int leftPos = tokenSpecs[i].leftPos;
            int rightPos = tokenSpecs[i].rightPos;
            tokenSpecs[i].leftPos = leftPos + offsetOfLine;
            tokenSpecs[i].rightPos = rightPos + offsetOfLine;
            Location location = EditorUtil.getLocationAt(document, tokenSpecs[i].leftPos, rightPos - leftPos);
            symbol = EditorUtil.lookupOriginalSymbol(UniqueString.uniqueStringOf(tokenSpecs[i].token), moduleNode,
                    location, null);
            if (symbol != null)
            {
                goodIndex = i;
                break;
            }
        }
        if (goodIndex == -1)
        {
            if (tokenSpecs.length == 0)
            {
                return null;
            } else
            {
                goodIndex = 0;
            }
        }
        TokenSpec result = new TokenSpec(tokenSpecs[goodIndex].token, tokenSpecs[goodIndex].leftPos,
                tokenSpecs[goodIndex].rightPos);
        result.resolvedSymbol = symbol;
        return result;
    }

    /** 
     * This method finds all possible symbol names containing the character at
     * or just before position inputPosition of line inputLine, in order of
     * decreasing length.  It returns their positions relative to the
     * beginning of the line.  There can be multiple possibilities because if
     * inputPosition is at the "a" in
     * 
     *    Foo!Bar!End
     * 
     * then the method return the array whose first element represents
     * Foo!Bar!End and whose second element represents Foo!Bar.  We don't
     * know which is correct, because End could either be a symbol defined
     * in an instantiated instantiated model, or else a label in the 
     * definition of the instantiated symbol Bar.
     * 
     * This method is the encoding of the PlusCal procedure of the same name in
     * module FindOp, which is appended as a comment to this file.
     * 
     * @param inputLine
     * @param inputPosition
     * @return
     */
    public static TokenSpec[] findTokenSpecs(String inputLine, int inputPosition)
    {
        // we pad the input line on the ends so we don't have to worry
        // about going off the end of the line.
        String line = Padding + inputLine + Padding;

        // Maintains the current position at which we are processing.
        int curPos = inputPosition + Padding.length();

        // Contains the result we've found so far.
        TokenSpec[] foundTokenSpecs = new TokenSpec[0];

        // Set true if there can be no tokens to right of first one found.
        boolean lastToken = false;

        // Set true if we find a "!" to the right of the first token found.
        boolean notLastToken = false;

        // temporary variable
        TokenSpec currentToken;

        System.out.println("Started");

        // Try to find the current TokenSpec and put it in foundTokenSpecs,
        // leaving curPos to the left of that token. If the token is a
        // step name, we can return that single TokenSpec as the spec.
        // If it is an unnamed step, or if it is not a possible identifier
        // or operator symbol, we return << >> (a zero-length array).

        // First, we must check if we may be inside a string a possibly empty
        // sequence of spaces, a "!", and a possibly empty sequence of spaces.
        // If so, we move to its left, setting notLastToken to true.
        if (line.charAt(curPos) == ' ')
        {
            curPos = skipLeftOverSpaces(line, curPos);
            if (line.charAt(curPos - 1) == '!' && line.charAt(curPos - 2) != '!')
            {
                notLastToken = true;
                curPos = curPos - 1;
                curPos = skipLeftOverSpaces(line, curPos);
            }
        } else if ((line.charAt(curPos) == '!') && (line.charAt(curPos - 1) != '!') && (line.charAt(curPos + 1) != '!'))
        {
            notLastToken = true;
            curPos = skipLeftOverSpaces(line, curPos);
        }
        ;

        // If we're to the right of a ")", we could be inside something like
        //
        // Foo(42) ! bar
        // ^
        // so we set notLastToken true and move to the left of the parenthesized string.
        if ((notLastToken || line.charAt(curPos) == ' ') && (line.charAt(curPos - 1) == ')'))
        {
            notLastToken = true;
            int returnVal = findMatchingLeftParen(line, curPos);
            if (returnVal < 0)
            {
                return new TokenSpec[0];
            }
            curPos = returnVal;
            curPos = skipLeftOverSpaces(line, curPos);
        }
        ;
        // If notLastToken is true, then we should be just to the right
        // of the token we are expecting to find to the left of the '!' or the
        // parenthesized expression.
        if (notLastToken)
        {
            curPos = curPos - 1;
        } else
        {
            if ((!(Character.isLetterOrDigit(line.charAt(curPos)) || (line.charAt(curPos) == '_')))
                    && (findTokenIn(line, curPos, Operators) == null))
            {
                curPos = curPos - 1;
            }
        }

        if (Character.isLetterOrDigit(line.charAt(curPos)) || line.charAt(curPos) == '_')
        {
            if ((line.charAt(curPos) == 'X') && findTokenIn(line, curPos, XOperators) != null)
            {
                TokenSpec returnVal = findTokenIn(line, curPos, XOperators);
                foundTokenSpecs = new TokenSpec[] { returnVal };
                curPos = returnVal.leftPos;
                lastToken = true;
            } else
            {
                currentToken = findMaximalIdCharSeq(line, curPos);

                // Check if token is part of step name. If it is, we set
                // First, see if currentToken could be the token after the "<...>".
                if (line.charAt(currentToken.leftPos - 1) == '>')
                {
                    TokenSpec returnVal = findMaximalIdCharSeq(line, currentToken.leftPos - 1);
                    returnVal = checkIfStepName(line, returnVal, currentToken);
                    if (returnVal != null)
                    {
                        return FixOrigin(new TokenSpec[] { returnVal });
                    }
                }
                ;
                // Next see if it's the token to the left of the '>'
                if (line.charAt(currentToken.rightPos) == '>')
                {
                    TokenSpec returnVal = findMaximalIdCharSeq(line, currentToken.rightPos + 1);
                    returnVal = checkIfStepName(line, currentToken, returnVal);
                    if (returnVal != null)
                    {
                        return FixOrigin(new TokenSpec[] { returnVal });
                    }
                }
                ;

                // Next, check if it's a number, and return if it is.
                if (IsNumber(currentToken.token))
                {
                    return new TokenSpec[0];
                }
                // Next, check if the token appears as a "\\" token, in
                // which case we adjust currentTok
                int left = currentToken.leftPos;
                int rt = currentToken.rightPos;
                if ((line.charAt(left - 1) == '\\') && (line.charAt(left - 2) != '\\')
                        && IsTeXSymbol(line.substring(left - 1, rt)))
                {
                    lastToken = true;
                    currentToken.leftPos = left - 1;
                    currentToken.token = line.substring(left - 1, rt);
                }
                ;
                foundTokenSpecs = new TokenSpec[] { currentToken };
                curPos = left;
            }
        } else
        {
            currentToken = findTokenIn(line, curPos, Operators);
            if (currentToken == null)
            {
                return new TokenSpec[0];
            }
            ;
            TokenSpec returnVal = findTokenIn(line, curPos, NonOperators);
            if (returnVal != null)
            {
                return new TokenSpec[0];
            }
            ;

            // Need to check if beginning or end of level specifier
            // of step number.
            if (currentToken.token.equals("<"))
            {
                TokenSpec temp1 = findMaximalIdCharSeq(line, currentToken.rightPos);
                if ((temp1 != null) && (line.charAt(temp1.rightPos) == '>'))
                {
                    TokenSpec temp2 = findMaximalIdCharSeq(line, temp1.rightPos + 1);
                    returnVal = checkIfStepName(line, temp1, temp2);
                    if (returnVal != null)
                    {
                        return FixOrigin(new TokenSpec[] { returnVal });
                    }
                }
            } else if (currentToken.token.equals(">"))
            {
                TokenSpec temp1 = findMaximalIdCharSeq(line, currentToken.leftPos);
                TokenSpec temp2 = findMaximalIdCharSeq(line, currentToken.rightPos);
                returnVal = checkIfStepName(line, temp1, temp2);
                if (returnVal != null)
                {
                    return FixOrigin(new TokenSpec[] { returnVal });
                }
            }

            // We check for the case of a '\\' starting a TeX token.
            if (currentToken.token.equals("\\"))
            {
                returnVal = findMaximalIdCharSeq(line, currentToken.rightPos);
                if ((returnVal != null) && IsTeXSymbol(line.substring(currentToken.leftPos, returnVal.rightPos)))
                {
                    currentToken.rightPos = returnVal.rightPos;
                    currentToken.token = line.substring(currentToken.leftPos, returnVal.rightPos);
                }
            }
            ;

            foundTokenSpecs = new TokenSpec[] { currentToken };
            curPos = currentToken.leftPos;
            lastToken = true;
        }
        ;

        // At this point, foundTokenSpecs.length = 1, and we have found the
        // base token. We now look to find extenders to the left of the form
        // idtoken '!'. These must be part of the name, so we prepend
        // them to foundTokenSpecs[0].
        curPos = foundTokenSpecs[0].leftPos;
        boolean notDone = true;
        while (notDone)
        {
            curPos = skipLeftOverSpaces(line, curPos);
            if (curPos < 0 || line.charAt(curPos - 1) == PaddingChar)
            {
                notDone = false;
            } else
            {
                if (line.charAt(curPos - 1) == '!' && (line.charAt(curPos - 2) != '!'))
                {
                    curPos = curPos - 1;
                    curPos = skipLeftOverSpaces(line, curPos);
                    curPos = findMatchingLeftParen(line, curPos);
                    if (curPos < 0)
                    {
                        notDone = false;
                    } else
                    {
                        curPos = skipLeftOverSpaces(line, curPos);
                        currentToken = findMaximalIdCharSeq(line, curPos);
                        if ((currentToken == null) || IsNumber(currentToken.token))
                        {
                            notDone = false;
                        } else
                        {
                            curPos = currentToken.leftPos;
                            foundTokenSpecs[0] = new TokenSpec(currentToken.token + "!" + foundTokenSpecs[0].token,
                                    curPos, foundTokenSpecs[0].rightPos);
                        }
                    }
                } else
                {
                    notDone = false;
                }
            }
        }

        // We have now completed the first token. If there are no more,
        // then we're done.
        if (lastToken == true)
        {
            return FixOrigin(foundTokenSpecs);
        }

        // There may be more "!" parts of the name to the right.
        curPos = foundTokenSpecs[0].rightPos;
        boolean foundBangToken = false;
        notDone = true;
        while (notDone)
        {
            curPos = skipRightOverSpaces(line, curPos);
            curPos = findMatchingRightParen(line, curPos);
            if (curPos < 0)
            {
                notDone = false;
            } else
            {
                curPos = skipRightOverSpaces(line, curPos);
                if ((line.charAt(curPos) != '!') || (line.charAt(curPos + 1) == '!'))
                {
                    notDone = false;
                } else
                {
                    curPos = curPos + 1;
                    curPos = skipRightOverSpaces(line, curPos);
                    currentToken = findMaximalIdCharSeq(line, curPos);
                    if ((currentToken == null) || IsNumber(currentToken.token))
                    {
                        notDone = false;
                    } else
                    {
                        foundBangToken = true;
                        // We now create a new TokenSpec by appending
                        // "!" + currentToken.token to the end of the
                        // first TokenSpec of foundTokenSpecs, and we prepend
                        // this TokenSpec to the beginning of foundTokenSpecs.
                        // We build the new foundTokenSpecs array in temp.
                        TokenSpec[] temp = new TokenSpec[1 + foundTokenSpecs.length];
                        temp[0] = new TokenSpec(foundTokenSpecs[0].token + "!" + currentToken.token,
                                foundTokenSpecs[0].leftPos, currentToken.rightPos);
                        for (int i = 0; i < foundTokenSpecs.length; i++)
                        {
                            temp[i + 1] = foundTokenSpecs[i];
                        }
                        foundTokenSpecs = temp;
                        curPos = currentToken.rightPos;
                    }
                }
            }
        }
        ;
        // If this wasn't the last token but we found no "!" following it,
        // then something is wrong so we return an empty result
        if (notLastToken && !foundBangToken)
        {
            return new TokenSpec[0];
        }
        ;

        System.out.println("Finisheded");

        return FixOrigin(foundTokenSpecs);

        // for (int i = Padding.length(); i < line.length() - Padding.length(); i++)
        // {
        // // TokenSpec ts = findMaximalIdCharSeq(line, i);
        // // if (ts != null)
        // // System.out.println("" + i + ": " + ts.toString());
        // System.out.println("" + i + ": " + IsNumber(findMaximalIdCharSeq(line, i).token));
        // }

    }

    /**
     *  Returns the TokenSpec for the token in the array tokArray of Java
     * strings (Java array of 1-character strings) in the line containing the
     * character at position pos, or NullTokenSpec if there is none.
     * 
     * @return
     */
    private static TokenSpec findTokenIn(String line, int pos, String[] tokArray)
    {
        int tokIdx;
        for (int i = 0; i < tokArray.length; i++)
        {
            tokIdx = tokArray[i].indexOf(line.charAt(pos), 0);
            while (tokIdx != -1)
            {
                int ftlft = pos - tokIdx;
                int ftrt = pos - tokIdx + tokArray[i].length();
                if (tokArray[i].equals(line.substring(ftlft, ftrt)))
                {
                    return new TokenSpec(tokArray[i], ftlft, ftrt);
                }
                tokIdx = tokArray[i].indexOf(line.charAt(pos), tokIdx + 1);
            }
        }
        return null;
    }

    /**
     * Returns the TokenSpec of the largest token containing digits, letters,
     * and "_" characters containing position pos.  Returns null if
     * that would be an empty token.
     */
    private static TokenSpec findMaximalIdCharSeq(String line, int pos)
    {
        int left = pos;
        int rt = pos;
        left = pos;
        while (Character.isLetterOrDigit(line.charAt(left - 1)) || line.charAt(left - 1) == '_')
        {
            left--;
        }
        while (Character.isLetterOrDigit(line.charAt(rt)) || line.charAt(left - 1) == '_')

        {
            rt++;
        }
        if (left == rt)
        {
            return null;
        } else
        {
            return new TokenSpec(line.substring(left, rt), left, rt);
        }
    }

    /**
     * Assumes that leftTok and rightTok are two TokenSpecs, possibly 
     * NullTokenSpecs, separated by a ">".  Checks if they form a step name.
     * If so, it returns the TokenSpec for that step name; otherwise it
     * returns null.
     * 
     * @param line
     * @param leftTok
     * @param rightTok
     * @return
     */
    private static TokenSpec checkIfStepName(String line, TokenSpec leftTok, TokenSpec rightTok)
    {
        if (leftTok == null || rightTok == null)
        {
            return null;
        }
        if (IsNumber(leftTok.token) && (line.charAt(leftTok.leftPos - 1) == '<')
                && (line.charAt(leftTok.leftPos - 2) != '<'))
        {
            return new TokenSpec(line.substring(leftTok.leftPos - 1, rightTok.rightPos), leftTok.leftPos - 1,
                    rightTok.rightPos);
        } else
        {
            return null;
        }
    }

    /**
     * Returns the position of the left paren matching a ")" at pos-1.  
     * If there is none, it returns -1.
     * 
     * @param line
     * @param pos
     * @return
     */
    private static int findMatchingLeftParen(String line, int pos)
    {
        if (line.charAt(pos - 1) != ')')
        {
            return pos;
        }
        ;
        return findMatchingLeftInner(line, pos, 0);
    }

    private static int findMatchingLeftInner(String line, int pos, int delim)
    {
        int ipos = pos;
        int jdelim;
        int delimLen = LeftDelimiters[delim].length();
        ipos = pos - delimLen;
        while (!line.substring(ipos - delimLen, ipos).equals(LeftDelimiters[delim]))
        {
            if (line.charAt(ipos - 1) == PaddingChar)
            {
                return -1;
            }
            ;
            ipos = ipos - 1;
            jdelim = 0;
            while (jdelim < LeftDelimiters.length)
            {
                if (line.substring(ipos - delimLen, ipos).equals(RightDelimiters[jdelim]))
                {
                    ipos = findMatchingLeftInner(line, ipos, jdelim);
                    if (ipos < 0)
                    {
                        return -1;
                    }
                    jdelim = 99999; // exit while loop
                }
                ;
                jdelim = jdelim + 1;
            }
        }
        ;
        return ipos - delimLen;
    }

    /**
     * Returns the position of the right paren matching a "(" at position pos.  
     * If there is none, it returns -1.
     * 
     * @param line
     * @param pos
     * @return
     */
    private static int findMatchingRightParen(String line, int pos)
    {
        if (line.charAt(pos) != '(')
        {
            return pos;
        }
        ;
        return findMatchingRightInner(line, pos, 0);
    }

    private static int findMatchingRightInner(String line, int pos, int delim)
    {
        int ipos = pos;
        int jdelim;
        int delimLen = RightDelimiters[delim].length();
        ipos = pos + delimLen;
        while (!line.substring(ipos, ipos + delimLen).equals(RightDelimiters[delim]))
        {
            if (line.charAt(ipos) == PaddingChar)
            {
                return -1;
            }
            ipos = ipos + 1;
            jdelim = 0;
            while (jdelim < RightDelimiters.length)
            {
                if (line.substring(ipos, ipos + delimLen).equals(LeftDelimiters[jdelim]))
                {
                    ipos = findMatchingRightInner(line, ipos, jdelim);
                    if (ipos < 0)
                    {
                        return -1;
                    }
                    jdelim = 99999; // exit while loop
                }
                ;
                jdelim = jdelim + 1;
            }
        }
        ;
        return ipos + delimLen;
    }

    private static int skipLeftOverSpaces(String line, int curPos)
    {
        int index = curPos;
        while (line.charAt(index - 1) == ' ')
        {
            index--;
        }
        return index;
    }

    private static int skipRightOverSpaces(String line, int curPos)
    {
        int index = curPos;
        while (line.charAt(index) == ' ')
        {
            index++;
        }
        return index;
    }

    private static boolean IsNumber(String str)
    {
        if (str.length() == 0)
        {
            return false;
        }
        for (int i = 0; i < str.length(); i++)
        {
            if (!Character.isDigit(str.charAt(i)))
            {
                return false;
            }
        }
        return true;
    }

    private static TokenSpec[] FixOrigin(TokenSpec[] tspec)
    {
        TokenSpec[] result = new TokenSpec[tspec.length];
        for (int i = 0; i < tspec.length; i++)
        {
            result[i] = new TokenSpec(tspec[i].token, tspec[i].leftPos - Padding.length(), tspec[i].rightPos
                    - Padding.length());
        }
        return result;
    }

    private static final char PaddingChar = '\u0000';

    private static final String Padding = "" + PaddingChar + PaddingChar + PaddingChar + PaddingChar + PaddingChar
            + PaddingChar + PaddingChar + PaddingChar + PaddingChar + PaddingChar;

    private static final String[] Operators = new String[] { "-+->", "<=>", "...", "::=", "(+)", "(-)", "(.)", "(/)",
            "(\\X)", "--", "**", "++", "<:", "<=", "<", ">=", "..", "||", "[]", "<>", "/\\", "\\/", "//", "/", "/=",
            "~>", "=>", "=<", "=|", "^^", "##", "|-", "|=", "&&", "$$", "??", "%%", "@@", "!!", ":>", ":=", "~", "=",
            "#", "^", "-", "*", ">", "<", "+", "|", "&", "$", "%", "\\" };

    /*
     * XOperators are the Operators containing an "X".  Note that "\\X" is in
     * a TeXSymbol, not in Operators.
     */
    private static final String[] XOperators = { "(\\X)" };

    // private static final String[] ParenOperators = new String[] { "(+)", "(-)", "(.)", "(/)", "(\\X)" };

    private static final String[] TeXSymbols = new String[] { "\\neg", "\\lnot", "\\approx", "\\asymp", "\\bigcirc",
            "\\bullet", "\\cap", "\\cdot", "\\circ", "\\cong", "\\cup", "\\div", "\\doteq", "\\equiv", "\\geq", "\\gg",
            "\\in", "\\intersect", "\\union", "\\land", "\\leq", "\\ll", "\\lor", "\\mod", "\\o", "\\odot", "\\ominus",
            "\\oplus", "\\oslash", "\\otimes", "\\prec", "\\preceq", "\\propto", "\\sim", "\\simeq", "\\sqcap",
            "\\sqcup", "\\sqsubset", "\\sqsupset", "\\sqsubseteq", "\\sqsupseteq", "\\star", "\\subset", "\\subseteq",
            "\\succ", "\\succeq", "\\supset", "\\supseteq", "\\uplus", "\\wr", "\\notin", "\\times", "\\X" };

    private static final String[] NonOperators = new String[] { "==", "---", "->", "<-", "***", "<<", ">>" };

    /**
     * Returns true iff str is an element of the array TeXSymbols.
     * 
     * @param str
     * @return
     */
    private static final boolean IsTeXSymbol(String str)
    {
        for (int i = 0; i < TeXSymbols.length; i++)
        {
            if (str.equals(TeXSymbols[i]))
            {
                return true;
            }
        }
        return false;
    }

    private static String[] RightDelimiters = { ")", "]", "}", ">>" };
    private static String[] LeftDelimiters = { "(", "[", "{", "<<" };

    public String toString()
    {
        String str = "[token |-> " + this.token + ", leftPos |-> " + this.leftPos +
        /*    */", rightPos |-> " + this.rightPos + ", resolvedSymbol |-> ";
        if (this.resolvedSymbol == null)
        {
            return str + "null]";
        }
        return str + this.resolvedSymbol.getName() + "]";

    }
}
