/**
 * 
 */
package org.lamport.tla.toolbox.editor.basic.tla;

import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;
import org.eclipse.jface.text.BadLocationException;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.IRegion;
import org.eclipse.jface.text.ITextSelection;
import org.eclipse.jface.text.Region;
import org.eclipse.jface.text.source.ISourceViewer;
import org.lamport.tla.toolbox.editor.basic.TLAEditor;
import org.lamport.tla.toolbox.editor.basic.TLAEditorActivator;
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
 * The main methods are the two is findCurrentTokenSpecs methods.  
 * Most of the work is done by findTokenSpecs, which was coded from 
 * a PlusCal spec that is appended to this file.
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
     * case if that token is a module name.  This method is used by
     * ShowUsesHandler.execute.
     * 
     * @return
     */
    public static TokenSpec findCurrentTokenSpec()
    {
        return findCurrentTokenSpec(null);
    }

    /**
     * This method is like findCurrentTokenSpec(), except it finds the
     * symbol at the position specified by a region, which is assumed
     * to be a region in the TLA editor with the current focus.  This method
     * is used by TLAHyperlinkDetector.detectHyperlinks.
     * 
     * @param regionInput
     * @return
     */
    public static TokenSpec findCurrentTokenSpec(IRegion regionInput)
    {
        // We first get the editor with focus and find its module and
        // its document, returning null if we get any nulls.
        // Note: Simon wrote a somewhat more baroque way of
        // getting the current editor at the beginning of
        // TLAEditor$OpenDeclarationHandler.execute. I don't know why.
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
        IRegion region = regionInput;
        if (regionInput == null)
        {
            region = new Region(selection.getOffset(), selection.getLength());
        }

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
                
                // silently prevent NPEs (hyperlinks will just not work)
                if (currentToken == null)
                {
					TLAEditorActivator
							.getDefault()
							.getLog()
							.log(new Status(IStatus.WARNING, TLAEditorActivator.PLUGIN_ID,
									"Hyperlinking failed for " + inputLine));
					return new TokenSpec[0];
                }
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

        return FixOrigin(foundTokenSpecs);
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

/****************************  file FindOp.tla ************************
Known Bugs:
- The operator may not be found if you click on a space inside its name, as in 
   "Bar   (x)  !  y"

Known Features:
- Detects the ">" and "<" in " <3> " as operators. 

- If at a label that is also the name of an operator, then that operator 
  will be found.

- An operator appearing inside a comment or a string will be found.

------------------------------- MODULE FindOp -------------------------------
EXTENDS Integers, Sequences, TLC
-----------------------------------------------------------------------------
(***************************************************************************)
(* Operations for doing things in Java coordinates.                        *)
(***************************************************************************)
JavaSeq(seq) == [i \in 0 .. (Len(seq)-1) |-> seq[i+1]]
   \* Turns a TLA sequence into a Java array.
   
JavaSubseq(seq, b, e) == [i \in 0 .. (e-1-b) |-> seq[i+b]]
  \* Corresponds to Java's Subseq String method.
  
JavaLen(seq) == IF DOMAIN seq = {}
                  THEN 0
                  ELSE 1 + 
                         CHOOSE i \in DOMAIN seq : \A j \in DOMAIN seq : i >= j
  \* Corresponds to Java's seq.size() for strings or seq.len for
  \* arrays.  

JavaIndex(jarray, elt, fromPos) == 
  \* For jarray a Java array, it equals the smallest i >= fromPos such that
  \* jarray[i] = elt, or -1 if there is no such i
  LET Found(i) == jarray[i] = elt
      lastIdx == JavaLen(jarray) - 1
  IN  IF \E i \in fromPos .. lastIdx : Found(i)
         THEN CHOOSE i \in fromPos .. lastIdx : /\ Found(i)
                                                /\ \A j \in fromPos .. (i-1): ~Found(j)
         ELSE -1
  
JavaSeqSeq(seq) == [i \in 0 .. (Len(seq)-1) |-> JavaSeq(seq[i+1])]
  \* Converts a TLA sequence of TLA sequences to the corresponding
  \* array of Java arrays
  
JavaAppend(seq, elt) == LET len == JavaLen(seq) 
                        IN  [i \in 0..len |-> IF i = len THEN elt ELSE seq[i]]
  \* Appends an element to the end  of a Java sequence.

JavaConcatenate(seq1, seq2) == LET len1 == JavaLen(seq1)
                                   len2 == JavaLen(seq2)
                               IN  [i \in 0..(len1 + len2-1) |->
                                     IF i < len1 THEN seq1[i] 
                                                 ELSE seq2[i-len1]]
  \* Concatenates two Java arrays
  
IsJavaArray(array, S) == array \in [0..(JavaLen(array)-1) ->  S]
  \* True iff array is a Java array of elements of "type" S
  
\* NullJavaArray == (-1 :> {})
-----------------------------------------------------------------------------                      
(***************************************************************************)
(* The input.                                                              *)
(***************************************************************************)

(***************************************************************************)
(* The contents of the current line of the module.                         *)
(***************************************************************************)
lineInput == JavaSeq(<< "f", "(" , "b", ")", " ", "!", " ", "a", "!" , " ", "g" , \* , " ", " ", " ", "(", "[", "x", "]", ")", " ",
                     "(", "e", ")", " ",
                     "<", "3", "4", ">", "a", "."
 >>)  

               
(***************************************************************************)
(* The current position (in Java coordinates) of the cursor in the module. *)
(***************************************************************************)
currentPosition == 7 
-----------------------------------------------------------------------------
Padding ==  JavaSeq(<<";", ";", ";", ";", ";", ";", ";", ";", ";", ";">>)
  \* In an implementation ";" is replaced by an untypable character


GoingLeft == FALSE
  \* TRUE would mean that we continue searching for the symbol to the left if 
  \* find that we're inside a subexpression selector.

XSymbols == JavaSeqSeq(<< <<"(", "\\", "X", ")">>  >>)
  \* These are the Operators that contain "X".
  \*  Note that "\\X" is a TeXSymbol, not an Operator.

Operators == JavaSeqSeq(<<
\*   "-+->", "<=>", "...", "::=", "(+)", "(-)", "(.)", "(/)", "(\\X)",
\*   "--", "**", "++", "<:", "<=", "<", ">=", "..", "||", "[]", "<>",
\*   "/\\", "\\/", "//", "/", "/=", "~>", "=>", "=<", "=|", "^^", "##",
\*   "|-", "|=", "&&", "$$", "??", "%%", "@@", "!!", ":>", ":=", "~", "=",
\*   "#", "^", "-", "*", ">", "<", "+", "|", "&", "$", "%", "\\"
<< "(", "+", ")" >>,
<< "-", "+", "-", ">" >>,
<< "<", "=", ">" >>,
<< ".", ".", "." >>,
<< ":", ":", "=" >>,
<< "(", "-", ")" >>,
<< "(", ".", ")" >>,
<< "(", "/", ")" >>,
<< "(", "\\", "X", ")" >>,
<< "-",  "-" >>,
<< "*",  "*" >>,
<< "+",  "+" >>,
<< "<",  ":" >>,
<< "<",  "=" >>,
<< "<", " " >>,
<< ">",  "=" >>,
<< ".",  "." >>,
<< "|",  "|" >>,
<< "[",  "]" >>,
<< "<",  ">" >>,
<< "/", "\\" >>,
<< "\\", "/" >>,
<< "/",  "/" >>,
<< "/",  "=" >>,
<< "~",  ">" >>,
<< "=",  ">" >>,
<< "=",  "<" >>,
<< "=",  "|" >>,
<< "^",  "^" >>,
<< "#",  "#" >>,
<< "|",  "-" >>,
<< "|",  "=" >>,
<< "&",  "&" >>,
<< "$",  "$" >>,
<< "?",  "?" >>,
<< "%",  "%" >>,
<< "@",  "@" >>,
<< "!",  "!" >>,
<< ":",  ">" >>,
<< ":",  "=" >>,
<<"^", "+">>,
<<"^", "*">>,
<<"^", "#">>,
<<"~">>,
<<"=">>,
<<"#">>,
<<"^">>,
<<"-">>,
<<"*">>,
<<">">>,
<<"<">>,
<<"+">>,
<<"|">>,
<<"&">>,
<<"$">>,
<<"%">>,
<<"\\">>,
<<"'">>
>>)

NonOperators == JavaSeqSeq( <<
<<"=", "=">>, 
<<"-", "-", "-">>,
<<"-", ">">>,
<<"<", "-">>,
<<"*", "*", "*">>,
<<"<", "<">>,
<<">", ">">>
>> )

\* ParenOperators == JavaSeqSeq( <<
\* << "(", "+", ")" >>,
\* << "(", "-", ")" >>,
\* << "(", ".", ")" >>,
\* << "(", "/", ")" >>,
\* << "(", "\\", "X", ")" >>
\* >> )

TeXSymbols == JavaSeqSeq(<<
\*   "\\neg", "\\lnot", "\\approx",
\*   "\\asymp", "\\bigcirc", "\\bullet", "\\cap", "\\cdot", "\\circ",
\*   "\\cong", "\\cup", "\\div", "\\doteq", "\\equiv", "\\geq", "\\gg",
\*   "\\in", "\\intersect", "\\union", "\\land", "\\leq", "\\ll", "\\lor",
\*   "\\mod", "\\o", "\\odot", "\\ominus", "\\oplus", "\\oslash",
\*   "\\otimes", "\\prec", "\\preceq", "\\propto", "\\sim", "\\simeq",
\*   "\\sqcap", "\\sqcup", "\\sqsubset", "\\sqsupset", "\\sqsubseteq",
\*   "\\sqsupseteq", "\\star", "\\subset", "\\subseteq", "\\succ",
\*   "\\succeq", "\\supset", "\\supseteq", "\\uplus", "\\wr", "\\notin",
\*   "\\times", "\\X" 
<<"\\", "n", "e", "g">>,
<<"\\", "l", "n", "o", "t">>,
<<"\\", "a", "p", "p", "r", "o", "x">>,
<<"\\", "a", "s", "y", "m", "p">>,
<<"\\", "b", "i", "g", "c", "i", "r", "c">>,
<<"\\", "b", "u", "l", "l", "e", "t">>,
<<"\\", "c", "a", "p">>,
<<"\\", "c", "d", "o", "t">>,
<<"\\", "c", "i", "r", "c">>,
<<"\\", "c", "o", "n", "g">>,
<<"\\", "c", "u", "p">>,
<<"\\", "d", "i", "v">>,
<<"\\", "d", "o", "t", "e", "q">>,
<<"\\", "e", "q", "u", "i", "v">>,
<<"\\", "g", "e", "q">>,
<<"\\", "g", "g">>,
<<"\\", "i", "n", "t", "e", "r", "s", "e", "c", "t">>,
<<"\\", "u", "n", "i", "o", "n">>,
<<"\\", "l", "a", "n", "d">>,
<<"\\", "l", "e", "q">>,
<<"\\", "l", "l">>,
<<"\\", "l", "o", "r">>,
<<"\\", "m", "o", "d">>,
<<"\\", "o", "d", "o", "t">>,
<<"\\", "o", "m", "i", "n", "u", "s">>,
<<"\\", "o", "p", "l", "u", "s">>,
<<"\\", "o", "s", "l", "a", "s", "h">>,
<<"\\", "o", "t", "i", "m", "e", "s">>,
<<"\\", "p", "r", "e", "c">>,
<<"\\", "p", "r", "e", "c", "e", "q", "">>,
<<"\\", "p", "r", "o", "p", "t", "o">>,
<<"\\", "s", "i", "m">>,
<<"\\", "s", "i", "m", "e", "q">>,
<<"\\", "s", "q", "c", "a", "p">>,
<<"\\", "s", "q", "c", "u", "p">>,
<<"\\", "s", "q", "s", "u", "b", "s", "e", "t">>,
<<"\\", "s", "q", "s", "u", "p", "s", "e", "t">>,
<<"\\", "s", "q", "s", "u", "b", "s", "e", "t", "e", "q">>,
<<"\\", "s", "q", "s", "u", "p", "s", "e", "t", "e", "q">>,
<<"\\", "s", "t", "a", "r">>,
<<"\\", "s", "u", "b", "s", "e", "t", "">>,
<<"\\", "s", "u", "b", "s", "e", "t", "e", "q">>,
<<"\\", "s", "u", "c", "c">>,
<<"\\", "s", "u", "c", "c", "e", "q">>,
<<"\\", "s", "u", "p", "s", "e", "t", "">>,
<<"\\", "s", "u", "p", "s", "e", "t", "e", "q">>,
<<"\\", "u", "p", "l", "u", "s">>,
<<"\\", "w", "r">>,
<<"\\", "n", "o", "t", "i", "n">>,
<<"\\", "t", "i", "m", "e", "s">>,
<<"\\", "o">>,
<<"\\", "i", "n">>,
<<"\\", "X">>
>>)

IsNumber(seq) == /\ \A i \in DOMAIN seq : 
                       seq[i] \in {"0", "1", "2", "3", "4", "5", "6", "7", "8", "9"}
                 /\ (DOMAIN seq) # {}
IdChar == {"a", "b", "c", "d", "e", "f", "g", "h", "i", "n", (* ... *) "X", "Y", "Z",  
           "0", "1", "2", "3", "4", "5", "6", "7", "8", "9", "_"}

RightDelimiters == JavaSeqSeq(<< <<")">>, <<"]">>, <<"}">>, <<">", ">">> >>)
LeftDelimiters == JavaSeqSeq(<< <<"(">>, <<"[">>, <<"{">>, <<"<", "<">> >>)
-----------------------------------------------------------------------------
TokenSpec == [token : STRING, leftPos : Nat, rightPos : Nat]
NullTokenSpec == [null |-> "null"]
(****************************************************************************
 
--algorithm FindOp {
variables 
  line = JavaConcatenate (Padding, JavaConcatenate(lineInput, Padding));
  foundTokenSpecs = << >>  ; 
   \* Array records of form [token   |-> string of a token,
   \*                        leftPos |-> location in line of left of token,
   \*                        rightPos   |-> location in line of just to the 
   \*                                    right of token]
  lastToken = FALSE; \* true if there can be no tokens to right of first
                     \* one found
  notLastToken = FALSE;  \* true if we found a "!" to the right of the
                         \* first token found.
  curPos = currentPosition  + JavaLen(Padding) ;
  returnVal; \* Use for returning values from a procedure call.
  tempVar1 ;
  tempVar2 ;
  tempVar3 ;
  
define 
{ 
  FixOrigin(tokarray) ==
  [i \in DOMAIN tokarray |->
           [token |->tokarray[i].token, rightPos |-> tokarray[i].rightPos - JavaLen(Padding), 
            leftPos |-> tokarray[i].leftPos - JavaLen(Padding)]]

};

macro vreturn(val)
{ returnVal := val;
  return;
}

\* Returns the TokenSpec for the token in the array tokArray of
\* Java strings (Java array of 1-character strings) in the line
\* containing the character at position pos, or NullTokenSpec
\* if there is none.
procedure findTokenIn(pos, tokArray) 
  variables i ; tokIdx ;
    { i := 0;
      while (i < JavaLen(tokArray)) 
       { tokIdx := JavaIndex(tokArray[i], line[pos], 0);
         while (tokIdx # -1) 
           { with (ftlft = pos - tokIdx,
                   ftrt = pos - tokIdx + JavaLen(tokArray[i]))
               { if (tokArray[i] = JavaSubseq(line, ftlft, ftrt))
                  { vreturn([token |-> tokArray[i],
                                  leftPos |-> ftlft, rightPos |-> ftrt])
                  };
               };
             tokIdx := JavaIndex(tokArray[i], line[pos], tokIdx+1);
           };
           i := i+1; 
        };
      vreturn(NullTokenSpec);
    }


\* Returns the TokenSpec of the largest token containing digits,
\* letters, and "_" characters containing position pos.  Returns
\* NullTokenSpec if that would be an empty token.
procedure findMaximalIdCharSeq(pos) 
  variables token = << >>; left = pos; rt = pos;
  { \* token := << >>;
    \* left := pos;
    while (line[left-1] \in IdChar)
      { left := left-1; 
      };
    while (line[rt] \in IdChar)
     { rt := rt+1
     };
   if (left = rt)
     { vreturn(NullTokenSpec) }
   else
     { vreturn([token |-> JavaSubseq(line, left, rt), 
                leftPos |-> left, rightPos |-> rt])
     }
  } 

\* Returns the position of the left paren matching a ")" at pos-1.
\* If there is none, it returns -1.
procedure findMatchingLeftParen(pos) 
{ if (line[pos-1] # ")") {vreturn(pos)};
  call findMatchingLeftInner(pos, 0);
  return;
 }

procedure findMatchingLeftInner(pos, delim) 
 variables ipos = pos; jdelim; delimLen;
{ delimLen := JavaLen(LeftDelimiters[delim]);
  ipos := pos - delimLen;
  while (JavaSubseq(line, ipos-delimLen, ipos) # LeftDelimiters[delim])
   { if (line[ipos-1] = ";") {vreturn(-1)};
     ipos := ipos-1;
     jdelim := 0;
     while (jdelim < JavaLen(LeftDelimiters))
      { if (JavaSubseq(line, ipos-delimLen, ipos) = RightDelimiters[jdelim])
         { call findMatchingLeftInner(ipos, jdelim);
           ipos := returnVal;
           if (ipos < 0) { vreturn(-1)};
           jdelim := 99 ; \* exit while loop
         };
        jdelim := jdelim+1;
      }
   };
   vreturn(ipos-delimLen);
 }

\* Returns the position of the right paren matching a "(" at position pos.
\* If there is none, it returns -1.
procedure findMatchingRightParen(pos) 
{ if (line[pos] # "(") {vreturn(pos)};
  call findMatchingRightInner(pos, 0);
  return;
 }

procedure findMatchingRightInner(pos, delim) 
 variables ipos = pos; jdelim; delimLen; 
{ delimLen := JavaLen(RightDelimiters[delim]);
  ipos := pos + delimLen;
  while (JavaSubseq(line, ipos, ipos+delimLen) # RightDelimiters[delim])
   { if (line[ipos] = ";") {vreturn(-1)};
     ipos := ipos+1;
     jdelim := 0;
     while (jdelim < JavaLen(RightDelimiters))
      { if (JavaSubseq(line, ipos, ipos+delimLen) = LeftDelimiters[jdelim])
         { call findMatchingRightInner(ipos, jdelim);
           ipos := returnVal;
           if (ipos < 0) { vreturn(-1)};
           jdelim := 99 ; \* exit while loop
         };
        jdelim := jdelim+1;
      }
   };
   vreturn(ipos+delimLen);
 }

\* Assumes that leftTok and rightTok are two TokenSpecs, 
\* possibly NullTokenSpecs, separated by a ">".  Checks
\* if they form a step name.  If so, it returns the
\* TokenSpec for that step name; otherwise it returns
\* NullTokenSpec.
procedure checkIfStepName(leftTok, rightTok)
{ if (leftTok = NullTokenSpec \/ rightTok = NullTokenSpec)
    { vreturn(NullTokenSpec) };
  if ( /\ IsNumber(leftTok.token)
       /\ line[leftTok.leftPos-1] = "<"
       /\ line[leftTok.leftPos-2] # "<" )
     { vreturn( [token |-> JavaSubseq(line, 
                                      leftTok.leftPos-1,
                                      rightTok.rightPos),
                 leftPos |-> leftTok.leftPos-1,
                 rightPos |-> rightTok.rightPos] )
     };
   else { vreturn(NullTokenSpec) };
}
procedure skipLeftOverSpaces() 
{ while (line[curPos-1] = " ") { curPos := curPos - 1; };
  return;
}

procedure skipRightOverSpaces() 
{ while (line[curPos] = " ") { curPos := curPos+1; };
  return;
}

\* Returns a TokenSpec array of possible tokens to be selected
\* when the cursor is at position curPos of line.  It 
\* returns a zero-length array if there are none.
\*
\* Known Bug: This will not work right in some cases when curPos
\* are spaces inside a name, as in
\*
\*    Foo   (x, y)!bar
\*        ^
procedure findTokenSpecs()
variables currentToken; left; rt; notDone; foundBangToken;
temp1; temp2; temp3;
{ \* Try to find the current TokenSpec and put it in foundTokenSpecs, 
  \* leaving curPos to the left of that token.  If the token is a
  \* step name, we can return that single TokenSpec as the spec.  
  \* If it is an unnamed step, or if it is not a possible identifier
  \* or operator symbol, we return << >> (a zero-length array).
  
  \* First, we must check if we may be inside a string of form (" ")^* "!" (" ")^*
  \* and, if so, move to its left, setting notLastToken to TRUE
  if (line[curPos] = " ") 
    { call skipLeftOverSpaces() ;
      if (line[curPos-1] = "!"  /\ line[curPos-2] # "!")
        { notLastToken := TRUE;
          curPos := curPos - 1;
          call skipLeftOverSpaces();
        }
    }
  else if (line[curPos] = "!" /\ line[curPos-1] # "!" /\ line[curPos+1] # "!")
    { notLastToken := TRUE;
      call skipLeftOverSpaces()
    };
    
  \* If we're to the right of a ")", we could be inside something like
  \*
  \*   Foo(42) ! bar
  \*          ^
  \* so we set notLastToken true and move to the left of the parentesized string.
  if ( /\ \/ notLastToken
          \/ line[curPos] = " "
       /\ line[curPos-1] = ")")
    { notLastToken := TRUE;
      call findMatchingLeftParen(curPos);
      if (returnVal < 0) {vreturn(<< >>)};
      curPos := returnVal;
      call skipLeftOverSpaces();
    };
  \* If notLastToken is true, then we should be just to the right
  \* of the token we are expecting to find to the left of the "!" or the
  \* parenthesized expression. 
  \* Otherwise, if we're not at an IdChar or at an operator, then
  \* let's try one character to the left.  
  \* Note: this happens to work if we're right before "<4>7" or "\in"
  \* because both "<" and "\\" are operators.

  if (notLastToken) { curPos := curPos - 1; };
  else 
    { if (line[curPos] \notin IdChar) 
        { call findTokenIn(curPos, Operators);
          if ( returnVal = NullTokenSpec )
            { curPos := curPos - 1
            }
        }

    } ;
\* \* Following code replaced by preceding "else" clause
\*
\*  \* If we didn't move left and we're at a "(" or "." that's not the beginning
\*  \* of an operator, let's move left 1.
\*  if (~ notLastToken /\ line[curPos] = "(")
\*    { call findTokenIn(curPos, ParenOperators);
\*      if (returnVal = NullTokenSpec) { curPos := curPos - 1 }
\*    }
\*  else if ( /\ ~ notLastToken 
\*            /\ line[curPos] = "."
\*            /\ line[curPos+1] # "." 
\*            /\ line[curPos-1] # "." )
\*         { curPos := curPos - 1 };
\*  
\*  \* If we're at a space (which means we haven't found a "!" or moved left
\*  \* over a parenthesized string), then try as if the cursor were
\*  \* one character to the left.
\*  if (line[curPos] = " ") { curPos := curPos - 1};
  
  if (line[curPos] \in IdChar)
    { \* Check if we're at an "X" that is inside an "\X" or "\X".
      \* Note: this works because there are no TeXSymbols besides
      if (line[curPos] = "X") { call findTokenIn(curPos, XSymbols); }
      else {returnVal := NullTokenSpec} ;
      if (returnVal # NullTokenSpec)
        { foundTokenSpecs := JavaSeq(<<returnVal>>);
          curPos := returnVal.leftPos;
          lastToken := TRUE;
         }
      else 
         { call findMaximalIdCharSeq(curPos);
           currentToken := returnVal;
           \* Check if token is part of step name.  If it is, we set
           \* First, see if currentToken could be the token after the "<...>".
           if ( line[currentToken.leftPos-1] = ">" )
             { call findMaximalIdCharSeq(currentToken.leftPos - 1);
               call checkIfStepName(returnVal, currentToken);
               if (returnVal # NullTokenSpec)
                 { foundTokenSpecs := JavaSeq(<<returnVal>>);
                   vreturn(FixOrigin(foundTokenSpecs));
                 }
             };
           \* Next see if it's the token to the left of the ">"
           if (line[currentToken.rightPos] = ">" )
             { call findMaximalIdCharSeq(currentToken.rightPos+1);
               call checkIfStepName(currentToken, returnVal);
               if (returnVal # NullTokenSpec)
                 { foundTokenSpecs := JavaSeq(<<returnVal>>);
                   vreturn(FixOrigin(foundTokenSpecs));
                 }
             };

           \* Next, check if it's a number, and abort if it is.
           if (IsNumber(currentToken.token)) 
             { vreturn(<< >>)
             };
           
           \* Next, check if the token appears as "\\"token, in
           \* which case we adjust currentTok
           left := currentToken.leftPos ;
           rt   := currentToken.rightPos ;
           if ( /\ line[left-1] = "\\" 
                /\ line[left-2] # "\\"
                /\ \E ii \in DOMAIN TeXSymbols :
                         JavaSubseq(line, left-1, rt) = TeXSymbols[ii] )
             { lastToken := TRUE;
               currentToken.leftPos := left - 1 ||
               currentToken.token := JavaSubseq(line, left-1, rt);
             };
           foundTokenSpecs := 
                 JavaSeq( << currentToken >>);
           curPos := left;
         }
    }
  else 
    { call findTokenIn(curPos, Operators);
      currentToken  := returnVal;
      if (currentToken = NullTokenSpec)
        { vreturn(<< >>);
        };
      call findTokenIn(curPos, NonOperators);
      if (returnVal # NullTokenSpec)
        { vreturn(<< >>);
        };

      \* Need to check if beginning or end of level specifier
      \* of step number.  
      if ( currentToken.token = JavaSeq(<< "<" >>) )
        { call findMaximalIdCharSeq(currentToken.rightPos);
          temp1 := returnVal;
          if (/\ temp1 # NullTokenSpec
              /\ line[temp1.rightPos] = ">")
            { call findMaximalIdCharSeq(temp1.rightPos + 1);
              temp2 := returnVal;
              call checkIfStepName(temp1, temp2);
              if (returnVal # NullTokenSpec)
               { foundTokenSpecs := JavaSeq(<<returnVal>>);
                 vreturn(FixOrigin(foundTokenSpecs));
               }
            }
          }
       else if (currentToken.token = JavaSeq(<< ">" >>))
         { call findMaximalIdCharSeq(currentToken.leftPos);
           temp1 := returnVal;
           call findMaximalIdCharSeq(currentToken.rightPos);
           temp2 := returnVal;
           call checkIfStepName(temp1, temp2);
              if (returnVal # NullTokenSpec)
               { foundTokenSpecs := JavaSeq(<<returnVal>>);
                 vreturn(FixOrigin(foundTokenSpecs));
               }
         };

      \* We check for the case of a "\\" starting a TeX token.
      if (currentToken.token = JavaSeq(<<"\\">>))
        { call findMaximalIdCharSeq(currentToken.rightPos);
          if ( /\ returnVal # NullTokenSpec
               /\ \E ii \in DOMAIN TeXSymbols :
                         JavaSubseq(line, 
                                    currentToken.leftPos, 
                                    returnVal.rightPos) = TeXSymbols[ii] )
            { currentToken.rightPos := returnVal.rightPos ||
              currentToken.token := JavaSubseq(line, 
                                    currentToken.leftPos, 
                                    returnVal.rightPos) 
            }
        };

      foundTokenSpecs := JavaSeq(<<currentToken>>);
      curPos := currentToken.leftPos;
      lastToken := TRUE;
     };

  assert JavaLen(foundTokenSpecs) = 1;

\*print <<"1", foundTokenSpecs[0]>>;
  \** We have now found the base token.  We now look to find extenders
  \*  to the left of the form  idtoken "!".  These must be part of the
  \*  name, so we prepend them to foundTokenSpecs[0].
  curPos := foundTokenSpecs[0].leftPos;
  notDone := TRUE;
  while (notDone) 
    { call skipLeftOverSpaces();
      if (curPos <  0 \/ line[curPos-1] = ";") 
        { notDone := FALSE; }
      else
        { if (line[curPos-1] = "!" /\ (line[curPos-2] # "!"))
            { curPos := curPos - 1;
              call skipLeftOverSpaces();
              call findMatchingLeftParen(curPos);
              curPos := returnVal;
              if (curPos < 0) { notDone := FALSE }
              else 
                { call skipLeftOverSpaces();
                  call findMaximalIdCharSeq(curPos);
                  currentToken := returnVal ;
                  if ( \/ currentToken = NullTokenSpec
                       \/ IsNumber(currentToken.token) )
                    { notDone := FALSE }
                  else
                    { curPos := currentToken.leftPos;
                      foundTokenSpecs[0] := 
                             [token |-> JavaConcatenate(
                                            JavaAppend(currentToken.token, "!"),
                                            foundTokenSpecs[0].token),
                              leftPos |-> curPos, 
                              rightPos |-> foundTokenSpecs[0].rightPos];
                    }
               }
             }
         else {notDone := FALSE;}
       };
       
    };

  assert foundTokenSpecs # << >> ;

  if (lastToken = TRUE) {vreturn(FixOrigin(foundTokenSpecs))};
  
\*  print <<"2", foundTokenSpecs[0]>>;
  
  curPos := foundTokenSpecs[0].rightPos;
  foundBangToken := FALSE;
  notDone := TRUE;
  while (notDone) 
    { call skipRightOverSpaces();
      call findMatchingRightParen(curPos);
      curPos := returnVal;
      if (curPos < 0) {notDone := FALSE}
      else
        { call skipRightOverSpaces();
          if (line[curPos] # "!"  \/ line[curPos+1] = "!")
            { notDone := FALSE } 
          else
            { curPos := curPos + 1;
              call skipRightOverSpaces();
              call findMaximalIdCharSeq(curPos);
              currentToken := returnVal ;
              if ( \/ currentToken = NullTokenSpec
                   \/ IsNumber(currentToken.token) )
                { notDone := FALSE }
              else
                { foundBangToken := TRUE;
                  foundTokenSpecs :=
                    JavaConcatenate(
                      JavaSeq( 
                        << [token |-> 
                              JavaConcatenate(JavaAppend(foundTokenSpecs[0].token,
                                                          "!"),
                                              currentToken.token),
                            leftPos |-> foundTokenSpecs[0].leftPos,
                            rightPos |-> currentToken.rightPos]
                         >> ) ,
                        foundTokenSpecs); 
                  curPos := currentToken.rightPos;
                }
            }
        }
    };

  if (notLastToken /\ ~ foundBangToken) { vreturn (<< >>) };

  vreturn(FixOrigin(foundTokenSpecs));
} \* end findTokenSpecs

\* Main Body:
{ curPos := JavaLen(Padding);
  tempVar1 := (-1 :> "");
  tempVar2 := JavaLen(Padding);
\*curPos := 15;
\*call findTokenSpecs();
\*print returnVal;
  print line;
  while (tempVar2 < JavaLen(lineInput) + JavaLen(Padding))
    { print <<"curPos: ", tempVar2>>;
      curPos := tempVar2;
      foundTokenSpecs := << >>  ;
      lastToken := FALSE;
      notLastToken := FALSE;
      call findTokenSpecs();
\*      if (tempVar2 >= 0 + JavaLen(Padding))
\*        { print "done with run" ;
\*          assert FALSE
\*        };
      if (returnVal = tempVar1)
        { print "same" \* ,"lastToken: ", lastToken, ", notLastToken: ", notLastToken>> 
        }
      else 
        { print returnVal;
   \*          print <<"lastToken: ", lastToken, ", notLastToken: ", notLastToken>>;
        };
      tempVar1 := returnVal;
      tempVar2 := tempVar2 + 1;
    };
  print "goodby world";

} \* end Main Body
} \* End algorithm
  
*****************************************************************************************)
\* BEGIN TRANSLATION
\* Procedure variable left of procedure findMaximalIdCharSeq at line 316 col 28 changed to left_
\* Procedure variable rt of procedure findMaximalIdCharSeq at line 316 col 40 changed to rt_
\* Procedure variable ipos of procedure findMatchingLeftInner at line 342 col 12 changed to ipos_
\* Procedure variable jdelim of procedure findMatchingLeftInner at line 342 col 24 changed to jdelim_
\* Procedure variable delimLen of procedure findMatchingLeftInner at line 342 col 32 changed to delimLen_
\* Parameter pos of procedure findTokenIn at line 291 col 23 changed to pos_
\* Parameter pos of procedure findMaximalIdCharSeq at line 315 col 32 changed to pos_f
\* Parameter pos of procedure findMatchingLeftParen at line 335 col 33 changed to pos_fi
\* Parameter pos of procedure findMatchingLeftInner at line 341 col 33 changed to pos_fin
\* Parameter delim of procedure findMatchingLeftInner at line 341 col 38 changed to delim_
\* Parameter pos of procedure findMatchingRightParen at line 364 col 34 changed to pos_find
CONSTANT defaultInitValue
VARIABLES line, foundTokenSpecs, lastToken, notLastToken, curPos, returnVal, 
          tempVar1, tempVar2, tempVar3, pc, stack

(* define statement *)
FixOrigin(tokarray) ==
[i \in DOMAIN tokarray |->
         [token |->tokarray[i].token, rightPos |-> tokarray[i].rightPos - JavaLen(Padding),
          leftPos |-> tokarray[i].leftPos - JavaLen(Padding)]]

VARIABLES pos_, tokArray, i, tokIdx, pos_f, token, left_, rt_, pos_fi, 
          pos_fin, delim_, ipos_, jdelim_, delimLen_, pos_find, pos, delim, 
          ipos, jdelim, delimLen, leftTok, rightTok, currentToken, left, rt, 
          notDone, foundBangToken, temp1, temp2, temp3

vars == << line, foundTokenSpecs, lastToken, notLastToken, curPos, returnVal, 
           tempVar1, tempVar2, tempVar3, pc, stack, pos_, tokArray, i, tokIdx, 
           pos_f, token, left_, rt_, pos_fi, pos_fin, delim_, ipos_, jdelim_, 
           delimLen_, pos_find, pos, delim, ipos, jdelim, delimLen, leftTok, 
           rightTok, currentToken, left, rt, notDone, foundBangToken, temp1, 
           temp2, temp3 >>

Init == (* Global variables *)
        /\ line = JavaConcatenate (Padding, JavaConcatenate(lineInput, Padding))
        /\ foundTokenSpecs = << >>
        /\ lastToken = FALSE
        /\ notLastToken = FALSE
        /\ curPos = currentPosition  + JavaLen(Padding)
        /\ returnVal = defaultInitValue
        /\ tempVar1 = defaultInitValue
        /\ tempVar2 = defaultInitValue
        /\ tempVar3 = defaultInitValue
        (* Procedure findTokenIn *)
        /\ pos_ = defaultInitValue
        /\ tokArray = defaultInitValue
        /\ i = defaultInitValue
        /\ tokIdx = defaultInitValue
        (* Procedure findMaximalIdCharSeq *)
        /\ pos_f = defaultInitValue
        /\ token = << >>
        /\ left_ = pos_f
        /\ rt_ = pos_f
        (* Procedure findMatchingLeftParen *)
        /\ pos_fi = defaultInitValue
        (* Procedure findMatchingLeftInner *)
        /\ pos_fin = defaultInitValue
        /\ delim_ = defaultInitValue
        /\ ipos_ = pos_fin
        /\ jdelim_ = defaultInitValue
        /\ delimLen_ = defaultInitValue
        (* Procedure findMatchingRightParen *)
        /\ pos_find = defaultInitValue
        (* Procedure findMatchingRightInner *)
        /\ pos = defaultInitValue
        /\ delim = defaultInitValue
        /\ ipos = pos
        /\ jdelim = defaultInitValue
        /\ delimLen = defaultInitValue
        (* Procedure checkIfStepName *)
        /\ leftTok = defaultInitValue
        /\ rightTok = defaultInitValue
        (* Procedure findTokenSpecs *)
        /\ currentToken = defaultInitValue
        /\ left = defaultInitValue
        /\ rt = defaultInitValue
        /\ notDone = defaultInitValue
        /\ foundBangToken = defaultInitValue
        /\ temp1 = defaultInitValue
        /\ temp2 = defaultInitValue
        /\ temp3 = defaultInitValue
        /\ stack = << >>
        /\ pc = "Lbl_77"

Lbl_1 == /\ pc = "Lbl_1"
         /\ i' = 0
         /\ pc' = "Lbl_2"
         /\ UNCHANGED << line, foundTokenSpecs, lastToken, notLastToken, 
                         curPos, returnVal, tempVar1, tempVar2, tempVar3, 
                         stack, pos_, tokArray, tokIdx, pos_f, token, left_, 
                         rt_, pos_fi, pos_fin, delim_, ipos_, jdelim_, 
                         delimLen_, pos_find, pos, delim, ipos, jdelim, 
                         delimLen, leftTok, rightTok, currentToken, left, rt, 
                         notDone, foundBangToken, temp1, temp2, temp3 >>

Lbl_2 == /\ pc = "Lbl_2"
         /\ IF i < JavaLen(tokArray)
               THEN /\ tokIdx' = JavaIndex(tokArray[i], line[pos_], 0)
                    /\ pc' = "Lbl_3"
                    /\ UNCHANGED << returnVal, stack, pos_, tokArray, i >>
               ELSE /\ returnVal' = NullTokenSpec
                    /\ pc' = Head(stack).pc
                    /\ i' = Head(stack).i
                    /\ tokIdx' = Head(stack).tokIdx
                    /\ pos_' = Head(stack).pos_
                    /\ tokArray' = Head(stack).tokArray
                    /\ stack' = Tail(stack)
         /\ UNCHANGED << line, foundTokenSpecs, lastToken, notLastToken, 
                         curPos, tempVar1, tempVar2, tempVar3, pos_f, token, 
                         left_, rt_, pos_fi, pos_fin, delim_, ipos_, jdelim_, 
                         delimLen_, pos_find, pos, delim, ipos, jdelim, 
                         delimLen, leftTok, rightTok, currentToken, left, rt, 
                         notDone, foundBangToken, temp1, temp2, temp3 >>

Lbl_3 == /\ pc = "Lbl_3"
         /\ IF tokIdx # -1
               THEN /\ LET ftlft == pos_ - tokIdx IN
                         LET ftrt == pos_ - tokIdx + JavaLen(tokArray[i]) IN
                           IF tokArray[i] = JavaSubseq(line, ftlft, ftrt)
                              THEN /\ returnVal' = [token |-> tokArray[i],
                                                         leftPos |-> ftlft, rightPos |-> ftrt]
                                   /\ pc' = Head(stack).pc
                                   /\ i' = Head(stack).i
                                   /\ tokIdx' = Head(stack).tokIdx
                                   /\ pos_' = Head(stack).pos_
                                   /\ tokArray' = Head(stack).tokArray
                                   /\ stack' = Tail(stack)
                              ELSE /\ pc' = "Lbl_4"
                                   /\ UNCHANGED << returnVal, stack, pos_, 
                                                   tokArray, i, tokIdx >>
               ELSE /\ i' = i+1
                    /\ pc' = "Lbl_2"
                    /\ UNCHANGED << returnVal, stack, pos_, tokArray, tokIdx >>
         /\ UNCHANGED << line, foundTokenSpecs, lastToken, notLastToken, 
                         curPos, tempVar1, tempVar2, tempVar3, pos_f, token, 
                         left_, rt_, pos_fi, pos_fin, delim_, ipos_, jdelim_, 
                         delimLen_, pos_find, pos, delim, ipos, jdelim, 
                         delimLen, leftTok, rightTok, currentToken, left, rt, 
                         notDone, foundBangToken, temp1, temp2, temp3 >>

Lbl_4 == /\ pc = "Lbl_4"
         /\ tokIdx' = JavaIndex(tokArray[i], line[pos_], tokIdx+1)
         /\ pc' = "Lbl_3"
         /\ UNCHANGED << line, foundTokenSpecs, lastToken, notLastToken, 
                         curPos, returnVal, tempVar1, tempVar2, tempVar3, 
                         stack, pos_, tokArray, i, pos_f, token, left_, rt_, 
                         pos_fi, pos_fin, delim_, ipos_, jdelim_, delimLen_, 
                         pos_find, pos, delim, ipos, jdelim, delimLen, leftTok, 
                         rightTok, currentToken, left, rt, notDone, 
                         foundBangToken, temp1, temp2, temp3 >>

findTokenIn == Lbl_1 \/ Lbl_2 \/ Lbl_3 \/ Lbl_4

Lbl_5 == /\ pc = "Lbl_5"
         /\ IF line[left_-1] \in IdChar
               THEN /\ left_' = left_-1
                    /\ pc' = "Lbl_5"
               ELSE /\ pc' = "Lbl_6"
                    /\ UNCHANGED left_
         /\ UNCHANGED << line, foundTokenSpecs, lastToken, notLastToken, 
                         curPos, returnVal, tempVar1, tempVar2, tempVar3, 
                         stack, pos_, tokArray, i, tokIdx, pos_f, token, rt_, 
                         pos_fi, pos_fin, delim_, ipos_, jdelim_, delimLen_, 
                         pos_find, pos, delim, ipos, jdelim, delimLen, leftTok, 
                         rightTok, currentToken, left, rt, notDone, 
                         foundBangToken, temp1, temp2, temp3 >>

Lbl_6 == /\ pc = "Lbl_6"
         /\ IF line[rt_] \in IdChar
               THEN /\ rt_' = rt_+1
                    /\ pc' = "Lbl_6"
                    /\ UNCHANGED << returnVal, stack, pos_f, token, left_ >>
               ELSE /\ IF left_ = rt_
                          THEN /\ returnVal' = NullTokenSpec
                               /\ pc' = Head(stack).pc
                               /\ token' = Head(stack).token
                               /\ left_' = Head(stack).left_
                               /\ rt_' = Head(stack).rt_
                               /\ pos_f' = Head(stack).pos_f
                               /\ stack' = Tail(stack)
                          ELSE /\ returnVal' = [token |-> JavaSubseq(line, left_, rt_),
                                                leftPos |-> left_, rightPos |-> rt_]
                               /\ pc' = Head(stack).pc
                               /\ token' = Head(stack).token
                               /\ left_' = Head(stack).left_
                               /\ rt_' = Head(stack).rt_
                               /\ pos_f' = Head(stack).pos_f
                               /\ stack' = Tail(stack)
         /\ UNCHANGED << line, foundTokenSpecs, lastToken, notLastToken, 
                         curPos, tempVar1, tempVar2, tempVar3, pos_, tokArray, 
                         i, tokIdx, pos_fi, pos_fin, delim_, ipos_, jdelim_, 
                         delimLen_, pos_find, pos, delim, ipos, jdelim, 
                         delimLen, leftTok, rightTok, currentToken, left, rt, 
                         notDone, foundBangToken, temp1, temp2, temp3 >>

findMaximalIdCharSeq == Lbl_5 \/ Lbl_6

Lbl_7 == /\ pc = "Lbl_7"
         /\ IF line[pos_fi-1] # ")"
               THEN /\ returnVal' = pos_fi
                    /\ pc' = Head(stack).pc
                    /\ pos_fi' = Head(stack).pos_fi
                    /\ stack' = Tail(stack)
               ELSE /\ pc' = "Lbl_8"
                    /\ UNCHANGED << returnVal, stack, pos_fi >>
         /\ UNCHANGED << line, foundTokenSpecs, lastToken, notLastToken, 
                         curPos, tempVar1, tempVar2, tempVar3, pos_, tokArray, 
                         i, tokIdx, pos_f, token, left_, rt_, pos_fin, delim_, 
                         ipos_, jdelim_, delimLen_, pos_find, pos, delim, ipos, 
                         jdelim, delimLen, leftTok, rightTok, currentToken, 
                         left, rt, notDone, foundBangToken, temp1, temp2, 
                         temp3 >>

Lbl_8 == /\ pc = "Lbl_8"
         /\ /\ delim_' = 0
            /\ pos_fin' = pos_fi
            /\ stack' = << [ procedure |->  "findMatchingLeftInner",
                             pc        |->  Head(stack).pc,
                             ipos_     |->  ipos_,
                             jdelim_   |->  jdelim_,
                             delimLen_ |->  delimLen_,
                             pos_fin   |->  pos_fin,
                             delim_    |->  delim_ ] >>
                         \o Tail(stack)
         /\ ipos_' = pos_fin'
         /\ jdelim_' = defaultInitValue
         /\ delimLen_' = defaultInitValue
         /\ pc' = "Lbl_9"
         /\ UNCHANGED << line, foundTokenSpecs, lastToken, notLastToken, 
                         curPos, returnVal, tempVar1, tempVar2, tempVar3, pos_, 
                         tokArray, i, tokIdx, pos_f, token, left_, rt_, pos_fi, 
                         pos_find, pos, delim, ipos, jdelim, delimLen, leftTok, 
                         rightTok, currentToken, left, rt, notDone, 
                         foundBangToken, temp1, temp2, temp3 >>

findMatchingLeftParen == Lbl_7 \/ Lbl_8

Lbl_9 == /\ pc = "Lbl_9"
         /\ delimLen_' = JavaLen(LeftDelimiters[delim_])
         /\ ipos_' = pos_fin - delimLen_'
         /\ pc' = "Lbl_10"
         /\ UNCHANGED << line, foundTokenSpecs, lastToken, notLastToken, 
                         curPos, returnVal, tempVar1, tempVar2, tempVar3, 
                         stack, pos_, tokArray, i, tokIdx, pos_f, token, left_, 
                         rt_, pos_fi, pos_fin, delim_, jdelim_, pos_find, pos, 
                         delim, ipos, jdelim, delimLen, leftTok, rightTok, 
                         currentToken, left, rt, notDone, foundBangToken, 
                         temp1, temp2, temp3 >>

Lbl_10 == /\ pc = "Lbl_10"
          /\ IF JavaSubseq(line, ipos_-delimLen_, ipos_) # LeftDelimiters[delim_]
                THEN /\ IF line[ipos_-1] = ";"
                           THEN /\ returnVal' = -1
                                /\ pc' = Head(stack).pc
                                /\ ipos_' = Head(stack).ipos_
                                /\ jdelim_' = Head(stack).jdelim_
                                /\ delimLen_' = Head(stack).delimLen_
                                /\ pos_fin' = Head(stack).pos_fin
                                /\ delim_' = Head(stack).delim_
                                /\ stack' = Tail(stack)
                           ELSE /\ pc' = "Lbl_11"
                                /\ UNCHANGED << returnVal, stack, pos_fin, 
                                                delim_, ipos_, jdelim_, 
                                                delimLen_ >>
                ELSE /\ returnVal' = ipos_-delimLen_
                     /\ pc' = Head(stack).pc
                     /\ ipos_' = Head(stack).ipos_
                     /\ jdelim_' = Head(stack).jdelim_
                     /\ delimLen_' = Head(stack).delimLen_
                     /\ pos_fin' = Head(stack).pos_fin
                     /\ delim_' = Head(stack).delim_
                     /\ stack' = Tail(stack)
          /\ UNCHANGED << line, foundTokenSpecs, lastToken, notLastToken, 
                          curPos, tempVar1, tempVar2, tempVar3, pos_, tokArray, 
                          i, tokIdx, pos_f, token, left_, rt_, pos_fi, 
                          pos_find, pos, delim, ipos, jdelim, delimLen, 
                          leftTok, rightTok, currentToken, left, rt, notDone, 
                          foundBangToken, temp1, temp2, temp3 >>

Lbl_11 == /\ pc = "Lbl_11"
          /\ ipos_' = ipos_-1
          /\ jdelim_' = 0
          /\ pc' = "Lbl_12"
          /\ UNCHANGED << line, foundTokenSpecs, lastToken, notLastToken, 
                          curPos, returnVal, tempVar1, tempVar2, tempVar3, 
                          stack, pos_, tokArray, i, tokIdx, pos_f, token, 
                          left_, rt_, pos_fi, pos_fin, delim_, delimLen_, 
                          pos_find, pos, delim, ipos, jdelim, delimLen, 
                          leftTok, rightTok, currentToken, left, rt, notDone, 
                          foundBangToken, temp1, temp2, temp3 >>

Lbl_12 == /\ pc = "Lbl_12"
          /\ IF jdelim_ < JavaLen(LeftDelimiters)
                THEN /\ IF JavaSubseq(line, ipos_-delimLen_, ipos_) = RightDelimiters[jdelim_]
                           THEN /\ /\ delim_' = jdelim_
                                   /\ pos_fin' = ipos_
                                   /\ stack' = << [ procedure |->  "findMatchingLeftInner",
                                                    pc        |->  "Lbl_13",
                                                    ipos_     |->  ipos_,
                                                    jdelim_   |->  jdelim_,
                                                    delimLen_ |->  delimLen_,
                                                    pos_fin   |->  pos_fin,
                                                    delim_    |->  delim_ ] >>
                                                \o stack
                                /\ ipos_' = pos_fin'
                                /\ jdelim_' = defaultInitValue
                                /\ delimLen_' = defaultInitValue
                                /\ pc' = "Lbl_9"
                           ELSE /\ pc' = "Lbl_16"
                                /\ UNCHANGED << stack, pos_fin, delim_, ipos_, 
                                                jdelim_, delimLen_ >>
                ELSE /\ pc' = "Lbl_10"
                     /\ UNCHANGED << stack, pos_fin, delim_, ipos_, jdelim_, 
                                     delimLen_ >>
          /\ UNCHANGED << line, foundTokenSpecs, lastToken, notLastToken, 
                          curPos, returnVal, tempVar1, tempVar2, tempVar3, 
                          pos_, tokArray, i, tokIdx, pos_f, token, left_, rt_, 
                          pos_fi, pos_find, pos, delim, ipos, jdelim, delimLen, 
                          leftTok, rightTok, currentToken, left, rt, notDone, 
                          foundBangToken, temp1, temp2, temp3 >>

Lbl_16 == /\ pc = "Lbl_16"
          /\ jdelim_' = jdelim_+1
          /\ pc' = "Lbl_12"
          /\ UNCHANGED << line, foundTokenSpecs, lastToken, notLastToken, 
                          curPos, returnVal, tempVar1, tempVar2, tempVar3, 
                          stack, pos_, tokArray, i, tokIdx, pos_f, token, 
                          left_, rt_, pos_fi, pos_fin, delim_, ipos_, 
                          delimLen_, pos_find, pos, delim, ipos, jdelim, 
                          delimLen, leftTok, rightTok, currentToken, left, rt, 
                          notDone, foundBangToken, temp1, temp2, temp3 >>

Lbl_13 == /\ pc = "Lbl_13"
          /\ ipos_' = returnVal
          /\ IF ipos_' < 0
                THEN /\ returnVal' = -1
                     /\ pc' = "Lbl_14"
                ELSE /\ pc' = "Lbl_15"
                     /\ UNCHANGED returnVal
          /\ UNCHANGED << line, foundTokenSpecs, lastToken, notLastToken, 
                          curPos, tempVar1, tempVar2, tempVar3, stack, pos_, 
                          tokArray, i, tokIdx, pos_f, token, left_, rt_, 
                          pos_fi, pos_fin, delim_, jdelim_, delimLen_, 
                          pos_find, pos, delim, ipos, jdelim, delimLen, 
                          leftTok, rightTok, currentToken, left, rt, notDone, 
                          foundBangToken, temp1, temp2, temp3 >>

Lbl_14 == /\ pc = "Lbl_14"
          /\ pc' = Head(stack).pc
          /\ ipos_' = Head(stack).ipos_
          /\ jdelim_' = Head(stack).jdelim_
          /\ delimLen_' = Head(stack).delimLen_
          /\ pos_fin' = Head(stack).pos_fin
          /\ delim_' = Head(stack).delim_
          /\ stack' = Tail(stack)
          /\ UNCHANGED << line, foundTokenSpecs, lastToken, notLastToken, 
                          curPos, returnVal, tempVar1, tempVar2, tempVar3, 
                          pos_, tokArray, i, tokIdx, pos_f, token, left_, rt_, 
                          pos_fi, pos_find, pos, delim, ipos, jdelim, delimLen, 
                          leftTok, rightTok, currentToken, left, rt, notDone, 
                          foundBangToken, temp1, temp2, temp3 >>

Lbl_15 == /\ pc = "Lbl_15"
          /\ jdelim_' = 99
          /\ pc' = "Lbl_16"
          /\ UNCHANGED << line, foundTokenSpecs, lastToken, notLastToken, 
                          curPos, returnVal, tempVar1, tempVar2, tempVar3, 
                          stack, pos_, tokArray, i, tokIdx, pos_f, token, 
                          left_, rt_, pos_fi, pos_fin, delim_, ipos_, 
                          delimLen_, pos_find, pos, delim, ipos, jdelim, 
                          delimLen, leftTok, rightTok, currentToken, left, rt, 
                          notDone, foundBangToken, temp1, temp2, temp3 >>

findMatchingLeftInner == Lbl_9 \/ Lbl_10 \/ Lbl_11 \/ Lbl_12 \/ Lbl_16
                            \/ Lbl_13 \/ Lbl_14 \/ Lbl_15

Lbl_17 == /\ pc = "Lbl_17"
          /\ IF line[pos_find] # "("
                THEN /\ returnVal' = pos_find
                     /\ pc' = Head(stack).pc
                     /\ pos_find' = Head(stack).pos_find
                     /\ stack' = Tail(stack)
                ELSE /\ pc' = "Lbl_18"
                     /\ UNCHANGED << returnVal, stack, pos_find >>
          /\ UNCHANGED << line, foundTokenSpecs, lastToken, notLastToken, 
                          curPos, tempVar1, tempVar2, tempVar3, pos_, tokArray, 
                          i, tokIdx, pos_f, token, left_, rt_, pos_fi, pos_fin, 
                          delim_, ipos_, jdelim_, delimLen_, pos, delim, ipos, 
                          jdelim, delimLen, leftTok, rightTok, currentToken, 
                          left, rt, notDone, foundBangToken, temp1, temp2, 
                          temp3 >>

Lbl_18 == /\ pc = "Lbl_18"
          /\ /\ delim' = 0
             /\ pos' = pos_find
             /\ stack' = << [ procedure |->  "findMatchingRightInner",
                              pc        |->  Head(stack).pc,
                              ipos      |->  ipos,
                              jdelim    |->  jdelim,
                              delimLen  |->  delimLen,
                              pos       |->  pos,
                              delim     |->  delim ] >>
                          \o Tail(stack)
          /\ ipos' = pos'
          /\ jdelim' = defaultInitValue
          /\ delimLen' = defaultInitValue
          /\ pc' = "Lbl_19"
          /\ UNCHANGED << line, foundTokenSpecs, lastToken, notLastToken, 
                          curPos, returnVal, tempVar1, tempVar2, tempVar3, 
                          pos_, tokArray, i, tokIdx, pos_f, token, left_, rt_, 
                          pos_fi, pos_fin, delim_, ipos_, jdelim_, delimLen_, 
                          pos_find, leftTok, rightTok, currentToken, left, rt, 
                          notDone, foundBangToken, temp1, temp2, temp3 >>

findMatchingRightParen == Lbl_17 \/ Lbl_18

Lbl_19 == /\ pc = "Lbl_19"
          /\ delimLen' = JavaLen(RightDelimiters[delim])
          /\ ipos' = pos + delimLen'
          /\ pc' = "Lbl_20"
          /\ UNCHANGED << line, foundTokenSpecs, lastToken, notLastToken, 
                          curPos, returnVal, tempVar1, tempVar2, tempVar3, 
                          stack, pos_, tokArray, i, tokIdx, pos_f, token, 
                          left_, rt_, pos_fi, pos_fin, delim_, ipos_, jdelim_, 
                          delimLen_, pos_find, pos, delim, jdelim, leftTok, 
                          rightTok, currentToken, left, rt, notDone, 
                          foundBangToken, temp1, temp2, temp3 >>

Lbl_20 == /\ pc = "Lbl_20"
          /\ IF JavaSubseq(line, ipos, ipos+delimLen) # RightDelimiters[delim]
                THEN /\ IF line[ipos] = ";"
                           THEN /\ returnVal' = -1
                                /\ pc' = Head(stack).pc
                                /\ ipos' = Head(stack).ipos
                                /\ jdelim' = Head(stack).jdelim
                                /\ delimLen' = Head(stack).delimLen
                                /\ pos' = Head(stack).pos
                                /\ delim' = Head(stack).delim
                                /\ stack' = Tail(stack)
                           ELSE /\ pc' = "Lbl_21"
                                /\ UNCHANGED << returnVal, stack, pos, delim, 
                                                ipos, jdelim, delimLen >>
                ELSE /\ returnVal' = ipos+delimLen
                     /\ pc' = Head(stack).pc
                     /\ ipos' = Head(stack).ipos
                     /\ jdelim' = Head(stack).jdelim
                     /\ delimLen' = Head(stack).delimLen
                     /\ pos' = Head(stack).pos
                     /\ delim' = Head(stack).delim
                     /\ stack' = Tail(stack)
          /\ UNCHANGED << line, foundTokenSpecs, lastToken, notLastToken, 
                          curPos, tempVar1, tempVar2, tempVar3, pos_, tokArray, 
                          i, tokIdx, pos_f, token, left_, rt_, pos_fi, pos_fin, 
                          delim_, ipos_, jdelim_, delimLen_, pos_find, leftTok, 
                          rightTok, currentToken, left, rt, notDone, 
                          foundBangToken, temp1, temp2, temp3 >>

Lbl_21 == /\ pc = "Lbl_21"
          /\ ipos' = ipos+1
          /\ jdelim' = 0
          /\ pc' = "Lbl_22"
          /\ UNCHANGED << line, foundTokenSpecs, lastToken, notLastToken, 
                          curPos, returnVal, tempVar1, tempVar2, tempVar3, 
                          stack, pos_, tokArray, i, tokIdx, pos_f, token, 
                          left_, rt_, pos_fi, pos_fin, delim_, ipos_, jdelim_, 
                          delimLen_, pos_find, pos, delim, delimLen, leftTok, 
                          rightTok, currentToken, left, rt, notDone, 
                          foundBangToken, temp1, temp2, temp3 >>

Lbl_22 == /\ pc = "Lbl_22"
          /\ IF jdelim < JavaLen(RightDelimiters)
                THEN /\ IF JavaSubseq(line, ipos, ipos+delimLen) = LeftDelimiters[jdelim]
                           THEN /\ /\ delim' = jdelim
                                   /\ pos' = ipos
                                   /\ stack' = << [ procedure |->  "findMatchingRightInner",
                                                    pc        |->  "Lbl_23",
                                                    ipos      |->  ipos,
                                                    jdelim    |->  jdelim,
                                                    delimLen  |->  delimLen,
                                                    pos       |->  pos,
                                                    delim     |->  delim ] >>
                                                \o stack
                                /\ ipos' = pos'
                                /\ jdelim' = defaultInitValue
                                /\ delimLen' = defaultInitValue
                                /\ pc' = "Lbl_19"
                           ELSE /\ pc' = "Lbl_26"
                                /\ UNCHANGED << stack, pos, delim, ipos, 
                                                jdelim, delimLen >>
                ELSE /\ pc' = "Lbl_20"
                     /\ UNCHANGED << stack, pos, delim, ipos, jdelim, delimLen >>
          /\ UNCHANGED << line, foundTokenSpecs, lastToken, notLastToken, 
                          curPos, returnVal, tempVar1, tempVar2, tempVar3, 
                          pos_, tokArray, i, tokIdx, pos_f, token, left_, rt_, 
                          pos_fi, pos_fin, delim_, ipos_, jdelim_, delimLen_, 
                          pos_find, leftTok, rightTok, currentToken, left, rt, 
                          notDone, foundBangToken, temp1, temp2, temp3 >>

Lbl_26 == /\ pc = "Lbl_26"
          /\ jdelim' = jdelim+1
          /\ pc' = "Lbl_22"
          /\ UNCHANGED << line, foundTokenSpecs, lastToken, notLastToken, 
                          curPos, returnVal, tempVar1, tempVar2, tempVar3, 
                          stack, pos_, tokArray, i, tokIdx, pos_f, token, 
                          left_, rt_, pos_fi, pos_fin, delim_, ipos_, jdelim_, 
                          delimLen_, pos_find, pos, delim, ipos, delimLen, 
                          leftTok, rightTok, currentToken, left, rt, notDone, 
                          foundBangToken, temp1, temp2, temp3 >>

Lbl_23 == /\ pc = "Lbl_23"
          /\ ipos' = returnVal
          /\ IF ipos' < 0
                THEN /\ returnVal' = -1
                     /\ pc' = "Lbl_24"
                ELSE /\ pc' = "Lbl_25"
                     /\ UNCHANGED returnVal
          /\ UNCHANGED << line, foundTokenSpecs, lastToken, notLastToken, 
                          curPos, tempVar1, tempVar2, tempVar3, stack, pos_, 
                          tokArray, i, tokIdx, pos_f, token, left_, rt_, 
                          pos_fi, pos_fin, delim_, ipos_, jdelim_, delimLen_, 
                          pos_find, pos, delim, jdelim, delimLen, leftTok, 
                          rightTok, currentToken, left, rt, notDone, 
                          foundBangToken, temp1, temp2, temp3 >>

Lbl_24 == /\ pc = "Lbl_24"
          /\ pc' = Head(stack).pc
          /\ ipos' = Head(stack).ipos
          /\ jdelim' = Head(stack).jdelim
          /\ delimLen' = Head(stack).delimLen
          /\ pos' = Head(stack).pos
          /\ delim' = Head(stack).delim
          /\ stack' = Tail(stack)
          /\ UNCHANGED << line, foundTokenSpecs, lastToken, notLastToken, 
                          curPos, returnVal, tempVar1, tempVar2, tempVar3, 
                          pos_, tokArray, i, tokIdx, pos_f, token, left_, rt_, 
                          pos_fi, pos_fin, delim_, ipos_, jdelim_, delimLen_, 
                          pos_find, leftTok, rightTok, currentToken, left, rt, 
                          notDone, foundBangToken, temp1, temp2, temp3 >>

Lbl_25 == /\ pc = "Lbl_25"
          /\ jdelim' = 99
          /\ pc' = "Lbl_26"
          /\ UNCHANGED << line, foundTokenSpecs, lastToken, notLastToken, 
                          curPos, returnVal, tempVar1, tempVar2, tempVar3, 
                          stack, pos_, tokArray, i, tokIdx, pos_f, token, 
                          left_, rt_, pos_fi, pos_fin, delim_, ipos_, jdelim_, 
                          delimLen_, pos_find, pos, delim, ipos, delimLen, 
                          leftTok, rightTok, currentToken, left, rt, notDone, 
                          foundBangToken, temp1, temp2, temp3 >>

findMatchingRightInner == Lbl_19 \/ Lbl_20 \/ Lbl_21 \/ Lbl_22 \/ Lbl_26
                             \/ Lbl_23 \/ Lbl_24 \/ Lbl_25

Lbl_27 == /\ pc = "Lbl_27"
          /\ IF leftTok = NullTokenSpec \/ rightTok = NullTokenSpec
                THEN /\ returnVal' = NullTokenSpec
                     /\ pc' = Head(stack).pc
                     /\ leftTok' = Head(stack).leftTok
                     /\ rightTok' = Head(stack).rightTok
                     /\ stack' = Tail(stack)
                ELSE /\ pc' = "Lbl_28"
                     /\ UNCHANGED << returnVal, stack, leftTok, rightTok >>
          /\ UNCHANGED << line, foundTokenSpecs, lastToken, notLastToken, 
                          curPos, tempVar1, tempVar2, tempVar3, pos_, tokArray, 
                          i, tokIdx, pos_f, token, left_, rt_, pos_fi, pos_fin, 
                          delim_, ipos_, jdelim_, delimLen_, pos_find, pos, 
                          delim, ipos, jdelim, delimLen, currentToken, left, 
                          rt, notDone, foundBangToken, temp1, temp2, temp3 >>

Lbl_28 == /\ pc = "Lbl_28"
          /\ IF /\ IsNumber(leftTok.token)
                /\ line[leftTok.leftPos-1] = "<"
                /\ line[leftTok.leftPos-2] # "<"
                THEN /\ returnVal' = [token |-> JavaSubseq(line,
                                                           leftTok.leftPos-1,
                                                           rightTok.rightPos),
                                      leftPos |-> leftTok.leftPos-1,
                                      rightPos |-> rightTok.rightPos]
                     /\ pc' = Head(stack).pc
                     /\ leftTok' = Head(stack).leftTok
                     /\ rightTok' = Head(stack).rightTok
                     /\ stack' = Tail(stack)
                ELSE /\ returnVal' = NullTokenSpec
                     /\ pc' = Head(stack).pc
                     /\ leftTok' = Head(stack).leftTok
                     /\ rightTok' = Head(stack).rightTok
                     /\ stack' = Tail(stack)
          /\ UNCHANGED << line, foundTokenSpecs, lastToken, notLastToken, 
                          curPos, tempVar1, tempVar2, tempVar3, pos_, tokArray, 
                          i, tokIdx, pos_f, token, left_, rt_, pos_fi, pos_fin, 
                          delim_, ipos_, jdelim_, delimLen_, pos_find, pos, 
                          delim, ipos, jdelim, delimLen, currentToken, left, 
                          rt, notDone, foundBangToken, temp1, temp2, temp3 >>

checkIfStepName == Lbl_27 \/ Lbl_28

Lbl_29 == /\ pc = "Lbl_29"
          /\ IF line[curPos-1] = " "
                THEN /\ curPos' = curPos - 1
                     /\ pc' = "Lbl_29"
                     /\ UNCHANGED stack
                ELSE /\ pc' = Head(stack).pc
                     /\ stack' = Tail(stack)
                     /\ UNCHANGED curPos
          /\ UNCHANGED << line, foundTokenSpecs, lastToken, notLastToken, 
                          returnVal, tempVar1, tempVar2, tempVar3, pos_, 
                          tokArray, i, tokIdx, pos_f, token, left_, rt_, 
                          pos_fi, pos_fin, delim_, ipos_, jdelim_, delimLen_, 
                          pos_find, pos, delim, ipos, jdelim, delimLen, 
                          leftTok, rightTok, currentToken, left, rt, notDone, 
                          foundBangToken, temp1, temp2, temp3 >>

skipLeftOverSpaces == Lbl_29

Lbl_30 == /\ pc = "Lbl_30"
          /\ IF line[curPos] = " "
                THEN /\ curPos' = curPos+1
                     /\ pc' = "Lbl_30"
                     /\ UNCHANGED stack
                ELSE /\ pc' = Head(stack).pc
                     /\ stack' = Tail(stack)
                     /\ UNCHANGED curPos
          /\ UNCHANGED << line, foundTokenSpecs, lastToken, notLastToken, 
                          returnVal, tempVar1, tempVar2, tempVar3, pos_, 
                          tokArray, i, tokIdx, pos_f, token, left_, rt_, 
                          pos_fi, pos_fin, delim_, ipos_, jdelim_, delimLen_, 
                          pos_find, pos, delim, ipos, jdelim, delimLen, 
                          leftTok, rightTok, currentToken, left, rt, notDone, 
                          foundBangToken, temp1, temp2, temp3 >>

skipRightOverSpaces == Lbl_30

Lbl_31 == /\ pc = "Lbl_31"
          /\ IF line[curPos] = " "
                THEN /\ stack' = << [ procedure |->  "skipLeftOverSpaces",
                                      pc        |->  "Lbl_32" ] >>
                                  \o stack
                     /\ pc' = "Lbl_29"
                     /\ UNCHANGED notLastToken
                ELSE /\ IF line[curPos] = "!" /\ line[curPos-1] # "!" /\ line[curPos+1] # "!"
                           THEN /\ notLastToken' = TRUE
                                /\ stack' = << [ procedure |->  "skipLeftOverSpaces",
                                                 pc        |->  "Lbl_33" ] >>
                                             \o stack
                                /\ pc' = "Lbl_29"
                           ELSE /\ pc' = "Lbl_33"
                                /\ UNCHANGED << notLastToken, stack >>
          /\ UNCHANGED << line, foundTokenSpecs, lastToken, curPos, returnVal, 
                          tempVar1, tempVar2, tempVar3, pos_, tokArray, i, 
                          tokIdx, pos_f, token, left_, rt_, pos_fi, pos_fin, 
                          delim_, ipos_, jdelim_, delimLen_, pos_find, pos, 
                          delim, ipos, jdelim, delimLen, leftTok, rightTok, 
                          currentToken, left, rt, notDone, foundBangToken, 
                          temp1, temp2, temp3 >>

Lbl_32 == /\ pc = "Lbl_32"
          /\ IF line[curPos-1] = "!"  /\ line[curPos-2] # "!"
                THEN /\ notLastToken' = TRUE
                     /\ curPos' = curPos - 1
                     /\ stack' = << [ procedure |->  "skipLeftOverSpaces",
                                      pc        |->  "Lbl_33" ] >>
                                  \o stack
                     /\ pc' = "Lbl_29"
                ELSE /\ pc' = "Lbl_33"
                     /\ UNCHANGED << notLastToken, curPos, stack >>
          /\ UNCHANGED << line, foundTokenSpecs, lastToken, returnVal, 
                          tempVar1, tempVar2, tempVar3, pos_, tokArray, i, 
                          tokIdx, pos_f, token, left_, rt_, pos_fi, pos_fin, 
                          delim_, ipos_, jdelim_, delimLen_, pos_find, pos, 
                          delim, ipos, jdelim, delimLen, leftTok, rightTok, 
                          currentToken, left, rt, notDone, foundBangToken, 
                          temp1, temp2, temp3 >>

Lbl_33 == /\ pc = "Lbl_33"
          /\ IF /\ \/ notLastToken
                   \/ line[curPos] = " "
                /\ line[curPos-1] = ")"
                THEN /\ notLastToken' = TRUE
                     /\ /\ pos_fi' = curPos
                        /\ stack' = << [ procedure |->  "findMatchingLeftParen",
                                         pc        |->  "Lbl_34",
                                         pos_fi    |->  pos_fi ] >>
                                     \o stack
                     /\ pc' = "Lbl_7"
                ELSE /\ pc' = "Lbl_36"
                     /\ UNCHANGED << notLastToken, stack, pos_fi >>
          /\ UNCHANGED << line, foundTokenSpecs, lastToken, curPos, returnVal, 
                          tempVar1, tempVar2, tempVar3, pos_, tokArray, i, 
                          tokIdx, pos_f, token, left_, rt_, pos_fin, delim_, 
                          ipos_, jdelim_, delimLen_, pos_find, pos, delim, 
                          ipos, jdelim, delimLen, leftTok, rightTok, 
                          currentToken, left, rt, notDone, foundBangToken, 
                          temp1, temp2, temp3 >>

Lbl_34 == /\ pc = "Lbl_34"
          /\ IF returnVal < 0
                THEN /\ returnVal' = << >>
                     /\ pc' = Head(stack).pc
                     /\ currentToken' = Head(stack).currentToken
                     /\ left' = Head(stack).left
                     /\ rt' = Head(stack).rt
                     /\ notDone' = Head(stack).notDone
                     /\ foundBangToken' = Head(stack).foundBangToken
                     /\ temp1' = Head(stack).temp1
                     /\ temp2' = Head(stack).temp2
                     /\ temp3' = Head(stack).temp3
                     /\ stack' = Tail(stack)
                ELSE /\ pc' = "Lbl_35"
                     /\ UNCHANGED << returnVal, stack, currentToken, left, rt, 
                                     notDone, foundBangToken, temp1, temp2, 
                                     temp3 >>
          /\ UNCHANGED << line, foundTokenSpecs, lastToken, notLastToken, 
                          curPos, tempVar1, tempVar2, tempVar3, pos_, tokArray, 
                          i, tokIdx, pos_f, token, left_, rt_, pos_fi, pos_fin, 
                          delim_, ipos_, jdelim_, delimLen_, pos_find, pos, 
                          delim, ipos, jdelim, delimLen, leftTok, rightTok >>

Lbl_35 == /\ pc = "Lbl_35"
          /\ curPos' = returnVal
          /\ stack' = << [ procedure |->  "skipLeftOverSpaces",
                           pc        |->  "Lbl_36" ] >>
                       \o stack
          /\ pc' = "Lbl_29"
          /\ UNCHANGED << line, foundTokenSpecs, lastToken, notLastToken, 
                          returnVal, tempVar1, tempVar2, tempVar3, pos_, 
                          tokArray, i, tokIdx, pos_f, token, left_, rt_, 
                          pos_fi, pos_fin, delim_, ipos_, jdelim_, delimLen_, 
                          pos_find, pos, delim, ipos, jdelim, delimLen, 
                          leftTok, rightTok, currentToken, left, rt, notDone, 
                          foundBangToken, temp1, temp2, temp3 >>

Lbl_36 == /\ pc = "Lbl_36"
          /\ IF notLastToken
                THEN /\ curPos' = curPos - 1
                     /\ pc' = "Lbl_38"
                     /\ UNCHANGED << stack, pos_, tokArray, i, tokIdx >>
                ELSE /\ IF line[curPos] \notin IdChar
                           THEN /\ /\ pos_' = curPos
                                   /\ stack' = << [ procedure |->  "findTokenIn",
                                                    pc        |->  "Lbl_37",
                                                    i         |->  i,
                                                    tokIdx    |->  tokIdx,
                                                    pos_      |->  pos_,
                                                    tokArray  |->  tokArray ] >>
                                                \o stack
                                   /\ tokArray' = Operators
                                /\ i' = defaultInitValue
                                /\ tokIdx' = defaultInitValue
                                /\ pc' = "Lbl_1"
                           ELSE /\ pc' = "Lbl_38"
                                /\ UNCHANGED << stack, pos_, tokArray, i, 
                                                tokIdx >>
                     /\ UNCHANGED curPos
          /\ UNCHANGED << line, foundTokenSpecs, lastToken, notLastToken, 
                          returnVal, tempVar1, tempVar2, tempVar3, pos_f, 
                          token, left_, rt_, pos_fi, pos_fin, delim_, ipos_, 
                          jdelim_, delimLen_, pos_find, pos, delim, ipos, 
                          jdelim, delimLen, leftTok, rightTok, currentToken, 
                          left, rt, notDone, foundBangToken, temp1, temp2, 
                          temp3 >>

Lbl_37 == /\ pc = "Lbl_37"
          /\ IF returnVal = NullTokenSpec
                THEN /\ curPos' = curPos - 1
                ELSE /\ TRUE
                     /\ UNCHANGED curPos
          /\ pc' = "Lbl_38"
          /\ UNCHANGED << line, foundTokenSpecs, lastToken, notLastToken, 
                          returnVal, tempVar1, tempVar2, tempVar3, stack, pos_, 
                          tokArray, i, tokIdx, pos_f, token, left_, rt_, 
                          pos_fi, pos_fin, delim_, ipos_, jdelim_, delimLen_, 
                          pos_find, pos, delim, ipos, jdelim, delimLen, 
                          leftTok, rightTok, currentToken, left, rt, notDone, 
                          foundBangToken, temp1, temp2, temp3 >>

Lbl_38 == /\ pc = "Lbl_38"
          /\ IF line[curPos] \in IdChar
                THEN /\ IF line[curPos] = "X"
                           THEN /\ /\ pos_' = curPos
                                   /\ stack' = << [ procedure |->  "findTokenIn",
                                                    pc        |->  "Lbl_39",
                                                    i         |->  i,
                                                    tokIdx    |->  tokIdx,
                                                    pos_      |->  pos_,
                                                    tokArray  |->  tokArray ] >>
                                                \o stack
                                   /\ tokArray' = XSymbols
                                /\ i' = defaultInitValue
                                /\ tokIdx' = defaultInitValue
                                /\ pc' = "Lbl_1"
                                /\ UNCHANGED returnVal
                           ELSE /\ returnVal' = NullTokenSpec
                                /\ pc' = "Lbl_39"
                                /\ UNCHANGED << stack, pos_, tokArray, i, 
                                                tokIdx >>
                ELSE /\ /\ pos_' = curPos
                        /\ stack' = << [ procedure |->  "findTokenIn",
                                         pc        |->  "Lbl_48",
                                         i         |->  i,
                                         tokIdx    |->  tokIdx,
                                         pos_      |->  pos_,
                                         tokArray  |->  tokArray ] >>
                                     \o stack
                        /\ tokArray' = Operators
                     /\ i' = defaultInitValue
                     /\ tokIdx' = defaultInitValue
                     /\ pc' = "Lbl_1"
                     /\ UNCHANGED returnVal
          /\ UNCHANGED << line, foundTokenSpecs, lastToken, notLastToken, 
                          curPos, tempVar1, tempVar2, tempVar3, pos_f, token, 
                          left_, rt_, pos_fi, pos_fin, delim_, ipos_, jdelim_, 
                          delimLen_, pos_find, pos, delim, ipos, jdelim, 
                          delimLen, leftTok, rightTok, currentToken, left, rt, 
                          notDone, foundBangToken, temp1, temp2, temp3 >>

Lbl_39 == /\ pc = "Lbl_39"
          /\ IF returnVal # NullTokenSpec
                THEN /\ foundTokenSpecs' = JavaSeq(<<returnVal>>)
                     /\ curPos' = returnVal.leftPos
                     /\ lastToken' = TRUE
                     /\ pc' = "Lbl_62"
                     /\ UNCHANGED << stack, pos_f, token, left_, rt_ >>
                ELSE /\ /\ pos_f' = curPos
                        /\ stack' = << [ procedure |->  "findMaximalIdCharSeq",
                                         pc        |->  "Lbl_40",
                                         token     |->  token,
                                         left_     |->  left_,
                                         rt_       |->  rt_,
                                         pos_f     |->  pos_f ] >>
                                     \o stack
                     /\ token' = << >>
                     /\ left_' = pos_f'
                     /\ rt_' = pos_f'
                     /\ pc' = "Lbl_5"
                     /\ UNCHANGED << foundTokenSpecs, lastToken, curPos >>
          /\ UNCHANGED << line, notLastToken, returnVal, tempVar1, tempVar2, 
                          tempVar3, pos_, tokArray, i, tokIdx, pos_fi, pos_fin, 
                          delim_, ipos_, jdelim_, delimLen_, pos_find, pos, 
                          delim, ipos, jdelim, delimLen, leftTok, rightTok, 
                          currentToken, left, rt, notDone, foundBangToken, 
                          temp1, temp2, temp3 >>

Lbl_40 == /\ pc = "Lbl_40"
          /\ currentToken' = returnVal
          /\ IF line[currentToken'.leftPos-1] = ">"
                THEN /\ /\ pos_f' = currentToken'.leftPos - 1
                        /\ stack' = << [ procedure |->  "findMaximalIdCharSeq",
                                         pc        |->  "Lbl_41",
                                         token     |->  token,
                                         left_     |->  left_,
                                         rt_       |->  rt_,
                                         pos_f     |->  pos_f ] >>
                                     \o stack
                     /\ token' = << >>
                     /\ left_' = pos_f'
                     /\ rt_' = pos_f'
                     /\ pc' = "Lbl_5"
                ELSE /\ pc' = "Lbl_43"
                     /\ UNCHANGED << stack, pos_f, token, left_, rt_ >>
          /\ UNCHANGED << line, foundTokenSpecs, lastToken, notLastToken, 
                          curPos, returnVal, tempVar1, tempVar2, tempVar3, 
                          pos_, tokArray, i, tokIdx, pos_fi, pos_fin, delim_, 
                          ipos_, jdelim_, delimLen_, pos_find, pos, delim, 
                          ipos, jdelim, delimLen, leftTok, rightTok, left, rt, 
                          notDone, foundBangToken, temp1, temp2, temp3 >>

Lbl_41 == /\ pc = "Lbl_41"
          /\ /\ leftTok' = returnVal
             /\ rightTok' = currentToken
             /\ stack' = << [ procedure |->  "checkIfStepName",
                              pc        |->  "Lbl_42",
                              leftTok   |->  leftTok,
                              rightTok  |->  rightTok ] >>
                          \o stack
          /\ pc' = "Lbl_27"
          /\ UNCHANGED << line, foundTokenSpecs, lastToken, notLastToken, 
                          curPos, returnVal, tempVar1, tempVar2, tempVar3, 
                          pos_, tokArray, i, tokIdx, pos_f, token, left_, rt_, 
                          pos_fi, pos_fin, delim_, ipos_, jdelim_, delimLen_, 
                          pos_find, pos, delim, ipos, jdelim, delimLen, 
                          currentToken, left, rt, notDone, foundBangToken, 
                          temp1, temp2, temp3 >>

Lbl_42 == /\ pc = "Lbl_42"
          /\ IF returnVal # NullTokenSpec
                THEN /\ foundTokenSpecs' = JavaSeq(<<returnVal>>)
                     /\ returnVal' = FixOrigin(foundTokenSpecs')
                     /\ pc' = Head(stack).pc
                     /\ currentToken' = Head(stack).currentToken
                     /\ left' = Head(stack).left
                     /\ rt' = Head(stack).rt
                     /\ notDone' = Head(stack).notDone
                     /\ foundBangToken' = Head(stack).foundBangToken
                     /\ temp1' = Head(stack).temp1
                     /\ temp2' = Head(stack).temp2
                     /\ temp3' = Head(stack).temp3
                     /\ stack' = Tail(stack)
                ELSE /\ pc' = "Lbl_43"
                     /\ UNCHANGED << foundTokenSpecs, returnVal, stack, 
                                     currentToken, left, rt, notDone, 
                                     foundBangToken, temp1, temp2, temp3 >>
          /\ UNCHANGED << line, lastToken, notLastToken, curPos, tempVar1, 
                          tempVar2, tempVar3, pos_, tokArray, i, tokIdx, pos_f, 
                          token, left_, rt_, pos_fi, pos_fin, delim_, ipos_, 
                          jdelim_, delimLen_, pos_find, pos, delim, ipos, 
                          jdelim, delimLen, leftTok, rightTok >>

Lbl_43 == /\ pc = "Lbl_43"
          /\ IF line[currentToken.rightPos] = ">"
                THEN /\ /\ pos_f' = currentToken.rightPos+1
                        /\ stack' = << [ procedure |->  "findMaximalIdCharSeq",
                                         pc        |->  "Lbl_44",
                                         token     |->  token,
                                         left_     |->  left_,
                                         rt_       |->  rt_,
                                         pos_f     |->  pos_f ] >>
                                     \o stack
                     /\ token' = << >>
                     /\ left_' = pos_f'
                     /\ rt_' = pos_f'
                     /\ pc' = "Lbl_5"
                ELSE /\ pc' = "Lbl_46"
                     /\ UNCHANGED << stack, pos_f, token, left_, rt_ >>
          /\ UNCHANGED << line, foundTokenSpecs, lastToken, notLastToken, 
                          curPos, returnVal, tempVar1, tempVar2, tempVar3, 
                          pos_, tokArray, i, tokIdx, pos_fi, pos_fin, delim_, 
                          ipos_, jdelim_, delimLen_, pos_find, pos, delim, 
                          ipos, jdelim, delimLen, leftTok, rightTok, 
                          currentToken, left, rt, notDone, foundBangToken, 
                          temp1, temp2, temp3 >>

Lbl_44 == /\ pc = "Lbl_44"
          /\ /\ leftTok' = currentToken
             /\ rightTok' = returnVal
             /\ stack' = << [ procedure |->  "checkIfStepName",
                              pc        |->  "Lbl_45",
                              leftTok   |->  leftTok,
                              rightTok  |->  rightTok ] >>
                          \o stack
          /\ pc' = "Lbl_27"
          /\ UNCHANGED << line, foundTokenSpecs, lastToken, notLastToken, 
                          curPos, returnVal, tempVar1, tempVar2, tempVar3, 
                          pos_, tokArray, i, tokIdx, pos_f, token, left_, rt_, 
                          pos_fi, pos_fin, delim_, ipos_, jdelim_, delimLen_, 
                          pos_find, pos, delim, ipos, jdelim, delimLen, 
                          currentToken, left, rt, notDone, foundBangToken, 
                          temp1, temp2, temp3 >>

Lbl_45 == /\ pc = "Lbl_45"
          /\ IF returnVal # NullTokenSpec
                THEN /\ foundTokenSpecs' = JavaSeq(<<returnVal>>)
                     /\ returnVal' = FixOrigin(foundTokenSpecs')
                     /\ pc' = Head(stack).pc
                     /\ currentToken' = Head(stack).currentToken
                     /\ left' = Head(stack).left
                     /\ rt' = Head(stack).rt
                     /\ notDone' = Head(stack).notDone
                     /\ foundBangToken' = Head(stack).foundBangToken
                     /\ temp1' = Head(stack).temp1
                     /\ temp2' = Head(stack).temp2
                     /\ temp3' = Head(stack).temp3
                     /\ stack' = Tail(stack)
                ELSE /\ pc' = "Lbl_46"
                     /\ UNCHANGED << foundTokenSpecs, returnVal, stack, 
                                     currentToken, left, rt, notDone, 
                                     foundBangToken, temp1, temp2, temp3 >>
          /\ UNCHANGED << line, lastToken, notLastToken, curPos, tempVar1, 
                          tempVar2, tempVar3, pos_, tokArray, i, tokIdx, pos_f, 
                          token, left_, rt_, pos_fi, pos_fin, delim_, ipos_, 
                          jdelim_, delimLen_, pos_find, pos, delim, ipos, 
                          jdelim, delimLen, leftTok, rightTok >>

Lbl_46 == /\ pc = "Lbl_46"
          /\ IF IsNumber(currentToken.token)
                THEN /\ returnVal' = << >>
                     /\ pc' = Head(stack).pc
                     /\ currentToken' = Head(stack).currentToken
                     /\ left' = Head(stack).left
                     /\ rt' = Head(stack).rt
                     /\ notDone' = Head(stack).notDone
                     /\ foundBangToken' = Head(stack).foundBangToken
                     /\ temp1' = Head(stack).temp1
                     /\ temp2' = Head(stack).temp2
                     /\ temp3' = Head(stack).temp3
                     /\ stack' = Tail(stack)
                ELSE /\ pc' = "Lbl_47"
                     /\ UNCHANGED << returnVal, stack, currentToken, left, rt, 
                                     notDone, foundBangToken, temp1, temp2, 
                                     temp3 >>
          /\ UNCHANGED << line, foundTokenSpecs, lastToken, notLastToken, 
                          curPos, tempVar1, tempVar2, tempVar3, pos_, tokArray, 
                          i, tokIdx, pos_f, token, left_, rt_, pos_fi, pos_fin, 
                          delim_, ipos_, jdelim_, delimLen_, pos_find, pos, 
                          delim, ipos, jdelim, delimLen, leftTok, rightTok >>

Lbl_47 == /\ pc = "Lbl_47"
          /\ left' = currentToken.leftPos
          /\ rt' = currentToken.rightPos
          /\ IF /\ line[left'-1] = "\\"
                /\ line[left'-2] # "\\"
                /\ \E ii \in DOMAIN TeXSymbols :
                         JavaSubseq(line, left'-1, rt') = TeXSymbols[ii]
                THEN /\ lastToken' = TRUE
                     /\ currentToken' = [currentToken EXCEPT !.leftPos = left' - 1,
                                                             !.token = JavaSubseq(line, left'-1, rt')]
                ELSE /\ TRUE
                     /\ UNCHANGED << lastToken, currentToken >>
          /\ foundTokenSpecs' = JavaSeq( << currentToken' >>)
          /\ curPos' = left'
          /\ pc' = "Lbl_62"
          /\ UNCHANGED << line, notLastToken, returnVal, tempVar1, tempVar2, 
                          tempVar3, stack, pos_, tokArray, i, tokIdx, pos_f, 
                          token, left_, rt_, pos_fi, pos_fin, delim_, ipos_, 
                          jdelim_, delimLen_, pos_find, pos, delim, ipos, 
                          jdelim, delimLen, leftTok, rightTok, notDone, 
                          foundBangToken, temp1, temp2, temp3 >>

Lbl_48 == /\ pc = "Lbl_48"
          /\ currentToken' = returnVal
          /\ IF currentToken' = NullTokenSpec
                THEN /\ returnVal' = << >>
                     /\ pc' = "Lbl_49"
                ELSE /\ pc' = "Lbl_50"
                     /\ UNCHANGED returnVal
          /\ UNCHANGED << line, foundTokenSpecs, lastToken, notLastToken, 
                          curPos, tempVar1, tempVar2, tempVar3, stack, pos_, 
                          tokArray, i, tokIdx, pos_f, token, left_, rt_, 
                          pos_fi, pos_fin, delim_, ipos_, jdelim_, delimLen_, 
                          pos_find, pos, delim, ipos, jdelim, delimLen, 
                          leftTok, rightTok, left, rt, notDone, foundBangToken, 
                          temp1, temp2, temp3 >>

Lbl_49 == /\ pc = "Lbl_49"
          /\ pc' = Head(stack).pc
          /\ currentToken' = Head(stack).currentToken
          /\ left' = Head(stack).left
          /\ rt' = Head(stack).rt
          /\ notDone' = Head(stack).notDone
          /\ foundBangToken' = Head(stack).foundBangToken
          /\ temp1' = Head(stack).temp1
          /\ temp2' = Head(stack).temp2
          /\ temp3' = Head(stack).temp3
          /\ stack' = Tail(stack)
          /\ UNCHANGED << line, foundTokenSpecs, lastToken, notLastToken, 
                          curPos, returnVal, tempVar1, tempVar2, tempVar3, 
                          pos_, tokArray, i, tokIdx, pos_f, token, left_, rt_, 
                          pos_fi, pos_fin, delim_, ipos_, jdelim_, delimLen_, 
                          pos_find, pos, delim, ipos, jdelim, delimLen, 
                          leftTok, rightTok >>

Lbl_50 == /\ pc = "Lbl_50"
          /\ /\ pos_' = curPos
             /\ stack' = << [ procedure |->  "findTokenIn",
                              pc        |->  "Lbl_51",
                              i         |->  i,
                              tokIdx    |->  tokIdx,
                              pos_      |->  pos_,
                              tokArray  |->  tokArray ] >>
                          \o stack
             /\ tokArray' = NonOperators
          /\ i' = defaultInitValue
          /\ tokIdx' = defaultInitValue
          /\ pc' = "Lbl_1"
          /\ UNCHANGED << line, foundTokenSpecs, lastToken, notLastToken, 
                          curPos, returnVal, tempVar1, tempVar2, tempVar3, 
                          pos_f, token, left_, rt_, pos_fi, pos_fin, delim_, 
                          ipos_, jdelim_, delimLen_, pos_find, pos, delim, 
                          ipos, jdelim, delimLen, leftTok, rightTok, 
                          currentToken, left, rt, notDone, foundBangToken, 
                          temp1, temp2, temp3 >>

Lbl_51 == /\ pc = "Lbl_51"
          /\ IF returnVal # NullTokenSpec
                THEN /\ returnVal' = << >>
                     /\ pc' = Head(stack).pc
                     /\ currentToken' = Head(stack).currentToken
                     /\ left' = Head(stack).left
                     /\ rt' = Head(stack).rt
                     /\ notDone' = Head(stack).notDone
                     /\ foundBangToken' = Head(stack).foundBangToken
                     /\ temp1' = Head(stack).temp1
                     /\ temp2' = Head(stack).temp2
                     /\ temp3' = Head(stack).temp3
                     /\ stack' = Tail(stack)
                ELSE /\ pc' = "Lbl_52"
                     /\ UNCHANGED << returnVal, stack, currentToken, left, rt, 
                                     notDone, foundBangToken, temp1, temp2, 
                                     temp3 >>
          /\ UNCHANGED << line, foundTokenSpecs, lastToken, notLastToken, 
                          curPos, tempVar1, tempVar2, tempVar3, pos_, tokArray, 
                          i, tokIdx, pos_f, token, left_, rt_, pos_fi, pos_fin, 
                          delim_, ipos_, jdelim_, delimLen_, pos_find, pos, 
                          delim, ipos, jdelim, delimLen, leftTok, rightTok >>

Lbl_52 == /\ pc = "Lbl_52"
          /\ IF currentToken.token = JavaSeq(<< "<" >>)
                THEN /\ /\ pos_f' = currentToken.rightPos
                        /\ stack' = << [ procedure |->  "findMaximalIdCharSeq",
                                         pc        |->  "Lbl_53",
                                         token     |->  token,
                                         left_     |->  left_,
                                         rt_       |->  rt_,
                                         pos_f     |->  pos_f ] >>
                                     \o stack
                     /\ token' = << >>
                     /\ left_' = pos_f'
                     /\ rt_' = pos_f'
                     /\ pc' = "Lbl_5"
                ELSE /\ IF currentToken.token = JavaSeq(<< ">" >>)
                           THEN /\ /\ pos_f' = currentToken.leftPos
                                   /\ stack' = << [ procedure |->  "findMaximalIdCharSeq",
                                                    pc        |->  "Lbl_56",
                                                    token     |->  token,
                                                    left_     |->  left_,
                                                    rt_       |->  rt_,
                                                    pos_f     |->  pos_f ] >>
                                                \o stack
                                /\ token' = << >>
                                /\ left_' = pos_f'
                                /\ rt_' = pos_f'
                                /\ pc' = "Lbl_5"
                           ELSE /\ pc' = "Lbl_59"
                                /\ UNCHANGED << stack, pos_f, token, left_, 
                                                rt_ >>
          /\ UNCHANGED << line, foundTokenSpecs, lastToken, notLastToken, 
                          curPos, returnVal, tempVar1, tempVar2, tempVar3, 
                          pos_, tokArray, i, tokIdx, pos_fi, pos_fin, delim_, 
                          ipos_, jdelim_, delimLen_, pos_find, pos, delim, 
                          ipos, jdelim, delimLen, leftTok, rightTok, 
                          currentToken, left, rt, notDone, foundBangToken, 
                          temp1, temp2, temp3 >>

Lbl_53 == /\ pc = "Lbl_53"
          /\ temp1' = returnVal
          /\ IF /\ temp1' # NullTokenSpec
                /\ line[temp1'.rightPos] = ">"
                THEN /\ /\ pos_f' = temp1'.rightPos + 1
                        /\ stack' = << [ procedure |->  "findMaximalIdCharSeq",
                                         pc        |->  "Lbl_54",
                                         token     |->  token,
                                         left_     |->  left_,
                                         rt_       |->  rt_,
                                         pos_f     |->  pos_f ] >>
                                     \o stack
                     /\ token' = << >>
                     /\ left_' = pos_f'
                     /\ rt_' = pos_f'
                     /\ pc' = "Lbl_5"
                ELSE /\ pc' = "Lbl_59"
                     /\ UNCHANGED << stack, pos_f, token, left_, rt_ >>
          /\ UNCHANGED << line, foundTokenSpecs, lastToken, notLastToken, 
                          curPos, returnVal, tempVar1, tempVar2, tempVar3, 
                          pos_, tokArray, i, tokIdx, pos_fi, pos_fin, delim_, 
                          ipos_, jdelim_, delimLen_, pos_find, pos, delim, 
                          ipos, jdelim, delimLen, leftTok, rightTok, 
                          currentToken, left, rt, notDone, foundBangToken, 
                          temp2, temp3 >>

Lbl_54 == /\ pc = "Lbl_54"
          /\ temp2' = returnVal
          /\ /\ leftTok' = temp1
             /\ rightTok' = temp2'
             /\ stack' = << [ procedure |->  "checkIfStepName",
                              pc        |->  "Lbl_55",
                              leftTok   |->  leftTok,
                              rightTok  |->  rightTok ] >>
                          \o stack
          /\ pc' = "Lbl_27"
          /\ UNCHANGED << line, foundTokenSpecs, lastToken, notLastToken, 
                          curPos, returnVal, tempVar1, tempVar2, tempVar3, 
                          pos_, tokArray, i, tokIdx, pos_f, token, left_, rt_, 
                          pos_fi, pos_fin, delim_, ipos_, jdelim_, delimLen_, 
                          pos_find, pos, delim, ipos, jdelim, delimLen, 
                          currentToken, left, rt, notDone, foundBangToken, 
                          temp1, temp3 >>

Lbl_55 == /\ pc = "Lbl_55"
          /\ IF returnVal # NullTokenSpec
                THEN /\ foundTokenSpecs' = JavaSeq(<<returnVal>>)
                     /\ returnVal' = FixOrigin(foundTokenSpecs')
                     /\ pc' = Head(stack).pc
                     /\ currentToken' = Head(stack).currentToken
                     /\ left' = Head(stack).left
                     /\ rt' = Head(stack).rt
                     /\ notDone' = Head(stack).notDone
                     /\ foundBangToken' = Head(stack).foundBangToken
                     /\ temp1' = Head(stack).temp1
                     /\ temp2' = Head(stack).temp2
                     /\ temp3' = Head(stack).temp3
                     /\ stack' = Tail(stack)
                ELSE /\ pc' = "Lbl_59"
                     /\ UNCHANGED << foundTokenSpecs, returnVal, stack, 
                                     currentToken, left, rt, notDone, 
                                     foundBangToken, temp1, temp2, temp3 >>
          /\ UNCHANGED << line, lastToken, notLastToken, curPos, tempVar1, 
                          tempVar2, tempVar3, pos_, tokArray, i, tokIdx, pos_f, 
                          token, left_, rt_, pos_fi, pos_fin, delim_, ipos_, 
                          jdelim_, delimLen_, pos_find, pos, delim, ipos, 
                          jdelim, delimLen, leftTok, rightTok >>

Lbl_56 == /\ pc = "Lbl_56"
          /\ temp1' = returnVal
          /\ /\ pos_f' = currentToken.rightPos
             /\ stack' = << [ procedure |->  "findMaximalIdCharSeq",
                              pc        |->  "Lbl_57",
                              token     |->  token,
                              left_     |->  left_,
                              rt_       |->  rt_,
                              pos_f     |->  pos_f ] >>
                          \o stack
          /\ token' = << >>
          /\ left_' = pos_f'
          /\ rt_' = pos_f'
          /\ pc' = "Lbl_5"
          /\ UNCHANGED << line, foundTokenSpecs, lastToken, notLastToken, 
                          curPos, returnVal, tempVar1, tempVar2, tempVar3, 
                          pos_, tokArray, i, tokIdx, pos_fi, pos_fin, delim_, 
                          ipos_, jdelim_, delimLen_, pos_find, pos, delim, 
                          ipos, jdelim, delimLen, leftTok, rightTok, 
                          currentToken, left, rt, notDone, foundBangToken, 
                          temp2, temp3 >>

Lbl_57 == /\ pc = "Lbl_57"
          /\ temp2' = returnVal
          /\ /\ leftTok' = temp1
             /\ rightTok' = temp2'
             /\ stack' = << [ procedure |->  "checkIfStepName",
                              pc        |->  "Lbl_58",
                              leftTok   |->  leftTok,
                              rightTok  |->  rightTok ] >>
                          \o stack
          /\ pc' = "Lbl_27"
          /\ UNCHANGED << line, foundTokenSpecs, lastToken, notLastToken, 
                          curPos, returnVal, tempVar1, tempVar2, tempVar3, 
                          pos_, tokArray, i, tokIdx, pos_f, token, left_, rt_, 
                          pos_fi, pos_fin, delim_, ipos_, jdelim_, delimLen_, 
                          pos_find, pos, delim, ipos, jdelim, delimLen, 
                          currentToken, left, rt, notDone, foundBangToken, 
                          temp1, temp3 >>

Lbl_58 == /\ pc = "Lbl_58"
          /\ IF returnVal # NullTokenSpec
                THEN /\ foundTokenSpecs' = JavaSeq(<<returnVal>>)
                     /\ returnVal' = FixOrigin(foundTokenSpecs')
                     /\ pc' = Head(stack).pc
                     /\ currentToken' = Head(stack).currentToken
                     /\ left' = Head(stack).left
                     /\ rt' = Head(stack).rt
                     /\ notDone' = Head(stack).notDone
                     /\ foundBangToken' = Head(stack).foundBangToken
                     /\ temp1' = Head(stack).temp1
                     /\ temp2' = Head(stack).temp2
                     /\ temp3' = Head(stack).temp3
                     /\ stack' = Tail(stack)
                ELSE /\ pc' = "Lbl_59"
                     /\ UNCHANGED << foundTokenSpecs, returnVal, stack, 
                                     currentToken, left, rt, notDone, 
                                     foundBangToken, temp1, temp2, temp3 >>
          /\ UNCHANGED << line, lastToken, notLastToken, curPos, tempVar1, 
                          tempVar2, tempVar3, pos_, tokArray, i, tokIdx, pos_f, 
                          token, left_, rt_, pos_fi, pos_fin, delim_, ipos_, 
                          jdelim_, delimLen_, pos_find, pos, delim, ipos, 
                          jdelim, delimLen, leftTok, rightTok >>

Lbl_59 == /\ pc = "Lbl_59"
          /\ IF currentToken.token = JavaSeq(<<"\\">>)
                THEN /\ /\ pos_f' = currentToken.rightPos
                        /\ stack' = << [ procedure |->  "findMaximalIdCharSeq",
                                         pc        |->  "Lbl_60",
                                         token     |->  token,
                                         left_     |->  left_,
                                         rt_       |->  rt_,
                                         pos_f     |->  pos_f ] >>
                                     \o stack
                     /\ token' = << >>
                     /\ left_' = pos_f'
                     /\ rt_' = pos_f'
                     /\ pc' = "Lbl_5"
                ELSE /\ pc' = "Lbl_61"
                     /\ UNCHANGED << stack, pos_f, token, left_, rt_ >>
          /\ UNCHANGED << line, foundTokenSpecs, lastToken, notLastToken, 
                          curPos, returnVal, tempVar1, tempVar2, tempVar3, 
                          pos_, tokArray, i, tokIdx, pos_fi, pos_fin, delim_, 
                          ipos_, jdelim_, delimLen_, pos_find, pos, delim, 
                          ipos, jdelim, delimLen, leftTok, rightTok, 
                          currentToken, left, rt, notDone, foundBangToken, 
                          temp1, temp2, temp3 >>

Lbl_60 == /\ pc = "Lbl_60"
          /\ IF /\ returnVal # NullTokenSpec
                /\ \E ii \in DOMAIN TeXSymbols :
                          JavaSubseq(line,
                                     currentToken.leftPos,
                                     returnVal.rightPos) = TeXSymbols[ii]
                THEN /\ currentToken' = [currentToken EXCEPT !.rightPos = returnVal.rightPos,
                                                             !.token = JavaSubseq(line,
                                                                       currentToken.leftPos,
                                                                       returnVal.rightPos)]
                ELSE /\ TRUE
                     /\ UNCHANGED currentToken
          /\ pc' = "Lbl_61"
          /\ UNCHANGED << line, foundTokenSpecs, lastToken, notLastToken, 
                          curPos, returnVal, tempVar1, tempVar2, tempVar3, 
                          stack, pos_, tokArray, i, tokIdx, pos_f, token, 
                          left_, rt_, pos_fi, pos_fin, delim_, ipos_, jdelim_, 
                          delimLen_, pos_find, pos, delim, ipos, jdelim, 
                          delimLen, leftTok, rightTok, left, rt, notDone, 
                          foundBangToken, temp1, temp2, temp3 >>

Lbl_61 == /\ pc = "Lbl_61"
          /\ foundTokenSpecs' = JavaSeq(<<currentToken>>)
          /\ curPos' = currentToken.leftPos
          /\ lastToken' = TRUE
          /\ pc' = "Lbl_62"
          /\ UNCHANGED << line, notLastToken, returnVal, tempVar1, tempVar2, 
                          tempVar3, stack, pos_, tokArray, i, tokIdx, pos_f, 
                          token, left_, rt_, pos_fi, pos_fin, delim_, ipos_, 
                          jdelim_, delimLen_, pos_find, pos, delim, ipos, 
                          jdelim, delimLen, leftTok, rightTok, currentToken, 
                          left, rt, notDone, foundBangToken, temp1, temp2, 
                          temp3 >>

Lbl_62 == /\ pc = "Lbl_62"
          /\ Assert(JavaLen(foundTokenSpecs) = 1, 
                    "Failure of assertion at line 618, column 3.")
          /\ curPos' = foundTokenSpecs[0].leftPos
          /\ notDone' = TRUE
          /\ pc' = "Lbl_63"
          /\ UNCHANGED << line, foundTokenSpecs, lastToken, notLastToken, 
                          returnVal, tempVar1, tempVar2, tempVar3, stack, pos_, 
                          tokArray, i, tokIdx, pos_f, token, left_, rt_, 
                          pos_fi, pos_fin, delim_, ipos_, jdelim_, delimLen_, 
                          pos_find, pos, delim, ipos, jdelim, delimLen, 
                          leftTok, rightTok, currentToken, left, rt, 
                          foundBangToken, temp1, temp2, temp3 >>

Lbl_63 == /\ pc = "Lbl_63"
          /\ IF notDone
                THEN /\ stack' = << [ procedure |->  "skipLeftOverSpaces",
                                      pc        |->  "Lbl_64" ] >>
                                  \o stack
                     /\ pc' = "Lbl_29"
                     /\ UNCHANGED << returnVal, currentToken, left, rt, 
                                     notDone, foundBangToken, temp1, temp2, 
                                     temp3 >>
                ELSE /\ Assert(foundTokenSpecs # << >>, 
                               "Failure of assertion at line 660, column 3.")
                     /\ IF lastToken = TRUE
                           THEN /\ returnVal' = FixOrigin(foundTokenSpecs)
                                /\ pc' = Head(stack).pc
                                /\ currentToken' = Head(stack).currentToken
                                /\ left' = Head(stack).left
                                /\ rt' = Head(stack).rt
                                /\ notDone' = Head(stack).notDone
                                /\ foundBangToken' = Head(stack).foundBangToken
                                /\ temp1' = Head(stack).temp1
                                /\ temp2' = Head(stack).temp2
                                /\ temp3' = Head(stack).temp3
                                /\ stack' = Tail(stack)
                           ELSE /\ pc' = "Lbl_69"
                                /\ UNCHANGED << returnVal, stack, currentToken, 
                                                left, rt, notDone, 
                                                foundBangToken, temp1, temp2, 
                                                temp3 >>
          /\ UNCHANGED << line, foundTokenSpecs, lastToken, notLastToken, 
                          curPos, tempVar1, tempVar2, tempVar3, pos_, tokArray, 
                          i, tokIdx, pos_f, token, left_, rt_, pos_fi, pos_fin, 
                          delim_, ipos_, jdelim_, delimLen_, pos_find, pos, 
                          delim, ipos, jdelim, delimLen, leftTok, rightTok >>

Lbl_64 == /\ pc = "Lbl_64"
          /\ IF curPos <  0 \/ line[curPos-1] = ";"
                THEN /\ notDone' = FALSE
                     /\ pc' = "Lbl_63"
                     /\ UNCHANGED << curPos, stack >>
                ELSE /\ IF line[curPos-1] = "!" /\ (line[curPos-2] # "!")
                           THEN /\ curPos' = curPos - 1
                                /\ stack' = << [ procedure |->  "skipLeftOverSpaces",
                                                 pc        |->  "Lbl_65" ] >>
                                             \o stack
                                /\ pc' = "Lbl_29"
                                /\ UNCHANGED notDone
                           ELSE /\ notDone' = FALSE
                                /\ pc' = "Lbl_63"
                                /\ UNCHANGED << curPos, stack >>
          /\ UNCHANGED << line, foundTokenSpecs, lastToken, notLastToken, 
                          returnVal, tempVar1, tempVar2, tempVar3, pos_, 
                          tokArray, i, tokIdx, pos_f, token, left_, rt_, 
                          pos_fi, pos_fin, delim_, ipos_, jdelim_, delimLen_, 
                          pos_find, pos, delim, ipos, jdelim, delimLen, 
                          leftTok, rightTok, currentToken, left, rt, 
                          foundBangToken, temp1, temp2, temp3 >>

Lbl_65 == /\ pc = "Lbl_65"
          /\ /\ pos_fi' = curPos
             /\ stack' = << [ procedure |->  "findMatchingLeftParen",
                              pc        |->  "Lbl_66",
                              pos_fi    |->  pos_fi ] >>
                          \o stack
          /\ pc' = "Lbl_7"
          /\ UNCHANGED << line, foundTokenSpecs, lastToken, notLastToken, 
                          curPos, returnVal, tempVar1, tempVar2, tempVar3, 
                          pos_, tokArray, i, tokIdx, pos_f, token, left_, rt_, 
                          pos_fin, delim_, ipos_, jdelim_, delimLen_, pos_find, 
                          pos, delim, ipos, jdelim, delimLen, leftTok, 
                          rightTok, currentToken, left, rt, notDone, 
                          foundBangToken, temp1, temp2, temp3 >>

Lbl_66 == /\ pc = "Lbl_66"
          /\ curPos' = returnVal
          /\ IF curPos' < 0
                THEN /\ notDone' = FALSE
                     /\ pc' = "Lbl_63"
                     /\ UNCHANGED stack
                ELSE /\ stack' = << [ procedure |->  "skipLeftOverSpaces",
                                      pc        |->  "Lbl_67" ] >>
                                  \o stack
                     /\ pc' = "Lbl_29"
                     /\ UNCHANGED notDone
          /\ UNCHANGED << line, foundTokenSpecs, lastToken, notLastToken, 
                          returnVal, tempVar1, tempVar2, tempVar3, pos_, 
                          tokArray, i, tokIdx, pos_f, token, left_, rt_, 
                          pos_fi, pos_fin, delim_, ipos_, jdelim_, delimLen_, 
                          pos_find, pos, delim, ipos, jdelim, delimLen, 
                          leftTok, rightTok, currentToken, left, rt, 
                          foundBangToken, temp1, temp2, temp3 >>

Lbl_67 == /\ pc = "Lbl_67"
          /\ /\ pos_f' = curPos
             /\ stack' = << [ procedure |->  "findMaximalIdCharSeq",
                              pc        |->  "Lbl_68",
                              token     |->  token,
                              left_     |->  left_,
                              rt_       |->  rt_,
                              pos_f     |->  pos_f ] >>
                          \o stack
          /\ token' = << >>
          /\ left_' = pos_f'
          /\ rt_' = pos_f'
          /\ pc' = "Lbl_5"
          /\ UNCHANGED << line, foundTokenSpecs, lastToken, notLastToken, 
                          curPos, returnVal, tempVar1, tempVar2, tempVar3, 
                          pos_, tokArray, i, tokIdx, pos_fi, pos_fin, delim_, 
                          ipos_, jdelim_, delimLen_, pos_find, pos, delim, 
                          ipos, jdelim, delimLen, leftTok, rightTok, 
                          currentToken, left, rt, notDone, foundBangToken, 
                          temp1, temp2, temp3 >>

Lbl_68 == /\ pc = "Lbl_68"
          /\ currentToken' = returnVal
          /\ IF \/ currentToken' = NullTokenSpec
                \/ IsNumber(currentToken'.token)
                THEN /\ notDone' = FALSE
                     /\ UNCHANGED << foundTokenSpecs, curPos >>
                ELSE /\ curPos' = currentToken'.leftPos
                     /\ foundTokenSpecs' = [foundTokenSpecs EXCEPT ![0] = [token |-> JavaConcatenate(
                                                                                         JavaAppend(currentToken'.token, "!"),
                                                                                         foundTokenSpecs[0].token),
                                                                           leftPos |-> curPos',
                                                                           rightPos |-> foundTokenSpecs[0].rightPos]]
                     /\ UNCHANGED notDone
          /\ pc' = "Lbl_63"
          /\ UNCHANGED << line, lastToken, notLastToken, returnVal, tempVar1, 
                          tempVar2, tempVar3, stack, pos_, tokArray, i, tokIdx, 
                          pos_f, token, left_, rt_, pos_fi, pos_fin, delim_, 
                          ipos_, jdelim_, delimLen_, pos_find, pos, delim, 
                          ipos, jdelim, delimLen, leftTok, rightTok, left, rt, 
                          foundBangToken, temp1, temp2, temp3 >>

Lbl_69 == /\ pc = "Lbl_69"
          /\ curPos' = foundTokenSpecs[0].rightPos
          /\ foundBangToken' = FALSE
          /\ notDone' = TRUE
          /\ pc' = "Lbl_70"
          /\ UNCHANGED << line, foundTokenSpecs, lastToken, notLastToken, 
                          returnVal, tempVar1, tempVar2, tempVar3, stack, pos_, 
                          tokArray, i, tokIdx, pos_f, token, left_, rt_, 
                          pos_fi, pos_fin, delim_, ipos_, jdelim_, delimLen_, 
                          pos_find, pos, delim, ipos, jdelim, delimLen, 
                          leftTok, rightTok, currentToken, left, rt, temp1, 
                          temp2, temp3 >>

Lbl_70 == /\ pc = "Lbl_70"
          /\ IF notDone
                THEN /\ stack' = << [ procedure |->  "skipRightOverSpaces",
                                      pc        |->  "Lbl_71" ] >>
                                  \o stack
                     /\ pc' = "Lbl_30"
                     /\ UNCHANGED << returnVal, currentToken, left, rt, 
                                     notDone, foundBangToken, temp1, temp2, 
                                     temp3 >>
                ELSE /\ IF notLastToken /\ ~ foundBangToken
                           THEN /\ returnVal' = << >>
                                /\ pc' = Head(stack).pc
                                /\ currentToken' = Head(stack).currentToken
                                /\ left' = Head(stack).left
                                /\ rt' = Head(stack).rt
                                /\ notDone' = Head(stack).notDone
                                /\ foundBangToken' = Head(stack).foundBangToken
                                /\ temp1' = Head(stack).temp1
                                /\ temp2' = Head(stack).temp2
                                /\ temp3' = Head(stack).temp3
                                /\ stack' = Tail(stack)
                           ELSE /\ pc' = "Lbl_76"
                                /\ UNCHANGED << returnVal, stack, currentToken, 
                                                left, rt, notDone, 
                                                foundBangToken, temp1, temp2, 
                                                temp3 >>
          /\ UNCHANGED << line, foundTokenSpecs, lastToken, notLastToken, 
                          curPos, tempVar1, tempVar2, tempVar3, pos_, tokArray, 
                          i, tokIdx, pos_f, token, left_, rt_, pos_fi, pos_fin, 
                          delim_, ipos_, jdelim_, delimLen_, pos_find, pos, 
                          delim, ipos, jdelim, delimLen, leftTok, rightTok >>

Lbl_71 == /\ pc = "Lbl_71"
          /\ /\ pos_find' = curPos
             /\ stack' = << [ procedure |->  "findMatchingRightParen",
                              pc        |->  "Lbl_72",
                              pos_find  |->  pos_find ] >>
                          \o stack
          /\ pc' = "Lbl_17"
          /\ UNCHANGED << line, foundTokenSpecs, lastToken, notLastToken, 
                          curPos, returnVal, tempVar1, tempVar2, tempVar3, 
                          pos_, tokArray, i, tokIdx, pos_f, token, left_, rt_, 
                          pos_fi, pos_fin, delim_, ipos_, jdelim_, delimLen_, 
                          pos, delim, ipos, jdelim, delimLen, leftTok, 
                          rightTok, currentToken, left, rt, notDone, 
                          foundBangToken, temp1, temp2, temp3 >>

Lbl_72 == /\ pc = "Lbl_72"
          /\ curPos' = returnVal
          /\ IF curPos' < 0
                THEN /\ notDone' = FALSE
                     /\ pc' = "Lbl_70"
                     /\ UNCHANGED stack
                ELSE /\ stack' = << [ procedure |->  "skipRightOverSpaces",
                                      pc        |->  "Lbl_73" ] >>
                                  \o stack
                     /\ pc' = "Lbl_30"
                     /\ UNCHANGED notDone
          /\ UNCHANGED << line, foundTokenSpecs, lastToken, notLastToken, 
                          returnVal, tempVar1, tempVar2, tempVar3, pos_, 
                          tokArray, i, tokIdx, pos_f, token, left_, rt_, 
                          pos_fi, pos_fin, delim_, ipos_, jdelim_, delimLen_, 
                          pos_find, pos, delim, ipos, jdelim, delimLen, 
                          leftTok, rightTok, currentToken, left, rt, 
                          foundBangToken, temp1, temp2, temp3 >>

Lbl_73 == /\ pc = "Lbl_73"
          /\ IF line[curPos] # "!"  \/ line[curPos+1] = "!"
                THEN /\ notDone' = FALSE
                     /\ pc' = "Lbl_70"
                     /\ UNCHANGED << curPos, stack >>
                ELSE /\ curPos' = curPos + 1
                     /\ stack' = << [ procedure |->  "skipRightOverSpaces",
                                      pc        |->  "Lbl_74" ] >>
                                  \o stack
                     /\ pc' = "Lbl_30"
                     /\ UNCHANGED notDone
          /\ UNCHANGED << line, foundTokenSpecs, lastToken, notLastToken, 
                          returnVal, tempVar1, tempVar2, tempVar3, pos_, 
                          tokArray, i, tokIdx, pos_f, token, left_, rt_, 
                          pos_fi, pos_fin, delim_, ipos_, jdelim_, delimLen_, 
                          pos_find, pos, delim, ipos, jdelim, delimLen, 
                          leftTok, rightTok, currentToken, left, rt, 
                          foundBangToken, temp1, temp2, temp3 >>

Lbl_74 == /\ pc = "Lbl_74"
          /\ /\ pos_f' = curPos
             /\ stack' = << [ procedure |->  "findMaximalIdCharSeq",
                              pc        |->  "Lbl_75",
                              token     |->  token,
                              left_     |->  left_,
                              rt_       |->  rt_,
                              pos_f     |->  pos_f ] >>
                          \o stack
          /\ token' = << >>
          /\ left_' = pos_f'
          /\ rt_' = pos_f'
          /\ pc' = "Lbl_5"
          /\ UNCHANGED << line, foundTokenSpecs, lastToken, notLastToken, 
                          curPos, returnVal, tempVar1, tempVar2, tempVar3, 
                          pos_, tokArray, i, tokIdx, pos_fi, pos_fin, delim_, 
                          ipos_, jdelim_, delimLen_, pos_find, pos, delim, 
                          ipos, jdelim, delimLen, leftTok, rightTok, 
                          currentToken, left, rt, notDone, foundBangToken, 
                          temp1, temp2, temp3 >>

Lbl_75 == /\ pc = "Lbl_75"
          /\ currentToken' = returnVal
          /\ IF \/ currentToken' = NullTokenSpec
                \/ IsNumber(currentToken'.token)
                THEN /\ notDone' = FALSE
                     /\ UNCHANGED << foundTokenSpecs, curPos, foundBangToken >>
                ELSE /\ foundBangToken' = TRUE
                     /\ foundTokenSpecs' = JavaConcatenate(
                                             JavaSeq(
                                               << [token |->
                                                     JavaConcatenate(JavaAppend(foundTokenSpecs[0].token,
                                                                                 "!"),
                                                                     currentToken'.token),
                                                   leftPos |-> foundTokenSpecs[0].leftPos,
                                                   rightPos |-> currentToken'.rightPos]
                                                >> ) ,
                                               foundTokenSpecs)
                     /\ curPos' = currentToken'.rightPos
                     /\ UNCHANGED notDone
          /\ pc' = "Lbl_70"
          /\ UNCHANGED << line, lastToken, notLastToken, returnVal, tempVar1, 
                          tempVar2, tempVar3, stack, pos_, tokArray, i, tokIdx, 
                          pos_f, token, left_, rt_, pos_fi, pos_fin, delim_, 
                          ipos_, jdelim_, delimLen_, pos_find, pos, delim, 
                          ipos, jdelim, delimLen, leftTok, rightTok, left, rt, 
                          temp1, temp2, temp3 >>

Lbl_76 == /\ pc = "Lbl_76"
          /\ returnVal' = FixOrigin(foundTokenSpecs)
          /\ pc' = Head(stack).pc
          /\ currentToken' = Head(stack).currentToken
          /\ left' = Head(stack).left
          /\ rt' = Head(stack).rt
          /\ notDone' = Head(stack).notDone
          /\ foundBangToken' = Head(stack).foundBangToken
          /\ temp1' = Head(stack).temp1
          /\ temp2' = Head(stack).temp2
          /\ temp3' = Head(stack).temp3
          /\ stack' = Tail(stack)
          /\ UNCHANGED << line, foundTokenSpecs, lastToken, notLastToken, 
                          curPos, tempVar1, tempVar2, tempVar3, pos_, tokArray, 
                          i, tokIdx, pos_f, token, left_, rt_, pos_fi, pos_fin, 
                          delim_, ipos_, jdelim_, delimLen_, pos_find, pos, 
                          delim, ipos, jdelim, delimLen, leftTok, rightTok >>

findTokenSpecs == Lbl_31 \/ Lbl_32 \/ Lbl_33 \/ Lbl_34 \/ Lbl_35 \/ Lbl_36
                     \/ Lbl_37 \/ Lbl_38 \/ Lbl_39 \/ Lbl_40 \/ Lbl_41 \/ Lbl_42
                     \/ Lbl_43 \/ Lbl_44 \/ Lbl_45 \/ Lbl_46 \/ Lbl_47 \/ Lbl_48
                     \/ Lbl_49 \/ Lbl_50 \/ Lbl_51 \/ Lbl_52 \/ Lbl_53 \/ Lbl_54
                     \/ Lbl_55 \/ Lbl_56 \/ Lbl_57 \/ Lbl_58 \/ Lbl_59 \/ Lbl_60
                     \/ Lbl_61 \/ Lbl_62 \/ Lbl_63 \/ Lbl_64 \/ Lbl_65 \/ Lbl_66
                     \/ Lbl_67 \/ Lbl_68 \/ Lbl_69 \/ Lbl_70 \/ Lbl_71 \/ Lbl_72
                     \/ Lbl_73 \/ Lbl_74 \/ Lbl_75 \/ Lbl_76

Lbl_77 == /\ pc = "Lbl_77"
          /\ curPos' = JavaLen(Padding)
          /\ tempVar1' = ( -1 :> "")
          /\ tempVar2' = JavaLen(Padding)
          /\ PrintT(line)
          /\ pc' = "Lbl_78"
          /\ UNCHANGED << line, foundTokenSpecs, lastToken, notLastToken, 
                          returnVal, tempVar3, stack, pos_, tokArray, i, 
                          tokIdx, pos_f, token, left_, rt_, pos_fi, pos_fin, 
                          delim_, ipos_, jdelim_, delimLen_, pos_find, pos, 
                          delim, ipos, jdelim, delimLen, leftTok, rightTok, 
                          currentToken, left, rt, notDone, foundBangToken, 
                          temp1, temp2, temp3 >>

Lbl_78 == /\ pc = "Lbl_78"
          /\ IF tempVar2 < JavaLen(lineInput) + JavaLen(Padding)
                THEN /\ PrintT(<<"curPos: ", tempVar2>>)
                     /\ curPos' = tempVar2
                     /\ foundTokenSpecs' = << >>
                     /\ lastToken' = FALSE
                     /\ notLastToken' = FALSE
                     /\ stack' = << [ procedure |->  "findTokenSpecs",
                                      pc        |->  "Lbl_79",
                                      currentToken |->  currentToken,
                                      left      |->  left,
                                      rt        |->  rt,
                                      notDone   |->  notDone,
                                      foundBangToken |->  foundBangToken,
                                      temp1     |->  temp1,
                                      temp2     |->  temp2,
                                      temp3     |->  temp3 ] >>
                                  \o stack
                     /\ currentToken' = defaultInitValue
                     /\ left' = defaultInitValue
                     /\ rt' = defaultInitValue
                     /\ notDone' = defaultInitValue
                     /\ foundBangToken' = defaultInitValue
                     /\ temp1' = defaultInitValue
                     /\ temp2' = defaultInitValue
                     /\ temp3' = defaultInitValue
                     /\ pc' = "Lbl_31"
                ELSE /\ PrintT("goodby world")
                     /\ pc' = "Done"
                     /\ UNCHANGED << foundTokenSpecs, lastToken, notLastToken, 
                                     curPos, stack, currentToken, left, rt, 
                                     notDone, foundBangToken, temp1, temp2, 
                                     temp3 >>
          /\ UNCHANGED << line, returnVal, tempVar1, tempVar2, tempVar3, pos_, 
                          tokArray, i, tokIdx, pos_f, token, left_, rt_, 
                          pos_fi, pos_fin, delim_, ipos_, jdelim_, delimLen_, 
                          pos_find, pos, delim, ipos, jdelim, delimLen, 
                          leftTok, rightTok >>

Lbl_79 == /\ pc = "Lbl_79"
          /\ IF returnVal = tempVar1
                THEN /\ PrintT("same")
                ELSE /\ PrintT(returnVal)
          /\ tempVar1' = returnVal
          /\ tempVar2' = tempVar2 + 1
          /\ pc' = "Lbl_78"
          /\ UNCHANGED << line, foundTokenSpecs, lastToken, notLastToken, 
                          curPos, returnVal, tempVar3, stack, pos_, tokArray, 
                          i, tokIdx, pos_f, token, left_, rt_, pos_fi, pos_fin, 
                          delim_, ipos_, jdelim_, delimLen_, pos_find, pos, 
                          delim, ipos, jdelim, delimLen, leftTok, rightTok, 
                          currentToken, left, rt, notDone, foundBangToken, 
                          temp1, temp2, temp3 >>

Next == findTokenIn \/ findMaximalIdCharSeq \/ findMatchingLeftParen
           \/ findMatchingLeftInner \/ findMatchingRightParen
           \/ findMatchingRightInner \/ checkIfStepName \/ skipLeftOverSpaces
           \/ skipRightOverSpaces \/ findTokenSpecs \/ Lbl_77 \/ Lbl_78 \/ Lbl_79
           \/ (* Disjunct to prevent deadlock on termination *)
              (pc = "Done" /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION
=============================================================================
\* Modification History
\* Last modified Fri Sep 24 02:20:56 PDT 2010 by lamport
\* Created Mon Sep 20 06:42:12 PDT 2010 by lamport
****************************************************************************)


*************************************************************************/
