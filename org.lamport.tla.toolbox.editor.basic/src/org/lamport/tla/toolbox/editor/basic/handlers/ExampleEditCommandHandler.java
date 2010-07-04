package org.lamport.tla.toolbox.editor.basic.handlers;

import org.eclipse.core.commands.AbstractHandler;
import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.core.commands.ExecutionException;
import org.eclipse.jface.text.BadLocationException;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.IRegion;
import org.eclipse.jface.text.ITextSelection;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.swt.SWT;
import org.eclipse.swt.custom.VerifyKeyListener;
import org.eclipse.swt.events.FocusEvent;
import org.eclipse.swt.events.FocusListener;
import org.eclipse.swt.events.VerifyEvent;
import org.lamport.tla.toolbox.Activator;
import org.lamport.tla.toolbox.editor.basic.TLAEditor;
import org.lamport.tla.toolbox.editor.basic.util.DocumentHelper;
import org.lamport.tla.toolbox.editor.basic.util.EditorUtil;

/**
 * Performs a useless command to illustrate how to get keyboard input
 * and modify the contents of an editor.
 * 
 * When execute is called, if a TLA editor currently has focus, this
 * handler starts listening for key strokes and starts listening
 * for focus events on the editor's underlying widget. It will stop listening for key
 * strokes if the widget loses focus or after the first key stroke is entered.
 * 
 * If the first key stroke to be entered is a digit, this handler finds
 * the word currently containing the caret in the editor and repeats that word
 * the number of times equal to the digit pressed. If the key pressed
 * is not a digit, this does nothing to the document and
 * removes itself from subsequent key events.
 * 
 * @author Daniel Ricketts
 *
 */
public class ExampleEditCommandHandler extends AbstractHandler implements VerifyKeyListener, FocusListener
{

    private TLAEditor editor;

    public Object execute(ExecutionEvent event) throws ExecutionException
    {
        /********
        String[] testName = { ColorPredicate.PROVED_STATUS, ColorPredicate.PROVED_STATUS, ColorPredicate.PROVED_STATUS };
        System.out.println(testName[0]);
        System.out.println(testName[1]);
        System.out.println(testName[2]);

        System.out.println(testName[0] + ", " + testName[1] + ", " + testName[2] + " -> "
                + ColorPredicate.numberOfState(testName));
         System.out.println("Inverse of number = " +
         ColorPredicate.numberToState(ColorPredicate.numberOfState(testName)));
         
         System.out.println("BitVector Test");
         String[][] test = { {"untried", "proved"}, {"untried", "proving"}, {"untried"}};
         long bitVector = ColorPredicate.bitVectorOfStates(test);
         ColorPredicate.printBitVectorOfStates(bitVector);
         *****/
        int[] states = new int[] {ColorPredicate.numberOfState(new int[] {3, 2, 0}),
                ColorPredicate.numberOfState(new int[] {2, 3, 0}),
                1
                };
        for (int i= 0; i < ColorPredicate.PREDEFINED_MACROS.length; i++) {
//            System.out.println(ColorPredicate.PREDEFINED_MACROS[i][0]);
            ColorPredicate cp = new ColorPredicate(ColorPredicate.PREDEFINED_MACROS[i][0]);
            System.out.println(ColorPredicate.PREDEFINED_MACROS[i][0] +
                    " value: " + cp.satisfiedByObligations(states));
            
        }
       
        ColorPredicate cp = new ColorPredicate(
                " leaf None" ); //   
        System.out.println(cp.toString());
        
        

         /***
        editor = EditorUtil.getTLAEditorWithFocus();
        if (editor != null)
        {
            install();
        }
        **/
        return null;
    }

    /**
     * Listens for the first key to be pressed. If it is a digit, it
     * finds the word currently containing the caret and repeats that word
     * the number of times equal to the digit pressed. If the key pressed
     * is not a digit, this does nothing to the document and
     * removes itself from subsequent key events.
     */
    public void verifyKey(VerifyEvent event)
    {
        try
        {
            // no other listeners should respond to this event
            event.doit = false;

            // the state mask indicates what modifier keys (such as CTRL) were being
            // pressed when the character was pressed

            // the digit should be pressed without any modifier keys
            if (event.stateMask == SWT.NONE && Character.isDigit(event.character))
            {
                // get the digit input
                int input = Character.getNumericValue(event.character);

                // get the text selection
                ISelection selection = editor.getSelectionProvider().getSelection();

                if (selection != null && selection instanceof ITextSelection)
                {
                    ITextSelection textSelection = (ITextSelection) selection;

                    IDocument document = editor.getDocumentProvider().getDocument(editor.getEditorInput());

                    // if one or more characters are highlighted, do nothing
                    if (textSelection.getLength() == 0 && document != null)
                    {

                        // retrieve the region describing the word containing
                        // the caret
                        IRegion region = DocumentHelper.getRegionExpandedBoth(document, textSelection.getOffset(),
                                DocumentHelper.getDefaultWordDetector());
                        try
                        {

                            // generate the insertion string
                            String insertionText = " " + document.get(region.getOffset(), region.getLength());
                            StringBuilder sb = new StringBuilder();
                            for (int i = 0; i < input; i++)
                            {
                                sb.append(insertionText);
                            }

                            // insert the string
                            document.replace(region.getOffset() + region.getLength(), 0, sb.toString());
                        } catch (BadLocationException e)
                        {
                            // TODO Auto-generated catch block
                            e.printStackTrace();
                        }
                    }
                }
            }
        } finally
        {

            uninstall();
        }
    }

    /**
     * This should never be called. The handler
     * should only be listening if there already is focus
     * and should be removed as a listener when focus
     * is lost.
     */
    public void focusGained(FocusEvent e)
    {
        // TODO Auto-generated method stub

    }

    /**
     * Uninstalls the handler.
     */
    public void focusLost(FocusEvent e)
    {
        uninstall();
    }

    /**
     * Should be called when the handler starts listening
     * for key strokes.
     * 
     * Adds this as a key stroke listener, adds to focus listeners
     * of the underlying text widget of the editor, and sets the
     * status line.
     * 
     * This is added as a focus listener so that it can uninstall()
     * itself if focus is lost.
     */
    private void install()
    {
        editor.getViewer().prependVerifyKeyListener(this);
        editor.getViewer().getTextWidget().addFocusListener(this);
        editor.setStatusMessage("Example command.");
    }

    /**
     * Should be called when the handler is done listening for
     * key strokes.
     * 
     * Removes itself as a key stroke listener, a focus listener, and sets
     * the status line to the empty string.
     */
    private void uninstall()
    {
        // do not listen to any other key strokes
        editor.getViewer().removeVerifyKeyListener(this);

        editor.getViewer().getTextWidget().removeFocusListener(this);

        editor.setStatusMessage("");
    }

    // TESTING
    public static class ColorPredicate
    {
        public boolean isLeaf; // true iff this predicate is true only for leaf proof steps
        public boolean isSome;
        public long set;

        // The prover names are used only for error messages. Provers are generally
        // referred to by number, where PROVER_NAMES[i] is the name of prover number i.
        public static final String[] PROVER_NAMES = { "isabelle", "other_backend", "tlapm" };

        // We name the possible prover statuses, so Java can catch misspellings.
        public static final String UNTRIED_STATUS = "untried";
        public static final String PROVING_STATUS = "proving";
        public static final String PROVED_STATUS = "proved";
        public static final String FAILED_STATUS = "failed";
        public static final String STOPPED_STATUS = "stopped";

        // The constant PROVER_STATUSES determines the set of possible obligation states.
        public static final String[] ISABELLE_STATUSES = { UNTRIED_STATUS, PROVING_STATUS, PROVED_STATUS, FAILED_STATUS,
                STOPPED_STATUS };
        public static final String[] OTHER_PROVER_STATUSES = ISABELLE_STATUSES;
        public static final String[] TLAPM_STATUSES = { UNTRIED_STATUS, PROVED_STATUS };
        public static final String[][] PROVER_STATUSES = { ISABELLE_STATUSES, OTHER_PROVER_STATUSES, TLAPM_STATUSES };

        public static final int NUMBER_OF_PROVERS = PROVER_NAMES.length;

        // The array of predefined macros
        public static final String[][] PREDEFINED_MACROS = { { "None", "some" }, //
                { "All", "every (,,)" }, //
                { "Proved", "every (proved, , ) (,proved,) (,,proved)" }, //
                { "ProvedOrOmitted", "every omitted (proved, , ) (,proved,) (,,proved)" }, //
                { "NotProved", "some (-proved, -proved, -proved)" }, //
                { "FailedUnproved", "some (failed,-proved,-proved) (-proved,failed,-proved)" }, //
                { "FailedOrStoppedUnproved", "some (failed stopped,-proved,-proved) (-proved,failed stopped,-proved)" }, //
                { "Failed", "some (failed,,) (,failed,)" }, //
                { "FailedOrStopped", "some (failed stopped,,) (,failed stopped,)" }, //
                { "BeingProved", "some (proving,,) (,proving,)" }, //            
                { "Missing", "some missing" }, //
                { "Omitted", "some omitted" }, //
                { "MissingOrOmitted", "some missing omitted" }, //
                { "ProvedByIsabelle", "every (proved,,)" }, //
                { "Stopped", "some (stopped,,) (,stopped,)" }, //
                { "StoppedUnproved", "some (stopped,-proved,-proved) (-proved,stopped,-proved)" }, //            
        };

        /**
         * Returns the macro with name macroName, else returns null if there
         * is none.  (Case of names is ignored.)  This implementation searches
         * only in the PREDEFINE_MACROS.  If users can define macros with
         * preferences, then we need to reimplement this.
         * 
         * @param macroName
         * @return
         */
        public static final String getMacro(String macroName)
        {
            for (int i = 0; i < PREDEFINED_MACROS.length; i++)
            {
                if (macroName.equalsIgnoreCase(PREDEFINED_MACROS[i][0]))
                {
                    return PREDEFINED_MACROS[i][1];
                }
            }
            return null;
        }

        /**
         * Returns the number of the status named statusName for prover numbered
         * proverNumber.  
         * 
         * @param proverNumber
         * @param statusName
         * @return
         * @throws IllegalArgumentException
         */
        public static final int numberOfProverStatus(int proverNumber, String statusName) throws IllegalArgumentException
        {
            if (proverNumber > NUMBER_OF_PROVERS || proverNumber < 0)
            {
                throw new IllegalArgumentException("No prover number " + proverNumber);
            }
            for (int i = 0; i < PROVER_STATUSES[proverNumber].length; i++)
            {
                if (statusName.equals(PROVER_STATUSES[proverNumber][i]))
                {
                    return i;
                }
            }
            throw new IllegalArgumentException("Prover " + PROVER_NAMES[proverNumber] + " has no status " + statusName);
        }

        /*
         * An obligation state is either Missing, Omitted, or an array indexed by
         * provers of prover statuses.  Each state has a unique number in the range
         * from 0 to one less than the total number of states.  Tge numbers of the 
         * Missing and Omitted states are: 
         */
        public static final int NUMBER_OF_MISSING_STATE = 0;
        public static final int NUMBER_OF_OMITTED_STATE = 1;

        /*
         * For other states, that number is returned by the following methods.
         */

        /**
         * Returns the obligation-state number for a state specified by an
         * array indexed by provers of of prover-status numbers.
         * 
         * @param statuses
         * @return
         * @throws IllegalArgumentException
         */
        public static final int numberOfState(int[] statuses) throws IllegalArgumentException
        {
            if (statuses.length != NUMBER_OF_PROVERS)
            {
                throw new IllegalArgumentException("Wrong number of provers specified");
            }
            int multiplier = 1;
            int result = 2;
            for (int i = 0; i < NUMBER_OF_PROVERS; i++)
            {
                if (statuses[i] >= PROVER_STATUSES[i].length || statuses[i] < 0)
                {
                    throw new IllegalArgumentException("Prover " + PROVER_NAMES[i] + " does not have status number "
                            + statuses[i]);
                }
                result = result + multiplier * statuses[i];
                multiplier = multiplier * PROVER_STATUSES[i].length;
            }
            return result;
        }

        /**
         * Returns the obligation-state number for a state specified by an
         * array indexed by provers of prover-status names.
         * 
         * @param statuses
         * @return
         * @throws IllegalArgumentException
         */
        public static final int numberOfState(String[] statuses) throws IllegalArgumentException
        {
            int[] statusNumbers = new int[statuses.length];
            for (int i = 0; i < statuses.length; i++)
            {
                statusNumbers[i] = numberOfProverStatus(i, statuses[i]);
            }
            return numberOfState(statusNumbers);
        }

        /** 
         * Returns a printable version of the state with number stateNumber.
         * Assumes that NUMBER_OF_PROVERS = 3.
         * 
         * @param stateNumber
         * @return
         */

        public static final String numberToState(int stateNumber)
        {
            if (stateNumber == NUMBER_OF_MISSING_STATE)
            {
                return "Missing";
            }
            if (stateNumber == NUMBER_OF_OMITTED_STATE)
            {
                return "Omitted";
            }
            int[] array = new int[3];
            if (3 != NUMBER_OF_PROVERS)
            {
                Activator.logDebug("Method ColorPredicate.numberToState must be reimplemented"
                        + " when number of provers changes");
            }
            for (int i = 0; i < PROVER_STATUSES[0].length; i++)
            {
                array[0] = i;
                for (int j = 0; j < PROVER_STATUSES[1].length; j++)
                {
                    array[1] = j;
                    for (int k = 0; k < PROVER_STATUSES[2].length; k++)
                    {
                        array[2] = k;
                        if (numberOfState(array) == stateNumber)
                        {
                            return "(" + PROVER_STATUSES[0][i] + ", " + PROVER_STATUSES[1][j] + ", "
                                    + PROVER_STATUSES[2][k] + ")";
                        }
                    }
                }
            }
            return "No state with number " + stateNumber;
        }

        /**
         * Returns the bitVector with bit i set iff there exists some j_0, j_1, ...
         * such that i = numberOfState(array) where array[0] = statuses[0][j_0],
         * array[1] = statuses[1][j_1], etc.
         * 
         * This implementation works only for 3 provers.
         * 
         * @param statuses
         * @return
         */
        public static final long bitVectorOfStates(int[][] statuses) throws IllegalArgumentException
        {
            if (statuses.length != NUMBER_OF_PROVERS)
            {
                Activator.logDebug("Method ColorPredicate.bitVectorOfStates must be reimplemented"
                        + " when number of provers changes");
            }
            long result = 0;
            int[] array = new int[3];
            for (int i = 0; i < statuses[0].length; i++)
            {
                array[0] = statuses[0][i];
                for (int j = 0; j < statuses[1].length; j++)
                {
                    array[1] = statuses[1][j];
                    for (int k = 0; k < statuses[2].length; k++)
                    {
                        array[2] = statuses[2][k];
                        result = result | (1L << numberOfState(array));
                    }
                }
            }
            return result;
        }

        public static final long bitVectorOfStates(String[][] statuses) throws IllegalArgumentException
        {
            int[][] arg = new int[statuses.length][];
            for (int i = 0; i < arg.length; i++)
            {
                arg[i] = new int[statuses[i].length];
                for (int j = 0; j < arg[i].length; j++)
                {
                    arg[i][j] = numberOfProverStatus(i, statuses[i][j]);
                }
            }
            return bitVectorOfStates(arg);
        }

        /**
         * For debugging.  Prints the list of states represented by a bit vector.
         * @param vector
         */
        public static final void printBitVectorOfStates(long vector)
        {
            System.out.println(bitVectorOfStatesToString(vector));
        }

        public static final String bitVectorOfStatesToString(long vector)
        {
            long rest = vector;
            String result = "";
            for (int i = 0; i < 60; i++)
            {
                if ((rest & 1) == 1)
                {
                    result = result + numberToState(i) + "\n";
                }
                rest = rest >>> 1;
            }
            return result;
        }

        /**
         * Returns true iff this color predicate is satisfied by a set of
         * obligations whose states have the numbers in the array
         * obligationStateNumbers.
         * 
         * @param obligationStateNumbers
         * @return
         */
        public boolean satisfiedByObligations(int[] obligationStateNumbers)
        {
            // Sets childValues[i] to true iff the i-th obligation state 
            // is in this.set; then calls satisfiedBasedOnChildrenValues.
            //
            boolean[] childValues = new boolean[obligationStateNumbers.length];
            for (int i = 0; i < obligationStateNumbers.length; i++)
            {
                long bit = 1L << obligationStateNumbers[i];
                childValues[i] = (bit & this.set) != 0;
            }
            return this.satisfiedBasedOnChildrenValues(childValues);
        }
       
        /**
         * Computes the value of this color predicate for a non-leaf proof
         * based on the values of the color predicate for its children.
         * 
         * @param childValues
         * @return
         */
        public boolean satisfiedBasedOnChildren(boolean[] childValues) {
            if (this.isLeaf) {
                return false;
            }
            return satisfiedBasedOnChildrenValues(childValues);
        }
        
        /**
         * Inner method for satisfiedBasedOnChildren for a non-leaf
         * color predicate.
         * 
         * @param childValues
         * @return
         */
        public boolean satisfiedBasedOnChildrenValues(boolean[] childValues)
        {
            boolean result = !this.isSome;
            if (this.isSome)
            {
                for (int i = 0; i < childValues.length; i++)
                {
                    result = result || childValues[i];
                }
            } else
            {
                for (int i = 0; i < childValues.length; i++)
                {
                    result = result && childValues[i];
                }
            }
            return result;
        }

        /**
         * Returns a ColorPredicate obtained by parsing its argument.
         * See the beginning of ProofStatus.tla for the grammar of
         * the input.
         * 
         * @param input
         */
        public ColorPredicate(String input) throws IllegalArgumentException
        {
            String rest = input.trim().toLowerCase();
            if (rest.startsWith("leaf"))
            {
                this.isLeaf = true;
                rest = rest.substring(4).trim();
            } else
            {
                this.isLeaf = false;
            }

            // if the next token is a macro name, set rest to the
            // macro definition
            int endOfStartToken = 0;
            while (endOfStartToken < rest.length() && Character.isLetter(rest.charAt(endOfStartToken)))
            {
                endOfStartToken++;
            }
            String startToken = rest.substring(0, endOfStartToken);
            String macro = getMacro(startToken);
            if (macro != null)
            {
                rest = macro;
            }

            if (rest.startsWith("some"))
            {
                this.isSome = true;
                rest = rest.substring(4).trim();
            } else if (rest.startsWith("every"))
            {
                this.isSome = false;
                rest = rest.substring(5).trim();
            } else
            {
                throw new IllegalArgumentException("Color predicate must have `every' or `some' specifier.");
            }

            this.set = 0;
            while (!rest.equals(""))
            {
                if (rest.startsWith("omitted"))
                {
                    this.set = this.set | (1 << NUMBER_OF_OMITTED_STATE);
                    rest = rest.substring(7).trim();
                } else if (rest.startsWith("missing"))
                {
                    this.set = this.set | (1 << NUMBER_OF_MISSING_STATE);
                    rest = rest.substring(7).trim();
                } else if (rest.startsWith("("))
                {
                    rest = rest.substring(1).trim();
                    // stateSetSpec[i] is set to the array of proof-status numbers
                    // specified for prover number i.
                    int[][] stateSetSpec = new int[NUMBER_OF_PROVERS][];
                    for (int i = 0; i < NUMBER_OF_PROVERS; i++)
                    {
                        // The body of the for loop computes stateSetSpec[i].

                        // Set invert to true iff there is a "=" specifier.
                        boolean invert = false;
                        if (rest.startsWith("-"))
                        {
                            invert = true;
                            rest = rest.substring(1).trim();
                        }
                        // We set appears[j] = true iff proof-status number
                        // j for prover i is to be included in stateSetSpec[i].
                        boolean[] appears = new boolean[PROVER_STATUSES[i].length];
                        for (int j = 0; j < appears.length; j++)
                        {
                            appears[j] = invert;
                        }
                        // endChar is the ending character for this prover's list of statuses.
                        String endChar = (i == NUMBER_OF_PROVERS - 1) ? ")" : ",";
                        // loop until the end character is found
                        while (rest.length() > 0 && !rest.startsWith(endChar))
                        {
                            // set token to the beginning string delimited by a
                            // non-letter
                            int endOfToken = 0;
                            while (endOfToken < rest.length() && Character.isLetter(rest.charAt(endOfToken)))
                            {
                                endOfToken++;
                            }
                            String token = rest.substring(0, endOfToken);
                            rest = rest.substring(endOfToken).trim();

                            // set statusNumber to number of status for prover i;
                            int statusNumber;
                            try
                            {
                                statusNumber = numberOfProverStatus(i, token);
                            } catch (IllegalArgumentException e)
                            {
                                String errorMsg = "Was expecting status of prover " + PROVER_NAMES[i] + " but found `"
                                        + token + "' followed by: \n `" + rest + "'";
                                throw new IllegalArgumentException(errorMsg);
                            }

                            // set appears[statusNumber]
                            appears[statusNumber] = !invert;
                        }

                        if (rest.length() == 0)
                        {
                            throw new IllegalArgumentException(
                                    "Color predicate specifier ended before `(...)' expression complete");
                        }

                        // Mustn't forget to remove the endChar
                        rest = rest.substring(1).trim();

                        // set count to the number of j for which appears[j] = true
                        int count = 0;
                        for (int j = 0; j < appears.length; j++)
                        {
                            if (appears[j])
                            {
                                count++;
                            }
                        }

                        // If no status was specified, then treat it as if every status
                        // was specified.
                        if (count == 0)
                        {
                            if (invert)
                            {
                                throw new IllegalArgumentException("A `-' must be followed by one or more statuses");
                            } else
                            {
                                count = appears.length;
                                for (int j = 0; j < count; j++)
                                {
                                    appears[j] = true;
                                }
                            }
                        }

                        // Finally, set stateSetSpec[i]
                        stateSetSpec[i] = new int[count];
                        int k = 0;
                        for (int j = 0; j < appears.length; j++)
                        {
                            if (appears[j])
                            {
                                stateSetSpec[i][k] = j;
                                k++;
                            }
                        }
                    }
                    // Having now computed stateSetSpec, we now convert it to
                    // a bit vector and OR it to this.set
                    this.set = this.set | bitVectorOfStates(stateSetSpec);

                } else
                {
                    throw new IllegalArgumentException("Unexpected token at: `" + rest + "'");
                }
            }
        }

        public String toString()
        {
            String result = "leaf: " + isLeaf + "\n";
            result = result + "type: " + ((isSome) ? "some" : "every") + "\n";
            result = result + "set of states:\n";
            try
            {
                result = result + bitVectorOfStatesToString(this.set);
            } catch (IllegalArgumentException e)
            {
                result = result + "Illegal Bit Vector\n";
            }

            return result;
        }
    }

 }
