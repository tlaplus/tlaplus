/**
 *  This is the Java implementation of color predicates described informally
 *  in the comments in ProofStatus.tla and formally in the module ProofStatus
 *  and its instantiated module ColorPredicates.  Both these files are appended
 *  in comments at the end of this file.
 *  
 *  Here is how Color Predicates are used by the Toolbox's Prover Plugin. 
 *  
 *  It must provide marker types numbered 1 through MAX_PROOF_COLOR whose color and
 *  whether or not they are displayed in the right-column can be set by the user.
 *  
 *  It must allow the user to provide a color predicate as a string for each
 *  marker type.  It uses the ColorPredicate constructor to turn that string
 *  into a ColorPredicate object.  (It should catch the IllegalArgumentException
 *  and use its message as an error message for the user.)  
 *  
 *  The user will usually specify a ColorPredicate with a string that
 *  begins with the optional string "leaf", indicating that the predicate 
 *  is true only for leaf proof steps followed by a predefined macro name. 
 *  The list of predefined macros is specified by the array
 *  PREDEFINED_MACROS.  You can probably figure out the syntax of macro
 *  definitions from that array; it is described in the comments at the
 *  end of this file.  The user should be given the option either of
 *  defining his own macros or of specifying a ColorPredicate in terms of
 *  the primitive language in which the macros are defined.  The constructor
 *  accepts them written either way.  However, if user-defined macros are
 *  introduced, then the getMacro method must be re-implemented so it can
 *  find their definitions. 
 *  
 *  Theorems and proof steps are colored by placing markers on them.  A marker 
 *  placed on a proof step will be of marker type i iff the i-th color predicate 
 *  is true and no lower-numbered color predicate is true.  (There should probably
 *  be a default marker that is uncolored for proofs in which all the
 *  color predicates are false.
 *  
 *  Here is how the Toolbox methods are used to determine the truth value 
 *  of a color predicate.
 *  
 *  A proof obligation has a state which is an array indexed by prover numbers of
 *  prover statuses.  There are currently 3 provers, numbered 0-2, of provers
 *  with names "isabelle", "other_backend", and "tlapm".  The possible statuses
 *  of those whose names and numbers are given by the arrays ISABELLE_STATUSES,
 *  OTHER_PROVER_STATUSES, and TLAPM_STATUSES.  (The status's number is the
 *  position of its name in the appropriate array, numbers of course starting
 *  at 0.)  
 *  
 *  In addition, a step that takes a proof but has none has a dummy obligation
 *  with the special state Missing or Omitted.
 *  
 *  Obligation states are passed to the methods in this class by their numbers.
 *  The Missing and Omitted status have numbers NUMBER_OF_MISSING_STATE and
 *  NUMBER_OF_OMITTED_STATE.  The number of any other proof-obligation state
 *  is obtained by calling one of the static methods named numberOfState
 *  (one takes the prover statuses as an array of status names [strings] and the
 *  other as an array of status numbers).
 *  
 *  To obtain the truth-value of a color predicate on a leaf step, you call
 *  satisfiedByObligations with argument an array of obligation state numbers--the
 *  numbers of the states of all the step's obligations.
 *  
 *  To obtain the truth-value of a color predicate on a leaf step, you call
 *  satisfiedBasedOnChildren with argument an array of the (truth) values of
 *  the color predicate on all the children of the step.
 *
 */
package org.lamport.tla.toolbox.tool.prover.ui.output.data;

import org.lamport.tla.toolbox.Activator;

/**
 * @author lamport
 *
 */
public class ColorPredicate
{
    public boolean isLeaf; // true iff this predicate is true only for leaf proof steps
    public boolean isSome;
    public long set;

    /**
     * The index into {@link #PROVER_STATUSES}.
     */
    public static final int ISABELLE_NUM = 0;
    public static final int OTHER_BACKEND_NUM = 1;
    public static final int TLAPM_NUM = 2;

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

    public static final int TO_BE_PROVED_STATE = numberOfState(new String[] { UNTRIED_STATUS, UNTRIED_STATUS,
            UNTRIED_STATUS });

    // The array of predefined macros, the i-th macro having name
    // PREDEFINED_MACROS[i][0] and definition PREDEFINED_MACROS[i][1].
    // We may or may not change the names to be descriptive, depending on
    // how we resolve the ComboFieldEditor mess.

    public static final String PREDICATE_NONE = "some";
    public static final String PREDICATE_ALL = "every missing omitted ( , , )";
    public static final String PREDICATE_PROVED = "every (proved, , ) (,proved,) (,,proved)";
    public static final String PREDICATE_PROVED_OR_OMITTED = "every omitted (proved, , ) (,proved,) (,,proved)";
    public static final String PREDICATE_PROVED_OR_OMITTED_OR_MISSING = "every omitted missing (proved, , ) (,proved,) (,,proved)";
    public static final String PREDICATE_UNPROVED = "some (-proved, -proved, -proved)";
    public static final String PREDICATE_FAILED = "some (failed,-proved,-proved) (-proved,failed,-proved)";
    public static final String PREDICATE_FAILED_OR_STOPPED_UNPROVED = "some (failed stopped,-proved,-proved) (-proved,failed stopped,-proved)";
    public static final String PREDICATE_FAILED_SO_FAR = "some (failed,-failed,)";
    public static final String PREDICATE_FAILED_OR_STOPPED = "some (failed stopped,,) (,failed stopped,)";
    public static final String PREDICATE_BEING_PROVED = "some (proving,,) (,proving,)";
    public static final String PREDICATE_MISSING = "some missing";
    public static final String PREDICATE_OMITTED = "some omitted";
    public static final String PREDICATE_MISSING_OR_OMITTED = "some missing omitted";
    public static final String PREDICATE_PROVED_BY_ISABELLE = "every (proved,,)";
    public static final String PREDICATE_PROVED_BY_ISABELLE_OR_TRIVIAL = "every (proved,,) (,,proved)";
    public static final String PREDICATE_STOPPED = "some (stopped,,) (,stopped,) (failed, untried)";
    public static final String PREDICATE_STOPPED_UNPROVED = "some (stopped,-proved,-proved) (-proved,stopped,-proved)";
    public static final String PREDICATE_TRIVIAL = "every (,,proved)";


     public static final String[][] PREDEFINED_MACROS = {  //

             { "none", PREDICATE_NONE }, // always false

             { "all proved", PREDICATE_PROVED },

             // every obligation either proved or OMITTED
             { "all proved or omitted", PREDICATE_PROVED_OR_OMITTED },
         
             // every obligation either proved or OMITTED    
             {"all proved, omitted, or missing", PREDICATE_PROVED_OR_OMITTED_OR_MISSING},
             
             // Some obligation has not been proved.
             { "some not proved", PREDICATE_UNPROVED },

             // The proof of some obligation was stopped.
             { "some stopped", PREDICATE_STOPPED },

             // The proof of some obligation that has not been proved was stopped.
             { "some stopped and unproven", PREDICATE_STOPPED_UNPROVED },

             // Some obligation has failed on one prover and not been proved by another.
             { "some failed", PREDICATE_FAILED },

             // Some obligation has failed or been stopped on one prover and not been proved by another.
             { "some failed or stopped", PREDICATE_FAILED_OR_STOPPED },

             // Some obligation has failed on some prover, but could yet be proved by Isabelle.
             { "Some failed on non-isabelle prover", PREDICATE_FAILED_SO_FAR },

             // Some obligation has failed or been stopped on some prover.
             { "Some failed or stopped", PREDICATE_FAILED_OR_STOPPED_UNPROVED },

             // Some obligation is still being proved or has failed a secondary prover
             // but not yet tried by Isabelle
             { "Some being proved", PREDICATE_BEING_PROVED },

             // Some obligation is missing.
             { "some missing", PREDICATE_MISSING },

             // Some obligation has PROOF OMITTED
             { "some omitted", PREDICATE_OMITTED },

             // Some obligation is either missing or has PROOF OMITTED
             { "some missing or omitted", PREDICATE_MISSING_OR_OMITTED },

             // Every obligation has been proved by Isabelle (aka proved in paranoid mode)
             { "all proved by isabelle", PREDICATE_PROVED_BY_ISABELLE },

             // Every nontrivial obligation has been proved by Isabelle
             { "all proved by isabelle or trivial", PREDICATE_PROVED_BY_ISABELLE_OR_TRIVIAL },

             // Every obligation was found by TLAPM to be trivial.
             { "all trivial", PREDICATE_TRIVIAL }, //

             { "all", PREDICATE_ALL }, // always true
             
             // every obligation proved
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
     * Returns an array giving the String status of each prover for the obligation
     * state. The statuses are in the order of the provers in {@link #PROVER_NAMES}.
     * 
     * Returns null if the stateNum is {@link #NUMBER_OF_MISSING_STATE}
     * or {@value #NUMBER_OF_OMITTED_STATE}
     * 
     * @param obligationState
     * @return
     */
    public static final String[] proverStatuses(int stateNum)
    {

        if (stateNum == NUMBER_OF_MISSING_STATE || stateNum == NUMBER_OF_OMITTED_STATE)
        {
            return null;
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
                    if (numberOfState(array) == stateNum)
                    {
                        return new String[] { PROVER_STATUSES[0][i], PROVER_STATUSES[1][j], PROVER_STATUSES[2][k] };
                    }
                }
            }
        }
        return null;

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
                        return PROVER_NAMES[0] + " : " + PROVER_STATUSES[0][i] + ", " + PROVER_NAMES[1] + " : "
                                + PROVER_STATUSES[1][j] + ", " + PROVER_NAMES[2] + " : " + PROVER_STATUSES[2][k];
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
     * Returns the number of the new state from the old state and the new status
     * of a prover.  Returns -1 if it's called with oldStateNumber the number
     * of an omitted or missing dummy obligation, or with a number larger than
     * any state number.
     * 
     * @param oldStateNumber
     * @param proverNumber
     * @param proverStatus
     * @return
     */
    public static final int newStateNumber(int oldStateNumber, int proverNumber, int proverStatus)
    {
        if ((oldStateNumber == NUMBER_OF_MISSING_STATE) || (oldStateNumber == NUMBER_OF_OMITTED_STATE))
        {
            return -1;
        }
        int[] array = new int[3];
        if (3 != NUMBER_OF_PROVERS)
        {
            Activator.logDebug("Method ColorPredicate.newStateNumber must be reimplemented"
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
                    if (numberOfState(array) == oldStateNumber)
                    {
                        array[proverNumber] = proverStatus;
                        return numberOfState(array);
                    }
                }
            }
        }
        return -1;
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
    public boolean satisfiedBasedOnChildren(boolean[] childValues)
    {
        if (this.isLeaf)
        {
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
            throw new IllegalArgumentException("" + " Color predicate must start with the optional keyword `leaf'\n"
                    + " followed by a legal macro name or `every' or `some'.");
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

/*************************************
=======================  File ProofStatus.tla =======================

The Toolbox will provide LOGICAL COLORS, numbered from 1 through
NumberOfStepColors, with which a theorem or proof step can be colored.
(The preference menu allows the user to assign physical colors to
these logical colors.)  Each logical color has a COLOR PREDICATE.  The
logical color of a step is the lowest-numbered logical color whose
color predicate is true.  (If none are true, the step is not colored.)

A PROOF TREE consists of a theorem or proof step (the ROOT) together
with its proof (which may be empty).  A non-LEAF proof tree is one
whose root's proof is a sequence of proof trees.  A LEAF proof tree is
one whose whose root either has no proof or has a leaf proof.  Each
leaf proof tree has zero or more proof OBLIGATIONS. For convenience,
we define a leaf proof whose root step can take a proof but for which
that proof is either missing or OMITTED to contain a single DUMMY
obligation.  The obligations of a proof tree are defined in the
obvious way to be the set of all obligations of all leaf proof tree in
the proof tree.

At any time, each obligation has a STATE. For a dummy obligation, the
status is either `missing' or `omitted'.  For an ordinary proof
obligation, that state consists of a STATUS for each prover.
Currently, there are three provers with the following possible
statuses:

 1. Isabelle:  untried, proving, proved, failed, stopped
 2. Other:     untried, proving, proved, failed, stopped
 3. TLAPM:     none, trivial

For now, "Other" includes Zenon, the Cooper algorithm, and any SMT
backend.  The state of an ordinary obligation is written as a triple
such as <<proving, failed, none>>, where the value of the i-th element
is the obligation's proof status for the i-th prover.

A color predicate is specified by three things:

 - A OS set of obligation states.
 - Whether it is an `every' or a `some' predicate.
 - Whether or not it is a `leaf' predicate.

A color predicate has the following boolean value for a proof tree.

  /\ \/ /\ It is an `every' predicate
        /\ The state of every obligation in the proof tree is
           in OS.
     \/ /\ It is a `some' predicate
        /\ The state of some obligation in the proof tree is
           in OS.
  /\ \/ It is not a `leaf' predicate
     \/ The proof tree is a leaf proof tree

A color predicate is specified by a string with the following syntax

   <color-predicate> ::=  ["leaf"]?  ["every" | "some"] <state-set>*

   <state-set> ::= "missing" | "omitted" 
                     | "(" <statuses> "," <statuses> "," <statuses> ")"

   <statuses> ::=  <status>* | "-" <status>+ 

Each <state-set> specifies a set of states, and a sequence of
<state-sets>s specifies their union.  The <state-set>s "missing" and
"omitted" specify the obvious singleton sets of dummy-obligation
states.  A <statuses> specifies a set of possible proofs statuses is
specified by a list, where "-" means `all statuses except' and the
empty list means all possible statuses.

A triple of sequences of statuses specifies the set of all
states in which the proof status of the i-th prover is one of the
statuses in the i-th component of the triple.  An empty sequence
of statuses is an abbreviation for all possible statuses.
For example, the <state-set>

   (proving proved, untried, ) 

is the set of all obligation states in which Isabelle's proof status
is either proving or proved, the `Other' prover's status is untried,
and TLAPM's prover status is either none or trivial.  For example,

   every missing omitted ( , , )

is a predicate that is always true and

   leaf every missing omitted ( , , )

is true of a proof tree iff it is a leaf proof.  The color predicate

   some

is false for every proof tree.  The predicate

   every omitted (proved, , ) (, proved, ) (, , trivial)

is true iff every obligation is either omitted, is proved by Isabelle
or the Other prover, or is found trivial by TLAPM. The predicate

  leaf some (failed, - proved, none) (- proved, failed, none)

is true for a leaf node if, for some obligation, one of Isabelle's and
the Other prover's status is failed, and the other one's status is not
proved, and TLAPM has not found it to be trivial.

We also allow 

  <color-specification> ::= ["leaf"]? <macro-name>
  
where <macro-name> is the name of a macro whose expansion is
a legal color specification not beginning with "leaf". 

----------------------------------------------------------------------------
The following spec shows how all the information needed to specify
provers and their statuses can be provided in one array of array of strings.
(Since this is TLA+, I use sequences instead of arrays.)  

The main module contains the definitions for obligation states.  The
instantiated module ColorPredicates explains how a color predicate is
represented using a bit vector plus an indication of whether it is an
"every" or "some" predicate.  The spec ignores the distinction between 
leaf and non-leaf color predicates.


---------------------------- MODULE ProofStatus ----------------------------
EXTENDS Naturals, Sequences, FiniteSets, TLC

(***************************************************************************)
(* ProofStatesSpec[i] is the sequence of possible statuses (which are      *)
(* strings) for prover i.                                                  *)
(***************************************************************************)
CONSTANT ProofStatesSpec  
ASSUME ConstantAssumps ==  ProofStatesSpec \in Seq(Seq(STRING))

NumberOfProvers == Len(ProofStatesSpec)
  
StatusesOfProver(i) == 
  (*************************************************************************)
  (* The set of possible statuses of prover i.                             *)
  (*************************************************************************)
  { ProofStatesSpec[i][j] : j \in 1..Len(ProofStatesSpec[i]) }

Statuses == 
  (*************************************************************************)
  (* The set of all possible statuses of all provers.                      *)
  (*************************************************************************)
  UNION {StatusesOfProver(i) : i \in 1..NumberOfProvers}                       
                         
ObligationState == 
  (*************************************************************************)
  (* The set of all possible obligation states.                            *)
  (*************************************************************************)
    [ type : {"missing", "omitted"} ]
  \cup
    { s \in [ type : {"proof"},
              status : [1..NumberOfProvers -> Statuses]] :
        \A i \in 1..NumberOfProvers : s.status[i] \in StatusesOfProver(i) }
(***************************************************************************)
(* We define Sum(f) and Product(f) to be the sum and product of f[i] for   *)
(* all i in the domain of the function f.                                  *)
(***************************************************************************)
RECURSIVE Sum(_), Product(_)
Sum(f) == IF DOMAIN f = {} 
            THEN 0
            ELSE LET i == CHOOSE v \in DOMAIN f : TRUE
                 IN  f[i] + Sum([j \in (DOMAIN f) \ {i} |-> f[j]])
Product(f) == IF DOMAIN f = {} 
                THEN 1
                ELSE LET i == CHOOSE v \in DOMAIN f : TRUE
                     IN  f[i] * Product([j \in (DOMAIN f) \ {i} |-> f[j]])

(***************************************************************************)
(* The StateNumber operator assigns distinct, consecutive numbers starting *)
(* from 0 to all obligation states minus.                                  *)
(***************************************************************************)
StateNumber(s) == 
  CASE s.type = "missing" -> 0
    [] s.type = "omitted" -> 1
    [] s.type = "proof" ->
         2 + Sum( [ i \in 1..NumberOfProvers |->
                    ((CHOOSE j \in 1..Len(ProofStatesSpec[i]) : 
                               ProofStatesSpec[i][j] = s.status[i]) - 1)
                     * Product( [ k \in 1..(i-1) |-> Len(ProofStatesSpec[k])
                                 ] )
                  ] )
                  
THEOREM IsNumbering == 
         /\ \A s \in ObligationState : 
              StateNumber(s) \in 0..(Cardinality(ObligationState)-1)
         /\ \A s, t \in ObligationState : s # t => StateNumber(s) # StateNumber(t)

(***************************************************************************)
(* NumberToState would be the inverse of StateNumber if StateNumber had    *)
(* been defined to be a function on states rather than an operator.        *)
(***************************************************************************)
NumberToState[i \in 0..(Cardinality(ObligationState)-1)] == 
   CHOOSE s \in ObligationState : PrintT(s) /\ StateNumber(s) = i

(***************************************************************************)
(* We instantiate the ColorPredicates module which describes color         *)
(* predicates for an arbitrary set of obligation states and an enumeration *)
(* of them.                                                                *)
(***************************************************************************)
INSTANCE ColorPredicates WITH State <- ObligationState, 
                              StateEnumeration <- NumberToState
                              

============================================================================
\* Modification History
\* Last modified Fri Jul 02 09:37:08 PDT 2010 by lamport
\* Created Wed Jun 30 01:51:58 PDT 2010 by lamport


================================= FILE ColorPredicates.tla
-------------------------- MODULE ColorPredicates --------------------------
EXTENDS Naturals, FiniteSets

CONSTANT State
ASSUME IsFiniteSet(State)

StateSet == SUBSET State

ColorPredicate == 
  (*************************************************************************)
  (* A color predicate is a set of states that is either a "good" set or a *)
  (* "bad" set.                                                            *)
  (*************************************************************************)
  [ type : {"every", "some"},
    set  : StateSet ]

Satisfies(stateSet, colorPredicate) ==
  (*************************************************************************)
  (* A set stateSet of states satisfies a color predicate colorPredicate   *)
  (* if the predicate is a good set and EVERY state in stateSet is in that *)
  (* good set, or else it is a bad set and SOME state in stateSet is in    *)
  (* that bad set.                                                         *)
  (*************************************************************************)
  \/ /\ colorPredicate.type = "every"  
     /\ stateSet \subseteq colorPredicate.set
  \/ /\ colorPredicate.type = "some"  
     /\ stateSet \cap colorPredicate.set # {}

THEOREM UnionTheorem ==
  (*************************************************************************)
  (* Asserts that one can compute whether the union of state sets          *)
  (* satisfies a color predicate by knowing whether each of them does.     *)
  (*                                                                       *)
  (* Checked by TLC for a set of 4 model values.                           *)
  (*************************************************************************)
          \A S, T \in StateSet :
             \A pred \in ColorPredicate :
                /\ (pred.type = "every") =>
                      Satisfies(S \cup T, pred) = /\ Satisfies(S, pred)
                                                  /\ Satisfies(T, pred)
                /\ (pred.type = "some") => 
                      Satisfies(S \cup T, pred) = \/ Satisfies(S, pred)
                                                  \/ Satisfies(T, pred)
----------------------------------------------------------------------------
(***************************************************************************)
(* We now show how to represent state sets by bit vectors and how to use   *)
(* the bit vectors to calculate the Satisfies relation for state sets and  *)
(* color predicates.                                                       *)
(***************************************************************************)

VectorDomain  ==  0 .. (Cardinality(State)-1)
CONSTANT StateEnumeration
ASSUME StateEnumerationAssumption == 
       /\ StateEnumeration \in [VectorDomain -> State]
       /\ \A i, j \in VectorDomain :
             (i # j) => (StateEnumeration[i] # StateEnumeration[j])
                
VectorEncoding(stateSet) == 
  [i \in VectorDomain |-> StateEnumeration[i] \in stateSet]
  
And(f, g) == [i \in VectorDomain |-> f[i] /\ g[i]]
ZeroVector == [i \in VectorDomain |-> FALSE]

THEOREM VectorComputation ==
  (*************************************************************************)
  (* How to use bit vectors to compute Satisfies.                          *)
  (*                                                                       *)
  (* Checked by TLC on a set of 4 states and a                             *)
  (*************************************************************************)
          \A S \in StateSet :
            \A pred \in ColorPredicate :
                /\ (pred.type = "every") =>
                      Satisfies(S, pred) = (And(VectorEncoding(S), VectorEncoding(pred.set))
                                              = VectorEncoding(S))
                /\ (pred.type = "some") => 
                      Satisfies(S, pred) = (And(VectorEncoding(S), VectorEncoding(pred.set))
                                              # ZeroVector)
=============================================================================
\* Modification History
\* Last modified Fri Jul 02 09:46:14 PDT 2010 by lamport
\* Created Thu Jul 01 07:55:00 PDT 2010 by lamport

****************************************************************************************/
