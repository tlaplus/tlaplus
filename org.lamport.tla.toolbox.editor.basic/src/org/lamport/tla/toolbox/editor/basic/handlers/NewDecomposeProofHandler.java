/**
 * THINGS TO DO:
 *  - Check that what I've done so far works with definition expansion.
 *  
 *  - Figure out how to control displaying of context assumptions once some assumption
 *    has been decomposed.  Perhaps the easiest thing to do is, once a context assumption has
 *    been \E-decomposed, remove it's NodeRepresentations from  assumeReps and put its 
 *    decomposition in the ASSUME section.  Once a CASE-decomposition is made, all context
 *    assumptions should be removed from assumeReps and the decomposition should be moved
 *    to the ASSUME section if it came from a context assumption.  What should be done
 *    on /\ decompositions?  Should all other decompositions be disabled/removed?  Should
 *    it depend on whether the /\ decomposition came from a \E.
 *    
 *  - Should original ASSUMEs that haven't been decomposed be removed from assumeReps
 *    once they can no longer be decomposed?
 *    
 *  - Fix proof generation so it adds the necessary BY steps and DEF names.
 *  
 *  - Handle substitutions of multi-line formulas.
 *  
 *  - Handle decompositions of formulas that come from other modules.
 *    
 * 
 * NEW Decompose Proof Handler Command
 *   This class is the development version of the new Decompose Proof Handler
 *   command.  If I could get Eclipse/Git to work, I would be building it in
 *   a different branch rather than in the master branch.
 * 
 * ENHANCEMENTS 
 * 
 * - Allow case splits and introduction of Skolem constants on usable assumptions--
 *   that is, assumption from relevant ASSUME or SUFFICES ASSUME clauses.
 *   I originally thought there are too many of them to display, but I no longer
 *   think this will be the case--although it would be distracting to display
 *   them when the user just wants to decompose the current assumptions.
 *   
 *   THIS WILL BE DONE AS FOLLOWS:
 *    - There will be a switch to determine whether potential decompositions
 *      from assumptions in the environment should be displayed.
 *    - The state of that switch will be remembered between invocations.
 *    - Clicking on the switch shows or hides the relevant assumptions
 *      immediately.
 *    - Only assumptions that have a possible decomposition (possibly
 *      within deeper conjunctions and definition expansions) are shown.
 *    To make this less cumbersome, once one assumption or conjunct of an
 *    assumption is chosen for decomposition, others are no longer shown.
 *      
 *   
 * CURRENT BUGS AND MISSING FEATURES:
 * 
 *  - Bug reported 16 Jan 2014 by Jael, fixed on 23 Aug 2014 by LL. 
 *    STILL FIXED IN NEW VERSION
 *    Decomposing
 *  
 *       THEOREM \A x, y : x /\ y => TRUE
 *       
 *    with \A then => then /\ puts the menu in a state in which P is not enabled.
 *    
 *    This may not be a bug, since there decomposing the /\ accomplished nothing.
 *    However, decomposing the /\ and then the \E in
 *    
 *       THEOREM ASSUME (\E x : TRUE) /\ FALSE
 *       PROVE   TRUE
 *       
 *    Leaves the Prove button disabled
 * 
 *    
 *    
 *    
 *  - Bug discovered 19 Aug 2014 by LL.  FIXED IN NEW VERSION
 *    Decomposing
 *    
 *       <1>3. ASSUME (\E x : D) /\ (A \/ D)
 *             PROVE  FALSE
 *             
 *    by /\ then \E then \/ does not add the necessary assumption <1>3 to
 *    the BY of the SUFFICES (or QED if USE SUFFICES not chosen).
 *    
 *    
 *
 *  - Bug discovered 23 Aug 2014 by LL:  
 *    FIXED IN NEW VERSION by not allowing a \A decomposition after 
 *    a \/ decomposition,
 *    The following produces a parse error on decomposition by \/ 
 *    then \A then Prove.
 *    Note especially what happens with USE SUFFICES option, where
 *    a NEW declaration is moved before a previous assumption in the
 *    proof.  (Without the SUFFICES option, the problem can be solved
 *    by preserving the original order of the assumptions.)
 *    
 *      S1b == A \/ ({y_1 \in {44} : y_1 > 0} = {x \in {44} : x > 0})
 *      THEOREM ASSUME NEW x , NEW y_1, S1b  
 *              PROVE  \A x_1 : FALSE   
 *      <1>3. ASSUME (\E x : D) /\ (A \/ D)
 *            PROVE  FALSE
 *            
 *    
 *  - The command does renaming of bound variables when necessary to avoid
 *    name clashes, but not of symbols defined in a LET.
 *    
 *    
 *  - The implementation contains code written to implement a "use Subexpression Names"
 *    feature that allowed the user to specify that decomposition that involved 
 *    expanding definitions was to be done by using subexpression names rather
 *    than actually expanding the definition in the proof text.  This feature
 *    was abandoned because the initial implementation did not allow renaming of
 *    identifiers to avoid name clashes in the subexpression names.  However, the
 *    code that was written remains; only the button for choosing the feature
 *    was made invisible.  This means that there is a lot of dead code 
 *    that was executed only when the option was chosen.
 *    THE DEAD CODE WILL PROBABLY BE REMOVED, PERHAPS LEAVING HOOKS INDICATING
 *    HOW USE OF SUBEXPRESSION NAMES CAN BE IMPLEMENTED, BUT THEY PROBABLY
 *    WON'T BE ALLOWED IN THE NEW RELEASE.
 *
 *  - If "use CASE" is chosen, an ASSUME / PROVE with multiple assumptions should be turned
 *    into a case if it contains no NEWs, with the assumptions being turned into a 
 *    conjunction.  Currently, it only is if there is a single assumption.
 *    FIXED IN NEW VERSION 
 *    
 *  - The decomposition will not expand definitions imported from other modules
 *    (except with the unfinished and hidden "Use subexpression names" option). 
 *    THIS HAS BEEN FIXED IN THE OLD VERSION only for imported definitions that
 *    don't come from an INSTANCE of a module with CONSTANT or VARIABLE 
 *    declarations.  The general case will be handled in the new version. 
 *    However, it probably will have the following bug for instantiation with 
 *    renaming:  
 *    
 *  - If decomposition requires expanding a definition, the decomposition will be
 *    performed only if each argument of the defined operator appears on a 
 *    single line of the source text.  (Different arguments may appear on 
 *    different lines.)
 *    THIS RESTRICTION MAY SOME DAY BE REMOVED.  See MODULE Substitution,
 *    appended below, for a spec of the necessary code.
 *    
 *  - Decomposition will never be performed on any decomposable formula that
 *    appears as an operator argument.  For example, in
 *    
 *      F(a, b) == a \/ b
 *      THEOREM F(G \/ H, I) => K
 *    then decomposition into the two cases G \/ H and I will be performed, but
 *    decomposition into the subcases G and H will not.
 *    THIS RESTRICTION WILL PROBABLY REMAIN.  IT DOESN'T SEEM LIKELY TO OCCUR OFTEN.
 *    
 *  - It would be useful to have the option of expanding an assumption or goal
 *    that is a LET formula.  This would create an initial DEFINE step in the proof.
 *    THIS RESTRICTION WILL PROBABLY REMAIN.  IT DOESN'T SEEM LIKELY TO OCCUR OFTEN.
 *    
 *  - Renaming of identifiers to avoid name clashes when expanding definitions doesn't do
 *    all the renaming it should.  In particular, it does not rename operators defined in
 *    a LET clause or their definition parameters.  See ResourceHelper.getBoundIdentifiers
 *    to get a start on fixing this.
 *    
 *  - Bug discovered by LL on 28 October 2014 
 *    If an operator argument contains a bound variable, as in Op(\E x : F(x)), and
 *    a decomposition is performed that expands the definition of Op, then decomposing
 *    other formulas can produce a decomposition that doesn't parse because of name
 *    conflicts with x in the expression \E x : F(x).  Fixing this would require
 *    major changes to the code, since the design is based on the assumption that
 *    substitutions will never have to be done in an expression that is substituted
 *    for some identifier.  One way to fix this would be to make a NodeRepresentation
 *    maintain with its NodeText the information about all substitutions that have
 *    been done in NodeText.
 * 
 * HOW THE COMMAND WORKS
 * 
 * A single object of this class is created and attached to the command.  Multiple
 * executions of the command use the same object, so data can be stored as (non-static)
 * fields of the object between executions of the command.
 * 
 * The structure of the methods is as follows.  Executing the command calls the
 * execute() method, which does some stuff and then calls realExecute() in a
 * Runnable.  That method initializes the state and calls raiseWindow to draw the
 * window, creating the buttons and their listeners.  Each formula shown in the
 * command's window is described by a NodeRepresentation object.
 * 
 * Clicking a button calls the widgetSelected method of the 
 * DecomposeProofButtonListener subclass.  This calls the appropriate one of the 
 * following methods to handle the click:
 * 
 *   andAction     (splitting an /\ assumption and producing an /\-split proof)
 *   forAllAction  (splitting a \A goal)
 *   existsAction  (splitting a \E assumption)
 *   impliesAction (splitting a => goal)
 *   orAction      (splitting a \/ assumption)
 *   sqsubAction   (splitting a [N]_v assumption)
 *   caseAction    (producing a case-split proof)
 *   
 *   A NodeRepresentation object is created for a formula in the window by
 *   calling the subNodeRep method of the NodeRepresentation method, which calls
 *   the decompose method to set the object's decomposition field that describes
 *   how that the proof can be split on that formula.  
 *   
 *   When a formula with NodeRepresentation nrep is split, the resulting formulas 
 *   have NodeRepresentation objects constructed by calling the 
 *   decompositionChildToNodeRep method (which calls the nrep.subNodeRep method).
 *   
 *   The value of state.assumeReps is initially set to the sequence of 
 *   decomposable context assumptions and all non-context assumptions.
 *   When an assumption is decomposed by anything other than an /\ decomposition,
 *   the newly created assumption is put in the section of state.assumeReps
 *   that begins at position state.firstAddedAssumption.  The order of created
 *   assumptions in that section is the same as the order of the original
 *   assumptions from which they came, except that the NodeRepresentation created 
 *   by \/ decomposition is always the last assumption.  An assumption added
 *   as a result of decomposing the goal is made the last assumption in
 *   state.assumeReps except for a node created by \/ decomposition.  (This
 *   ordering is implemented using NodeRepresentation.initialPosition.)
 *   
 *   IMPLEMENTATION NOTE: substitution
 *   - When something is substituted for an operator argument, the substitution
 *     is done at the level of strings.  Therefore, any identifiers that appear
 *     in the substituting expression will never be found when looking for name
 *     clashes.  This should not cause any problem because any substitution needed
 *     in the operator argument should be performed before the operator's 
 *     definition is expanded.   
 *     
 *   - To eliminate name clashes, new identifiers are substituted for existing
 *     bound identifiers.  These new identifiers clash with nothing when they
 *     are introduced.  To keep them from clashing with identifiers introduced
 *     or revealed later, these names are remembered in the renaming field of the 
 *     Decomposition object.
 */

/***************************************************************************
            A SPEC OF DECOMPOSITION

The following decompositions are provided.

   => decomposition:
     The goal A => B is changed to the goal B by adding assumption A
  
   \A decomposition:
      The goal \A x \in S : G is changed to the goal G by adding assumption
      NEW x \in S.  (Unbounded \A is transformed similarly.)
  
   \E decomposition:
       The assumption \E x \in S : A is changed to the two assumptions
       NEW x \in S, A .  (A change of variable may occur to prevent name
       clash.)
  
   \/ decomposition:
        The assumption A_1 \/ ... \/ A_n is decomposed into n cases,
        in each of which one A_i is assumed.  Only a single 
        \/ decomposition of an assumption may be performed.  However,
        a case may be further decomposed by \/ or \E decomposition.      
  
   /\ assumption decomposition:
       The assumption A_1 /\ ... /\ A_n is replaced by the n separate
       assumptions A_1, ... , A_n
  
   /\ goal decomposition:
       The goal A_1 /\ ... /\ A_n produces a decomposition of the proof 
       into separate proofs of the A_i.  This is a final step that
       produces the proof.

Each of these decompositions can be performed if the goal or assumption
has the indicated form, or if it consists of a single operator whose
definition has that form.

After an \/ decomposition has been performed, no further \/
decomposition may be performed.

An /\ decomposition can be performed only if it, or further /\
decompositions of the assumptions it produces can lead to 
  - a \E decomposition or 
  - a \/ decomposition when no \/ decomposition has yet been
    performed.

Context assumptions that are not decomposible should not be shown.

POSSIBLE OPTION: Whether or not non-decomposible assumptions from
the statement being decomposed (either ASSUME clauses or a CASE
assumption) should be shown.  Current choice: do not show.

All case assumptions produced by \/ decomposition and any assumption
created by =>, \A, or \E decomposition should be shown.  All of these
assumptions will appear explicitly, in the appropriate ASSUME or CASE
clauses, as assumptions in the proof that is generated.

POSSIBLE OPTION: Whether or not non-decomposible assumptions produced
by /\ decomposition should be shown.  This might depend on whether
or not the decomposed assumption was a context assumption.  Current
choice: not to show.

POSSIBLE OPTION: Whether or not non-decomposed assumptions produced by
/\ decomposition should appear as explicit assumptions in the
generated proof.  They are not logically necessary because they are
implied by assumptions in the generated proof's context (which
includes the ASSUME clauses of the decomposed step).  Current choice
(preferred by Damien, Stephan, and LL): not to appear.
**************************************************************************/

 
/*************************************************
 A SPEC OF PROOF GENERATION

 The |= Notation
 ---------------
 I will write A |= P as an abbreviation for ASSUME A PROVE P, for
 A a list of assumptions and P a formula.

 A formula P is equivalent to |= P (the case of A the empty list).

 Define A_1 |= (A_2 |= P) to be A_1, A2 |= P , where I use "," to mean
 concatenation of lists of assumptions.

 I will also allow assumptions of the form A_1 \/ ... \/ A_n
 where the A_i are sequents of the form  A |= P .  I hope its meaning
 is obvious.  It obeys the rule that

 A, (B_1 \/ ... \/ B_n), C |= P

 is equivalent to

 (A, B_1, C |= P) /\ ... /\ (A, B_n, C |= P)

 CASE
 ----
 If the A_i are formulas and P is the current goal, then the step

 <i>j. A_1, ... , A_n |= P 

 can be written 

 <i>j. CASE A_1 /\ ... /\ A_n


 Proofs with and without SUFFICES
 --------------------------------
 Any proof of the form

 <i> SUFFICES A |= P
 BY DEF D_1, ... , D_k
 <i>1. S_1
 ...
 <i>n. S_n
 <i> QED
 BY <i>1, ... , <i>n DEF P

 is equivalent to

 <i>1. A |= S_1
 ...
 <i>n. A |= S_n
 <i> QED
 BY <i>1, ... , <i>n DEF D_1, ... , D_k, P

 I will therefore only consider proofs with SUFFICES.


 Proof by Conjunction Splitting
 -----------------------------
 Suppose an obligation A |= P is transformed into the obligation 
 A, H |= C by expanding definitions D_1, ...  , D_k, where 
 C == C_1 /\ ...  /\ C_n.  Then A |= P has the proof:

 <i> SUFFICES  H |= C
 BY DEF D_1, ... , D_k
 <i>1. C_1
 ...
 <i>n. C_n
 <1> QED
 BY <i>1, ... , <i>n DEF C

 If C is equal to C_1 /\ ... /\ C_n (rather than equal after the
 definition of C is expanded, then the DEF C is eliminated.


 Proof by Disjunction Splitting
 -------------------------------
 Suppose an obligation A |= P is transformed into the obligation 
 A, H |= C by expanding definitions D_1, ... , D_k.

 Suppose that A, H |= C is then transformed to the equivalent
 obligation  J, K, L |= C by expanding definitions E_1, ... , E_m,
 and K == K_1 \/ ... \/ K_n.  Then A |= P has the
 proof

 <i> SUFFICES H, J, K, L |= C
 BY DEF D_1, ... , D_k, E_1, ... , E_m
 <i>1. K_1 |= C
 ...
 <i>n. K_n |= C
 <1> QED
 BY <i>1, ... , <i>n DEF K

 (The DEF K can be eliminated if K equals 

 The transformation of A, H |= C to J, K, L |= C will be done in
 two steps:

 1. Splitting conjunctions into separate assumptions.

 2. Performing the transformations:

 \E x : S   ->  NEW x, S .

 NEW x, S_1 \/ ... \/ S_n  ->  
 (NEW x |= S_1) \/ ... \/ (NEW x |= S_n)

 **************************************************************************/

/*
 * To figure out how to lay out a nice popup, see 
 *    
 *    http://www.eclipse.org/articles/article.php?file=Article-Understanding-Layouts/index.html
 *    
 * to find out how to use GridLayout, and see ObligationsView.updateItem 
 * to see how to add things to a Composite nested inside other things.  
 * See also the ScrolledComposite method, which with luck will just be
 * a composite with scrollbars when needed.
 */

package org.lamport.tla.toolbox.editor.basic.handlers;

import java.util.HashSet;
import java.util.Hashtable;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;
import java.util.Vector;

import org.eclipse.core.commands.AbstractHandler;
import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.core.commands.ExecutionException;
import org.eclipse.core.commands.IHandler;
import org.eclipse.core.resources.IFile;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.NullProgressMonitor;
import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.jface.resource.JFaceResources;
import org.eclipse.jface.text.BadLocationException;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.IRegion;
import org.eclipse.jface.text.TextSelection;
import org.eclipse.jface.viewers.ISelectionProvider;
import org.eclipse.swt.SWT;
import org.eclipse.swt.events.DisposeEvent;
import org.eclipse.swt.events.DisposeListener;
import org.eclipse.swt.events.SelectionAdapter;
import org.eclipse.swt.events.SelectionEvent;
import org.eclipse.swt.events.SelectionListener;
import org.eclipse.swt.graphics.Point;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Button;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Label;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.ui.IEditorReference;
import org.eclipse.ui.PartInitException;
import org.eclipse.ui.editors.text.FileDocumentProvider;
import org.eclipse.ui.part.FileEditorInput;
import org.lamport.tla.toolbox.Activator;
import org.lamport.tla.toolbox.editor.basic.TLAEditor;
import org.lamport.tla.toolbox.editor.basic.util.EditorUtil;
import org.lamport.tla.toolbox.spec.Spec;
import org.lamport.tla.toolbox.spec.parser.IParseConstants;
import org.lamport.tla.toolbox.spec.parser.ModuleParserLauncher;
import org.lamport.tla.toolbox.spec.parser.ParseResult;
import org.lamport.tla.toolbox.util.HelpButton;
import org.lamport.tla.toolbox.util.ResourceHelper;
import org.lamport.tla.toolbox.util.StringHelper;
import org.lamport.tla.toolbox.util.StringSet;
import org.lamport.tla.toolbox.util.UIHelper;

import tla2sany.parser.SyntaxTreeNode;
import tla2sany.semantic.ASTConstants;
import tla2sany.semantic.AssumeProveNode;
import tla2sany.semantic.DefStepNode;
import tla2sany.semantic.ExprNode;
import tla2sany.semantic.ExprOrOpArgNode;
import tla2sany.semantic.FormalParamNode;
import tla2sany.semantic.InstanceNode;
import tla2sany.semantic.LeafProofNode;
import tla2sany.semantic.LevelNode;
import tla2sany.semantic.ModuleNode;
import tla2sany.semantic.NewSymbNode;
import tla2sany.semantic.NonLeafProofNode;
import tla2sany.semantic.OpApplNode;
import tla2sany.semantic.OpDeclNode;
import tla2sany.semantic.OpDefNode;
import tla2sany.semantic.ProofNode;
import tla2sany.semantic.SemanticNode;
import tla2sany.semantic.Subst;
import tla2sany.semantic.SubstInNode;
import tla2sany.semantic.SymbolNode;
import tla2sany.semantic.SymbolTable;
import tla2sany.semantic.TheoremNode;
import tla2sany.st.Location;
import tla2sany.st.TreeNode;
import util.UniqueString;

public class NewDecomposeProofHandler extends AbstractHandler implements
        IHandler {

    /***************************************************************
     * Fields holding information about the module, its source text, the
     * selected text, the selected step, and the theorem in which it appears.
     ****************************************************************/
    /**
     * The document being edited.
     */
    private IDocument doc;

    /**
     * A mapping from module names to IDocuments, containing IDocuments for
     * all modules that have been encountered in the course of expanding
     * imported definitions.
     * 
     */
    private Hashtable<String, IDocument> moduleNameToDoc ;
    
    /**
     * Some Eclipse thingee that seems to be needed.
     */
    private ISelectionProvider selectionProvider;

    /**
     * The current selection.
     */
    private TextSelection selection;

    /**
     * The current offset.
     */
    private int offset;

    /**
     * The module being edited.
     */
    private ModuleNode moduleNode;

    /**
     * The theorem containing the selected step
     */
    private TheoremNode theorem;

    /**
     * The step being decomposed.
     */
    private TheoremNode step;

    /**
     * The step's node representation.
     */
    private NodeRepresentation stepRep;

    /**
     * The step's proof which should be either null or a LeafProofNode.
     */
    private ProofNode proof;

    /**
     * If the step being proved is numbered <2>3, then this equals 2.
     */
    private int proofLevel;

    /**
     * The proofLevel converted to a string like "<2>", except that a level of 0
     * or -1 (which are possible) is converted to 1.
     */
    private String proofLevelString;

    /**
     * If the step is number <2>3, then this is "<2>3". If the step is
     * unnumbered, as in <2>, or if it is the entire theorem, then this string
     * is null.
     * 
     * Note that the SANY parser appears to replace <+> or <*> by <n> for the
     * appropriate number n, so the Toolbox doesn't have to deal with <+> or
     * <*>.
     */
    private String stepNumber;

    /**
     * The column in which the step begins.
     */
    private int stepColumn;

    /**
     * PREFERENCES
     * 
     * The following fields are constants, some of which should perhaps be set
     * as preferences.
     */
    /**
     * The default value of showContextValue
     */
    private static final boolean SHOW_CONTEXT_DEFAULT = true;
    
    /**
     * The default value of useSufficesValue ;
     */
    private static final boolean USE_SUFFICES_DEFAULT = true;

    /**
     * The default value of useCaseValue ;
     */
    private static final boolean USE_CASE_DEFAULT = true;

    /**
     * The default value of subexpressionValue.
     */
    private static final boolean SUBEXPRESSION_DEFAULT = false;

    /**
     * The number of columns to the right of stepColumn to which the created
     * proof is to be indented.
     */
    private static final int PROOF_INDENT = 2;

    /**
     * Whether or not to leave a blank line between the created proof steps.
     */
    private static final boolean BLANK_LINE_BETWEEN_STEPS = false;

    /**
     * True iff an "obvious" proof should be written "PROOF OBVIOUS" rather than
     * just "OBVIOUS".
     */
    private static final boolean OBVIOUS_HAS_PROOF = false;

    /**
     * True iff the QED step of the new proof should have a number rather than
     * just a level.
     */
    private static final boolean NUMBER_QED_STEP = true;

    /**
     * The string that should follow a step number like <2>7 in proofs
     * constructed by decomposition.
     */
    private static final String STEP_NUMBER_PUNCTUATION = ".";

    /**
     * When renaming identifiers to avoid name conflicts, an identifier id is
     * renamed to id + RENAMING_SUFFIX + i for some number i. Any identifier
     * that has this form is considered to be a renamed identifier, and it will
     * be renamed by changing i.
     * 
     * If the value of RENAMING_SUFFIX is "", everything will work but the
     * renaming will be a little weird for identifiers whose original name ends
     * in a digit, or if an identifier that gets renamed with i > 9 gets
     * re-renamed.
     */
    private static final String RENAMING_SUFFIX = "_";

    /*************************************************************************
     * Fields that contain the current assumptions and goal.
     * 
     * The data for the current assumptions are kept in vectors, the i-th
     * element containing data for the i-th assumption. This is done to make it
     * easy to replace one assumption by several. Other objects contain pointers
     * to these vectors, so once the vectors are constructed by
     * NewDecomposeProofHandler.execute, they can be modified but must not be
     * replaced by new vectors.
     *************************************************************************/

    /**
     * The NodeRepresentation objects for the current assumptions.
     */
    // private Vector<NodeRepresentation> assumeReps; // moved to state

    /**
     * The NodeRepresentation object for the current goal.
     */
    // private NodeRepresentation goalRep; // moved to state

    // Fields for displaying the Decompose Proof window.
    private Shell windowShell; // The shell of the Decompose Proof window
    private Point location = null; // The location at which window should open.
    private TLAEditor editor; // The editor from which window was raised.
    private IFile editorIFile; // The IFile of the editor, used for making
                               // it read-only.

    /**
     * Holds the current state of the decomposition. It will be cloned when the
     * state is changed, the clone modified and its previousState field set to
     * the current value of state, and state set to the new DecompositionState.
     */
    private DecompositionState state = null;

    /* *
     * MANY OF THE FOLLOWING FIELDS WILL BE PUT INTO THE state
     * DecompositionState OBJECT
     */

    /**
     * If the user has done an OR split on an assumption, then this is the index
     * of the assumption in assumes and state.assumeReps. Otherwise, it equals
     * -1.
     */
    // int chosenSplit; // MOVED TO DecompositionState (not sure IF STILL
    // NEEDED)

    /**
     * True if the proof of a SUFFICES step (or of the QED step if there is no
     * SUFFICES step) needs the name of the step being decomposed in the BY
     * clause if that step has a name. I believe this is the case iff an
     * \E-split has been done on an assumption that was not moved from the goal.
     * 
     * 
     */
    // boolean needsStepNumber; // TO BE MOVED TO DecompositionState

    /**
     * The original DecomposeProofHandler documentation said:
     * 
     *   True iff the step/theorem being decomposed is an ASSUME/PROVE. This is
     *   relevant for setting state.needsStepNumber.
     *   
     * To try to maintain the meaning of this field, it is set true iff the step
     * being decomposed is an ASSUME/PROOF (or CASE) that has an assumption other
     * than a NEW.
     * 
     */
    boolean hasAssumes;

// UP-DOWN ARROWS REMOVED
//    /**
//     * Once the user has performed an AND split on an assumption, then another
//     * AND split can be performed only on one of the results of that split. The
//     * indices of the nodes in <code>assumes</code> and
//     * <code>state.assumeReps</code> resulting from AND splits range from
//     * andSplitBegin through (including) andSplitEnd. If no AND split has been
//     * performed, then andSplitBegin and andSplitEnd equal -1.
//     * 
//     */
    // int andSplitBegin; // moved to state
    // int andSplitEnd; // moved to state
    // private HashSet<String> goalDefinitions; // MOVED TO state
    // private HashSet<String> assumpDefinitions; // MOVED TO state

    /**
     * The set of all user-definable identifiers that are declared or defined
     * before the theorem or step being decomposed. It consists of the
     * following:
     * 
     * - CONSTANTS and VARIABLES of the current module declared before the step.
     * These are obtained from moduleNode.getConstantDecls() and
     * moduleNode.getVariableDecls(). (See ShowDeclarationsHandler.setList.)
     * 
     * - Operators and Theorem/Assumption name defined before the current step.
     * These are obtained from moduleNode.getOpDefs() and
     * moduleNode.getThmOrAssDefs(). To do this, we first find the names of all
     * modules whose definitions are imported by INSTANCE statements that occur
     * before the step. We do this from moduleNode.getInstances() to find all
     * unnamed INSTANCE statements occurring before the step, and then follow
     * the getInstances() pointers to find them. To determine if the identifier
     * defined by an OpDefNode or ThmOrAssumpDefNode node n occurs before the
     * step, we examine n.getSource() and if its not moduleNode, we see if it's
     * a member of the set of relevant instantiated modules.
     * 
     * - Identifiers used in named instantiations (e.g., the I in I == INSTANCE
     * ...). They are obtained from moduleNode.getInstances().
     * 
     * - Identifiers declared by NEW clauses in ASSUME/PROVE or SUFFICES
     * ASSUME/PROVE statements in whose scope the step lies.
     * 
     * - Definitions in DEFINE steps (represented by DefStepNode objects) in
     * whose scope the step lies.
     */
    private  StringSet declaredIdentifiers;
    

    /********************************************************************
     * METHODS INVOLVED IN RENAMING
     *********************************************************************/
    /**
     * Returns the current name of the FormalParamNode `node'. If it has been
     * renamed, then this name is found in rename.newNames. Otherwise, it is the
     * original name.
     * 
     * @param node
     * @param rename
     * @return
     */
    private String getCurrentName(FormalParamNode node, Renaming rename) {
        String newName = null;
        int i = 0;
        while ((i < rename.identifiers.size()) && (newName == null)) {
            if (rename.identifiers.elementAt(i) == node) {
                newName = rename.newNames.elementAt(i);
            }
            i++;
        }

        if (newName == null) {
            return node.getName().toString();
        } else {
            return newName;
        }
    }

    /**
     * Modifies the Renaming object rename to indicate that the current name of
     * `node' is `name'. If the current name of `node' is its original name,
     * then do nothing.
     * 
     * @param node
     * @param name
     * @param rename
     */
    private void addCurrentName(FormalParamNode node, String name,
            Renaming rename) {
        // If node is in rename.identifiers, then set i to its index.
        // Otherwise, set i to rename.identiers.size().
        int i = 0;
        while ((i < rename.identifiers.size())
                && (rename.identifiers.elementAt(i) != node)) {
            i++;
        }

        // Either replace the current renaming of `name' in `rename'
        // if there is one, otherwise add the renaming iff it's not
        // the same as its original name.
        if (i < rename.identifiers.size()) {
            rename.newNames.remove(i);
            rename.newNames.insertElementAt(name, i);
        } else {
            if (!name.equals(node.getName().toString())) {
                rename.identifiers.add(node);
                rename.newNames.add(name);
            }
        }
    }

    /**
     * Returns a new name for `node' that is different from any of the names in
     * the set currentlyDeclared of names . If getCurrentName(node, rename) is
     * not in currentlyDeclared, then that's the name returned. Otherwise, if
     * there's a node n with the same original name as `node' that is being
     * renamed by `rename', and getCurrentName(n, rename) not in
     * currentlyDeclared, then the methods return getCurrentName(n, rename).
     * Otherwise, it returns the string nm + RENAMING_SUFFIX + i where nm is the
     * original name of `node', and i is the smallest positive integer such that
     * this string is not in currentlyDeclared.
     * 
     * @param node
     * @param currentlyDeclared
     * @param rename
     * @return
     */
    private String getNewName(FormalParamNode node,
            StringSet currentlyDeclared, Renaming rename) {

        String curName = getCurrentName(node, rename);
        if (!currentlyDeclared.contains(curName)) {
            return curName;
        }

        String oldName = getNewNamePrefix(node.getName().toString());
        int i = 1;
        while (currentlyDeclared.contains(oldName + i)) {
            i++;
        }

        return oldName + i;
    }

    /**
     * The return value is the string str such that if the identifier with name
     * oldname is to be renamed, its new name should have the form str+i for
     * some positive integer i. See RENAMING_SUFFIX.
     * 
     * The method assumes that oldname is a string containing at least one
     * character.
     * 
     * @param oldname
     * @return
     */
    private String getNewNamePrefix(String oldname) {

        // Return oldname unless it has a single character or doesn't end with a
        // digit.
        if ((oldname.length() < 2)
                || !Character.isDigit(oldname.charAt(oldname.length() - 1))) {
            return oldname + RENAMING_SUFFIX;
        }

        // Set newname to oldname minus the last digit.
        String newname = oldname.substring(0, oldname.length() - 1);

        // Keep removing digits from the end of newname until it ends with
        // RENAMING_SUFFIX or gets too short.
        while ((newname.length() > RENAMING_SUFFIX.length())
                && Character.isDigit(newname.charAt(newname.length() - 1))
                && !newname.endsWith(RENAMING_SUFFIX)) {
            newname = newname.substring(0, newname.length() - 1);
        }

        if (newname.endsWith(RENAMING_SUFFIX)) {
            return newname;
        } else {
            return oldname + RENAMING_SUFFIX;
        }
    }
    
    // 
    /**
     * Returns the index in state.assumeReps at which to put the new nodes
     * obtained by decomposing a top-level node.  If the node being decomposed was in state.assumeReps,
     * then we assume that it was at position oldIndex, has been removed, but state.firstAddedAssumption
     * has not been changed.  In that case, state.firstAddedAssumption is updated appropriately.
     * Otherwise, oldIndex should be set to -1 -- for example if the new nodes are obtained by
     * decomposing the goal.
     * 
     * @param oldIndex
     * @param initPos
     * @return
     */
    private int newAssumeRepsIndex(int oldIndex, int initPos ) {
        if (oldIndex >= state.firstAddedAssumption) {
            return oldIndex ;
        }
        if (oldIndex != -1) {
          state.firstAddedAssumption-- ;
        }
        int i = state.firstAddedAssumption ;
        while (   (i < state.assumeReps.size() ) 
               && (initPos >= state.assumeReps.elementAt(i).initialPosition) ) {
            i++ ;
        }
        
        return i;
    }

    /****************************************
     * THE TOP MENU BUTTONS.
     *****************************************/
    // NOT CLEAR IF THESE BUTTON VALUES SHOULD BE PUT IN DecompositionState
    // OR IF PERHAPS EVEN THE BUTTONS SHOULD BE PUT THERE.
    
    /**
     * The showContextButton is true iff decomposible assumptions coming 
     * from the context should be displayed.
     */
    private boolean showContextValue = SHOW_CONTEXT_DEFAULT;
    private Button showContextButton;
    
    /**
     * The useSufficesButton determines whether the created proof will use an
     * initial SUFFICES step to declare the newly created assumptions, or if
     * those assumptions will be put on each step of the proof in an
     * ASSUME/PROVE.
     */
    private boolean useSufficesValue = USE_SUFFICES_DEFAULT;
    private Button useSufficesButton; //

    /**
     * The useSufficesButton determines whether the created proof will use an
     * initial SUFFICES step to declare the newly created assumptions, or if
     * those assumptions will be put on each step of the proof in an
     * ASSUME/PROVE.
     */
    private boolean useCaseValue = USE_CASE_DEFAULT;
    private Button useCaseButton; //

    /**
     * The subexpressionButton determines if an occurrence of a user-defined
     * operator should be expanded by replacing it with its definition, or by
     * using subexpression names like Op(43)!2. In the initial implementation,
     * definitions that come from a different module are always expanded by
     * using subexpression names.
     */
    private boolean subexpressionValue = SUBEXPRESSION_DEFAULT;
    private Button subexpressionButton;

    /**
     * Record the state of the top menu's check buttons.
     */
    private void readButtons() {
        showContextValue = showContextButton.getSelection();
        useSufficesValue = useSufficesButton.getSelection();
        useCaseValue = useCaseButton.getSelection();
        subexpressionValue = subexpressionButton.getSelection();
    }

    /**
     * THE REAL EXECUTE METHOD
     * 
     * This method is called by a synchronous job launched in the execute method
     * to do most of the work of executing the Decompose Proof command.
     * 
     * @see org.eclipse.core.commands.IHandler#execute(org.eclipse.core.commands.
     *      ExecutionEvent)
     * 
     * @return
     * @throws ExecutionException
     */
    /**
     * @return
     * @throws ExecutionException
     */
    /**
     * @return
     * @throws ExecutionException
     */
    /**
     * @return
     * @throws ExecutionException
     */
    /**
     * @return
     * @throws ExecutionException
     */
    /**
     * @return
     * @throws ExecutionException
     */
    /**
     * @return
     * @throws ExecutionException
     */
    /**
     * @return
     * @throws ExecutionException
     */
    /**
     * @return
     * @throws ExecutionException
     */
    /**
     * @return
     * @throws ExecutionException
     */
    /**
     * @return
     * @throws ExecutionException
     */
    /**
     * @return
     * @throws ExecutionException
     */
    /**
     * @return
     * @throws ExecutionException
     */
    /**
     * @return
     * @throws ExecutionException
     */
    /**
     * @return
     * @throws ExecutionException
     */
    /**
     * @return
     * @throws ExecutionException
     */
    /**
     * @return
     * @throws ExecutionException
     */
    /**
     * @return
     * @throws ExecutionException
     */
    /**
     * @return
     * @throws ExecutionException
     */
    public Object realExecute() throws ExecutionException {
        // Activator.getDefault().logDebug("Decompose Proof Called");
         /**
         * Is set to the set of ASSUMEs of the selected step/theorem,
         * excluding inner ASSUME/PROVE assumptions.
         */
        Vector<SemanticNode> assumes = new Vector<SemanticNode>();
    
        /**
         * Is set to the goal of the selected step or theorem, which
         * may come from the context.  It is set to null if the goal
         * cannot be handled.
         */
        SemanticNode  goal = null ;  
        
        /**
         * The step from which the goal comes.
         */
        
        LevelNode goalStep = null ;
        /**
         * If goal is set to null, this describes why not in an error
         * message saying "Step has goal that comes from" + nullReason + "step".
         */
        String nullReason = "[This string should never be displayed]";
        
        /**
         * Is set to all prior facts asserted by the theorem or its steps
         * that could be used in proving the selected step.  (Empty if the
         * theorem itself is selected.)  It does not contain inner
         * ASSUME/PROVE assumptions
         */
        Vector <SemanticNode> contextAssumptions = new Vector<SemanticNode>() ;
        
        /**
         * For each assumption in contextAssumptions, the following two vectors
         * give the step from which the assumption comes and its name, which is
         * "" if it comes from  an unnamed step or the theorem itself.
         */     
        Vector <LevelNode> contextSteps = new Vector<LevelNode>() ;
        Vector <String> contextSources = new Vector<String> () ;
        // String[] blankLine = new String[] { "" };
        // String[] oneline = new String[] { "1" };
        
        
        /******************************************************************
         * Perform various checks to see if the command should be executed, and
         * possibly raise an error warning if it shouldn't.
         *******************************************************************/
        // Do nothing if already executing command.
        if (this.windowShell != null) {
            if (!this.windowShell.isDisposed()) {
                System.out.println("Command called when being executed.");
                return null;
            }
        }

        // Report an error if there are dirty modules.
        // This should not happen
        if (existDirtyModules()) {
            MessageDialog.openError(UIHelper.getShellProvider().getShell(),
                    "Decompose Proof Command", "There is an unsaved module.");
            return null;
        }

        // Pop up an error if the spec is not parsed.
        Spec spec = Activator.getSpecManager().getSpecLoaded();
        if (spec == null || spec.getStatus() != IParseConstants.PARSED) {
            MessageDialog
                    .openError(UIHelper.getShellProvider().getShell(),
                            "Decompose Proof Command",
                            "The spec status must be \"parsed\" to execute this command.");
            return null;
        }

        /*
         * The following text for finding the editor, document, selection, and
         * module is copied from other commands.
         */
        // The following should be a no-op, because the editor was already
        // found to be non-null.
        if (editor == null) {
            Activator.getDefault().logDebug(
                    "2nd call of getTLAEditorWithFocus returned null");
            return null;
        }
        editorIFile = ((FileEditorInput) editor.getEditorInput()).getFile();

        // The editor should not be dirty, so the following should be a no-op.
        if (editor.isDirty()) {
            MessageDialog.openError(UIHelper.getShellProvider().getShell(),
                    "Decompose Proof Command",
                    "The module is dirty; this should not happen.");
            return null;
        }

        /**********************************************
         * Initialize the state of the decomposition.
         **********************************************/
        this.state = new DecompositionState();
        state.hasChanged = false;
        // state.chosenSplit = -1;
        state.needsStepNumber = false;
        state.goalDefinitions = new StringSet();
        state.assumpDefinitions = new HashSet<String>();

        // selectedLocation is Location of selected region.
        Location selectedLocation = EditorUtil.getLocationAt(doc, offset,
                selection.getLength());

        /****************************************************
         * Set the `theorem' field.
         *****************************************************/
        TheoremNode[] allTheorems = moduleNode.getTheorems();
        theorem = null;
        int i = 0;
        String moduleFile = moduleNode.stn.getFilename();
        while ((theorem == null) & (i < allTheorems.length)) {
            if (allTheorems[i].stn.getFilename().equals(moduleFile)
                    && EditorUtil.lineLocationContainment(selectedLocation,
                            allTheorems[i].stn.getLocation())) {
                theorem = allTheorems[i];
            }
            i++;
        }

        if (theorem == null) {
            MessageDialog.openError(UIHelper.getShellProvider().getShell(),
                    "Decompose Proof Command",
                    "The cursor is not in a theorem.");
            return null;
        }

        /****************************************************************
         * Initialize goal to the theorem's goal
         ****************************************************************/
        goal = theorem.getTheorem() ;
        if (goal instanceof AssumeProveNode) {
            goal = ((AssumeProveNode) goal).getProve();            
        }
        goalStep = theorem ;
        
        // Set declaredIdentifiers to all the defined or declared symbols
        // whose scope contains `theorem'
        this.declaredIdentifiers = 
                ResourceHelper.declaredSymbolsInScopeSet(
                this.moduleNode, theorem.stn.getLocation());

        
        /********************************************************************
         * Set the following fields: step,  proofLevel, proof. Add the necessary
         * declarations to this.declaredIdentifiers.  Also compute the following
         * two values.
         *********************************************************************/
        // ExprNode goal = null ;
        
        step = theorem;
        boolean notDone = true;
        /*
         * proofLevel is set to the level of the current proof, if there is one;
         * otherwise it is set to -1. This is tricky because for a proof node
         * that is a DefStepNode (which comes from a DEFINE step or a step of
         * the form Foo == INSTANCE...) or an InstanceNode (which comes from a
         * step that is a simple INSTANCE statement) from an unnumbered step,
         * the level number is nowhere in the semantic (or syntax) tree. So, we
         * have to keep checking proof steps until we find a step whose node is
         * not a DefStepNode or InstanceNode. If we don't find one, proofLevel
         * is set to -1. Fortunately, the chosen step can't be decomposed in
         * that case, so an error should be raised before any use is made of
         * proofLevel.
         * 
         * This represents a change made by LL on 8 Mar 2013. Before then,
         * stepLevel was called on pfsteps[0], causing a bug if pfsteps[0] was a
         * DefStepNode or InstanceNode.
         */
        proofLevel = -1;
        proof = step.getProof();
        while (notDone && (proof != null)
                && (proof instanceof NonLeafProofNode)) {
            LevelNode[] pfsteps = ((NonLeafProofNode) proof).getSteps();
            LevelNode foundLevelNode = null;
            i = 0;
            // The following step added by LL on 24 April 2013. Without
            // it, the added steps get the level number of 1 plus the
            // highest-level of the proof.
            proofLevel = -1;
            while ((foundLevelNode == null) && (i < pfsteps.length)) {
                if (    (proofLevel == -1) 
                    && !(pfsteps[i] instanceof DefStepNode)
                    && !(pfsteps[i] instanceof InstanceNode)) {
                   proofLevel = stepLevel(pfsteps[i]);
                }
                // Set currStepName to name of the current step.
                String currStepName = null ;
                if (pfsteps[i] instanceof TheoremNode) {
                  currStepName = getStepName((TheoremNode) pfsteps[i]) ;
                }

                if (EditorUtil.lineLocationContainment(selectedLocation,
                        pfsteps[i].stn.getLocation())) {
                    foundLevelNode = pfsteps[i];
                    

                    // pfsteps[i] is either the selected step
                    // or a step whose proof contains the selected step.
                    // Here's what must be done:
                    //   For a non-SUFFICES step:  
                    //     IF it's an ASSUME/PROVE:
                    //      - Add its NEW declarations to declaredIdentifiers.
                    //      - Add its other assumptions to either assumes or
                    //        context assumptions, depending on whether this is the
                    //        selected step.
                    //      - set goal to its PROVE formula
                    //     IF it's not an assume prove:
                    //       IF it's a CASE, add its formula to assumes or contextAssumptions.
                    //       IF it's a PICK, set goal to null.
                    //       IF it's a QED step, do nothing.
                    //       IF it's an ordinary formula, set goal to it.
                    //   For a SUFFICES step:
                    //       Set goal to null.
                    if (pfsteps[i] instanceof TheoremNode) {
                       TheoremNode thmNode = (TheoremNode) pfsteps[i];
                       ProofNode pfNode =  thmNode.getProof() ;
                       // Set isChosenStep true if pfsteps[i] has no proof.
                       // If pfsteps[i] is the chosen step, then either isChosenStep is true, 
                       // or else the user has chosen a step with a proof and an error will
                       // later be raised.
                       boolean isChosenStep = (pfNode == null) || (pfNode instanceof LeafProofNode) ;
                       if (!thmNode.isSuffices()) {
                           if (thmNode.getTheorem() instanceof AssumeProveNode) {
                              // ordinary ASSUME/PROVE
                              SemanticNode[] assumptions = ((AssumeProveNode) thmNode
                                      .getTheorem()).getAssumes();
                              for (int j = 0; j < assumptions.length; j++) {
                                  if (assumptions[j] instanceof NewSymbNode) {
                                      declaredIdentifiers
                                              .add(((NewSymbNode) assumptions[j])
                                                      .getOpDeclNode().getName()
                                                      .toString());
                                  } else {
                                      if (! (assumptions[j] instanceof AssumeProveNode)) {
                                        if (isChosenStep) {
                                            assumes.addElement(assumptions[j]) ;
                                        } else {
                                            contextAssumptions.addElement(assumptions[j]);
                                            contextSteps.addElement(thmNode) ;
                                            contextSources.addElement(currStepName);
                                        }
                                      }
                                  }
                              }
                              goal = ((AssumeProveNode) thmNode.getTheorem()).getProve();
                              goalStep = thmNode ;
                          } else {
                            // not SUFFICES or ASSUME/PROVE
                              SemanticNode newGoalSemNode = thmNode.getTheorem() ;
                              if (newGoalSemNode instanceof OpApplNode) {
                                  OpApplNode newGoal = (OpApplNode) newGoalSemNode ;
                                  UniqueString goalOpName = newGoal.getOperator().getName();
                                  if (goalOpName == ASTConstants.OP_pfcase) {
                                      if (isChosenStep) {
                                          assumes.addElement(newGoal.getArgs()[0]) ;
                                      } else {
                                          contextAssumptions.addElement(newGoal.getArgs()[0]);
                                          contextSteps.addElement(thmNode) ;
                                          contextSources.addElement(currStepName);
                                      }
                                  } else if (goalOpName == ASTConstants.OP_pick) {
                                      goal = null;
                                      nullReason = "PICK";
                                  } else if (goalOpName == null) {
                                      // I don't know what this is, so it must be weird.
                                      goal = null;
                                      nullReason = "weird";
                                  } else if (goalOpName == ASTConstants.OP_qed) {
                                      // do nothing
                                  }
                                  else {
                                      // an ordinary formula
                                      goal = newGoal ; 
                                      goalStep = thmNode ;
                                  }                           
                              } else {
                                  // Not an OpApplNode, so it's something weird.
                                  goal = null;
                                  nullReason = "weird";
                              }
                           }                        
                       } else {
                           // A SUFFICES step.
                           goal = null;
                           nullReason = "SUFFICES";
                         }
                    } // end of if (pfsteps[i] instanceof TheoremNode)
                    else { goal = null;
                           nullReason = "weird" ;
                    }
                } else {
                    // Selected step must come after this step.  Have the
                    // following cases:
                    // For a SUFFICES step:
                    //   If it's an ASSUME/PROVE then:
                    //     - Add its ASSUMEs to contextAssumptions
                    //     - Add its NEW declarations to declaredIdentifiers.
                    //     - Set goal to its PROVE formula
                    //   If it's not a SUFFICES step:
                    //     - Set goal to its formula.
                    //  For a non-SUFFICES step:
                    //    If it's a PICK step, then:
                    //      - Add its declared formulas to declaredIdentifiers.
                    //      - Add its body to contextAssumptions
                    //    If it's a TAKE step, then:
                    //      - Add its declared formulas to declaredIdentifiers.
                    //      - Set goal to null.
                    //    If it's a HAVE step, then:
                    //      - Add its formula to contextAssumptions
                    //      - Set goal to null.
                    //    If it's a WITNESS step, then set goal to null.
                    //    If it's just a plain formula, add it to contextAssumptions.
                    //    If it's a DEFINE or INSTANCE step, then add its definitions
                    //      to declaredIdentifiers.
                    // 
                    // Bug fixed by LL on 24 June 2014: Failed to add PICK step's
                    // introduced identifiers to declaredIdentifiers.
                    // 
                    if (pfsteps[i] instanceof TheoremNode) {
                        TheoremNode node = (TheoremNode) pfsteps[i];
                        if (node.isSuffices()) {
                           // For SUFFICES, must set goal to this node's goal
                           // and add any non-NEW assumptions to contextAssumptions.                           
                           if (node.getTheorem() instanceof AssumeProveNode) {
                                 goal = ((AssumeProveNode) node.getTheorem()).getProve() ;
                                 goalStep = node ;
                                 SemanticNode[] assumptions = ((AssumeProveNode) node
                                         .getTheorem()).getAssumes();
                                 for (int j = 0; j < assumptions.length; j++) {
                                     if (assumptions[j] instanceof NewSymbNode) {
                                         declaredIdentifiers
                                                 .add(((NewSymbNode) assumptions[j])
                                                         .getOpDeclNode().getName()
                                                         .toString());
                                     } else {
                                         // Non-NEW assumptions added to contextAssumptions.
                                         if (! (assumptions[j] instanceof AssumeProveNode)) {
                                           contextAssumptions.addElement(assumptions[j]) ;
                                           contextSteps.addElement(node) ;
                                           contextSources.addElement(currStepName) ;
                                         }
                                     }
                                 }
                           } else {
                               goal = (SemanticNode) node.getTheorem();
                               goalStep = node ;
                               if (! (goal instanceof OpApplNode)){
                                   goal = null ;
                                   nullReason = "weird";
                               }
                           }
                        } else if (node.getTheorem() instanceof OpApplNode) {
                            // Check if it's a $Pick step and if it is, add declared
                            // identifiers and add body to contextAssumptions.
                            OpApplNode oanode = (OpApplNode) node.getTheorem();
                            String operatorName = oanode.getOperator().getName().toString();

                            if (   operatorName.equals("$Pick")
                                || operatorName.equals("$Witness")
                                || operatorName.equals("$Take")) {
                                FormalParamNode[] fp = oanode
                                        .getUnbdedQuantSymbols();
                                
                                // Add body of PICK to contextAssumptions
                                if (operatorName.equals("$Pick")) {
                                    contextAssumptions.addElement(oanode.getArgs()[0]) ;
                                    contextSteps.addElement(node) ;
                                    contextSources.addElement(currStepName) ;
                                }
                                if (! operatorName.equals("$Witness")) {
                                    // add to declaredIdentifiers
                                    if (fp != null) {
                                        // This is an unbounded PICK or TAKE -- 
                                        //  e.g., PICK  x, y : exp
                                        for (int j = 0; j < fp.length; j++) {
                                            declaredIdentifiers.add(fp[j].getName()
                                                    .toString());
                                        }
                                    } else {
                                        // This is a bounded PICK or TAKE -- e.g., 
                                        // PICK x, y \in S, z \in T : exp
                                        FormalParamNode[][] fpn = oanode
                                                .getBdedQuantSymbolLists();
                                        for (int j = 0; j < fpn.length; j++) {
                                            for (int k = 0; k < fpn[j].length; k++) {
                                                declaredIdentifiers.add(fpn[j][k]
                                                        .getName().toString());
                                            }
                                        }
                                    }
                                    
                                    if (operatorName.equals("$Take")) {
                                        goal = null ;
                                        nullReason = "TAKE" ;
                                    }
                                } else {
                                    goal = null ;
                                    nullReason = "WITNESS" ;
                                }
                                

                            } else if (operatorName.equals("$Have")) {
                                goal = null ;
                                nullReason = "HAVE" ;
                                contextAssumptions.addElement(oanode.getArgs()[0]) ;
                                contextSteps.addElement(node) ;
                                contextSources.addElement(currStepName) ;           
                            } else if (! operatorName.equals("$Pfcase"))  {
                                // I think the only possibility left is for this to be 
                                // an ordinary formula.
                                contextAssumptions.addElement(oanode) ;
                                contextSteps.addElement(node) ;
                                contextSources.addElement(currStepName) ;
                            }
                        }
                    }

                    // It it's a DEFINE step, must add the defined
                    // operator names to declaredIdentifiers.
                    if (pfsteps[i] instanceof DefStepNode) {
                        OpDefNode[] defs = ((DefStepNode) pfsteps[i]).getDefs();
                        for (int j = 0; j < defs.length; j++) {
                            declaredIdentifiers.add(defs[j].getName()
                                    .toString());
                        }
                    }
                    // If its an INSTANCE step, must add the instantiated
                    // module's definitions.
                    if (pfsteps[i] instanceof InstanceNode) {
                        ResourceHelper.addDeclaredSymbolsInScopeSet(
                                declaredIdentifiers,
                                ((InstanceNode) pfsteps[i]).getModule(),
                                ResourceHelper.infiniteLoc);
                    }
                }

                i++;
            }
            if (foundLevelNode == null) {
                notDone = false;
            } else if (!(foundLevelNode instanceof TheoremNode)) {
                MessageDialog.openError(UIHelper.getShellProvider().getShell(),
                        "Decompose Proof Command",
                        "The cursor is in a non-provable step.");
                return null;
            } else {
                step = (TheoremNode) foundLevelNode;
                proof = step.getProof();
            }
        }
        
        /**************************************************************
         * Check that the step has either no proof or a leaf proof.
         *************************************************************/
        if ((proof != null) && !(proof instanceof LeafProofNode)) {
            MessageDialog
                    .openError(UIHelper.getShellProvider().getShell(),
                            "Decompose Proof Command",
                            "You have selected a step that already has a non-leaf proof.");
            return null;
        }

        /**
         * Because of the poor organization of the code, there are two
         * edge cases not handled properly and must be handled here
         * as special cases.  The first is the case of the statement of
         * the theorem being the decomposed step.  The code for this case  
         * was cloned from the code executed above within the body 
         * of the
         * 
         *    if (!step.isSuffices())
         *    
         * statement which handles setting goal and assumes for a
         * decomposed step.
         * 
         * The second case not handled properly is that of the theorem 
         * statement being an ASSUME/PROVE and is not itself being 
         * decomposed.  In this cases, the theorem's ASSUMES must be 
         * prepended to contextAssumptions.
         */
        if (step == theorem) {
            if (step.getTheorem() instanceof AssumeProveNode) {
                // ordinary ASSUME/PROVE
                SemanticNode[] assumptions = ((AssumeProveNode) step
                        .getTheorem()).getAssumes();
                for (int j = 0; j < assumptions.length; j++) {
                    if (assumptions[j] instanceof NewSymbNode) {
                        declaredIdentifiers
                                .add(((NewSymbNode) assumptions[j])
                                        .getOpDeclNode().getName()
                                        .toString());
                        assumes.addElement(assumptions[j]) ;
                    } else {
                        if (! (assumptions[j] instanceof AssumeProveNode)) {
                         assumes.addElement(assumptions[j]) ;
                        }
                    }
                }
                goal = ((AssumeProveNode) step .getTheorem()).getProve();
                goalStep = step ;

           } else {
            // not  ASSUME/PROVE
            SemanticNode newGoalSemNode = step.getTheorem() ;
             if (newGoalSemNode instanceof OpApplNode) {
                OpApplNode newGoal = (OpApplNode) newGoalSemNode ;
                UniqueString goalOpName = newGoal.getOperator().getName();
                if (goalOpName == ASTConstants.OP_pfcase) {
                    goal = newGoal.getArgs()[0] ;
                } else if (goalOpName == ASTConstants.OP_pick) {
                    goal = null;
                    nullReason = "PICK";
                } else if (goalOpName == null) {
                    // I don't know what this is, so it must be weird.
                    goal = null;
                    nullReason = "weird";
                } else if (goalOpName == ASTConstants.OP_qed) {
                    // do nothing
                }
                else {
                    // an ordinary formula
                    goal = newGoal ; 
                    goalStep = step ;
                }                           
             } else {
                // Not an OpApplNode, so it's something weird.
                goal = null;
                nullReason = "weird";
             }
           }
        } else { // step != theorem
            if (theorem.getTheorem() instanceof AssumeProveNode) {
                SemanticNode[] thmAssumps = 
                    ((AssumeProveNode) theorem.getTheorem()).getAssumes() ;
                // assumption inserted as the k-th assumption in contextAssumptions
                int k = 0 ;
                for (int j = 0; j < thmAssumps.length; j++) {
                    if (thmAssumps[j] instanceof NewSymbNode) {
                        declaredIdentifiers
                                .add(((NewSymbNode) thmAssumps[j])
                                        .getOpDeclNode().getName()
                                        .toString());
                    } else {
                        contextAssumptions.insertElementAt(thmAssumps[j], k) ;  
                        contextSteps.insertElementAt(theorem.getTheorem(), k) ;
                        contextSources.insertElementAt(null, k) ;
                        k++ ;
                    }                    
                }
            }
        }
        /**
         * Found the and processed step. Raise an error if the step's goal can't 
         * be handled.
         */
        if (goal == null) {
            MessageDialog.openError(UIHelper.getShellProvider().getShell(),
                    "Decompose Proof Command",
                    "Cannot decompose because goal is from a " + nullReason + " step.");
            return null;
        }
        /*
         * set proofLevelString
         */
        int level = this.proofLevel;
        if (level < 0) {
            level = 0;
        }
        proofLevelString = "<" + (level + 1) + ">";

        /*************************************************************
         * Set stepNumber and stepColumn.  
         * 
         * Most of this code has been cloned to implement the
         * getStepName method.  It should be replaced by a call
         * to that method, but if it ain't broke, why fix it?
         ************************************************************/
        SyntaxTreeNode nd = (SyntaxTreeNode) step.stn;
        if (step == theorem) {
            stepNumber = null;
        } else {
            stepNumber = nd.getHeirs()[0].image.toString();
            if (stepNumber.indexOf('>') == stepNumber.length() - 1) {
                stepNumber = null;
            } else {
                // Need to remove punctuation after the number:
                i = stepNumber.indexOf('>') + 1;
                while ((i < stepNumber.length() && (Character
                        .isLetterOrDigit(stepNumber.charAt(i)) || (stepNumber
                        .charAt(i) == '_')))) {
                    i++;
                }
                if (i < stepNumber.length()) {
                    stepNumber = stepNumber.substring(0, i);
                }
            }
        }
        stepColumn = nd.getLocation().beginColumn();


        /**************************************************************
         * Set stepRep
         *************************************************************/
        try {
            stepRep = new NodeRepresentation(doc, step);
        } catch (BadLocationException e) {
            e.printStackTrace();
            MessageDialog.openError(UIHelper.getShellProvider().getShell(),
                    "Decompose Proof Command",
                    "An error that should not happen has occurred in "
                            + "line 1479 of NewDecomposeProofHandler.");
            return null;
        }

        // MOVED THE SETTING OF assumes, goal to the main loop above.
        /**************************************************************
         * Set state.assumeReps,  and state.goalRep
         *************************************************************/
            state.assumeReps = new Vector<NodeRepresentation>();

            // Add to state.assumeReps the decomposable context assumptions.
            for (i = 0; i < contextAssumptions.size(); i++) {
                NodeRepresentation contextStepRep = null ;
                try {
                    contextStepRep = new NodeRepresentation(doc, contextSteps.elementAt(i));
                } catch (BadLocationException e) {
                    e.printStackTrace();
                    MessageDialog.openError(UIHelper.getShellProvider().getShell(),
                            "Decompose Proof Command",
                            "An error that should not happen has occurred in "
                                    + "line 1544 of NewDecomposeProofHandler.");
                    return null;
                }
                NodeRepresentation nodeRep = contextStepRep.subNodeRep(contextAssumptions.elementAt(i),
                        state.assumeReps, null, null, null, true);
                nodeRep.contextStepName = contextSources.elementAt(i) ;
                if ((nodeRep.decomposition != null) && (nodeRep.nodeSubtype != NodeRepresentation.IMPLIES_TYPE)) {
                    nodeRep.initialPosition = state.assumeReps.size() ;
                    state.assumeReps.addElement(nodeRep);
                    state.numberOfContextAssumptions++;                  
                }
            }

            // Add to state.assumeReps the assumptions in assumes,
            // which come from the step being decomposed that is either
            // an ASSUME/PROVE or a CASE step.  Set hasAssumes true
            // iff there is such an assumption
            hasAssumes = false;
            if (assumes.size() > 0) {
                hasAssumes = true ;
            }
            for (i = 0; i < assumes.size(); i++) {
                NodeRepresentation nodeRep = stepRep.subNodeRep(assumes.elementAt(i),
                        state.assumeReps, null, null, null, true);
                nodeRep.contextStepName = this.stepNumber ;
// I THINK THE FOLLOWING COMMENT IS OBSOLETE:
// If we want to add an option not to show non-decomposible assumptions, here's
// the code to implement it. 
//                if (nodeRep.decomposition != null) {
                    nodeRep.initialPosition = state.assumeReps.size() ;
                    state.assumeReps.addElement(nodeRep);                  
//                }
            }
            // Initially there are no added assumptions, so state.firstAddedAssumption
            // points to the position after the end of state.assumeReps.
            state.firstAddedAssumption = state.assumeReps.size();
            
           // Similarly to the handling of contextAssumptions, we create the NodeRepresentation
           // of the current goal from the NodeRepresentation of goalStep.
           NodeRepresentation goalStepRep = null;
        try {
            goalStepRep = new NodeRepresentation(doc, goalStep);
        } catch (BadLocationException e) {
            // TODO Auto-generated catch block
            e.printStackTrace();
            MessageDialog.openError(UIHelper.getShellProvider().getShell(),
                    "Decompose Proof Command",
                    "An error that should not happen has occurred in "
                            + "line 1583 of NewDecomposeProofHandler.");
            return null;
        }
           state.goalRep = goalStepRep.subNodeRep(goal, null, null, null, null, false);
           state.goalRep.initialPosition = Integer.MAX_VALUE - 42;
           state.goalRep.fromGoal = true ;
         // END OF SETTING state.assumeReps and state.goalRep

        /***************************************************************************
         * Make the editor read-only.
         ***************************************************************************/
        // The following method is deprecated because it is actually possible to
        // use it, so it has been replaced by something that requires a PhD in
        // Eclipse to figure out how to use. The command
        //
        // EditorUtil.setReadOnly(editorIFile, true);
        //
        // that has worked in other places in the Toolbox code seems to work
        // here only occasionally. This being modern 21st century code, I have
        // the choice of reading 10^6 lines of code to figure out what is going
        // on, or doing what seems to work.
        editorIFile.setReadOnly(true);
        raiseWindow();
        // Activator.getDefault().logDebug(
        // "Finished Decompose Proof Handler execute");
        return null;
    }

    /**
     * Returns the name of a proof step, or null if it has no name (but only
     * a level).  Thus for the step
     * 
     *     <3>4ax. 1+1=2
     *     
     * it returns "<3>4ax", but returns null for the step:
     * 
     *     <3> 2+2=5
     *     
     * This code cloned from the code that sets the stepNumber and
     * stepColumn fields.  That code should be replaced by a call
     * of this method.
     * @param step
     * @return
     */
    static String getStepName (TheoremNode step) {
        SyntaxTreeNode nd = (SyntaxTreeNode) step.stn;
        String result = nd.getHeirs()[0].image.toString();
        if (result.indexOf('>') == result.length() - 1) {
            result = null;
        } else {
            // Need to remove punctuation after the number:
            int i = result.indexOf('>') + 1;
            while ((i < result.length() && (Character
                    .isLetterOrDigit(result.charAt(i)) || (result
                    .charAt(i) == '_')))) {
                i++;
            }
            if (i < result.length()) {
                result = result.substring(0, i);
            }
        }
        return result ;
    }
    /**
     * This method is called when the user issues a the Decompose Proof command.
     * It launches a synchronous task that calls realExecute() to do most of the
     * work. However, before doing that, it sets various fields of the
     * NewDecomposeProofHandler object that can't be set from the separate
     * thread.
     * 
     * This running of a separate task was done to allow the command to ask the
     * user if he wants to save and parse dirty modules, and to not run the code
     * in realExecute() before those modules were actually saved and parsed. I
     * tried all sorts of things until coming up with this code, which seems to
     * work. However, previous versions seemed to work until bugs
     * appeared--perhaps because the weather changed in Bangladesh. So, I have
     * no idea if it will still work when the monsoons come.
     * 
     * Apparently the monsoons came, and the race condition re-appeared.
     * However, so far, its only effect seems to be a race between two
     * executions of the parser, which can make the command fail and may produce
     * a bogus parsing error. Of course, when the monsoons stop, some other
     * failure mode may appear.
     * 
     * @see org.eclipse.core.commands.IHandler#execute(org.eclipse.core.commands.
     *      ExecutionEvent)
     */
    public Object execute(ExecutionEvent event) throws ExecutionException {
        /*******************************************************************
         * Set the following fields: doc, text, selectionProvider, selection,
         * offset, moduleNode.
         ******************************************************************/
        this.editor = EditorUtil.getTLAEditorWithFocus();
        this.doc = editor.getDocumentProvider().getDocument(
                editor.getEditorInput());
        this.selectionProvider = editor.getSelectionProvider();
        this.selection = (TextSelection) selectionProvider.getSelection();
        this.offset = selection.getOffset();

        // Get the module.
        String moduleName = editor.getModuleName();
        this.moduleNode = ResourceHelper.getModuleNode(moduleName);

        // Initialize moduleNameToDoc
        moduleNameToDoc = new Hashtable<String, IDocument>() ;
        moduleNameToDoc.put(this.moduleNode.getName().toString(), this.doc) ;

        /**
         * The Following code copied from ProverHelper.
         */

        boolean proceed = UIHelper.promptUserForDirtyModules();
        if (!proceed) {
            // the user cancelled
            return null;
        }

        if (editor == null) {
            Activator.getDefault().logDebug(
                    "getTLAEditorWithFocus returned null");
            return null;
        }
        editorIFile = ((FileEditorInput) editor.getEditorInput()).getFile();

        ParseResult parseResult = ResourceHelper
                .getValidParseResult(editorIFile);

        if (parseResult == null) {
            /*
             * The following comments taken from ProverJob.initializeFields,
             * from which the code here was cloned.
             * 
             * Its necessary to call this parsing within the job's run method.
             * Its a bad idea to have two calls to SANY executing at the same
             * time, and its possible for a launch of the prover to trigger
             * background parsing. For example, the user might have dirty
             * editors open when launching the prover. He will be prompted to
             * save them. This could trigger background parsing. The run method
             * will not be executed while the background parsing completes. This
             * ensures that the following parsing will not occur while the
             * background parsing executes.
             */
            parseResult = new ModuleParserLauncher().parseModule(editorIFile,
                    new NullProgressMonitor());
        }

        /**
         * ProverHelper at this point schedules a new job. I couldn't get that
         * to work right, so I tried a runnable.
         */
        DecomposeProofRunnable runnable = new DecomposeProofRunnable(this);

        UIHelper.runUISync(runnable);
        return null;
    }

    /**
     * The Runnable class extension for running the realExecute() method.
     * 
     * @author lamport
     * 
     */
    public class DecomposeProofRunnable implements java.lang.Runnable {
        NewDecomposeProofHandler handler;

        DecomposeProofRunnable(NewDecomposeProofHandler h) {
            handler = h;
        }

        public void run() {
            try {
                handler.editor = EditorUtil.getTLAEditorWithFocus();
                handler.doc = editor.getDocumentProvider().getDocument(
                        editor.getEditorInput());
                handler.selectionProvider = editor.getSelectionProvider();
                handler.selection = (TextSelection) selectionProvider
                        .getSelection();
                handler.offset = selection.getOffset();

                // Get the module.
                String moduleName = editor.getModuleName();
                handler.moduleNode = ResourceHelper.getModuleNode(moduleName);

                handler.realExecute();
            } catch (ExecutionException e) {
                // TODO Auto-generated catch block
                e.printStackTrace();
            }
        }
    }

    /**
     * METHODS FOR DISPLAYING THE COMMAND'S WINDOW
     */

    // Note: Experimentation seems to show that horizontalSpan doesn't apply to
    // a Label or a Button, so I've been putting the Label or Button inside a
    // composite to do that.
    private void raiseWindow() {
//if ((state.numberOfContextAssumptions > state.assumeReps.size())) {
//    return ;
//}
        if ((windowShell != null) && (!windowShell.isDisposed())) {
            location = windowShell.getLocation();
            windowShell.close();
            windowShell.dispose();
        }
        Shell topshell = UIHelper.getShellProvider().getShell();

        // Since minimizing the window does something weird--namely,
        // makes it contain just the top bar and puts it in a corner
        // of the screen--we create a resizable window with only a
        // close button.
        windowShell = new Shell(topshell, SWT.CLOSE | SWT.TITLE | SWT.RESIZE);
        windowShell.setText("Decompose Proof - New Version Under Development");
        windowShell.addDisposeListener(new WindowDisposeListener(this));
        Composite shell = new Composite(windowShell, SWT.NONE);
        GridLayout gridLayout = new GridLayout(3, false);
        shell.setLayout(gridLayout);
        /**
         * Display the top-line window
         */
        // topMenu is a composite containing the stuff on the menu line.
        Composite topMenu = new Composite(shell, SWT.NONE);
        gridLayout = new GridLayout(7, false); 
           // was 5 then 6.  Needs to be 7 because of invisible subexpressionButton.
        gridLayout.marginBottom = 0;
        topMenu.setLayout(gridLayout);
        GridData gridData = new GridData();
        gridData.horizontalSpan = 3;
        topMenu.setLayoutData(gridData);

        // Display "Back Button"
        Button backButton = new Button(topMenu, SWT.PUSH);
        setupMenuButton(backButton, BACK_BUTTON, "\u2190");
        backButton.setFont(JFaceResources.getFontRegistry().get(
                JFaceResources.HEADER_FONT));
        backButton.setEnabled(state.previousState != null);

        // Display "Replace Step" button
        // The enabling condition for the button was changed by LL on 23 Aug
        // 2014
        // to the following: This button is enabled iff the following are all
        // true
        //
        // - some change has been made
        // - A Case split has not been chosen. (If it has, then
        // it has an enabled P button.
        // - The last decomposition action (as opposed to a Back
        // action or movement of an assumption up or down) was
        // NOT clicking on an /\ decomposition button
        // (of an assumption).
        //
        // One should click on an /\ decomposition button
        // only to reveal a \E or \/ decomposition. The third
        // condition doesn't insure this, since the user could
        // perform two separate /\ decomposition and only
        // do a further decomposition on one of the results. But,
        // it approximates that condition.
        Button replaceButton = new Button(topMenu, SWT.PUSH);
        setupMenuButton(replaceButton, PROVE_BUTTON, "P");
        replaceButton.setFont(JFaceResources.getFontRegistry().get(
                JFaceResources.HEADER_FONT));
        replaceButton.setEnabled(state.hasChanged && (! state.splitChosen())
        /* && (state.andSplitEnd == -1) removed with 23 Aug 2014 changes. */
        );

        
        // Display "Show Context" checkbox.
        showContextButton = new Button(topMenu, SWT.CHECK);
        setupCheckButton(showContextButton, "Show Context");
        showContextButton.setSelection(showContextValue);
        // This checkbox needs a listener to toggle the display of the
        // context assumptions.
        showContextButton.addSelectionListener(new DecomposeProofButtonListener(this,
                new Integer(SHOW_CONTEXT_BUTTON), MENU));


        // Display "Use SUFFICES" checkbox.
        useSufficesButton = new Button(topMenu, SWT.CHECK);
        setupCheckButton(useSufficesButton, "Use SUFFICES");
        useSufficesButton.setSelection(useSufficesValue);

        // Display "Use CASE" checkbox.
        useCaseButton = new Button(topMenu, SWT.CHECK);
        setupCheckButton(useCaseButton, "Use CASE");
        useCaseButton.setSelection(useCaseValue);

        // Display checkbox to choose whether to expand definitions with
        // subexpression names.
        subexpressionButton = new Button(topMenu, SWT.CHECK);
        setupCheckButton(subexpressionButton, "Use subexpression names");
        subexpressionButton.setSelection(subexpressionValue);
        gridData = new GridData();
        gridData.horizontalAlignment = GridData.FILL;
        gridData.grabExcessHorizontalSpace = true;
        subexpressionButton.setLayoutData(gridData);
        // Hide the option. See comments at beginning of file.
        subexpressionButton.setVisible(false);

        // Display Help button that should raise help page for this
        // dialog window. I wish I knew how to move the button to
        // the right edge of the window. But it's been a mere 36
        // years since Knuth invented the idea of expandable glue,
        // so we can't expect the Eclipse people to have heard of it
        // yet.  However, this seems to produce a reasonable approximation.
        Button helpButton = HelpButton.helpButton(topMenu,
                "prover/decompose.html");
        gridData = new GridData();
        gridData.horizontalIndent = 20;
        helpButton.setLayoutData(gridData);

        /**************************************************************
         * Display the ASSUME Section
         **************************************************************/
        // Display the "ASSUME", which must be put in a
        // composite because it spans multiple rows, and it appears
        // that a Label can't do that.
        Label assumeLabel ;
//        gridData = new GridData();
//        gridData.horizontalSpan = 3;
//        Label assumeLabel = new Label(shell, SWT.NONE);
//        assumeLabel.setText("ASSUME");
//        assumeLabel.setFont(JFaceResources.getFontRegistry().get(
//                JFaceResources.HEADER_FONT));
//        assumeLabel.setLayoutData(gridData);
        if (state.assumeReps != null) {
            addAssumptionsToComposite(state.assumeReps, shell);
        }

        /**********************************************************
         * Display the Goal
         **********************************************************/
        // Display the "PROVE", which must be put in a
        // composite because it spans multiple rows, and it appeared
        // that a Label can't do that. However, for some reason it
        // now appears that a label can do that.
        gridData = new GridData();
        gridData.horizontalSpan = 3;
        assumeLabel = new Label(shell, SWT.NONE);
        assumeLabel.setLayoutData(gridData);
        assumeLabel.setText("PROVE");
        assumeLabel.setFont(JFaceResources.getFontRegistry().get(
                JFaceResources.HEADER_FONT));
        String labelText = null;

        // isProver = true means clicking on the button produces the proof.
        boolean isProver = false;
        // Set disable to disable the button, which should be done iff
        // decomposition of an assumption has been started and this is
        // an AND node.
        boolean disable = false;
        switch (state.goalRep.nodeSubtype) {
        case NodeRepresentation.AND_TYPE:
            labelText = "/\\";
            isProver = true;
            disable = (state.splitChosen()) ;
            break;
        case NodeRepresentation.FORALL_TYPE:
            labelText = "\\A";
            // We disable \A decomposition when an OR-split has been 
            // made because it will produce a name conflict if one of 
            // the \A variables occurs (bound) in the OR-split.  This 
            // could be avoided by making the forAllAction() method 
            // smart enough to do the necessary renaming.  A simpler 
            // thing to implement would be to add code here that sets 
            // disable true only if there actually is such a name conflict.
            disable = state.splitChosen() ;
            break;
        case NodeRepresentation.IMPLIES_TYPE:
            labelText = "=>";
            break;
        default:
            labelText = null;
        }
        if (labelText != null) {
            Button goalButton = new Button(shell, SWT.PUSH);
            setupActionButton(goalButton, state.goalRep, labelText);
            goalButton.setEnabled(!disable);
        } else {
            assumeLabel = new Label(shell, SWT.NONE);
            assumeLabel.setText("  ");
        }

        // Add a spacer between the button and the formula
        Composite comp;
        comp = new Composite(shell, SWT.NONE);
        gridLayout = new GridLayout(1, false);
        comp.setLayout(gridLayout);
        if (isProver && !disable) {
            assumeLabel = new Label(comp, SWT.NONE);
            assumeLabel.setText("P");
            assumeLabel.setFont(JFaceResources.getFontRegistry().get(
                    JFaceResources.HEADER_FONT));
        }
        comp.setSize(0, 5);

        assumeLabel = new Label(shell, SWT.NONE);
        assumeLabel
                .setText(stringArrayToString(state.goalRep.primedNodeText()));
        gridData = new GridData();
        gridData.verticalAlignment = SWT.TOP;
        assumeLabel.setLayoutData(gridData);

        // The following sets the font to be the Toolbox editor's text font.
        assumeLabel.setFont(JFaceResources.getFontRegistry().get(
                JFaceResources.TEXT_FONT));
        shell.pack();
        // Point shellSize = shell.getSize();
        windowShell.pack();
        windowShell.update();
        if (this.location != null) {
            windowShell.setLocation(this.location);
        }
        windowShell.open();

        /***************************************************************************
         * For some reason, reraising the window seems to cause the editor to
         * become writable, so we make it read-only again.
         ***************************************************************************/
        // See the comments on the following command where it is used in the
        // execute method.
        editorIFile.setReadOnly(true);
    }

    /**
     * This method assumes that `composite' is a composite with a gridlayout
     * having 3 columns. It populates it with the buttons and stuff for an
     * assumptions list to go in the Decompose Proof window. It is called only
     * by RaiseWindow to produce the top-level list of assumptions, with
     * nodeRepVector equal to assume
     * 
     * @param nodeRepVector
     * @param composite
     */
    void addAssumptionsToComposite(Vector<NodeRepresentation> nodeRepVector,
            Composite composite) {

        // This code was moved from a place in which the following variables
        // were declared. Their original values are irrelevant here.
        Composite comp;
        GridData gridData;
        GridLayout gridLayout;
        Label assumeLabel;

        /*************************************************************
         * Displaying the assumptions.
         * 
         * First, Set assumeWidth to the number of characters in the widest line
         * among all the lines in the assumptions.
         **************************************************************/
        int assumeWidth = 0;
        for (int i = 0; i < nodeRepVector.size(); i++) {
            for (int j = 0; j < nodeRepVector.elementAt(i).nodeText.length; j++) {
                assumeWidth = Math.max(assumeWidth,
                        nodeRepVector.elementAt(i).nodeText[j].length());
            }
        }

        
         /**
         * Add the assumptions to the composite.
         */
        
         // We first set haveContextAssumpsToDisplay to true
         // iff there is at least one context assumption to be
         // displayed, and then add the "CONTEXT ASSUMPTIONS" heading
         // iff it is true.
         boolean haveContextAssumpsToDisplay = false ;
         for (int i = 0; i < state.numberOfContextAssumptions; i++) {
             if (displayContextAssump(nodeRepVector.elementAt(i), i)) {
                 haveContextAssumpsToDisplay = true ;
             }
         }
         
         if (haveContextAssumpsToDisplay) {
           gridData = new GridData();
           gridData.horizontalSpan = 3;
           assumeLabel = new Label(composite, SWT.NONE);
           assumeLabel.setText("CONTEXT ASSUMPTIONS");
           assumeLabel.setFont(JFaceResources.getFontRegistry().get(
                   JFaceResources.HEADER_FONT));
           assumeLabel.setLayoutData(gridData);
         }
        
        for (int i = 0; i < nodeRepVector.size(); i++) {               
            if (i == state.numberOfContextAssumptions) {
                // ADD "ASSUME" heading
                gridData = new GridData();
                gridData.horizontalSpan = 3;
                assumeLabel = new Label(composite, SWT.NONE);
                assumeLabel.setText("ASSUME");
                assumeLabel.setFont(JFaceResources.getFontRegistry().get(
                        JFaceResources.HEADER_FONT));
                assumeLabel.setLayoutData(gridData);
            }   
            if (i == state.firstAddedAssumption) {
                // ADD ----- splitting added assumptions from original ones.
                gridData = new GridData();
                gridData.horizontalSpan = 3;
                assumeLabel = new Label(composite, SWT.NONE);
                assumeLabel.setText("    - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -");
                assumeLabel.setFont(JFaceResources.getFontRegistry().get(
                        JFaceResources.HEADER_FONT));
                assumeLabel.setLayoutData(gridData);
             }
            
            NodeRepresentation aRep = nodeRepVector.elementAt(i);

            // We display aRep iff it is non-context assumption that
            // should be displayed (which is a complicated decision)
            // or it is a context assumption that should be displayed
            // (which is simple because most of the context assumptions
            // that shouldn't be displayed don't appear in nodeRepVector)
            if (  ((i >= state.numberOfContextAssumptions) 
                       && displayNonContextAssump(aRep, i))
                || ((i < state.numberOfContextAssumptions) 
                       && displayContextAssump(aRep, i))) {
              // We should display aRep  
              //
              if (aRep.nodeType != NodeRepresentation.OR_DECOMP) {
                  // This is an ordinary assumption (and Expression or NEW
                  // node).
                  // assumeLabel = new Label(comp, SWT.NONE);
                  /*************************************************************
                   * Add the button or blank area to the first column.
                   *************************************************************/
                  String labelText = null;
                  
                  // set false if button to be disabled
                  boolean enable = true ;
                  // The null test is because created NEW nodes have null
                  // semanticNode fields.
                  if ((aRep.semanticNode != null)
                          && (aRep.semanticNode.getKind() == ASTConstants.OpApplKind)) {
                      switch (aRep.nodeSubtype) {
                      case NodeRepresentation.AND_TYPE:
                          labelText = "/\\";
                          
                          // In an attempt to allow /\ decompositions to occur for
                          // \E after a case-split had been chosen, the following
                          // statement was originally
                          //    enabled == conjIsDecomposable((OpApplNode) aRep.semanticNode) ;
                          // However, this didn't work because conjIsDecomposible assumes
                          // that its input is a conjunction and not an occurrence of
                          // a defined operator whose definition is a conjunction,
                          // which may be the case here.  So, we just disable
                          // /\-decomposition after a case-split is chosen.  The user
                          // can just do the /\-decomposition before the case split.
                          //
                          enable = ! state.splitChosen() ;
                  
                           break;
                      case NodeRepresentation.OR_TYPE:
                      case NodeRepresentation.SQSUB_TYPE:
                          labelText = "\\/";
                          enable = ! state.splitChosen() ;
                          break;
                      case NodeRepresentation.EXISTS_TYPE:
                          labelText = "\\E";
                          break;
                      default:
                          labelText = null;
                      }
                  }
                  if (labelText != null) {
                      /*************************************************************
                       * Add a button
                       *************************************************************/
                      Button button = new Button(composite, SWT.PUSH);
                      setupActionButton(button, nodeRepVector.elementAt(i),
                              labelText);
                      if (!enable) { 
                          button.setEnabled(false);
                      }
                  } else {
                      /*************************************************************
                       * Add a blank area.
                       *************************************************************/
                      comp = new Composite(composite, SWT.NONE);
                      gridLayout = new GridLayout(1, false);
                      comp.setLayout(gridLayout);
                      assumeLabel = new Label(comp, SWT.NONE);
                      assumeLabel.setText("  ");
                      gridData = new GridData();
                      gridData.horizontalIndent = 25;
                      comp.setLayoutData(gridData);
                  }
                  comp = new Composite(composite, SWT.NONE);
                  gridLayout = new GridLayout(1, false);
                  comp.setLayout(gridLayout);
                  comp.setSize(0, 5);
              
                  /********************************************************************
                   * Add the text of the clause, preceded by appropriate up/down
                   * arrows for a node that comes from an AND-SPLIT. Combine it
                   * with the next node if its onSameLineAsNext field is true
                   * (which implies it and the next node are NEW nodes.
                   ********************************************************************/
                  comp = new Composite(composite, SWT.NONE);
                  gridLayout = new GridLayout(3, false);
                  comp.setLayout(gridLayout);
                  // Add arrow buttons if necessary
// UP-DOWN ARROWS REMOVED
//                  if ((state.chosenSplit == -1) && (state.andSplitBegin <= i)
//                          && (i <= state.andSplitEnd)) {
//                      Button arrowButton = new Button(comp, SWT.ARROW | SWT.UP);
//                      arrowButton
//                              .addSelectionListener(new ArrowSelectionListener(i,
//                                      SWT.UP, this));
//                      gridData = new GridData();
//                      gridData.verticalAlignment = SWT.TOP;
//                      arrowButton.setLayoutData(gridData);
//                      if (i == state.andSplitBegin) {
//                          arrowButton.setEnabled(false);
//                      }
//                      arrowButton = new Button(comp, SWT.ARROW | SWT.DOWN);
//                      arrowButton
//                              .addSelectionListener(new ArrowSelectionListener(i,
//                                      SWT.DOWN, this));
//              
//                      gridData = new GridData();
//                      gridData.verticalAlignment = SWT.TOP;
//                      arrowButton.setLayoutData(gridData);
//                      if (i == state.andSplitEnd) {
//                          arrowButton.setEnabled(false);
//                      }
//                  }
              
                  assumeLabel = new Label(comp, SWT.BORDER); // SWT.NONE);
                  String text = stringArrayToString(nodeRepVector.elementAt(i)
                          .primedNodeText());
                  // Combine this with following NEW nodes if necessary
                  while (nodeRepVector.elementAt(i).onSameLineAsNext) {
                      i++;
                      text = text
                              + ", "
                              + stringArrayToString(nodeRepVector.elementAt(i).nodeText);
              
                  }
                  assumeLabel.setText(text);
                  // Set the font to be the editors main text font.
                  assumeLabel.setFont(JFaceResources.getFontRegistry().get(
                          JFaceResources.TEXT_FONT));
                  gridData = new GridData();
                  // I have no idea why (undoubtedly a feature that no one has
                  // ever bothered to document), but the following statement did
                  // not have any effect before I added the new composite between
                  // the
                  // button and it. Now it can be used to add positive or negative
                  // space
                  // to the left of the label.
                  gridData.horizontalIndent = 0;
                  gridData.verticalAlignment = SWT.TOP;
                  gridData.horizontalAlignment = SWT.LEFT;
                  assumeLabel.setLayoutData(gridData);
              } else {
                  // This is an OR_DECOMP node.
                  // Add a P button and a P
                  //
                  Button goalButton = new Button(composite, SWT.PUSH);
                  setupActionButton(goalButton, aRep, "P");
                  gridData = new GridData();
                  gridData.horizontalIndent = 15;
                  goalButton.setLayoutData(gridData);
              
                  goalButton.setFont(JFaceResources.getFontRegistry().get(
                          JFaceResources.HEADER_FONT));
              
                  // Add a spacer between the button and the cases
                  comp = new Composite(composite, SWT.NONE);
                  gridLayout = new GridLayout(1, false);
                  comp.setLayout(gridLayout);
              
                  // inner is the composite that contains the CASEs
                  Composite inner = new Composite(composite, SWT.NONE);
                  gridLayout = new GridLayout(2, false);
                  inner.setLayout(gridLayout);
              
                  for (int j = 0; j < aRep.children.size(); j++) {
                      assumeLabel = new Label(inner, SWT.NONE);
                      assumeLabel.setText("CASE");
                      assumeLabel.setFont(JFaceResources.getFontRegistry().get(
                              JFaceResources.TEXT_FONT));
                      Composite caseComp = new Composite(inner, SWT.BORDER); // SWT.NONE)
                                                                             // ;
                      gridLayout = new GridLayout(3, false);
                      caseComp.setLayout(gridLayout);
                      addCaseToComposite(aRep.children.elementAt(j), caseComp);
                      gridData = new GridData();
                      gridData.verticalAlignment = SWT.TOP;
                      caseComp.setLayoutData(gridData);
              
                  }
              }
         } // end if (this should be displayed)
        }
    }
    
    /**
     * This returns true iff we should display a context assumption 
     * rep = state.assumeReps(i).  It equals:
     *
     *   \/ i = chosenSplit
     *   \/ rep.isCreated = true
     *   \/ /\ state.chosenSplit =  -1
     *      /\ 
     *      /\ showContextValue = true
     *      
     * Note that any of the first three disjunctions can be true when 
     * showContextValue is false because it was set to false after 
     * a context assumption was decomposed.
     * @param rep
     * @param i
     * @return
     */
    boolean displayContextAssump(NodeRepresentation rep, int i) {
        return   //  (i == state.chosenSplit) ||
                   rep.isCreated
// UP-DOWN ARROWS REMOVED
//                || (    (state.andSplitBegin <= i)
//                     && (i <= state.andSplitEnd) )
                || (    (! state.splitChosen())
//                     && (state.andSplitBegin == -1)
                     && showContextValue ) ;
    }
    
    /**
     * This returns true iff we should display an assumption 
     * rep = state.assumeReps(i) from the selected step.  Unlike for
     * context assumptions, we display not only an assumption that
     * is now decomposable, but also one that would be decomposable
     * if an OR-decomposition had not already been chosen.  It equals:
     * 
     *   \/ rep.isCreated
     *   \/ rep.nodeType = OR_DECOMP
     *   \/ rep.nodeType = EXISTS_TYPE
     *   \/ /\ rep.nodeType = AND_TYPE
     *      /\ rep.nodeSubtype != OTHER_TYPE
     *  
     * @param rep
     * @param i
     * @return
     */
    boolean displayNonContextAssump(NodeRepresentation rep, int i) {
        return    rep.isCreated
               || (rep.nodeType == NodeRepresentation.OR_DECOMP)
               || (rep.nodeType == NodeRepresentation.EXISTS_TYPE)
               || (   (rep.nodeType == NodeRepresentation.AND_TYPE)
                    && (rep.nodeSubtype != NodeRepresentation.OTHER_TYPE)  ) ;
    }
    /**
     * This method assumes that `composite' is a composite with a gridlayout
     * having 3 columns. It populates it with the buttons and stuff for an
     * assumptions list to go in the Decompose Proof window. It is called to
     * produce the contents of a CASE decomposition in the window. It is called
     * by addAssumptionsToComposite and by itself.
     * 
     * @param nodeRepVector
     * @param composite
     */
    void addCaseToComposite(Vector<NodeRepresentation> nodeRepVector,
            Composite composite) {
        Composite comp;
        GridData gridData;
        GridLayout gridLayout;
        Label assumeLabel;

        for (int i = 0; i < nodeRepVector.size(); i++) {
            NodeRepresentation aRep = nodeRepVector.elementAt(i);

            if ((aRep.nodeType == NodeRepresentation.NEW_NODE)
                    || (aRep.nodeType == NodeRepresentation.OTHER_NODE)
                    || ((aRep.nodeType == NodeRepresentation.EXPR_NODE)
                            && (aRep.nodeSubtype != NodeRepresentation.OR_TYPE)
                            && (aRep.nodeSubtype != NodeRepresentation.EXISTS_TYPE) && (aRep.nodeSubtype != NodeRepresentation.SQSUB_TYPE))) {
                /**
                 * For a CASE decomposition, these nodes are not split. We
                 * therefore put the text of the the assumption all the way on
                 * the left, filling its line.
                 */

                // For a New node, combine it with following NEW nodes if
                // necessary.
                String text = stringArrayToString(nodeRepVector.elementAt(i)
                        .primedNodeText());
                while (nodeRepVector.elementAt(i).onSameLineAsNext) {
                    i++;
                    text = text
                            + ", "
                            + stringArrayToString(nodeRepVector.elementAt(i)
                                    .primedNodeText());
                }
                assumeLabel = new Label(composite, SWT.NONE);
                assumeLabel.setText(text);
                assumeLabel.setFont(JFaceResources.getFontRegistry().get(
                        JFaceResources.TEXT_FONT));
                gridData = new GridData();
                gridData.horizontalSpan = 3;
                assumeLabel.setLayoutData(gridData);
            } else if (aRep.nodeType != NodeRepresentation.OR_DECOMP) {
                // This is an ordinary assumption (an Expression or NEW node).
                /*************************************************************
                 * Add the button or blank area to the first column.
                 *************************************************************/
                String labelText = null;
                // The null test was originally added because created NEW nodes
                // have null
                // semanticNode fields. However, NEW nodes are no longer
                // processed
                // by this code. However, it seems harmless to keep it and I may
                // have forgotten some case in which a NodeRepresentation with a
                // null semanticNode field is created.
                if ((aRep.semanticNode != null)
                        && (aRep.semanticNode.getKind() == ASTConstants.OpApplKind)) {
                    switch (aRep.nodeSubtype) {
                    case NodeRepresentation.AND_TYPE:
                        labelText = null;
                        break;
                    case NodeRepresentation.OR_TYPE:
                    case NodeRepresentation.SQSUB_TYPE:
                        labelText = "\\/";
                        break;
                    case NodeRepresentation.EXISTS_TYPE:
                        labelText = "\\E";
                        break;
                    default:
                        labelText = null;
                    }
                }
                if (labelText != null) {
                    /*************************************************************
                     * Add a button
                     *************************************************************/
                    Button button = new Button(composite, SWT.PUSH);
                    setupActionButton(button, nodeRepVector.elementAt(i),
                            labelText);
                    if ((aRep.nodeSubtype == NodeRepresentation.AND_TYPE)
                            || (aRep.nodeSubtype == NodeRepresentation.FORALL_TYPE)) {
                        button.setEnabled(false);
                    }
                } else {
                    /*************************************************************
                     * Add a blank area.
                     *************************************************************/
                    comp = new Composite(composite, SWT.NONE);
                    gridLayout = new GridLayout(1, false);
                    comp.setLayout(gridLayout);
                    assumeLabel = new Label(comp, SWT.NONE);
                    assumeLabel.setText("  ");
                    gridData = new GridData();
                    gridData.horizontalIndent = 25;
                    comp.setLayoutData(gridData);
                }

                // Add a spacer between the button and the formula
                comp = new Composite(composite, SWT.NONE);
                gridLayout = new GridLayout(1, false);
                comp.setLayout(gridLayout);
                comp.setSize(0, 5);

                /********************************************************************
                 * Add the text of the clause, preceded by appropriate up/down
                 * arrows for a node that comes from an AND-SPLIT.
                 ********************************************************************/
                comp = new Composite(composite, SWT.NONE);
                gridLayout = new GridLayout(3, false);
                comp.setLayout(gridLayout);
             // UP-DOWN ARROWS REMOVED
                // Add arrow buttons if necessary
//                if ((state.chosenSplit == -1) && (state.andSplitBegin <= i)
//                        && (i <= state.andSplitEnd)) {
//                    Button arrowButton = new Button(comp, SWT.ARROW | SWT.UP);
//                    arrowButton
//                            .addSelectionListener(new ArrowSelectionListener(i,
//                                    SWT.UP, this));
//                    gridData = new GridData();
//                    gridData.verticalAlignment = SWT.TOP;
//                    arrowButton.setLayoutData(gridData);
//                    if (i == state.andSplitBegin) {
//                        arrowButton.setEnabled(false);
//                    }
//                    arrowButton = new Button(comp, SWT.ARROW | SWT.DOWN);
//                    arrowButton
//                            .addSelectionListener(new ArrowSelectionListener(i,
//                                    SWT.DOWN, this));
//
//                    gridData = new GridData();
//                    gridData.verticalAlignment = SWT.TOP;
//                    arrowButton.setLayoutData(gridData);
//                    if (i == state.andSplitEnd) {
//                        arrowButton.setEnabled(false);
//                    }
//                }

                assumeLabel = new Label(comp, SWT.NONE);
                String text = stringArrayToString(nodeRepVector.elementAt(i)
                        .primedNodeText());
                assumeLabel.setText(text);
                // Set the font to be the editors main text font.
                assumeLabel.setFont(JFaceResources.getFontRegistry().get(
                        JFaceResources.TEXT_FONT));
                gridData = new GridData();
                // I don't think the following setting of the gridData fields
                // has any effect, but it doesn't seem to hurt.
                gridData.horizontalIndent = 0;
                gridData.verticalAlignment = SWT.TOP;
                gridData.horizontalAlignment = SWT.LEFT;
                assumeLabel.setLayoutData(gridData);

            } else {
                // This is an OR_DECOMP node.
                {
                    // Add a blank label
                    assumeLabel = new Label(composite, SWT.NONE);
                    assumeLabel.setText("  ");
                    comp = new Composite(composite, SWT.NONE);
                    gridLayout = new GridLayout(1, false);
                    comp.setLayout(gridLayout);
                }

                // Add a spacer between the button and the cases
                comp = new Composite(composite, SWT.NONE);
                gridLayout = new GridLayout(1, false);
                comp.setLayout(gridLayout);

                // inner is the composite that contains the CASEs
                Composite inner = new Composite(composite, SWT.NONE);
                // The following commands were an effort to remove
                // excess height above the Composite inner. They failed.
                // ((GridLayout) composite.getLayout()).marginHeight = 0;
                // ((GridLayout) composite.getLayout()).marginTop = 0;
                gridLayout = new GridLayout(2, false);
                // The following commands tried to remove excess vertical
                // space above the Composite inner. They failed.
                // gridLayout.marginHeight = 0;
                // gridLayout.marginTop = 0;
                inner.setLayout(gridLayout);

                for (int j = 0; j < aRep.children.size(); j++) {
                    assumeLabel = new Label(inner, SWT.NONE);
                    assumeLabel.setText("CASE");
                    assumeLabel.setFont(JFaceResources.getFontRegistry().get(
                            JFaceResources.TEXT_FONT));
                    Composite caseComp = new Composite(inner, SWT.BORDER); // SWT.NONE)
                                                                           // ;
                    gridLayout = new GridLayout(3, false);
                    caseComp.setLayout(gridLayout);
                    addCaseToComposite(aRep.children.elementAt(j), caseComp);
                    gridData = new GridData();
                    gridData.verticalAlignment = SWT.TOP;
                    caseComp.setLayoutData(gridData);
                }
            }
        }
    }

    /***************************************************************************
     * The action-button handlers
     ****************************************************************************/
    /**
     * The /\ action, both for a goal (which generates the proof) and for an
     * assumption (which splits the assumption).  This action will only be
     * enabled if the conjunction contains within it, or within one of its
     * conjuncts, a \/ or \E formula.
     * 
     * Note that nodeRep must be either the goal or else a top-level assumption
     * of state.assumeReps.
     * 
     * @param nodeRep
     */
    void andAction(NodeRepresentation nodeRep) {
        if (nodeRep.getParentVector() == null) {
            /**
             * This is a "prove by AND-split" operation.
             */
            makeProof(nodeRep, true, false);
        } else {
            /**
             * This is an AND-SPLIT of an assumption, so nodeRep equals
             * state.assumeReps(i) for some i and parentNode = null.
             * We set idx to i, and we set decomp to the Decomposition
             * object.
             * 
             */
            int idx = nodeRep.getParentIndex();
            Decomposition decomp = nodeRep.decomposition;

            // Modify state.hasChanged, assumeHasChanged, and
            // state.goalDefinitions.
            state.hasChanged = false; // Changed from true to false by LL on 23
                                      // Aug 2014. See
                                      // comments on hasChanged's declaration.
            // assumeHasChanged = true;
            if (decomp.definedOp != null) {
                // Modified by LL on 4 Feb 2013 to change
                // state.assumpDefinitions
                // instead of state.goalDefinitions to fix a bug. But I'm not
                // sure that this is always the correct thing to do.
                // state.goalDefinitions.add(decomp.definedOp);
                state.assumpDefinitions.add(decomp.definedOp);
            }

            // Remove this assumption and insert the split nodes in its place.
            // Set newSemanticNodes to the vector of new assumptions. However,
            // the call to decompositionChildToNodeRep calls
            // decompSubstituteInNodeText,
            // which requires nodeRep to still be in state.assumeReps.
            // Therefore, we
            // accumulate the NodeRepresentation objects for the children and
            // replace nodeRep afterwards.
            Vector<SemanticNode> addedAssumps = decomp.children;
            Vector<NodeRepresentation> addedToAssumeReps = new Vector<NodeRepresentation>();
            for (int i = 0; i < addedAssumps.size(); i++) {
                // Call decompositionChildToNodeRep to construct the child's
                // NodeRepresentation.
                NodeRepresentation rep = decompositionChildToNodeRep(nodeRep,
                        i, this.state.assumeReps, null);
                rep.initialPosition = nodeRep.initialPosition ;
                rep.isCreated = false;  // changed from true by LL on 8 Oct 2014
                addedToAssumeReps.add(rep);
            }
            this.state.assumeReps.remove(idx);
            for (int i = 0; i < addedToAssumeReps.size(); i++) {
                this.state.assumeReps.add(idx + i,
                        addedToAssumeReps.elementAt(i));
            }
//         // UP-DOWN ARROWS REMOVED
//            // Update state.andSplitBegin & state.andSplitEnd. Recall the
//            // precondition.
//            if (state.andSplitBegin == -1) {
//                state.andSplitBegin = idx;
//                state.andSplitEnd = idx + addedAssumps.size() - 1;
//            } else {
//                state.andSplitEnd = state.andSplitEnd + addedAssumps.size() - 1;
//            }
            
            // Update state.numberOfContextAssumptions
            if (idx < state.numberOfContextAssumptions) {
                state.numberOfContextAssumptions = 
                        state.numberOfContextAssumptions + (addedAssumps.size()-1) ;
            }
            if (idx < state.firstAddedAssumption) {
                state.firstAddedAssumption = state.firstAddedAssumption + (addedAssumps.size()-1) ;
            }
            raiseWindow();
        }
    }

    /**
     * Execute a \A split of the goal.
     * 
     * @param nodeRep
     */
    void forAllAction(NodeRepresentation nodeRep) {
        Decomposition decomp = nodeRep.decomposition;
        state.hasChanged = true;
        if (decomp.definedOp != null) {
            state.assumpDefinitions.add(decomp.definedOp);
        }

        QuantifierDecomposition qdc = decomposeQuantifier(nodeRep, true);
        this.state.goalRep = qdc.body;
        // I think that, once we start decomposing things, goal
        // may be used in calling primingNeedsParens
        // this.goal = qdc.body.semanticNode ;

        int newIdx = newAssumeRepsIndex(-1, nodeRep.initialPosition) ;
        for (int i = 0; i < qdc.news.size(); i++) {
            this.state.assumeReps.add(newIdx+i, qdc.news.elementAt(i));
            // this.assumes.add(qdc.news.elementAt(i).semanticNode) ;
        }
        raiseWindow();
    }

    /**
     * Executes an \E split of an assumption. If this is a top-level assumption,
     * then the NEW variables may have to be changed to avoid a name clash with
     * NEW variables or other bound variables of later assumptions or of the
     * goal.
     * 
     * Also, for a top-level assumption , if an AND-split has been performed,
     * then this has to increment state.andSplitEnd because it adds an
     * assumption to the AND-split region.
     * 
     * @param nodeRep
     */
    void existsAction(NodeRepresentation nodeRep) {
        // Set decomp to nodeRep's decomposition and idx
        // and parentVec so that nodeRep = parentVec.elementAt(idx).

        int idx = nodeRep.getParentIndex();
        Vector<NodeRepresentation> parentVec = nodeRep.getParentVector();

        Decomposition decomp = nodeRep.decomposition;
        state.hasChanged = true;
        if (decomp.definedOp != null) {
            if (parentVec == state.assumeReps) {
                state.assumpDefinitions.add(decomp.definedOp);
            } else {
                state.goalDefinitions.add(decomp.definedOp);
            }
        }

        // Set state.needsStepNumber if necessary. (See that field's
        // documentation.)
        //
        // Bug discovered by LL 19 Aug 2014. The spec of isCreated indicates
        // that nodeRep.isCreated is true if this exists was created by an
        // AND-split on an assumption, in which case the documentation of
        // state.needsStepNumber implies that state.needsStepNumber should be
        // set true.
        //
        // This bug was apparently fixed in the new version.
        //
        if (!nodeRep.isCreated && this.hasAssumes) {
            state.needsStepNumber = true;
        }

        QuantifierDecomposition qdc = decomposeQuantifier(nodeRep, false);

        // This added by LL on 11 Feb 2013
        qdc.body.isCreated = true;
        
        qdc.body.fromExists = true ;

        parentVec.remove(idx);

// UP-DOWN ARROWS REMOVED
        // If this is a top-level assumption and an AND-split has been
        // performed, then increment state.andSplitEnd
//        if ((parentVec == state.assumeReps) && (state.andSplitBegin != -1)) {
//            state.andSplitEnd = state.andSplitEnd + qdc.news.size();
//        }

        // If this is a top-level context assumption, then
        // decrement state.numberOfContextAssumptions, and set idx to the appropriate
        // place to put the new assumptions
        if (parentVec == state.assumeReps) {
            int newIdx =  newAssumeRepsIndex(idx, nodeRep.initialPosition) ;            
            if (idx < state.numberOfContextAssumptions) {
               state.numberOfContextAssumptions = state.numberOfContextAssumptions-1  ;
            }

            idx = newIdx ;
        }
        for (int i = 0; i < qdc.news.size(); i++) {
            parentVec.add(idx + i, qdc.news.elementAt(i));
            // parentVec.add(idx + i, qdc.news.elementAt(i).semanticNode) ;
        }
        parentVec.add(idx + qdc.news.size(), qdc.body);
        // parentVec.add(idx + qdc.news.size(), qdc.body.semanticNode) ;
        raiseWindow();
    }

    /**
     * Execute an IMPLIES split.
     * 
     * @param nodeRep
     */
    void impliesAction(NodeRepresentation nodeRep) {
        Decomposition decomp = nodeRep.decomposition;
        state.hasChanged = true;
        if (decomp.definedOp != null) {
            state.assumpDefinitions.add(decomp.definedOp);
        }

        // If this is within the subexpression-name expansion of a definition,
        // set NodeTextRep to the NodeTextRep that is the name of the formula
        // represented by nodeRep.
        NodeTextRep newNodeText = null;
        if ((decomp.definedOp != null) && (subexpressionButton.getSelection())) {
            newNodeText = decomp.definedOpRep;
        } else if (nodeRep.isSubexpressionName) {
            newNodeText = new NodeTextRep(nodeRep.nodeText, nodeRep.mapping);
        }

        NodeRepresentation nrep = decompositionChildToNodeRep(nodeRep, 0,
                this.state.assumeReps, nodeRep.parentNode);

        nrep.isCreated = true;
        nrep.isPrimed = nrep.isPrimed || decomp.primed;
        int newIdx = newAssumeRepsIndex(-1, nodeRep.initialPosition) ;
        this.state.assumeReps.add(newIdx, nrep);
        nrep = decompositionChildToNodeRep(nodeRep, 1,
                nodeRep.getParentVector(), nodeRep.parentNode);
        nrep.isCreated = true;
        this.state.goalRep = nrep;

        raiseWindow();
    }

    /**
     * Perform an or-split action. This turns nodeRep to an OR_DECOMP type node.
     * 
     * @param nodeRep
     */
    void orAction(NodeRepresentation nodeRep) {
        
        // Set decomp to nodeRep's decomposition and idx
        // and parentVec so that nodeRep = parentVec.elementAt(idx).
        // to the value such that
        int idx = nodeRep.getParentIndex();
        Vector<NodeRepresentation> parentVec = nodeRep.getParentVector();
        // If this is an OR-split of a top-level assumption, then
        // set state.chosenSplit to idx (NO LONGER NEEDED) and
        // move the node to the end of assumeReps
        if (parentVec == this.state.assumeReps) {
           int oldIdx = nodeRep.getParentIndex() ;
           if (oldIdx < state.numberOfContextAssumptions) {
               state.numberOfContextAssumptions-- ;
           }
           if (oldIdx < state.firstAddedAssumption) {
               state.firstAddedAssumption-- ;
           }
           state.assumeReps.remove(oldIdx) ;
           // this.state.chosenSplit = state.assumeReps.size() ;
           state.assumeReps.add(nodeRep) ;
        }

        Decomposition decomp = nodeRep.decomposition;
        state.hasChanged = true;
        if (decomp.definedOp != null) {
            state.goalDefinitions.add(decomp.definedOp);
        }

        nodeRep.nodeType = NodeRepresentation.OR_DECOMP;
        nodeRep.nodeSubtype = NodeRepresentation.OTHER_TYPE;
        nodeRep.children = new Vector<Vector<NodeRepresentation>>();
        nodeRep.initialPosition = Integer.MAX_VALUE ;

        for (int i = 0; i < decomp.children.size(); i++) {
            Vector<NodeRepresentation> repVec = new Vector<NodeRepresentation>();
            nodeRep.children.add(repVec);
            NodeRepresentation rep = decompositionChildToNodeRep(nodeRep, i,
                    repVec, nodeRep);
            repVec.add(rep);
        }
        raiseWindow();
    }

    /**
     * Perform the or-split for a [N]_v formula.
     * 
     * @param nodeRep
     */
    void sqsubAction(NodeRepresentation nodeRep) {
        // Set decomp to nodeRep's decomposition and idx
        // and parentVec so that nodeRep = parentVec.elementAt(idx).
        // to the value such that
        int idx = nodeRep.getParentIndex();
        Vector<NodeRepresentation> parentVec = nodeRep.getParentVector();
        // If this is an OR-split of a top-level assumption, then
        // set state.chosenSplit to idx. (NO LONGER NEEDED)
        // and move the node to the end of state.assumeReps.
        if (parentVec == this.state.assumeReps) {
         
            
            nodeRep.initialPosition = Integer.MAX_VALUE;
            // this.state.chosenSplit = idx;
            int oldIdx = nodeRep.getParentIndex() ;
            if (oldIdx < state.numberOfContextAssumptions) {
                state.numberOfContextAssumptions-- ;
            }
            if (oldIdx < state.firstAddedAssumption) {
                state.firstAddedAssumption-- ;
            }
            state.assumeReps.remove(oldIdx) ;
            state.assumeReps.add(nodeRep) ;
        }

        Decomposition decomp = nodeRep.decomposition;
        state.hasChanged = true;
        if (decomp.definedOp != null) {
            state.goalDefinitions.add(decomp.definedOp);
        }

        nodeRep.nodeType = NodeRepresentation.OR_DECOMP;
        nodeRep.nodeSubtype = NodeRepresentation.OTHER_TYPE;
        nodeRep.children = new Vector<Vector<NodeRepresentation>>();

        for (int i = 0; i < decomp.children.size(); i++) {
            Vector<NodeRepresentation> repVec = new Vector<NodeRepresentation>();
            nodeRep.children.add(repVec);
            NodeRepresentation rep = decompositionChildToNodeRep(nodeRep, i,
                    repVec, nodeRep);
            if (i == 1) {
                // Have to fix the UNCHANGED node. We prepend the "UNCHANGED"
                // to nodeText and set it to be a node of type OTHER, which
                // means it
                // will never be split.
                rep.nodeType = NodeRepresentation.OTHER_NODE;
                rep.nodeSubtype = NodeRepresentation.OTHER_TYPE;
                rep.nodeText = prependToStringArray(rep.nodeText, "UNCHANGED ");

            }
            repVec.add(rep);
        }
        raiseWindow();
    }

    /**
     * Create the proof for a case-split.
     * 
     * @param nodeRep
     */
    void caseAction(NodeRepresentation nodeRep) {
        makeProof(nodeRep, false, false);
    }

    /**
     * makeProof(nodeRep, isAndProof, sufficesOnly) creates the proof.  
     * It is called three ways:
     * 
     *  - isAndProof = true /\ sufficesOnly = false
     *      The user has selected /\ decomposition
     *      
     *  - isAndProof = false /\ sufficesOnly = true
     *      The user has selected the top "P" button, which
     *      is enabled if only \E decompositions and/or =>
     *      decompositions have been chosen.
     *      
     *  - isAndProof =  sufficesOnly = false
     *      The user has chosen a case split.
     *      
     * Here is how (I think) a proof should be constructed. 
     *  
     *  userProof = a BY proof of the decomposed step, with BY and DEF clauses
     *              userProof.BY and userProof.DEF.  (Obvious representations if
     *              either or both of those clauses are empty--e.g. OBVIOUS if
     *              both are empty.)
     *              
     *  createdAssumps = Sequence of all new assumptions added by decomposition,
     *                   except for assumption on which case split is being done (if any)
     *                   
     *  caseSplitAssump = Disjunction on which case split being done, or null if none.
     *   
     *  createdAssumps.defs = 
     *    Sequence of names of operators expanded to obtain assumptions
     *    in createdAssumps, including assumptions that were originally
     *    part of the goal.
     * 
     *  createdAssumps.stepNames =
     *    Sequence of names of all named steps from which assumptions
     *    in createdAssumps were obtained, excluding ones from assumptions
     *    that were originally part of the goal (but including the decomposed
     *    step's name for assumptions coming from its assumptions).
     * 
     *  caseSplitAssump.defs (implemented by the case-split nodes fromDefs) = 
     *    Sequence of names of operators expanded to obtain the top-level caseSplitAssump
     * 
     *  caseSplitDefs (implemented as state.goalDefinitions) =
     *     Sequence of names of operators expanded to obtain all the case splits from
     *     caseSplitAssump.
     *     
     *  caseSplitAssump.stepName =
     *    Sequence containing name of step from which 
     *    caseSplitAssump came, or empty seq if either: 
     *        - caseSplitAssump = null 
     *        - that step is unnamed
     *        - the case split formula came from the original goal.
     *    
     *  decompGoal = The goal created by the decomposition.
     *  
     * Here are the proofs created for different cases (assuming a level <1> statement):
     *    
     * CASE 1: \/ sufficesOnly = true         \* CASE 1a
     *         \/ /\ isAndProof = true        \* CASE 1b
     *            /\ "Use SUFFICES" chosen ->
     * 
     *   <2> SUFFICES ASSUME createdAssumps
     *                PROVE  decompGoal
     *      BY createdAssumps.stepNames DEF createdAssumps.defs
     *      [NOTE: IF createdAssumps is empty, then the SUFFICES
     *             step is eliminated.  This can 
     *             be the case only if sufficesOnly = false.]
     *   IF isAndProof = true 
     *      THEN ... 
     *           <2>i. conjunct i of decompGoal
     *             BY userProof
     *           ...
     * 
     *   <2>n. QED
     *     IF sufficesOnly = true
     *       THEN userProof
     *       ELSE BY <2>1, ... , <2>n-1, createdAssumps.stepNames 
     *          \o IF there is no SUFFICES 
     *               THEN DEF decompGoal.fromDefs
     *           \o IF is a defined op THEN <<the operator name>>
     *                                 ELSE << >>
     * 
     * 
     * CASE 2: /\ isAndProof = true
     *         /\ "Use SUFFICES" not chosen ->
     * 
     *   ...
     *   <2>i. ASSUME createdAssumps
     *         PROVE  conjunct i of decompGoal
     *     BY userProof.BY, <2>i DEF userProof.DEF
     *   ...
     * 
     *   <2>n. QED
     *     BY <2>1, ... , <2>n-1, createdAssumps.stepNames
     *     DEF createdAssump.defs \o
     *           IF decompGoal is a defined op THEN <<the operator name>>
     *                                         ELSE << >>
     *  
     * CASE 3: /\ isAndProof = sufficesOnly = FALSE
     *         /\ "Use SUFFICES" chosen  -> 
     * 
     *   <2> SUFFICES ASSUME createdAssumps \o
     *                       IF case-split came from original goal or was in the body of a \E
     *                         THEN , top-level caseSplitAssump formula (possibly an operator name)
     *                PROVE  decompGoal
     *      BY createdAssumps.stepNames 
     *      DEF createdAssumps.defs \o IF case-split came from original goal
     *                                   THEN , caseSplitAssump.defs
     *      NOTE: IF the ASSUMES is empty, then SUFFICES step is eliminated and 
     *            the BY and DEF clauses are made part of the QED step's proof.
     *            (However, in that case BY clause should be empty.)
     *   ...
     *   <2>i. ASSUME case i of caseSplitAssump
     *         PROVE  decompGoal
     *              [This ASSUME/PROVE should be replaced by a CASE
     *               statement if "Use CASE" chosen and all of the ASSUME
     *               clauses are formulas.]
     *           BY userProof.BY, <2>i DEF userProof.DEF
     *   ...
     *   <2>n. QED
     *     BY <2>1, ... , <2>n-1, caseSplitAssump.stepNames 
     *     DEF caseSplitDefs \o  IF case-split not from original goal 
     *                              and not from the body of a \E
     *                             THEN caseSplitAssump.defs
     * 
     * CASE 4: /\ isAndProof = sufficesOnly = FALSE
     *         /\ "Use SUFFICES" not chosen   ->
     * 
     *   ...
     *   <2>i. ASSUME case i of caseSplitAssump
     *         PROVE  decompGoal
     *               [This ASSUME/PROVE should be replaced by a CASE
     *                statement if "Use CASE" chosen and all of the ASSUME
     *                clauses are formulas.]
     *           BY userProof.BY, <2>i,  DEF userProof.DEF
     *   ...
     *   <2>n. QED
     *     BY <2>1, ... , <2>n-1, createdAssumps.stepNames, caseSplitAssump.stepName 
     *     DEF createdAssumps.defs, caseSplitAssump.defs, caseSplitDefs
     * 
     * @param nodeRep
     * @param isAndProof
     * @param sufficesOnly
     */
    void makeProof(NodeRepresentation nodeRep, boolean isAndProof,
            boolean sufficesOnly) {

        /**
         * Set proofIndent to the amount to indent both the new proof and the
         * proofs of its steps. We may want to do something clever about
         * inferring what the user wants from the indentation he used if the
         * step has a leaf proof. However, this can be complicated because some
         * people put the proof on the last line of the obligation. So for now,
         * we just set it to PROOF_INDENT.
         * 
         * We also set proofIndentString to a string of that number of spaces.
         */
        // StringSet aaTestSet = new StringSet();
        // addDeclaredSymbols(aaTestSet, state.goalRep);

        // Compute createdAssumps, createdAssumps.defs and createdAssump.stepNames, 
        // defined in the spec above.  Also, set createdAssumpsNodeTexts to
        // the vector of the String arrays representing createdAssumps.
        
        Vector<NodeRepresentation> createdAssumps = new Vector<NodeRepresentation>();
        StringSet createdAssumpsDefs = new StringSet();
        StringSet createdAssumpStepNames = new StringSet();
        for (int i=state.firstAddedAssumption; i < state.assumeReps.size() ; i++) {
           NodeRepresentation rep = state.assumeReps.elementAt(i);
           if (rep.nodeType != NodeRepresentation.OR_DECOMP) {
               createdAssumps.add(rep) ;
               if ((rep.contextStepName != null) && ! rep.fromGoal) {
                   createdAssumpStepNames.add(rep.contextStepName);           
               }
               createdAssumpsDefs.addAll(rep.fromDefs) ;
           }  
           else {
               if (rep != nodeRep) {
                   MessageDialog.openError(UIHelper.getShellProvider().getShell(),
                           "Decompose Proof Command",
                           "Something unexpected is going on at "
                                   + "line 3247 of NewDecomposeProofHandler.");
               }

           }
         }
        
        Vector<String[]> createdAssumpsNodeTexts = new Vector<String[]>() ;
        for (int i =0; i < createdAssumps.size(); i++) {
            createdAssumpsNodeTexts.add(createdAssumps.elementAt(i).nodeText) ;
        }
        
        // Sanity check
        if (sufficesOnly && (createdAssumps.size() == 0)) {
            MessageDialog.openError(UIHelper.getShellProvider().getShell(),
                    "Decompose Proof Command",
                    "Sanity check failed at "
                            + "line 3255 of NewDecomposeProofHandler.");
        }
        
        
        int proofIndent = PROOF_INDENT;
        String proofIndentString = StringHelper.copyString(" ", proofIndent);

        // Set assumptionsText to a string array such that applying 
        // stringArrayToString to it produces the text of the list of 
        // assumptions in createdAssumps.
        String[] assumptionsText = createdAssumptions();
        
        // If createdAssumps contains only formulas (and no NEW assumptions),
        // then set assumptionsAsConjText to a string array such that applying 
        // stringArrayToString to it produces the text of the conjunction of
        // all the assumptions in createdAssumps.  Otherwise, assumptionsAsConjText
        // is set to null.
        
        String[] assumptionsAsConjText = new String[createdAssumps.size()] ;
        
        int k = 0 ;
        while ((assumptionsAsConjText) != null && (k < createdAssumps.size())){
            NodeRepresentation rep = createdAssumps.elementAt(k) ;
            if (rep.nodeType == NodeRepresentation.NEW_NODE){
                assumptionsAsConjText = null ;
            }
            else {
                if (createdAssumps.size() > 1) {
                    assumptionsAsConjText[k] = 
                      stringArrayToString(prependToStringArray(rep.nodeText, "/\\ ")) ;
                }
                else {
                    assumptionsAsConjText[k] = stringArrayToString(rep.nodeText) ;
                }
            }
            k++ ;
        }
            
            
        // If there is a proof, set proofText to its string array
        // representation, with indentation prepended to it, and delete it.
        // Set proofBY and proofDEF to the sets of BY and DEF elements.
        String[] proofText = null;
        StringSet proofBY = null;
        StringSet proofDEF = null ;
        if (this.proof != null) {
            proofText = this.stepRep.subNodeText(this.proof).nodeText;
            proofText = prependToStringArray(proofText, proofIndentString);
            try {
                IRegion proofRegion = EditorUtil.getRegionOf(this.doc,
                        ((SyntaxTreeNode) this.proof.stn).getLocation());
                this.doc.replace(proofRegion.getOffset(),
                        proofRegion.getLength(), "");
            } catch (BadLocationException e) {
                MessageDialog.openError(UIHelper.getShellProvider().getShell(),
                        "Decompose Proof Command",
                        "An error that should not happen has occurred in "
                                + "line 3275 of NewDecomposeProofHandler.");
                e.printStackTrace();
            }
            proofBY = new StringSet();
            proofDEF = new StringSet();
            
            
            // Set proofBY and proofDEF
            // line = current line in proofText, trimmed
            // lineNum = line number of line
            // idx = current index in current line
            String line = "";
            int lineNum = 0;
            int idx = 0;
            boolean notfound = true ;
            // find "BY" 
            while (notfound && lineNum < proofText.length) {
               line = proofText[lineNum].trim();
               if (line.startsWith("BY")) {
                   idx = proofText[lineNum].indexOf("BY") + 2;
                   notfound = false;
               }
               else if (line.equals("")){
                   lineNum++ ;
               }
               else {
                   // Must be an OBVIOUS proof
                   lineNum = Integer.MAX_VALUE ;
               }  
            }
            
            if (!notfound) {
                // Do nothing if there is no BY step.  
                // Otherwise, first set stringBY to comma separated list of BY clauses
                // and set notfound false if there is a DEF 
                String stringBY = "" ;
                boolean defNotfound = true ;
                while (defNotfound && lineNum < proofText.length) {
                    line = proofText[lineNum].substring(idx, proofText[lineNum].length()) ;
                    // If line contains "DEF"
                    //   THEN set defIdx to its index and notfound to false
                    //   ELSE set defIdx to line.length()
                    int defIdx = 0 ;
                    while ((defIdx < line.length()) && defNotfound) {
                       defIdx = line.indexOf("DEF", defIdx) ; 
                       if (defIdx == -1) {
                            defIdx = line.length() ;
                       }
                       else if (   ((defIdx == 0) || 
                                            Character.isWhitespace(line.charAt(defIdx-1)))
                                    && ((defIdx+3 == line.length()) || 
                                            Character.isWhitespace(line.charAt(defIdx+3)))
                              ) {
                          defNotfound = false ;
                         // defIdx = defIdx;
                       }
                       else {
                           defIdx = defIdx+3 ;
                       }
                    }
                    
                    stringBY = stringBY + line.substring(0, defIdx) ; 
                    
                   if (defNotfound) {
                       lineNum ++;
                       idx = 0;
                   }
                   else {
                       idx = idx + defIdx+3 ;
                   }
                }
                
                proofBY.addAll(StringSet.CommaSeparatedListToStringSet(stringBY)) ;
                

                if (!defNotfound) {
                    // A DEF was found, so we have to add everything after it to
                    // proofDEF
                    String stringDEF = "" ;
                    while (lineNum < proofText.length) {
                        line = proofText[lineNum].substring(idx, proofText[lineNum].length()) ;
                        stringDEF = stringDEF + line ;
                        lineNum++ ;
                        idx = 0 ;
                    }
                    proofDEF.addAll(StringSet.CommaSeparatedListToStringSet(stringDEF)) ;  
                }
            }
        }

        
        // Set addStepNumber true iff we need to add the step number to the
        // BY clause of a SUFFICES step or of the QED step.  This should not
        // be needed any more, but it has one use and it seems safest to just
        // let sleeping code lie.
        boolean addStepNumber = (stepNumber != null)
                && this.state.needsStepNumber;

        // Set sufficesStep to the string array of the suffices step,
        // or null if there is none. There is a suffices step iff either
        //  - the user has selected the Use SUFFICES option, and the
        //    decomposition of the goal has created an assumption, or
        //  - sufficesOnly = true
        String[] sufficesStep = null;
        boolean hasSufficesStep = 
                       (useSufficesButton.getSelection() && (createdAssumps.size() != 0))
                    || sufficesOnly ;
        if (hasSufficesStep) {           
            // CASE 1 or CASE 3
            String sufficesProof = null;

//            String[] sufficesAssumeText = new String[0] ;
//            
//            for (int i = 0; i < createdAssumpsNodeTexts.size(); i++) {
//                sufficesAssumeText = concatStringArrays
//                                       (sufficesAssumeText, 
//                                        createdAssumpsNodeTexts.elementAt(i));
//                if (i != createdAssumpsNodeTexts.size() - 1) {
//                    sufficesAssumeText = appendToStringArray(sufficesAssumeText, ",") ;
//                }
//            }
                    
            StringSet sufficesDEF = createdAssumpsDefs.clone();

            if (    (nodeRep != null)
                 && (nodeRep.nodeType == NodeRepresentation.OR_DECOMP) 
                 && (nodeRep.fromGoal || nodeRep.fromExists) ) {
                // CASE 3 with case-split from original goal
                if (createdAssumps.size() != 0) {
                    assumptionsText = appendToStringArray(assumptionsText, ",") ;
                }
                assumptionsText = concatStringArrays(assumptionsText, nodeRep.nodeText);
                
                sufficesDEF.addAll(nodeRep.fromDefs) ;
            }
            
            String[] suffices = prependToStringArray(
                    concatStringArrays(
                            prependToStringArray(assumptionsText, "ASSUME "),
                            prependToStringArray(
                                    this.state.goalRep.primedNodeText(),
                                    "PROVE  ")), proofLevelString
                            + " SUFFICES ");

            // Fhe following is the only use of addStepNumber
            // it should probably be replaced by something else.
            // See comments for declaration of addStepNumber.
            if (state.assumpDefinitions.isEmpty() && !addStepNumber) {
                // No goal definitions were expanded; the proof is obvious.
                if (OBVIOUS_HAS_PROOF) {
                    sufficesProof = "PROOF OBVIOUS";
                } else {
                    sufficesProof = "OBVIOUS";
                }
            } else {
                // Need a BY proof, with a DEF if there are expanded
                // definitions
                sufficesProof = "BY ";
                
                if (!createdAssumpStepNames.isEmpty()) {
                    sufficesProof = sufficesProof + 
                                     createdAssumpStepNames.toCommaSeparatedString() + " ";
                }
                
                if (!sufficesDEF.isEmpty()) {
                    sufficesProof = sufficesProof + "DEF " + sufficesDEF.toCommaSeparatedString();
                }
                
                
//                if (addStepNumber) {
//                    sufficesProof = sufficesProof + this.stepNumber + " ";
//                }
//                if (!state.assumpDefinitions.isEmpty()) {
//                    sufficesProof = sufficesProof + "DEF "
//                            + setOfStringsToList(state.assumpDefinitions);
//                }
            }

            sufficesStep = concatStringArrays(suffices,
                    new String[] { proofIndentString + sufficesProof });
        }

        
        // Set
        // - mainProofSteps to be an array of string arrays for the
        //   steps of the proof other than the SUFFICES and QED steps. ,
        // - numberOfSteps to the number of those steps (which
        //   should equal mainProofSteps.length;
        // - proofDef to be the name of the operator whose definition
        //   is the current goal, if this is an and-split proof.
        //   It is null otherwise.

        String[][] mainProofSteps = null;
        int numberOfSteps = 0;
        
        // For /\ proof whose conjunction comes from
        // a defined operator, proofDef equals that operator.
        // otherwise it equals null ;
        String proofDef = null;

        if (!sufficesOnly) {

            if (isAndProof) {
                /**
                 * This is an and-decomposition proof (CASES 1b and 2)
                 */
                Decomposition decomp = nodeRep.decomposition;
                numberOfSteps = decomp.children.size();
                mainProofSteps = new String[numberOfSteps][];
                proofDef = decomp.definedOp;

                for (int i = 0; i < numberOfSteps; i++) {
                    // Set goalArray to the String array of the goal.
                    NodeRepresentation stepGoalRep = decompositionChildToNodeRep(
                            nodeRep, i, null, null);
                    String[] goalArray = stepGoalRep.primedNodeText();
                    

                    // Set step to step number + the step's obligation.
                    String[] step;

                    // Set isAssumeProve to indicate if this is an ASSUME/PROVE
                    // step, rather than an ordinary assertion.
                    boolean isAssumeProve = false;
                    // If there is no SUFFICES step but the goal decomposition
                    // created new ASSUME clauses, then they must be the ASSUME
                    // of an ASSUME / PROVE
                    if ((sufficesStep == null && createdAssumps.size() != 0)) {
                        step = concatStringArrays(
                                prependToStringArray(assumptionsText, "ASSUME "),
                                prependToStringArray(goalArray, "PROVE  "));
                        isAssumeProve = true;

                    } else {
                        // Just a simple step, no ASSUME/PROVE.
                        step = goalArray;
                    }
                    // Set stepNum to the step number--e.g. "<2>3"
                    String stepNum = proofLevelString + (i + 1);

                    step = prependToStringArray(step, stepNum
                            + STEP_NUMBER_PUNCTUATION + " ");

                    // Add the proof to step, if there is one.
                    if (proofText != null) {
                        String[] newProofText = proofText.clone();
                        if (isAssumeProve) {
                            // Need to add step number to the BY part;
                            addStepNumToProof(stepNum, newProofText);
                        }
                        step = concatStringArrays(step, newProofText);
                    }

                    // Set the i-th conjunctStep to step
                    mainProofSteps[i] = step;
                }
            } else {
                /**
                 * This is a case-split proof.
                 * Note that caseSplitAssumpDefs = nodeRep.fromDefs()
                 * caseSplitDefs = state.goalDefinitions = 
                 *   union of nd.fromDefs() for all descendant nodes 
                 *   (via the child field) nd of nodeRep.
                 * 
                 */
                // Set pfStepVec to a Vector of proof steps.
                Vector<String[]> pfStepVec = new Vector<String[]>();
                for (int i = 0; i < nodeRep.children.size(); i++) {
                    Vector<NodeRepresentation> childVec = nodeRep.children
                            .elementAt(i);
                    String[] assumpArray;
                    if (!hasSufficesStep) {
                        assumpArray = new String[assumptionsText.length];
                        for (int j = 0; j < assumptionsText.length; j++) {
                            assumpArray[j] = assumptionsText[j];
                        }
                    } else {
                        assumpArray = new String[0];
                        assumptionsAsConjText = new String[0] ;
                    }
                    
                    boolean assumpArrayOnlyFormulas = true ;
                    for (int j = 0; j < createdAssumps.size(); j++) {
                        assumpArrayOnlyFormulas = 
                          assumpArrayOnlyFormulas && 
                            (createdAssumps.elementAt(j).nodeType != NodeRepresentation.NEW_NODE) ;
               
                    }
                    addCaseProofs(pfStepVec, childVec, assumpArray,
                            proofText, assumptionsAsConjText);
                }

                // turn pfStepVec into the array mainProofSteps
                mainProofSteps = new String[pfStepVec.size()][];
                for (int i = 0; i < mainProofSteps.length; i++) {
                    mainProofSteps[i] = pfStepVec.elementAt(i);
                }
                numberOfSteps = mainProofSteps.length;
            }
        }
        
        // Set qedStep to the QED step (with its step number and proof).
        String[] qedStep = new String[2];
        qedStep[0] = proofLevelString;
        if (NUMBER_QED_STEP && (numberOfSteps != 0)) {
            qedStep[0] = qedStep[0] + (numberOfSteps + 1)
                    + STEP_NUMBER_PUNCTUATION;
        }
        qedStep[0] = qedStep[0] + " QED";
        
        if (sufficesOnly) {
            // CASE 1a
            if (proofText != null) {
                qedStep[1] = stringArrayToString(proofText) ;
            } 
            else {
                qedStep = new String[] {qedStep[0]} ;
            }

        }
        else {
            // not CASE 1a
            // Set qedBY and qedDEF to the BY and DEF clauses
            StringSet qedBY = new StringSet() ;
            StringSet qedDEF = new StringSet() ;
            
            // Add the names of mainProofSteps to qedBY
            for (int i = 1; i <= numberOfSteps; i++) {
                qedBY.add(proofLevelString + i) ;
            }
            
            if (isAndProof) {
                // CASES 1b and 2
                qedBY.addAll(createdAssumpStepNames) ;
                if (proofDef != null) {
                    qedDEF.add(proofDef) ;
                }
                if (! hasSufficesStep) {
                    qedDEF.addAll(nodeRep.fromDefs) ;
                }
            }
            else {
                // CASES 3 and 4
                if (useSufficesButton.getSelection()) {
                    // CASE 3
                    if (nodeRep.contextStepName != null) {
                        qedBY.add(nodeRep.contextStepName) ;
                    }
                    
                    qedDEF.addAll(state.goalDefinitions) ;
                    
                    if (!hasSufficesStep && nodeRep.fromGoal) {
                        qedDEF.addAll(nodeRep.fromDefs) ;
                    }
                    
                }
                else {
                    // CASE 4
                    qedBY.addAll(createdAssumpStepNames) ;
                    if (nodeRep.contextStepName != null) {
                        qedBY.add(nodeRep.contextStepName) ;
                    }
                    qedDEF.addAll(createdAssumpsDefs) ;
                    qedDEF.addAll(nodeRep.fromDefs) ;
                    qedDEF.addAll(state.goalDefinitions) ;
                }
            }
            
            qedStep[1] = proofIndentString + "BY "
                    + qedBY.toCommaSeparatedString() ;
            if (! qedDEF.isEmpty()) {
                qedStep[1] = qedStep[1] + " DEF " 
                    + qedDEF.toCommaSeparatedString() ;
            }
        }
        
        
        
        
//        /*
//         * The following is much too complicated in the sufficesOnly case. In
//         * that case, hasGoalDefs and hasAssumeDefs will all be set to false, so
//         */
//                
//        qedStep[1] = proofIndentString + "BY "   
//                + ((numberOfSteps > 0) ? (proofLevelString + 1) : "");
//        for (int i = 2; i <= numberOfSteps; i++) {
//            qedStep[1] = qedStep[1] + ", " + proofLevelString + i;
//        }
//        // Add step number if necessary.
//        if ((sufficesStep == null) && state.needsStepNumber
//                && (this.stepNumber != null)) {
//            qedStep[1] = qedStep[1] + ", " + this.stepNumber;
//        }
//
//        boolean hasGoalDefs = (!this.state.assumpDefinitions.isEmpty())
//                && (sufficesStep == null);
//        boolean hasAssumeDefs = !this.state.goalDefinitions.isEmpty();
//
//        String goalAndAssumeDefs = (hasGoalDefs ? setOfStringsToList(this.state.assumpDefinitions)
//                : "")
//                + ((hasGoalDefs && hasAssumeDefs) ? ", " : "")
//                + (hasAssumeDefs ? this.state.goalDefinitions.toCommaSeparatedString()
//                        : "");
//        if (sufficesOnly) {
//            if (this.proof != null) {
//                qedStep = concatStringArrays(new String[] { qedStep[0] },
//                        prependToStringArray(proofText, proofIndentString));
//            } else {
//                qedStep[1] = "";
//            }
//        } else {
//            // Either not a suffices only proof, or proof = null. In
//            // either case, can construct the QED step as if it
//            boolean hasDEF = false;
//            if (hasGoalDefs || hasAssumeDefs) {
//                hasDEF = true;
//                qedStep[1] = qedStep[1] + " DEF " + goalAndAssumeDefs;
//            }
//            if (proofDef != null) {
//                if (hasDEF) {
//                    qedStep[1] = qedStep[1] + ", " + proofDef;
//                } else {
//                    qedStep[1] = qedStep[1] + " DEF " + proofDef;
//                }
//            }
//        }
// Here's where we can stop changing things (I hope) 
        String[] blankLine = new String[] { "" };
        String[] completeProof = new String[0];
        if (sufficesStep != null) {
            if (BLANK_LINE_BETWEEN_STEPS) {
                completeProof = concatStringArrays(sufficesStep, blankLine);
            } else {
                completeProof = sufficesStep;
            }
        }

        if (mainProofSteps != null) {
            completeProof = concatStringArrays(completeProof, mainProofSteps[0]);
            for (int i = 1; i < mainProofSteps.length; i++) {
                if (BLANK_LINE_BETWEEN_STEPS) {
                    completeProof = concatStringArrays(completeProof,
                            concatStringArrays(blankLine, mainProofSteps[i]));
                } else {
                    completeProof = concatStringArrays(completeProof,
                            mainProofSteps[i]);
                }
            }

            if (BLANK_LINE_BETWEEN_STEPS) {
                completeProof = concatStringArrays(completeProof, blankLine);
            }
        }
        completeProof = concatStringArrays(completeProof, qedStep);

        // we indent the proof.
        completeProof = prependToStringArray(
                completeProof,
                StringHelper.copyString(" ", this.step.getLocation()
                        .beginColumn() - 1 + proofIndent));

        // we now add the proof to the module. We put it on the line
        // after the last line of the theorem.
        try {
            int nextLineOffset = doc.getLineInformation(
                    this.step.getTheorem().getLocation().endLine()).getOffset();
            this.doc.replace(nextLineOffset, 0,
                    stringArrayToString(completeProof) + "\n");
        } catch (BadLocationException e) {
            MessageDialog.openError(UIHelper.getShellProvider().getShell(),
                    "Decompose Proof Command",
                    "An error that should not happen has occurred in "
                            + "line 1465 of NewDecomposeProofHandler.");
            e.printStackTrace();
        }

        // We dispose of the window. The disposal listener will do
        // everythingthat's supposed to happen when the window is
        // removed.
        this.windowShell.dispose();
        return;
    }

    /**
     * Adds the proof steps for a CASE decomposition.
     * 
     * @param pfStepVec
     *            The vector to which proof steps should be added.
     * @param childVec
     *            The vector of CASE assumptions' NodeRepresentation objects,
     *            which may include OR_DECOMP nodes.
     * @param assumpArray
     *            The assumptions that must be prepended to each case.
     * @param proofText
     *            The user's proof, or null if none.
     *            
     * @param assumpArrayAsFormula
     *            Non-null iff all the assumptions in assumpArray are formulas,
     *            (so none are NEW declarations), in which case it is assumpArray
     *            written as a single formula (which is a conjunction if assumpArray
     *            has length > 1).
     */
    void addCaseProofs(Vector<String[]> pfStepVec,
            Vector<NodeRepresentation> childVec, String[] assumpArray,
            String[] proofText, String[] assumpArrayAsFormula) {

        // Set newAssumpArray to the concatenation of assumpArray and
        // the NEW assumptions of childVec --- which must be all the elements of
        // childVec except the last.
        // First set newAssumpCount to the length of newAssumpArray. Note that
        // it includes the last element of childVec iff that element is not an
        // OR_DECOMP
        // node.
        int newAssumpCount = assumpArray.length;

        String[] newAssumpArrayAsFormula = assumpArrayAsFormula ;
                if (childVec.elementAt(0).nodeType == NodeRepresentation.NEW_NODE){
                    newAssumpArrayAsFormula = null ;
                }
                else {
                    newAssumpArrayAsFormula = new String[0] ;
                }

        NodeRepresentation lastChildNode = childVec
                .elementAt(childVec.size() - 1);

        // The assumptions to be added to newAssumpArray the elements 0 through
        // lenOfChildAssumps - 1.
        int lenOfChildAssumps = childVec.size();
        if (lastChildNode.nodeType == NodeRepresentation.OR_DECOMP) {
            lenOfChildAssumps--;
        }

        for (int i = 0; i < lenOfChildAssumps; i++) {
            newAssumpCount = newAssumpCount
                    + childVec.elementAt(i).primedNodeText().length;
            
        }
        String[] newAssumpArray = new String[newAssumpCount];
        for (int i = 0; i < assumpArray.length; i++) {
            newAssumpArray[i] = assumpArray[i];
        }
        if (lenOfChildAssumps > 0) {
            if (assumpArray.length > 0) {
                newAssumpArray[assumpArray.length - 1] = newAssumpArray[assumpArray.length - 1]
                        + ",";
            }
            int idx = assumpArray.length;
            for (int i = 0; i < lenOfChildAssumps; i++) {
                String[] assump = childVec.elementAt(i).primedNodeText();
                for (int j = 0; j < assump.length; j++) {
                    newAssumpArray[idx] = assump[j];
                    idx++;
                }
                if (i != lenOfChildAssumps - 1) {
                    newAssumpArray[idx - 1] = newAssumpArray[idx - 1] + ",";
                }
            }
        }

        if (lastChildNode.nodeType == NodeRepresentation.OR_DECOMP) {
            // Need to recurse through the children
            for (int i = 0; i < lastChildNode.children.size(); i++) {
                addCaseProofs(pfStepVec, lastChildNode.children.elementAt(i),
                        newAssumpArray, proofText, newAssumpArrayAsFormula);
            }
        } else {
            // This is a terminal node. Construct the proof step.
            // Set step to the step's obligation.
            String[] step;
            // We use a CASE step if there's just a single new assumption,
            //  assumpArrayAsFormula != false, and "use CASE" is selected.

            if ((assumpArrayAsFormula != null) && useCaseButton.getSelection() && (childVec.size() == 1)) {
                // This is a CASE step.
                if (assumpArrayAsFormula.length == 0) {
                   // There are no assumptions to add.
                   step = prependToStringArray(lastChildNode.primedNodeText(),
                           "CASE ");
                } 
                else {
                  // 
                    step = prependToStringArray(
                            concatStringArrays(assumpArrayAsFormula, 
                                               prependToStringArray(
                                                     lastChildNode.primedNodeText(),
                                                     "/\\ "))  ,
                            "CASE ");
                }
            } else {
                // This is an ASSUME/PROVE step.
                step = concatStringArrays(
                        prependToStringArray(newAssumpArray, "ASSUME "),
                        prependToStringArray(
                                this.state.goalRep.primedNodeText(), "PROVE  "));
            }

            String stepNum = proofLevelString + (pfStepVec.size() + 1);
            step = prependToStringArray(step, stepNum + STEP_NUMBER_PUNCTUATION
                    + " ");
            // Add the proof to step, if there is one. Since this is always
            // either
            // a CASE or an ASSUME/PROVE, if there is a proof, then we must add
            // the step
            // number to the proof's BY facts.
            if (proofText != null) {
                String[] newProofText = proofText.clone();
                addStepNumToProof(stepNum, newProofText);
                step = concatStringArrays(step, newProofText);
            }
            pfStepVec.add(step);
        }

    }

    /**
     * Adds the stepNum as a fact to the BY part of the leaf proof represented
     * by proofText--unless the proof is "OMITTED", in which case it does
     * nothing.
     * 
     * @param stepNum
     *            A step number such as "<2>3"
     * @param proofText
     *            A leaf proof as a string array of the proof of the step being
     *            decomposed, which is assumed to be non-null.
     */
    private void addStepNumToProof(String stepNum, String[] proofText) {
        LeafProofNode pfNode = (LeafProofNode) this.proof;

        if (pfNode.getOmitted()) {
            return;
        }

        if (((pfNode.getFacts() == null) || (pfNode.getFacts().length == 0))
                && ((pfNode.getDefs() == null) || (pfNode.getDefs().length == 0))) {
            // This is an "OBVIOUS" proof. Must replace the "OBVIOUS"
            // by "BY " + stepNum
            int i = 0;
            boolean notDone = true;
            while (notDone && (i < proofText.length)) {
                int idx = proofText[i].indexOf("OBVIOUS");
                if (idx != -1) {
                    proofText[i] = proofText[i].replaceFirst("OBVIOUS", "BY "
                            + stepNum);
                    notDone = false;
                }
                i++;
            }
        } else {
            // There is a "BY". Set comesAfter to either "BY"
            // or "ONLY", depending on whether there is not or there
            // is not a "BY ONLY"
            String comesAfter = "BY";
            if (pfNode.getOnlyFlag()) {
                comesAfter = "ONLY";
            }

            // Have to add a "," after stepNum if there already are BY
            // facts.
            String stepNumAdded = stepNum;
            if ((pfNode.getFacts() != null) && (pfNode.getFacts().length > 0)) {
                stepNumAdded = stepNum + ",";
            }
            int i = 0;
            boolean notDone = true;
            while (notDone && (i < proofText.length)) {
                int idx = proofText[i].indexOf(comesAfter);
                if (idx != -1) {
                    proofText[i] = proofText[i].replaceFirst(comesAfter,
                            comesAfter + " " + stepNumAdded);
                    notDone = false;
                }
                i++;
            }
        }
    }

    /**
     * Returns the NodeRepresentation for a child in nodeRep's decomposition
     * when nodeRep's formula is decomposed. It is called when processing an
     * AND-split, => Split, or OR split action.  It assumes that the result
     * is the goal iff vec = null ;
     * 
     * @param nodeRep
     *            The NodeRepresentation whose decomposition child's
     *            representation is returned.
     * @param i
     *            The index of the child in nodeRep's decomposition's children
     *            vector.
     * @param vec
     *            The result's parentVector field.
     * @param father
     *            The result's parentNode field.
     * @return
     */
    /**
     * @param nodeRep
     * @param i
     * @param vec
     * @param father
     * @return
     */
    /**
     * @param nodeRep
     * @param i
     * @param vec
     * @param father
     * @return
     */
    NodeRepresentation decompositionChildToNodeRep(NodeRepresentation nodeRep,
            int i, Vector<NodeRepresentation> vec, NodeRepresentation father) {
        // decomp is the nodeRep's decomposition
        Decomposition decomp = nodeRep.decomposition;

        // Set newNodeText to be null if the result's nodeText is to be obtained
        // from nodeText's semantic node. Otherwise, set it to the appropriate
        // subexpression name.
        NodeTextRep newNodeText = null;
        if ((decomp.definedOp != null)
                && this.subexpressionButton.getSelection()) {
            newNodeText = appendToNodeText(decomp.definedOpRep,
                    decomp.namePath.elementAt(i));
        } else if (nodeRep.isSubexpressionName) {
            newNodeText = appendToNodeText(new NodeTextRep(nodeRep.nodeText,
                    nodeRep.mapping), decomp.namePath.elementAt(i));
        }

        // Set childDoc to the IDocument in which the children are to
        // be found. 
        IDocument childDoc = this.doc;
        String moduleName = this.moduleNode.getName().toString() ;
        if (decomp.moduleName != null) {
            childDoc = moduleNameToIDocument(moduleName) ;
        }

        // Set result to the node representation.
        NodeRepresentation result;
        if ((decomp.definedOp != null) && (newNodeText == null)) {
            // Have to expand nodeRep's definition node.
            try {
                // this.doc replaced by childDoc by LL 15 Aug 2014:
                NodeRepresentation res = new NodeRepresentation(childDoc,
                        decomp.children.elementAt(i));
                NodeTextRep ntext = decompSubstituteInNodeText(nodeRep,
                        (ExprNode) decomp.children.elementAt(i),
                        new NodeTextRep(res.nodeText, res.mapping), nodeRep);
                res.nodeText = ntext.nodeText;
                res.mapping = ntext.mapping;

                // This is a hack, calling subNodeRep for the subnode of
                // the definition body consisting of the entire definition body.
                // But a little thought reveals that this does what needs to be
                // done.
                result = res.subNodeRep(decomp.children.elementAt(i), vec,
                        father, null, decomp, vec != null);
                result.isPrimed = nodeRep.isPrimed;
                if (!(decomp.children.elementAt(i) instanceof ExprNode)) {
                    MessageDialog.openError(UIHelper.getShellProvider()
                            .getShell(), "Decompose Proof Command",
                            "An error that should not happen has occurred in "
                                    + "line 2534 of NewDecomposeProofHandler.");
                }
            } catch (BadLocationException e) {
                // TODO Auto-generated catch block
                e.printStackTrace();
                MessageDialog.openError(UIHelper.getShellProvider().getShell(),
                        "Decompose Proof Command",
                        "An error that should not happen has occurred in "
                                + "line 2714 of NewDecomposeProofHandler.");
                return null;
            }

        } else {
            // Call subNodeRep to construct the result.
            result = nodeRep.subNodeRep(decomp.children.elementAt(i), vec,
                  father, newNodeText, decomp, vec != null);
            NodeTextRep ntext = decompSubstituteInNodeText(nodeRep,
                    (ExprNode) decomp.children.elementAt(i),
                    new NodeTextRep(result.nodeText, result.mapping), nodeRep);
            result.nodeText = ntext.nodeText;
            result.mapping = ntext.mapping;
            
        }
        // Set various fields whose values can be inferred from nodeRep and
        // decomp.
        // Don't set rep.isCreated because don't want it set for an
        // AND-split of an assumption, unless that assumption came from
        // a split of the goal.
        result.isPrimed = result.isPrimed || decomp.primed;
        result.isSubexpressionName = nodeRep.isSubexpressionName
                || newNodeText != null;
        result.initialPosition = nodeRep.initialPosition ;
        result.contextStepName = nodeRep.contextStepName ;
        result.fromGoal = nodeRep.fromGoal ;
        result.fromExists = nodeRep.fromExists ;
        result.fromDefs = nodeRep.fromDefs.clone();
        if (decomp.definedOp != null) {
            result.fromDefs.add(decomp.definedOp) ;
        }
        return result;
    }
    
    // The following code was copied from the jumpToLocation
    // method in UIHelper.java
    IDocument moduleNameToIDocument(String moduleName) {
        IDocument result = this.moduleNameToDoc.get(moduleName) ;
        if (result == null ) {
            IFile moduleIFile = (IFile) ResourceHelper
                    .getResourceByModuleName(moduleName);
            FileEditorInput fileEditorInput = new FileEditorInput(moduleIFile);
            FileDocumentProvider moduleFileDocProvider = new FileDocumentProvider();

            try {
                moduleFileDocProvider.connect(fileEditorInput);
            } catch (CoreException e1) { // I don't know what to do here
                MessageDialog.openError(UIHelper.getShellProvider().getShell(),
                        "Decompose Proof Command",
                        "An error that should not happen has occurred in "
                                + "line 2737 of NewDecomposeProofHandler.");
            }
            result = moduleFileDocProvider.getDocument(fileEditorInput);
        }
        return result ;
    }

    /**
     * Since Java doesn't allow structs, this is a class whose sole purpose is
     * to provide a return type for the following method. Its fields are a
     * vector of NodeRepresentations that will be a vector of NEW nodes obtained
     * from a quantified expression, and a NodeRepresentation obtained from the
     * body of that expression.
     */
    static class QuantifierDecomposition {
        Vector<NodeRepresentation> news;
        NodeRepresentation body;
    }

    /**
     * Returns the NodeRepresentations of the nodes forming the decomposition
     * for a \A or \E split. It assumes that the decomposition is a \A or \E
     * decomposition, so its quantIds field is not null. The NodeRepresentations
     * for the NEW assumptions are given a null semanticNode field, since I
     * don't think that field is ever used once decomposition begins. The
     * isForAll argument is used to determine whether the body's created field
     * should be set true.
     * 
     * If this is a top-level \E split, then the NEW variables may have to be
     * changed to avoid name clashes with NEW variables or other bound variables
     * of later assumptions or of the goal. This is not a problem for a \A split
     * because, since the \A formula is the goal, there are no later items to
     * clash with.  THE LATTER IS NO LONGER VALID WITH THE NEW METHOD FOR ORDERING
     * ASSUMPTIONS.  IT LED TO BUGS IN THE OLD VERSION BECAUSE THE \A SPLIT NEW
     * ASSUMPTION COULD APPEAR BEFORE CASE-SPLIT ASSUMPTIONS.
     * 
     * 
     * @param nodeRepArg
     *            The node being decomposed.
     * @param isForAll
     *            True iff this is called for a \A split
     * @return
     */
    QuantifierDecomposition decomposeQuantifier(NodeRepresentation nodeRepArg,
            boolean isForAll) {
        QuantifierDecomposition result = new QuantifierDecomposition();
        result.news = new Vector<NodeRepresentation>();
        NodeRepresentation nodeRep = nodeRepArg;
        Decomposition decomp = nodeRep.decomposition;

        // If this is within the subexpression-name expansion of a definition,
        // set NodeTextRep to the NodeTextRep that is the name of the formula
        // represented by nodeRep.
        NodeTextRep newNodeText = null;
        if ((decomp.definedOp != null) && (subexpressionButton.getSelection())) {
            newNodeText = decomp.definedOpRep;
        } else if (nodeRep.isSubexpressionName) {
            newNodeText = new NodeTextRep(nodeRep.nodeText, nodeRep.mapping);
        } else if (decomp.definedOp != null) {
            // Must expand the definition. We do this by creating a new
            // NodeRepresentation whose semanticNode, nodeText, and mapping
            // fields are what they should be for the definition body,
            // and creating a decomposition field for it.
            try {
                // NEED TO SUBSTITUTE FOR DEFINITION'S FORMAL PARAMETERS

                // Strip prime from nodeRepArg.semanticNode if it has one.
                OpApplNode oan = (OpApplNode) nodeRepArg.semanticNode;
                if (oan.getOperator().getName() == ASTConstants.OP_prime) {
                    if (!(oan instanceof OpApplNode)) {
                        return null;
                    }
                    oan = (OpApplNode) oan.getArgs()[0];
                }
                ExprNode sn = ((OpDefNode) oan.getOperator()).getBody();
                
                // LL-XXXX  -- doing some testing
                // (We are in decomposeQuantifier(nodeRepArg, isForAll)
                // 
                // If sn is a SubstInNode, then the definition has been
                // instantiated with renaming, so we must set the decomposition's
                // instantiationSubstitutionsD field to the substitutions
                // implied by the chain of SubstInNodes.  If sn is not a SubstInNode,
                // then we set instantiationSubstitutionsD to 
                // nodeRepArg.instantiationSubstitutions--even if sn is in a 
                // different module than nodeRepArg came from.  This is because
                // that other module might be one EXTENDed by nodeRepArg's
                // module, so it might have contributed module parameters
                // to sn's module, and those parameters might be instantiated
                // by a substitution in nodeRepArg.instantiationSubstitutions.
                // (We should add a test checking this situation.)
                // This isn't possible if sn's module was instantiated (but
                // has no module parameters), but there's no harm in trying to
                // do the instantiations from nodeRepArg.instantiationSubstitutions
                // because sn's module won't contain any of the nodes
                // being substituted for.  
                while (sn instanceof SubstInNode) {
                    Renaming rn = substInNodeToRenaming((SubstInNode) sn, nodeRep) ;
                    // Remem
                    sn = ((SubstInNode)sn).getBody() ;
                    
                }
                
                // LL-XXXX We have to set instantiatedNamePrefixD to the
                // concatenation of nodeRepArg.instantiatedNamePrefix
                // and all the text through the last "!" in the operator's
                // name.
                
                // Need to create the NodeRepresentation using the
                // module in which the definition occurs.  
                // LL-XXXX  If the definition
                // comes from a model that is instantiated with substitution,
                // should those substitions be done here?
                String moduleName = sn.getLocation().source() ;
                IDocument idoc = moduleNameToIDocument(moduleName);
                NodeRepresentation res = new NodeRepresentation(idoc, sn);
                // This is a hack, calling subNodeRep for the subnode of
                // the definition body consisting of the entire definition body.
                // But a little thought reveals that this does what needs to be
                // done.
                // Note: I don't think the last argument of the subNodeRep call
                // matters.
                nodeRep = res.subNodeRep(sn, nodeRepArg.getParentVector(),
                        nodeRepArg.parentNode, null, decomp, !isForAll);
                nodeRep.isPrimed = nodeRepArg.isPrimed;
                nodeRep.fromGoal = nodeRepArg.fromGoal ;
                nodeRep.fromExists = nodeRepArg.fromExists ;
                nodeRep.fromDefs = nodeRepArg.fromDefs.clone() ;
                if (decomp.definedOp != null) {
                    nodeRep.fromDefs.add(decomp.definedOp) ;
                }

                // We now want to call decompSubstituteInNodeText using the
                // substitutions in nodeRepArg.decomposition, rather than the
                // one computed by this  call to subNodeRep. So, we just set 
                // the necessary fields. LL-XXXX do we have to set the
                // instantiatedNamePrefix and instantiationSubstitutions
                // fields?  
                nodeRep.decomposition.formalParams = nodeRepArg.decomposition.formalParams;
                nodeRep.decomposition.arguments = nodeRepArg.decomposition.arguments;
                nodeRep.decomposition.argNodes = nodeRepArg.decomposition.argNodes;

                NodeTextRep ntext = decompSubstituteInNodeText(nodeRep, sn,
                        new NodeTextRep(nodeRep.nodeText, nodeRep.mapping),
                        nodeRepArg);
                nodeRep.nodeText = ntext.nodeText;
                nodeRep.mapping = ntext.mapping;
            } catch (BadLocationException e) {
                // TODO Auto-generated catch block
                e.printStackTrace();
                MessageDialog.openError(UIHelper.getShellProvider().getShell(),
                        "Decompose Proof Command",
                        "An error that should not happen has occurred in "
                                + "line 3787 of NewDecomposeProofHandler.");
                return null;
            }
        }

        // At this point, for a \E decomposition, we must perform any needed
        // substitutions in nodeRep for the \E's bound identifiers that can
        // cause a clash with bound identifiers or NEW declarations that occur
        // after this assumption.

        // Set idsToRename to the vector of NEW identifiers to be renamed,
        // and set idNewNames to the vector of their new names. These will be
        // empty vectors for a \A decomposition.
        Vector<FormalParamNode> idsToRename = new Vector<FormalParamNode>();
        Vector<String> idNewNames = new Vector<String>();

        if (!isForAll) {
            // Set prevDeclared to the set of all identifiers declared or
            // defined at the location of nodeRepArg.
            StringSet prevDeclared = this.declaredIdentifiers.clone();
            addDeclaredSymbols(prevDeclared, nodeRepArg);

            addSymbolsDeclaredLater(prevDeclared, nodeRepArg, true);

            // set idsToRename to the vector of NEW identifiers to be renamed,
            // and set idNewNames to the vector of their new names.
            // nrenaming is the renaming field of nodeRep, which will have
            // changed if the
            for (int i = 0; i < decomp.quantIds.size(); i++) {
                FormalParamNode id = decomp.quantIds.elementAt(i);
                if (prevDeclared.contains(getCurrentName(id, decomp.renaming))) {
                    idsToRename.add(id);
                    idNewNames
                            .add(getNewName(id, prevDeclared, decomp.renaming));
                }
            }

            // Call substituteInNode to do the renamings in nodeRep.
            FormalParamNode[] formalParams = new FormalParamNode[idsToRename
                    .size()];
            String[] arguments = new String[idsToRename.size()];
            boolean[] isBoundedIdRenaming = new boolean[idsToRename.size()];
            SemanticNode[] argNodes = new SemanticNode[idsToRename.size()];
            for (int i = 0; i < idsToRename.size(); i++) {
                formalParams[i] = idsToRename.elementAt(i);
                arguments[i] = idNewNames.elementAt(i);
                isBoundedIdRenaming[i] = true;
                argNodes[i] = null;
            }

            NodeTextRep nText = substituteInNodeText(formalParams, arguments,
                    isBoundedIdRenaming, argNodes,
                    (ExprNode) nodeRep.semanticNode, new NodeTextRep(
                            nodeRep.nodeText, nodeRep.mapping),
                    nodeRep.decomposition);
            nodeRep.nodeText = nText.nodeText;
            nodeRep.mapping = nText.mapping;
            for (int i = 0; i < idsToRename.size(); i++) {
                addCurrentName(idsToRename.elementAt(i),
                        idNewNames.elementAt(i), nodeRep.decomposition.renaming);
            }
        }

        int lastLine = -1;
        for (int i = 0; i < decomp.quantIds.size(); i++) {
            // Loop invariant:
            // lastRow != -1 iff
            // /\ i > 0
            // /\ \/ this is an unbounded quantifier
            //    \/ the i-1st NEW fits entirely on line lastLine
            NodeRepresentation rep = new NodeRepresentation();
            rep.initialPosition = nodeRepArg.initialPosition ;
            rep.semanticNode = null;
            rep.nodeType = NodeRepresentation.NEW_NODE;
            rep.newId = getCurrentName(decomp.quantIds.elementAt(i),
                    nodeRep.decomposition.renaming);
            rep.isCreated = true;
            rep.parentNode = nodeRep.parentNode;
            if (nodeRep.getParentVector() != null) {
                rep.setParentVector(nodeRep.getParentVector());
            } else {
                // nodeRep is the current goal and so the NEW assumptions
                // will become top-level assumptions and rep.parentVector
                // should be set to the NewDecomposeProofHandler's assumeRep
                // vector.
                rep.setParentVector(this.state.assumeReps);
            }

            // set id to "NEW" plus the bound identifier
            NodeTextRep ntrep = new NodeTextRep();
            String id = "NEW " + rep.newId;
            // + decomp.quantIds.elementAt(i).getName().toString();

            // beginLine is set to the line containing the source if there is
            // no quantifier bound or the quantifier bound occupies a single
            // line. Otherwise, it is set to -1.
            int beginLine = ((SyntaxTreeNode) decomp.quantIds.elementAt(i).stn)
                    .getLocation().beginLine();
            if (decomp.quantBounds == null) {
                // Set ntrep to a trivial NodeTextRep representing a
                // 1-line string with a standard mapping that should never
                // be used.
                ntrep.nodeText = new String[1];
                ntrep.nodeText[0] = id;
                ntrep.mapping = new Vector[1];
                ntrep.mapping[0] = new Vector<MappingPair>();
                ntrep.mapping[0].addElement(new MappingPair(1, -1));
            } else {
                // Set ntrep to be a NodeTextRep for the quantifier bound,
                // primed if decomp.primed or nodeRep.isPrimed is = true.
                if (newNodeText == null) {
                    // The bound is not a subexpression name.
                    ntrep = nodeRep
                            .subNodeText(decomp.quantBounds.elementAt(i));
                    if (decomp.primed || nodeRep.isPrimed) {
                        if (primingNeedsParens(decomp.quantBounds.elementAt(i))) {
                            ntrep = prependToNodeText(
                                    appendToNodeText(ntrep, ")'"), "(");
                        } else {
                            ntrep = appendToNodeText(ntrep, "'");
                        }
                    }
                } else {
                    // The bound is a subexpression name.
                    String str = decomp.quantBoundsubexpNames.elementAt(i);
                    if (decomp.primed) {
                        str = str + "'";
                    }
                    ntrep = appendToNodeText(newNodeText, str);
                }
                ntrep = prependToNodeText(ntrep, " \\in ");
                if (ntrep.nodeText.length > 1) {
                    beginLine = -1;
                }
            }

            if (decomp.quantBounds != null) {
                ntrep = prependToNodeText(ntrep, id);
            }
            rep.nodeText = ntrep.nodeText;
            rep.mapping = ntrep.mapping;
            
            // Set node's contextStepName to be that of nodeRepArg
            rep.contextStepName = nodeRepArg.contextStepName ;
            rep.fromGoal = nodeRepArg.fromGoal ;
            // nodeRep.fromDefs = 
            // IF nodeRep obtained from nodeRepArg  by expanding def of Op
            //   THEN nodeRepArg.fromDefs \cup {Op}
            //   ELSE nodeRepArg.fromDefs
            rep.fromDefs = nodeRep.fromDefs ;

            result.news.add(rep) ;
            if ((beginLine != -1) && (beginLine == lastLine)) {
                result.news.elementAt(i - 1).onSameLineAsNext = true;
            }
            lastLine = beginLine;
        }

        // We next compute the NodeRepresentation for the body of the quantified
        // expression.
        if (newNodeText != null) {
            // We are using subexpression names, so we append to newNodeText
            // the "!(id1, ... , idn)" needed to form the subexpression name
            // of the body.
            String str = "!(";
            for (int i = 0; i < decomp.quantIds.size(); i++) {
                if (i != 0) {
                    str = str + ", ";
                }
                str = str + decomp.quantIds.elementAt(i).getName().toString();
            }
            str = str + ")";
            newNodeText = appendToNodeText(newNodeText, str);
        }
        result.body = nodeRep.subNodeRep(decomp.children.elementAt(0),
                nodeRep.getParentVector(), nodeRep.parentNode, newNodeText,
                nodeRep.decomposition, !isForAll);
        result.body.isCreated = true ; // changed to true from isForAll by LL on 8 Oct 2014
        result.body.isPrimed = result.body.isPrimed || decomp.primed;
        result.body.isSubexpressionName = nodeRep.isSubexpressionName
                || (newNodeText != null);
        result.body.initialPosition = nodeRepArg.initialPosition ;
        // set contextStepName for the body.
        result.body.contextStepName = nodeRepArg.contextStepName ;
        result.body.fromGoal = nodeRep.fromGoal ;
        result.body.fromExists = nodeRep.fromExists ;
        result.body.fromDefs = nodeRep.fromDefs.clone() ;
        return result;
    }

    /**
     * Returns string array such that applying stringArrayToString to it
     * produces the text of the list of assumptions in createdAssumps of
     * the spec of MakeProof.
     */
    String[] createdAssumptions() {
        /**
         * Sets vec to a vector of string arrays such that applying
         * stringArrayToString to each of them produces the text of an
         * assumption in this.state.assumeReps for which the isCreated field
         * equals true--except that multiple one-line NEW assumptions are
         * combined into a single 1-line string array.
         */
        Boolean sufficesSelected = useSufficesButton.getSelection();
        Vector<String[]> vec = new Vector<String[]>();
        
        // Set lastAddedAssump so that state.firstAddedAssumption .. lastAddedAssump-1
        // are the added non-case-split assumptions of state.assumeReps.
        int lastAddedAssump = state.assumeReps.size() ;
        if (state.splitChosen()) {
            lastAddedAssump--;
        }
        
        for (int i = state.firstAddedAssumption; i < lastAddedAssump; i++) {
            NodeRepresentation rep = state.assumeReps.elementAt(i);
                String newDecls = null;
                while (rep.onSameLineAsNext) {
                    if (newDecls != null) {
                        newDecls = newDecls + ", ";
                    } else {
                        newDecls = "";
                    }
                    newDecls = newDecls + rep.nodeText[0];
                    i++;
                    rep = state.assumeReps.elementAt(i);
                }
                if (newDecls == null) {
                    vec.add(rep.primedNodeText());
                } else {
                    vec.add(new String[] { newDecls + ", " + rep.nodeText[0] });
                }
//            }
        }

        /**
         * Sets resVec to a single vector obtained by combining the elements of
         * vec, putting commas between them.
         */
        Vector<String> resVec = new Vector<String>();
        for (int i = 0; i < vec.size(); i++) {
            String[] strArray = vec.elementAt(i);
            for (int j = 0; j < strArray.length; j++) {
                String str = strArray[j];
                if ((j == strArray.length - 1) && (i != vec.size() - 1)) {
                    str = str + ",";
                }
                resVec.add(str);
            }
        }

        // Convert resVec to the array result and return it.
        String[] result = new String[resVec.size()];
        for (int i = 0; i < result.length; i++) {
            result[i] = resVec.elementAt(i);
        }
        return result;
    }

    /**
     * The following bug fixed by LL on 3 July 2014: Decomposing
     * 
     * foo(p) == \A x : p <=> A \/ B THEOREM foo(\/ C')
     * 
     * produces the new goal
     * 
     * ASSUME NEW x PROVE \/ C' <=> A \/ B 
     * --------- 
     * Assumes that nodeTextRep is
     * the NodeTextRep for the ExprNode sn (possibly after some substitutions
     * have been made). It returns the NodeTextRep object representing sn after
     * substituting arguments[i] for formalParams[i], for each i. It assumes
     * that argNodes[i] is the semantic node whose string representation is
     * arguments[i]. That string representation must be a single-line string (no
     * line breaks).
     * 
     * Note: this assumes that none of the substitutions made before this one
     * have added any of the formal parameter symbols being substituted for. We
     * also assume that the node sn is being used as a complete assume clause or
     * goal.
     * 
     * @param formalParams
     *            The formal parameters to be substituted for.
     * @param arguments
     *            The String representations of argNodes, which must be a
     *            single-line expression.
     * @param isBoundedIdRenaming
     *            An array whose i-th element is true iff formalParams[i] is the
     *            FormalParamNode of a bound identifier in sn that is being
     *            renamed to arguments[i].
     * @param argNodes
     *            The semantic nodes of the expressions to be substituted,
     *            except that argNodes[i] is not used and may be null if
     *            isBoundedIdRenaming[i] = true.
     * @param sn
     *            SemanticNode in which the substitutions are being made.
     * @param nodeTextRep
     *            Representation of sn (perhaps after other substitutions).
     * @param decomp
     *            A decomposition from which to find renamings of identifiers.
     * @return
     */
    NodeTextRep substituteInNodeText(FormalParamNode[] formalParams,
            String[] arguments, boolean[] isBoundedIdRenaming,
            SemanticNode[] argNodes, ExprNode sn, NodeTextRep nodeTextRep,
            Decomposition decomp) {
        NodeTextRep result = nodeTextRep.clone();

        int numOfLines = result.nodeText.length;

        // We set inserts to an array of Insertion vectors that describe the
        // modification made
        // to nodeTextRep to get result. This is used to call adjustIndentation
        // to fix the
        // indentation of result.
        Vector<Insertion>[] inserts = new Vector[numOfLines];
        for (int i = 0; i < numOfLines; i++) {
            inserts[i] = new Vector();
        }
        // Line of first token of sn, used to translate from Location line
        // numbers to
        // indices in noteTextRep.nodeText.
        int beginLine = sn.stn.getLocation().beginLine();

        for (int i = 0; i < arguments.length; i++) {
            SemanticNode[] uses = ResourceHelper.getUsesOfSymbol(
                    formalParams[i], sn);

            String replacementText = arguments[i];

            // NOTE: If we were substituting for a formal parameter for which a
            // different identifier had been substituted, we have to use as
            // sourceTextLength the length of the new identifier.
            int sourceTextLength = getCurrentName(formalParams[i],
                    decomp.renaming).length();
            // Set mayNeedParens true if replacementText doesn't end in ' and
            // would
            // need parentheses around it in order to prime it.
            boolean mayNeedParens = false;
            if (primingNeedsParens(argNodes[i])
                    && ((replacementText.charAt(replacementText.length() - 1) != '\'')
                            // Following disjuncts added on 3 July 2014 to fix
                            // bug
                            // described above.
                            || replacementText.startsWith("\\/") || replacementText
                                .startsWith("/\\"))) {
                mayNeedParens = true;
            }
            for (int j = 0; j < uses.length; j++) {
                if (!(uses[j] instanceof OpApplNode)) {
                    MessageDialog.openError(UIHelper.getShellProvider()
                            .getShell(), "Decompose Proof Command",
                            "An error that should not happen has occurred in "
                                    + "line 2842 of NewDecomposeProofHandler.");
                    return result;
                }
                // Note: the following code outside the if (mayNeedParens) has
                // been cloned below for renaming the FormalParamNode
                // declaration
                // if isBoundedIdRenaming[i] is true.
                Location useLocation = uses[j].stn.getLocation();
                int useIdx = useLocation.beginLine() - beginLine;
                int offset = colToLoc(useLocation.beginColumn(),
                        result.mapping[useIdx]);
                String thisReplaceText = replacementText;
                if (mayNeedParens) {
                    // Define text that, if it surrounds the replaced text,
                    // implies
                    // that no parentheses are needed.
                    String[] precedingSafe = new String[] { "(", "[", "{", ",",
                            "<<", "->", ":" };
                    String[] followingSafe = new String[] { ")", "]", "}", ",",
                            ">>", "->", "~>" };

                    // Because we assume that the formula we're substituting
                    // into is a complete
                    // assumption or goal, the end of the formula is also a safe
                    // preceding
                    // or following "string".
                    String testString = result.nodeText[useIdx].substring(0,
                            offset).trim();
                    int line = useIdx;
                    while (testString.equals("") && line > 0) {
                        line--;
                        testString = result.nodeText[line];
                    }
                    boolean terminated = testString.equals("");
                    int k = 0;
                    while (!terminated && k < precedingSafe.length) {
                        terminated = testString.endsWith(precedingSafe[k]);
                        k++;
                    }
                    if (terminated) {
                        testString = result.nodeText[useIdx].substring(
                                offset + sourceTextLength).trim();
                        line = useIdx;
                        while (testString.equals("")
                                && line < result.nodeText.length - 1) {
                            line++;
                            testString = result.nodeText[line];
                        }
                        terminated = testString.equals("");
                        k = 0;
                        while (!terminated && k < precedingSafe.length) {
                            terminated = testString
                                    .startsWith(followingSafe[k]);
                            k++;
                        }
                    }
                    if (!terminated) {
                        thisReplaceText = "(" + replacementText + ")";
                    }
                }
                result.nodeText[useIdx] = result.nodeText[useIdx].substring(0,
                        offset)
                        + thisReplaceText
                        + result.nodeText[useIdx].substring(offset
                                + sourceTextLength);
                adjustMappingPairVector(useLocation.beginColumn()
                        + sourceTextLength, thisReplaceText.length()
                        - sourceTextLength, result.mapping[useIdx]);

                // Update inserts
                inserts[useIdx].add(new Insertion(offset, sourceTextLength,
                        thisReplaceText.length()));
            }

            // if isBoundedIdRenaming[i] is true, then rename the occurrence of
            // the FormalParamNode. The code was cloned for the code above that
            // renames uses.
            //
            // This can be called with decomp.renaming containing renamings for
            // bounded identifiers that occur in a different part of the spec
            // because we're now inside an expanded definition. We therefore
            // have to not try to do the renaming in that case.
            if (isBoundedIdRenaming[i]) {
                Location useLocation = formalParams[i].stn.getLocation();
                // We do this replacement iff the identifier declaration is
                // contained
                // in the location in which the renaming is being performed.
                if (EditorUtil.locationContainment(useLocation,
                        sn.stn.getLocation())) {
                    int useIdx = useLocation.beginLine() - beginLine;
                    int offset = colToLoc(useLocation.beginColumn(),
                            result.mapping[useIdx]);
                    result.nodeText[useIdx] = result.nodeText[useIdx]
                            .substring(0, offset)
                            + replacementText
                            + result.nodeText[useIdx].substring(offset
                                    + sourceTextLength);
                    adjustMappingPairVector(useLocation.beginColumn()
                            + sourceTextLength, replacementText.length()
                            - sourceTextLength, result.mapping[useIdx]);

                    // Update inserts
                    inserts[useIdx].add(new Insertion(offset, sourceTextLength,
                            replacementText.length()));
                }
            }

        }

        // Adjust the indentation.
        adjustIndentation(nodeTextRep, result, inserts);

        return result;
    }
    
    

    /**
     * Calls substituteInNodeText to perform the substitution of arguments for
     * formal parameters in a decomposition that is the expansion of a
     * definition, as well as for bound identifiers that must be renamed because
     * of name clashes with declarations and definitions occurring earlier in
     * the module.
     * 
     * @param nodeRep
     *            NodeRepresentation being decomposed.
     * @param sn
     * @param nodeTextRep
     * @param originalNodeRep
     *            NodeRepresentation that is currently in the state.assumeReps /
     *            state.goalRep data structure at the place where nodeRep will
     *            go.
     * 
     * @return
     */
    NodeTextRep decompSubstituteInNodeText(NodeRepresentation nodeRep,
            ExprNode sn, NodeTextRep nodeTextRep,
            NodeRepresentation originalNodeRep) {
        Decomposition decomp = nodeRep.decomposition;

        // Set prevDeclared to the set of all identifiers declared or defined at
        // the location of nodeRep.
        StringSet prevDeclared =  this.declaredIdentifiers.clone();
        addDeclaredSymbols(prevDeclared, originalNodeRep);

        // Added by LL on 10 Feb 2013 because formulas that are being decomposed
        // may wind up added in the scope later NEW declarations.
        addSymbolsDeclaredLater(prevDeclared, originalNodeRep, false);

        // Set rename to a new Renaming object containing the renamings
        // in decomp.renamings together with all additional renamings
        // necessary to avoid name conflicts with names in prevDeclared.
        Renaming rename = decomp.renaming.clone();

        addToRenaming(rename, prevDeclared, sn);

        // Compile the arguments for calling substituteInNodeText.
        // Set decompParamsLen to the number of formal parameters, which is 0
        // if decomp.formalParams = null
        int decompParamsLen = 0;
        if (decomp.formalParams != null) {
            decompParamsLen = decomp.formalParams.length;
        }
        FormalParamNode[] formalParams = new FormalParamNode[decompParamsLen
                + rename.identifiers.size()];
        String[] arguments = new String[formalParams.length];

        boolean[] isBoundedIdRenaming = new boolean[formalParams.length];
        SemanticNode[] argNodes = new SemanticNode[formalParams.length];

        for (int i = 0; i < decompParamsLen; i++) {
            formalParams[i] = decomp.formalParams[i];
            arguments[i] = decomp.arguments[i];
            isBoundedIdRenaming[i] = false;
            argNodes[i] = decomp.argNodes[i];
        }

        // Save the new names chosen for the identifiers in renameIdentifiers
        // in the vector renameIdentifiersNames. They must be added
        // to renamedIdentifiers and newIdentifierNames after the call
        // to substituteInNode because, if an identifier gets re-renamed,
        // then substituteInNode needs to know the name of the
        // identifier (actually, its length) before the re-renaming.
        for (int i = 0; i < rename.identifiers.size(); i++) {
            formalParams[i + decompParamsLen] = rename.identifiers.elementAt(i);
            arguments[i + decompParamsLen] = rename.newNames.elementAt(i);
            isBoundedIdRenaming[i + decompParamsLen] = true;
            argNodes[i + decompParamsLen] = null;
        }

        NodeTextRep result = substituteInNodeText(formalParams, arguments,
                isBoundedIdRenaming, argNodes, sn, nodeTextRep, decomp);
        // The following commented out by LL on 8 Feb 2013 because it seems
        // wrong.
        // The renamings for decomp are for the expression that is the use
        // of the operator in whose definition we are performing the
        // substitutions.
        // Add the renamings to decomp.renaming
        // On 10 Feb 2013, LL realized that seems to be wrong, because some
        // bounded id renaming is getting lost.
        decomp.renaming = rename;

        return result;
    }
    
    /**
     * Creates a Renaming object that represents the renamings
     * of the SubstInNode node, where the substituting expression
     * nodes are assumed to be subexpressions of the semantic node
     * represented by contextNodeRep (and hence need to be renamed
     * according to contextNodeRep.instantiationSubstitutions).
     * Returns null if any of the expressions being substituted
     * for identifiers are multi-line, or if it fails for any
     * other reason because the code doesn't know what to do with
     * some substitution the node.
     * 
     * @param node
     * @param currRenaming
     * @return
     */
    private Renaming substInNodeToRenaming(SubstInNode node, 
                                           NodeRepresentation contextNodeRep) {
        
        Renaming result = new Renaming() ;
        
        // Construct the arguments to substituteInNodeText for performing
        // the substitutions in contextNodeRep.instantiationSubstitutions.
        
        Renaming contextRenaming = contextNodeRep.instantiationSubstitutions ;
        int clen = contextRenaming.identifiers.size() ;
        FormalParamNode[] formalParams = new FormalParamNode[clen] ;
        SemanticNode[] argNodes = new SemanticNode[clen] ;
        String[] arguments = new String[clen] ;
        boolean[] isBoundedIdRenaming = new boolean[clen] ;
        for(int i=0; i < clen; i++) {
          isBoundedIdRenaming[i] = false ;
            // I'm hoping that substituteInNodeText does the right thing with 
            // a substituting expression if it pretends that it's an identifier.
          formalParams[i] = contextRenaming.identifiers.elementAt(i) ;
          argNodes[i] = null ;
          arguments[i] = contextRenaming.newNames.elementAt(i) ;
        }
        
        Subst[] subst = node.getSubsts() ;

        for (int i = 0; i < subst.length; i++ ) {
            // SubstInNode substitutions substitute for OpDeclNodes.
            // substituteInNodeText substitutes for FormalParamNodes.
            // As a Kludge to connect them, we construct a FormalParamNode
            // from an OpDeclNode and hope that it looks enough like one
            // to work.
            OpDeclNode opdec = subst[i].getOp() ;
            FormalParamNode fpn =
                new FormalParamNode(opdec.getName(), 
                                    opdec.getArity(), 
                                    opdec.stn,  
                                    opdec.getSymbolTable(),
                                    opdec.getOriginallyDefinedInModuleNode()
                                    ) ;
            result.identifiers.add(fpn) ;
            if (!(subst[i].getExpr() instanceof ExprNode)) {
                return null ;
            }
            ExprNode sn = (ExprNode) subst[i].getExpr() ;
            
            // LL-XXXX This is wrong because sn is the semantic node
            // of an expression in the INSTANCE statement, so it's
            // not a subnode of contextNodeRep.
            IDocument idoc = 
                    moduleNameToIDocument(sn.getLocation().source());
            NodeRepresentation randomNodeRep;
            try {
                randomNodeRep = new NodeRepresentation(idoc, sn);
            } catch (BadLocationException e) {
                // TODO Auto-generated catch block
                return null ;
            }
            NodeTextRep snNodeText = new NodeTextRep(randomNodeRep.nodeText, 
                                                     randomNodeRep.mapping) ;            
            NodeTextRep nrep = 
                    substituteInNodeText(formalParams,
                          arguments, isBoundedIdRenaming,
                          argNodes, sn,  snNodeText,
                          new Decomposition()) ;
                   // note: the Decomposition argument is just used to do some
                   // renamings, which I think are irrelevant here because I
                   // think any of the renamings have already been performed
                   // when we construct the NodeTextRep argument.
                   // LL-XXXXX This may be wrong, in which case we need to
                   // add another argument to this method.  Check that it works
                   // in a decomposition of \E x : Foo!Bar(x) that requires
                   // renaming of the x.
            if (nrep.nodeText.length != 1) {
                return null ;
            }
            result.newNames.add(nrep.nodeText[0]) ;
        }

        return result ;
    }

    /**
     * Adds to `renaming' all the renamings to bound identifiers in expr that
     * are necessary to eliminate clashes with names in the set prevDeclared.
     * 
     * This code was obtained by modifying the implementation of
     * ResourceHelper.innerGetBoundIdentifiers.
     * 
     * @param rename
     * @param prevDeclared
     * @param expr
     * @return
     */
    private void addToRenaming(Renaming renaming, StringSet prevDeclared,
            ExprNode expr) {
        if (!(expr instanceof OpApplNode)) {
            return;
        }

        StringSet newDeclared =  prevDeclared.clone();

        OpApplNode node = (OpApplNode) expr;
        if (node.getUnbdedQuantSymbols() != null) {
            for (int i = 0; i < node.getUnbdedQuantSymbols().length; i++) {
                FormalParamNode id = node.getUnbdedQuantSymbols()[i];
                if (newDeclared.contains(getCurrentName(id, renaming))) {
                    String newname = getNewName(id, newDeclared, renaming);
                    newDeclared.add(newname);
                    addCurrentName(id, newname, renaming);
                }
            }
        }

        if (node.getBdedQuantSymbolLists() != null) {
            for (int i = 0; i < node.getBdedQuantSymbolLists().length; i++) {
                addToRenaming(renaming, prevDeclared,
                        node.getBdedQuantBounds()[i]);
                FormalParamNode[] nodeList = node.getBdedQuantSymbolLists()[i];
                for (int j = 0; j < nodeList.length; j++) {
                    FormalParamNode id = nodeList[j];
                    if (newDeclared.contains(getCurrentName(id, renaming))) {
                        String newname = getNewName(id, newDeclared, renaming);
                        newDeclared.add(newname);
                        addCurrentName(id, newname, renaming);
                    }
                }
            }
        }

        for (int i = 0; i < node.getArgs().length; i++) {
            if (node.getArgs()[i] instanceof ExprNode) {
                addToRenaming(renaming, newDeclared,
                        (ExprNode) node.getArgs()[i]);
            }
        }

    }

    /**
     * A DecompositionState describes the current state of the decomposition,
     * and determines what is shown in the command's popup window. There will be
     * a chain of such objects to support the "Back" option.
     */
    private class DecompositionState {
        /**
         * previousState is the decomposition state to which the "Back" button
         * goes. It should be null only for the initial state.
         */
        DecompositionState previousState = null;

        /**
         * The hasChanged field is (I believe) used only to determine if the
         * replaceButton on the command's window raised by raiseWindow() is
         * enabled. For reasons explained in the comments describing that
         * button, hasChanged is set true by any decomposition action except
         * clicking on an /\ decomposition, which sets it false.
         */
        boolean hasChanged;

        /*************************************************************************
         * Fields that contain the current assumptions and goal.
         * 
         * The data for the current assumptions are kept in vectors, the i-th
         * element containing data for the i-th assumption. This is done to make
         * it easy to replace one assumption by several. Other objects contain
         * pointers to these vectors, so once the vectors are constructed by
         * NewDecomposeProofHandler.execute, they can be modified but must not
         * be replaced by new vectors.
         *************************************************************************/
        /**
         * The NodeRepresentation objects for the current assumptions.
         */
        private Vector<NodeRepresentation> assumeReps;

        /**
         * The NodeRepresentation object for the current goal.
         */
        private NodeRepresentation goalRep;

        /**
         * The number of assumptions in assumeReps that are context assumptions.
         */
        private int numberOfContextAssumptions ;
        
        /**
         * state.assumeReps.elementAt(firstAddedAssumption) through
         * state.assumeReps.elementAt(state.assumeReps.size()-1) are
         * all the added assumptions that must appear as assumptions in
         * the decomposed proof.
         *   
         */
        private int firstAddedAssumption ;
        
        /**
         * On 15 Oct 2014 the field chosenSplit was removed.  It contained
         * the index of an OR-split entry in assumeReps, if there is one.
         * Now, such an OR-split entry must be the last one in assumeReps,
         * so the splitChosen() method replaces it.
         */
        boolean splitChosen() {
            return    (assumeReps.size() > 0)
                   && (assumeReps.elementAt(assumeReps.size()-1).nodeType 
                           == NodeRepresentation.OR_DECOMP) ;
        }

        /**
         * True if the proof of a SUFFICES step (or of the QED step if there is
         * no SUFFICES step) needs the name of the step being decomposed in the
         * BY clause if that step has a name. I believe this is the case iff an
         * \E-split has been done on an assumption that was not moved from the
         * goal.
         */
        boolean needsStepNumber;

        /**
         * Once the user has performed an AND split on an assumption, then
         * another AND split can be performed only on one of the results of that
         * split. The indices of the nodes in <code>assumes</code> and
         * <code>state.assumeReps</code> resulting from AND splits range from
         * state.andSplitBegin through (including) state.andSplitEnd. If no AND
         * split has been performed, then state.andSplitBegin and
         * state.andSplitEnd equal -1.
         * 
         */
// UP-DOWN ARROWS REMOVED
//        int andSplitBegin; // NOT CLEAR IF THESE WILL BE USED IN NEW VERSION.
//        int andSplitEnd; // NOT CLEAR IF THESE WILL BE USED IN NEW VERSION.

        /**
         * The set of Ids of user-defined operations that must appear in the DEF
         * clause of the QED step's proof. They are definitions that were
         * expanded in decomposing non-top level \E and/or \/ assumptions.
         */
        private StringSet goalDefinitions;

        private HashSet<String> assumpDefinitions;

        // PERHAPS CAN BE COMBINED WITH goalDefinitions

        public DecompositionState clone() {
            DecompositionState result = new DecompositionState();

            result.hasChanged = hasChanged;
            result.assumeReps = new Vector<NodeRepresentation>();
            for (int i = 0; i < assumeReps.size(); i++) {
                result.assumeReps.addElement(assumeReps.elementAt(i).deepClone(
                        null, result.assumeReps));
            }

            result.goalRep = goalRep.deepClone(null, null);
            result.numberOfContextAssumptions = numberOfContextAssumptions ;
            result.firstAddedAssumption = firstAddedAssumption ;
            // result.chosenSplit = chosenSplit;
            result.needsStepNumber = needsStepNumber;
// UP-DOWN ARROWS REMOVED
//            result.andSplitBegin = andSplitBegin;
//            result.andSplitEnd = andSplitEnd;
            result.goalDefinitions = goalDefinitions.clone();
            result.assumpDefinitions = (HashSet<String>) assumpDefinitions
                    .clone();

            return result;
        }
    }

    /**
     * A NodeRepresentation object describes the TLA+ source text that produced
     * a SemanticNode, after substitutions have been performed for some
     * identifiers. It contains the following information:
     * <ul>
     * <li>The SemanticNode <code>node</code>.
     * 
     * <li>A String[] object <code>nodeText</code> that describes the source
     * text after substitutions have been performed.
     * 
     * <li>A mapping from <line, column> coordinates occurring in locations in
     * the syntax tree of <code>node</code> to the corresponding positions in
     * <code>nodeText</code>.
     * </ul>
     * Substitutions are performed for an identifier for two reasons:
     * <ul>
     * <li>The formal parameter of a definition is replaced by an argument when
     * expanding the definition. To simplify the implementation, such an
     * expansion is performed only when all the arguments consist of text
     * occurring on a single line.
     * 
     * <li>A bound identifier has been renamed to avoid a name conflict.
     * </ul>
     * A substitution cannot be performed for any occurrence that was added by a
     * substitution. Hence, an identifier introduced by renaming cannot be
     * renamed.
     * 
     * An OR-decomposition node represents an assumption that has been
     * decomposed into a disjunction for a proof by cases. Such a node has a
     * vector of children, which can include OR-decomposition nodes.
     * 
     * 
     * @author lamport
     * 
     */
    public class NodeRepresentation {
        /**
         * The original semantic node
         */
        SemanticNode semanticNode;

        /**
         * We represent the text of a TLA+ syntactic unit as a String array,
         * each element representing one line of the text with no end-of-line
         * characters.
         * 
         * The text from the module that represents <code>node</code>,
         * represented by the array nodeText of strings as follows. Let S be the
         * region of the module that produces the node. If S lies entirely on
         * one line, then nodeText has length 1 and nodeText[0] = S. Otherwise,
         * suppose S lies on N lines. Let B be the array with B[0] containing
         * the beginning of S up until the end of the first line, with B[1], ...
         * , B[n-1] containing the next n-2 lines of S, and with B[n] containing
         * the rest of S. Then nodeText is the array obtained from B by possibly
         * adding spaces to the beginning of B[0] and possibly removing spaces
         * from the beginning of B[1], ... , B[n] so that there is at least one
         * line of nodeText that does not begin with a space and the formatting
         * of the original text is maintained in nodeText.
         * 
         * This is not quite accurate.
         * 
         * @param document
         * @param semanticNode
         * @return
         */
        String[] nodeText;

        // mapping defines the mapping from <line, column> coordinates
        // within the syntax tree of `node' to positions in nodeText,
        // where <ln, c> is mapped into the position mapping[j](c) in
        // string nodeText[j], where j = ln - node.stn.beginLine()
        // (node.stn.beginLine() is the number of the line on which the
        // source text of `node' begins. (See the comments on the
        // MappingPair class for a definition of mapping[j](c).
        Vector<MappingPair>[] mapping;

        // Suppose that we are decomposing a proof in module M, and 
        // this NodeRepresentation nr represents an expression in module N.
        // Thus, nr.semanticNode is a node in the semantic tree of N,
        // so the name op and definition expr of a defined operator used in 
        // nr are expressions that make sense in module N, not in the
        // proof's module M.  Then operator op is known in module m
        // by the name instantiatedNamePrefix + op, and the definition
        // expr is imported into M by performing the substitutions
        // instantiationSubstitutions in expr.  Example:
        //
        //   MODULE M contains  IP == INSTANCE P WITH CP <- expM
        //                      ... ASSUME IP!POp(argM), ...
        //   MODULE P contains  IN == INSTANCE N WITH CN <- expP
        //                      POp(a) == ... \/ IN!NOp(a, argP) 
        //   MODULE N contains  NOp(b, c) == expr(b, c)
        //   
        // Then decomposing IP!Pop(argM) produces the following
        // assumption, where exp WITH C <- sub means with the expression
        // sub for all instances of the node C with the expr sub.
        //      
        //   ... \/ IN!NOp(argM, argP WITH CP <- expM)
        //
        // Decomposing that disjunction produces a case
        //
        //   expr(argM, argP WITH CP <- expM)  
        //                    WITH   CN <- (expP WITH CP <- expM)
        //
        // Note that argM is equivalent to argM WITH CP <- expM
        // which is equivalent to (argM WITH CP <- expM) WITH CN <- expP
        // because neither CP (which is declared in module P) nor
        // CN (which is declared in module N) can occur in argM (which
        // is an expression module M.  Note that CP and CN denote semantic
        // nodes, not the strings that represent those nodes (which
        // could be the same string for both of them).
        //
        Renaming instantiationSubstitutions = new Renaming() ;
        String   instantiatedNamePrefix = "" ;
        
        // The nodeType is the type of node.
        private static final int EXPR_NODE = 0; // An OpApplNode
        private static final int NEW_NODE = 1; // A NewSymbNode
        private static final int OR_DECOMP = 2;
        // A node representing a decomposition into the disjunction of its
        // children.
        private static final int PROOF_NODE = 4;
        // The LeafProofNode of the step. This may not be needed.
        private static final int OTHER_NODE = 5;
        private int nodeType = 0;

        // An EXPR_NODE has a subtype, indicating what
        // decomposition can be applied.
        // Subtypes for decomposing a goal:
        private static final int AND_TYPE = 0; // A conjunction
        private static final int IMPLIES_TYPE = 2; // An implication
        private static final int FORALL_TYPE = 3; // A \A
        // Subtypes for decomposing an assumption
        private static final int OR_TYPE = 1; // A disjunction
        private static final int EXISTS_TYPE = 4; // An \E
        private static final int SQSUB_TYPE = 5; // An [A]_v expression
//        private static final int MULTI_TYPE = 6;
        // An assumption that is the conjunction of formulas, two or more
        // of which can be decomposed.
        // Subtype for something that can't be decomposed
        private static final int OTHER_TYPE = 99; // anything else

        public int nodeSubtype = OTHER_TYPE;

        /**
         * If this NodeRepresentation object is of type NEW_NODE, then this is
         * the NEW identifier.
         */
        public String newId = null;
        
        /**
         * This NodeRepresentation object either was or was obtained from the
         * assumption that was originally state.assumeReps.elementAt(initialPosition),
         * except that initialPosition equals approximately Integer.MAX_VALUE - 42
         * if it came from the goal and equals Integer.MAX_VALUE if it is the
         * (only) object of type OR_DECOMP in state.assumeReps.
         */
        int initialPosition = -1 ;  // -1 indicates that value not set.

        /********************************************************************
         * An OR-Split operation can be performed on a node of type EXPR_NODE
         * and subtype OR_TYPE. This operation replaces the node with one of
         * type OR_DECOMP, whose children field is a vector with one element for
         * each disjunct of the semanticNode's disjuncts, where
         * children.elementAt(i) is a vector of length 1 containing a node of
         * type EXPR_NODE for that disjunct. Further operations on that node can
         * turn children.elementAt(i) into a vector consisting of a sequence of
         * NEW_NODE NodeRepresentation objects followed by an EXPR_NODE or
         * OR_DECOMP node. The `children' field is null for a node of type other
         * than OR_DECOMP.
         *********************************************************************/
        Vector<Vector<NodeRepresentation>> children = null;

        /********************************************************************
         * If this node has parentNode # null, then it equals
         * n.children.elementAt(i).elementAt(j) for an OR_DECOMP node n, where
         * parentNode = n and parentVector = n.children.elementAt(i). In this
         * case, the node is of type EXPR_NODE, NEW_NODE, or OR_DECOMP.
         * 
         * If parentNode = null, then there are two cases:
         * 
         * - The node is either an element of state.assumeReps. In that case, it
         * equals h.state.assumeReps.elementAt(j) for the
         * NewDecomposeProofHandler object h, and parentVector =
         * state.assumeReps.
         * 
         * - the node is state.goalRep and parentVector = null .
         ********************************************************************/
        NodeRepresentation parentNode = null;
        private Vector<NodeRepresentation> parentVector = null;

        Vector<NodeRepresentation> getParentVector() {
            return this.parentVector;
        }

        void setParentVector(Vector<NodeRepresentation> parentVector) {
            this.parentVector = parentVector;
        }

        /**
         * The two methods NodeRepresentation.nodeRepPath and
         * NewDecomposeProofHandler.pathToNodeRep() provide a means of
         * describing a NodeRepresentation object that identifies the "same"
         * object described by a DecompositionState or by a clone of it. They
         * are defined as follows:
         * 
         * The set NS of all NodeRepresentation objects is defined by:
         * 
         * - state.goal \in NS - \A i, j : state.assumeReps.elementAt(i) \in NS
         * - \A ns \in NS : \A i : ns.children.elementAt(i).elementAt(j) \in NS
         * 
         * For any ns \in NS, ns.nodePath() is a vector <<v0, ... , v2N>> of
         * Integers (for N >= 0) such that
         * 
         * ns = root.children.elementAt(vN-1).elementAt(vN-2)
         * .children.elementAt(vN-3).elementAt(vN-4) ...
         * .children.elementAt(1).elementAt(0)
         * 
         * where root == IF vN = -1 THEN this.goalRep ELSE
         * this.assumeReps.elementAt(vN)
         * 
         * For any vector V of Integers, there exists ns \in NS such that V =
         * ns.nodeRepPath(), then pathToNodeRep(V) = ns.
         * 
         * nodeRepPath is defined below. pathToNodeRep is a method in the outer
         * NewDecomposeProofHandler class.
         * 
         * @return
         */
        Vector<Integer> nodeRepPath() {
            Vector<Integer> result = new Vector<Integer>();
            NodeRepresentation currNR = this;
            while (currNR.parentNode != null) {
                int idx1 = currNR.getParentIndex();
                result.addElement(new Integer(idx1));
                Vector<NodeRepresentation> parVec = currNR.getParentVector();
                currNR = currNR.parentNode;
                Vector<Vector<NodeRepresentation>> childs = currNR.children;
                boolean notFound = true;
                int idx2 = 0;
                while (notFound && (idx2 < childs.size())) {
                    if (childs.elementAt(idx2) == parVec) {
                        notFound = false;
                    } else {
                        idx2++;
                    }
                }

                if (notFound) {
                    MessageDialog.openError(UIHelper.getShellProvider()
                            .getShell(), "Decompose Proof Command",
                            "An error that should not happen has occurred in "
                                    + "line 5208 of NewDecomposeProofHandler.");
                    return null;
                }

                result.addElement(new Integer(idx2));

            }

            if (currNR.getParentVector() == null) {
                result.addElement(new Integer(-1));
            } else {
                result.addElement(new Integer(currNR.getParentIndex()));
            }

            return result;
        }

        /**
         * If parentVector is non-null, then the current node equals
         * parentVector.elementAt(getParentIndex()). If parentVector is null,
         * then getParentIndex() equals -l.
         * 
         * @return
         */
        int getParentIndex() {
            if (getParentVector() == null) {
                return -1;
            }
            for (int i = 0; i < getParentVector().size(); i++) {
                if (this == getParentVector().elementAt(i)) {
                    return i;
                }
            }
            return -2; // this shouldn't happen
        }

           // State information about this clause.

        /**
         * True iff this is a NEW assumption that was not in the original
         * obligation, or it is an ExprNode that was created by splitting the
         * goal or by doing an AND-split on an assumption.  Its only function
         * in the displayContextAssump() method, where it causes a node
         * created by an /\ split to be displayed even if the user has
         * unchecked the "Show Context" option.
         */
        boolean isCreated = false;
        
        /**
         * Despite the name, this is the step name of the assumption from
         * which this assumption came, whether it is a context assumption
         * or an assumption from the step being decomposed.  However,
         * it is null if this NodeRepresentation is the goal, or an assumption
         * that came by decomposing the node.  It is also null if it comes from
         * an unnamed step (one with only a level number).
         */
        String contextStepName ;
        
        /**
         * True iff this NodeRepresentation came from a (sub)formula of the goal.
         */
        boolean fromGoal = false ;
        
        /**
         * True iff this NodeRepresentation came from decomposing a \E .
         */
        boolean fromExists = false ;
        /**
         * The names of operators whose definitions were expanded to produce this
         * NodeRepresentation.
         */
        StringSet fromDefs = new StringSet();
        
        /**
         * True iff this is a NEW node that is to be displayed on the same line
         * as the next node, which is also a NEW node. For nodes that come from
         * the step, this is true iff this and the next node are NEW nodes that
         * all appear entirely on the same line. For added NEW nodes, it will be
         * true iff:
         * 
         * - The NEW statement fits on a single line (meaning that it is NOT of
         * the form NEW x \in S where S is a multi-line formula)
         * 
         * - It and the next node come from the same \A or \E, as in the NEW x
         * and NEW y from \A x, y : ...
         * 
         * A sequence of same-line NEWs will not all be put on the same line in
         * the proof if its width plus proofIndent is greater than the
         * module-editor right margin preference, which is obtained with
         * 
         * Activator.getDefault().getPreferenceStore().getInt(
         * EditorPreferencePage.EDITOR_RIGHT_MARGIN);
         */
        boolean onSameLineAsNext = false;

        /**
         * True iff the formula represented by this node has an implicit prime
         * that does not appear in the semanticNode or nodeText fields.
         */
        boolean isPrimed = false;

        /**
         * If this is true, then the semanticNode field represents the expansion
         * of the subexpression name that appears in the nodeText field. This
         * means that the node has been obtained by decomposing another node by
         * expanding a definition, so no further decomposition by expanding a
         * definition is possible. (Using a subexpression name, it's impossible
         * to name the result of expanding a definition unless it's a LET
         * definition inside the current definition. I'm not sure what should be
         * done with LET definitions inside assumptions or goals.)
         */
        boolean isSubexpressionName = false;

        /**
         * Non-null iff the node can be decomposed as indicated by the
         * Decomposition object.
         */
        Decomposition decomposition = null;

        /**
         * Create a NodeRepresentation for a subnode of this node.
         * 
         * @param sn
         *            The subnode
         * @param vec
         *            The result's parentVector field.
         * @param father
         *            The result's parentNode field.
         * @param setNodeText
         *            If non-null, then the result's nodeText field is to be set
         *            to this rather than the NodeTextRep representation of the
         *            semanticNode field. It will be non-null if the nodeText is
         *            to be set to a subexpression name, so set
         *            isSubexpressionName field true in that case.
         * @param decomp
         *            The Decomposition from which the identifier renamings for
         *            the result's decomposition field are to be obtained.
         * 
         * @param isAssumption
         *            True iff this is an assumption, rather than the goal,
         *            whose NodeRepresentation is being constructed.
         *            
         * @return
         */
        NodeRepresentation subNodeRep(SemanticNode sn,
                Vector<NodeRepresentation> vec, NodeRepresentation father,
                NodeTextRep setNodeText, Decomposition decomp, boolean isAssumption) {

            NodeRepresentation result = new NodeRepresentation();
            result.parentNode = father;
            result.setParentVector(vec);
            result.semanticNode = sn;

            // Set the fields of the result that are inherited from the node
            // it's a subnode of.
            result.isPrimed = this.isPrimed;
            result.isSubexpressionName = this.isSubexpressionName;

            // If the original node came from splitting the
            // goal, then this node also came from splitting the
            // goal.
            result.isCreated = this.isCreated;

            NodeTextRep nodeTextRep = setNodeText;
            if (nodeTextRep == null) {
                nodeTextRep = this.subNodeText(sn);
            } else {
                result.isSubexpressionName = true;
            }
            result.nodeText = nodeTextRep.nodeText;
            result.mapping = nodeTextRep.mapping;

            /*
             * Compute the type, subType, and decomposition fields.
             */
            switch (sn.getKind()) {
            case ASTConstants.OpApplKind:
                result.nodeType = EXPR_NODE;

                result.decomposition = decompose(result, decomp, isAssumption);
                if (result.decomposition == null) {
                    result.nodeSubtype = OTHER_TYPE;
                } else {
                    result.nodeSubtype = result.decomposition.type;
                }
                break;
            case ASTConstants.NewSymbKind:
                result.nodeType = NEW_NODE;
                NewSymbNode newNode = (NewSymbNode) sn;
                result.newId = newNode.getOpDeclNode().getName().toString();
                break;
            case ASTConstants.LeafProofKind:
                result.nodeType = PROOF_NODE;
                break;
            default:
                result.nodeType = OTHER_NODE;
            }

            return result;
        }

        /**
         * This is like subNodeRep except it returns only the fields contained
         * in a NodeText. It is called by subNodeRep to set those fields.
         * 
         * @param sn
         * @return
         */
        NodeTextRep subNodeText(SemanticNode sn) {
            NodeTextRep result = new NodeTextRep();
            // result.semanticNode = sn ;
            // set beginId to be the index in this.nodeText representing the
            // first line of the source of SemanticNode node sn.
            int beginIdx = getBeginLine(sn) - getBeginLine(this.semanticNode);
            result.nodeText = new String[getEndLine(sn) - getBeginLine(sn) + 1];
            result.mapping = new Vector[result.nodeText.length];
            // Set beginCol to the column of the first token of sn.
            // Set beginPos to the position of the first token of sn in the
            // string
            // this.result.nodeText[beginLine - 1] containing its text.
            int beginCol = sn.stn.getLocation().beginColumn();
            int beginPos = colToLoc(beginCol, this.mapping[beginIdx]);

            /*
             * Set the nodeText and mapping fields.
             */
            // Set result.nodeText[0] to the string containing the first
            // token and everything to its right in this.nodeText[...].
            // Set result.mapping[0] to the MappingVector obtained by
            // subtracting beginPos from all increments.
            result.nodeText[0] = this.nodeText[beginIdx].substring(beginPos);
            Vector<MappingPair> mv = cloneMappingPairVector(this.mapping[beginIdx]);
            // Since we just removed beginPos characters to the left of
            // beginCol, we should execute
            adjustMappingPairVector(beginCol, -beginPos, mv);

            result.mapping[0] = mv;

            // Set result.nodeText[i] to a copy of this.nodeText[i+...]
            // and result.mapping[i] to a copy of this.mapping[i] for
            // all other lines of the subnode's text.
            // Set minPos = the minimum of beginPos and the smallest number
            // of leading spaces of any subsequent line of result.nodeText.
            // However, we need to ignore lines consisting of only spaces.
            int minPos = beginPos;
            for (int i = 1; i < result.mapping.length; i++) {
                result.nodeText[i] = this.nodeText[i + beginIdx];
                if (!StringHelper.onlySpaces(result.nodeText[i])) {
                    minPos = Math.min(minPos,
                            StringHelper.leadingSpaces(result.nodeText[i]));
                }
                result.mapping[i] = new Vector<MappingPair>();
                for (int j = 0; j < this.mapping[i + beginIdx].size(); j++) {
                    result.mapping[i].add(this.mapping[i + beginIdx].elementAt(
                            j).clone());
                }
            }

            // Remove the part of the last line of result.nodeText that doesn't
            // belong to the subnode
            result.nodeText[result.nodeText.length - 1] = result.nodeText[result.nodeText.length - 1]
                    .substring(
                            0,
                            colToLoc(sn.stn.getLocation().endColumn() + 1,
                                    result.mapping[result.mapping.length - 1]));

            // Add any necessary space at the beginning of result.nodeText[0]
            int spacesAddedToFirstLine = beginPos - minPos;
            result.nodeText[0] = StringHelper.copyString(" ",
                    spacesAddedToFirstLine) + result.nodeText[0];
            // Since we now have added spacesAddedToFirstLine, we execute
            adjustMappingPairVector(beginCol, spacesAddedToFirstLine,
                    result.mapping[0]);

            // Trim any necessary space from the beginning of result.nodeText[i]
            // for i > 0.
            for (int i = 1; i < result.nodeText.length; i++) {
                if (!StringHelper.onlySpaces(result.nodeText[i])) {
                    result.nodeText[i] = result.nodeText[i].substring(minPos);
                    adjustMappingPairVector(1, -minPos, result.mapping[i]);
                }
            }
            return result;
        }

        /**
         * If this.isPrimed is false, it just returns this.nodeText. Otherwise,
         * it returns the primed version of this.nodeText. It tries to be clever
         * and not put parentheses around the text if they're not needed.
         * Parentheses are not needed if isSubexpressionName is true, or if
         * primingNeedsParens(...) says they're not needed.
         */
        String[] primedNodeText() {
            if (!this.isPrimed) {
                return this.nodeText;
            }

            boolean needsParens = (!this.isSubexpressionName)
                    && primingNeedsParens(this.semanticNode);

            String[] result = this.nodeText.clone();
            if (needsParens) {
                result = prependToStringArray(result, "(");
                result[result.length - 1] = StringHelper
                        .trimEnd(result[result.length - 1]) + ")'";
            } else {
                result[result.length - 1] = StringHelper
                        .trimEnd(result[result.length - 1]) + "'";
            }
            return result;
        }

        /**
         * This constructor is used to construct a NodeRepresentation object for
         * the entire selected step and its leaf proof (if any), and for an
         * expanded definition body. It just sets the semanticNode, nodeText and
         * mapping fields.
         * 
         * @param document
         *            The document of the editor
         * @param node
         * @throws BadLocationException
         */
        NodeRepresentation(IDocument document, SemanticNode node)
                throws BadLocationException {
            this.semanticNode = node;
            Location location = node.stn.getLocation();
            nodeText = new String[location.endLine() - location.beginLine() + 1];
            mapping = new Vector[nodeText.length];
            for (int i = 0; i < mapping.length; i++) {
                mapping[i] = new Vector<MappingPair>();
                mapping[i].add(new MappingPair(1, -node.stn.getLocation()
                        .beginColumn()));
            }
            if (location.beginLine() == location.endLine()) {
                IRegion thmregion = EditorUtil.getRegionOf(document,
                        node.stn.getLocation());
                String str = document.get(thmregion.getOffset(),
                        thmregion.getLength());
                nodeText[0] = str;
                return;
            }

            IRegion region = document
                    .getLineInformation(location.beginLine() - 1);
            nodeText[0] = document.get(
                    region.getOffset() + location.beginColumn() - 1,
                    region.getLength() - location.beginColumn() + 1);
            // minCol is the min of the beginning column of the first line (with
            // the first column numbered 0) and the smallest number of leading
            // spaces of any later line. However, lines with no text
            // should be ignored.
            int minCol = location.beginColumn() - 1;
            for (int i = 1; i < nodeText.length; i++) {
                region = document.getLineInformation(location.beginLine() - 1
                        + i);
                nodeText[i] = document.get(region.getOffset(),
                        region.getLength());
                if (!StringHelper.onlySpaces(nodeText[i])) {
                    minCol = Math.min(minCol,
                            StringHelper.leadingSpaces(nodeText[i]));
                }
            }

            // remove the rest of the last line that's not part of the token's
            // text
            nodeText[nodeText.length - 1] = nodeText[nodeText.length - 1]
                    .substring(0, location.endColumn());

            // Add any necessary space at the beginning of nodeText[0]
            int spacesAddedToFirstLine = location.beginColumn() - minCol - 1;
            nodeText[0] = StringHelper.copyString(" ", spacesAddedToFirstLine)
                    + nodeText[0];
            mapping[0].elementAt(0).inc = -minCol - 1;

            // Trim any necessary space from the beginning of nodeText[i] for i
            // > 0. However, must check for the case of an empty line.
            for (int i = 1; i < nodeText.length; i++) {
                if (!StringHelper.onlySpaces(nodeText[i])) {
                    nodeText[i] = nodeText[i].substring(minCol);
                    mapping[i].elementAt(0).inc = -1 - minCol;
                }
            }
            return;
        }

        /**
         * Constructs an empty object
         */
        public NodeRepresentation() {
            // TODO Auto-generated constructor stub
        }

        /**
         * Make a deep clone of this NodeRepresentation object, with given
         * parent fields.
         * 
         * @param parNode
         *            The parentNode field of the cloned object.
         * @param parVector
         *            The parentVector field of the cloned object
         * @return
         */
        protected NodeRepresentation deepClone(NodeRepresentation parNode,
                Vector<NodeRepresentation> parVector) {
            NodeRepresentation result = new NodeRepresentation();

            result.semanticNode = this.semanticNode;

            // clone the nodeText field
            result.nodeText = new String[this.nodeText.length];
            for (int i = 0; i < result.nodeText.length; i++) {
                result.nodeText[i] = this.nodeText[i];
            }

            // clone the mapping field
            result.mapping = null;
            if (this.mapping != null) {
                result.mapping = this.mapping.clone();
                for (int i = 0; i < result.mapping.length; i++) {
                    result.mapping[i] = new Vector<MappingPair>();
                    for (int j = 0; j < this.mapping[i].size(); j++) {
                        result.mapping[i].add(this.mapping[i].elementAt(j));
                    }
                }
            }

            // recursively clone the children
            result.children = null;
            if (this.children != null) {
                result.children = new Vector<Vector<NodeRepresentation>>();
                for (int i = 0; i < this.children.size(); i++) {
                    Vector<NodeRepresentation> oldParVec = this.children
                            .elementAt(i);
                    Vector<NodeRepresentation> newParVec = new Vector<NodeRepresentation>();
                    for (int j = 0; j < oldParVec.size(); j++) {
                        newParVec.addElement(oldParVec.elementAt(j).deepClone(
                                result, newParVec));
                    }
                    result.children.addElement(newParVec);
                }
            }

            result.instantiationSubstitutions = this.instantiationSubstitutions.clone() ;
            result.instantiatedNamePrefix = this.instantiatedNamePrefix ;
            result.nodeType = this.nodeType;
            result.nodeSubtype = this.nodeSubtype;
            // result.stepName = this.stepName ;
            result.newId = this.newId;
            result.initialPosition = this.initialPosition;
            result.contextStepName = this.contextStepName;
            result.fromGoal = this.fromGoal;
            result.fromExists = this.fromExists ;
            result.parentNode = parNode;
            result.parentVector = parVector;
            result.isCreated = this.isCreated;
            result.onSameLineAsNext = this.onSameLineAsNext;
            result.isPrimed = this.isPrimed;
            result.isSubexpressionName = this.isSubexpressionName;

            result.fromDefs = this.fromDefs.clone() ;
            result.decomposition = null;
            if (this.decomposition != null) {
                result.decomposition = this.decomposition.clone();
            }

            // The following was added for testing. It should no longer be
            // necessary.
            // But if it fails, there's a serious bug, so we might as well keep
            // it.
            if (result.children != null) {
                for (int i = 0; i < result.children.size(); i++) {
                    Vector<NodeRepresentation> pvec = result.children
                            .elementAt(i);
                    for (int j = 0; j < pvec.size(); j++) {
                        NodeRepresentation nr = pvec.elementAt(j);
                        if (nr.parentNode != result || nr.parentVector != pvec) {
                            MessageDialog.openError(UIHelper.getShellProvider()
                                    .getShell(), "Decompose Proof Command",
                                    "An error that should not happen has occurred in "
                                            + "line 4310 of NewDecomposeProofHandler.");
                        }
                    }
                }
            }

            return result;
        }

        public String toString() {
            String val = "";
            // if (originalOperator != null) {
            // val = "Original Operator: " + originalOperator + "\n" ;
            // }
            val = val + "nodeText: |=\n" + stringArrayToString(nodeText) + "=|";
            for (int i = 0; i < mapping.length; i++) {
                val = val + "\n" + i + ":";
                for (int j = 0; j < mapping[i].size(); j++) {
                    val = val + "  " + mapping[i].elementAt(j).toString();
                }
            }

            return val;
        }

    }

    /**
     * This is the "inverse" of the method NodeRepresentation.nodeRepPath(). See
     * the comments for that method to understand what pathToNodeRep is doing.
     * 
     * @param vec
     *            Should be the result produced by a call of nodeRepPath().
     * @return Should be a NodeRepresentation nr such that nr.nodeRepPath() =
     *         vec.
     */
    NodeRepresentation pathToNodeRep(Vector<Integer> vec) {
        NodeRepresentation result = null;
        int i = vec.size() - 1;
        int idx = vec.elementAt(i).intValue();
        if (idx == -1) {
            return state.goalRep;
        }
        ;
        result = state.assumeReps.elementAt(idx);
        i--;
        while (i >= 0) {
            int idx1 = vec.elementAt(i).intValue();
            i--;
            int idx2 = vec.elementAt(i).intValue();
            result = result.children.elementAt(idx1).elementAt(idx2);
            i--;
        }
        return result;
    }

    /**
     * A NodeTextRep object contains only the nodeText, and mapping fields of a
     * NodeRepresentation object. I should probably refactor things so that
     * instead of having those two fields, a NodeRepresentation object contains
     * a NodeText field
     */
    static class NodeTextRep {
        // SemanticNode semanticNode = null ;
        String[] nodeText = null;
        Vector<MappingPair>[] mapping = null;

        public NodeTextRep(String[] text, Vector<MappingPair>[] map) {
            // semanticNode = node ;
            nodeText = text;
            mapping = map;
        }

        public NodeTextRep() {
            // TODO Auto-generated constructor stub
        }

        /**
         * Makes a deep copy of the NodeTextRep object.
         */
        public NodeTextRep clone() {
            NodeTextRep result = new NodeTextRep();
            result.nodeText = new String[this.nodeText.length];
            for (int i = 0; i < result.nodeText.length; i++) {
                result.nodeText[i] = this.nodeText[i];
            }
            result.mapping = null;
            if (this.mapping != null) {
                result.mapping = this.mapping.clone();
                for (int i = 0; i < result.mapping.length; i++) {
                    result.mapping[i] = new Vector<MappingPair>();
                    for (int j = 0; j < this.mapping[i].size(); j++) {
                        result.mapping[i].add(this.mapping[i].elementAt(j));
                    }
                }
            }
            return result;
        }

        public String toString() {
            String val = "";
            val = val + "nodeText: |=\n" + stringArrayToString(nodeText) + "=|";
            for (int i = 0; i < mapping.length; i++) {
                val = val + "\n" + i + ":";
                for (int j = 0; j < mapping[i].size(); j++) {
                    val = val + "  " + mapping[i].elementAt(j).toString();
                }
            }

            return val;
        }
    }

    /**
     * Returns a brand new NodeTextRep that's equal to the nodeRep argument
     * except that the String str has been appended to the last line.
     */
    static NodeTextRep appendToNodeText(NodeTextRep nodeRep, String str) {
        NodeTextRep result = nodeRep.clone();
        result.nodeText[result.nodeText.length - 1] = result.nodeText[result.nodeText.length - 1]
                + str;
        return result;
    }

    /**
     * Returns a brand new NodeTextRep that's equal to the nodeRep argument
     * except that the String str has been prepended to the first line and
     * subsequent lines have been indented to preserve the alignment with the
     * original first line.
     */
    static NodeTextRep prependToNodeText(NodeTextRep nodeRep, String str) {
        NodeTextRep result = nodeRep.clone();
        for (int i = 0; i < nodeRep.nodeText.length; i++) {
            if (i == 0) {
                result.nodeText[0] = str + result.nodeText[0];
            } else {
                result.nodeText[i] = StringHelper.copyString(" ", str.length())
                        + result.nodeText[i];
            }
            adjustMappingPairVector(1, str.length(), result.mapping[i]);
        }
        return result;
    }

    /**
     * Returns a new string array that's the same as `array' except that the
     * String str has been appended to the last line.
     */
    static String[] appendToStringArray(String[] array, String str) {
        String[] result = new String[array.length];
        for (int i = 0; i < result.length; i++) {
            result[i] = array[i];
        }
        result[result.length - 1] = array[result.length - 1] + str;
        return result;
    }

    /**
     * Returns a new string array that's the same as `array' except that the
     * String str has been prepended to the first line and subsequent lines have
     * added spaces to indent them to preserve the alignment with the original
     * first line.
     */
    static String[] prependToStringArray(String[] array, String str) {
        String[] result = new String[array.length];
        for (int i = 0; i < result.length; i++) {
            if (i == 0) {
                result[0] = str + array[0];
            } else {
                result[i] = StringHelper.copyString(" ", str.length())
                        + array[i];
            }
        }
        return result;
    }

    /**
     * Returns the concatenation of array1 and array2.
     */
    static String[] concatStringArrays(String[] array1, String[] array2) {
        String[] result = new String[array1.length + array2.length];
        for (int i = 0; i < array1.length; i++) {
            result[i] = array1[i];
        }
        for (int i = 0; i < array2.length; i++) {
            result[i + array1.length] = array2[i];
        }
        return result;
    }
    
    /**
     * returns the comma separated list obtained by concatening two
     * (possibly empty) comma separated lists.
     * 
     * @param str1
     * @param str2
     * @return
     */
    static String concatCommaSeparatedLists(String str1, String str2) {
        if (str1 == null || (str1.trim().equals(""))) {
            return str2 ;
        }
        String result = str1.trim();
        
        if (str2 == null || (str2.trim().equals(""))) {
            return result ;
        }
        
        return result + ", " + str2.trim();
    }

    /**
     * Returns a string containing a comma-separated list of the elements in the
     * set.
     */
    static String setOfStringsToList(Set<String> set) {
        String result = "";
        Iterator<String> iter = set.iterator();
        boolean first = true;
        while (iter.hasNext()) {
            if (first) {
                first = false;
            } else {
                result = result + ", ";
            }
            result = result + iter.next();
        }
        return result;
    }

    /**
     * A renaming object indicates that the name of each node
     * identifiers.elementAt(i) has been renamed to newNames.elementAt(i).
     * More generally, it indicates that instances of the node have
     * been replaced by the corresponding string, which may be an expression.
     * It is used both for recording the renaming of identifiers to 
     * avoid name clashes and the substitution of expressions for
     * module parameters in an instantiation.  (It does not seem to be
     * used to represent the substitution of arguments for operator-definition
     * expansion.)
     * 
     * @author lamport
     */
    private static class Renaming {
        Vector<FormalParamNode> identifiers = new Vector<FormalParamNode>();
        Vector<String> newNames = new Vector<String>();

        /**
         * Returns a new Renaming object whose fields are clones of this
         * object's fields (meaning that they are new Vector objects containing
         * the same elements).
         */
        public Renaming clone() {
            Renaming result = new Renaming();
            result.identifiers = (Vector<FormalParamNode>) this.identifiers
                    .clone();
            result.newNames = (Vector<String>) this.newNames.clone();
            return result;
        }
        
        public String toString() {
            String result = "[" ;
            for (int i=0; i < newNames.size(); i++) {
                if (i > 0) {
                    result = result + ", " ;
                } 
                result = result + identifiers.elementAt(i).getName() +
                           " <- " + "\"" + newNames.elementAt(i) + "\"" ;
            }
            return result + "]" ;
        }
    }

    /**
     * A Decomposition object describes the possible decomposition of an
     * assumption or goal.
     * 
     * @author lamport
     * 
     */
    static class Decomposition {
        /**
         * The type of decomposition. Its value is any of the first six possible
         * nodeSubtype values of a NodeRepresentation object. This is redundant
         * information, since for any NodeRepresentation object nd,
         * nd.nodeSubtype should equal nd.decomposition.type if nd.decomposition
         * is non-null.
         */
        int type;

        /**
         * If non-null, then the decomposition is to be performed by expanding
         * the definition of this (user-defined) symbol.
         */
        String definedOp = null;

        /**
         * If definedOp != null, so this decomposition is expanding a
         * definition, then formalParms[i] is the FormalParamNode of the i-th
         * formal parameter of the definition, argNodes[i] is the semantic node
         * of the i-th argument, and arguments[i] is its string representation,
         * which must appear on a single line.
         */
        FormalParamNode[] formalParams = null;
        String[] arguments = null;
        SemanticNode[] argNodes = null;

        /**
         * If non-null, then this is the NodeTextRep representing the operator
         * use that is to be expanded. E.g., it could represent source text such
         * as Bar(a + b, c) . If this decomposition is effected by the user with
         * the appropriate button push, then
         */
        NodeTextRep definedOpRep = null;

        /**
         * If definedOp != null, then `renaming' indicates the renaming of bound
         * identifiers that have been performed in the definition of definedOp
         * to avoid name clashes.  For example, if \E decomposition is performed
         * on the assumption  \E x : A \/ B , which results in renaming x
         * to x_1, then the decomposition.renaming field for the  A \/ B
         * node will record the renaming of the bound symbol x to x_1.
         */
        Renaming renaming = new Renaming();

        /**
         * If instantiationSubstitutionsD and instantiatedNamePrefixD
         * are non-null, then they are the values that the 
         * instantiationSubstitutions and instantiatedNamePrefix fields
         * should equal for the NodeRepresentations of the decomposition's
         * children.  If null, then those fields of the children should
         * be the same as the NodeRepresentation containing this
         * Decomposition.
         */
        Renaming instantiationSubstitutionsD = new Renaming() ;
        String   instantiatedNamePrefixD = "" ;

        /**
         * If definedOp is not null, then this is the name of the module
         * containing the node's definition.
         */
        String moduleName = null;

        /**
         * The nodes into which the assumption or goal is to be decomposed.
         */
        Vector<SemanticNode> children = new Vector<SemanticNode>();

        /**
         * If definedOp is the string "foo", then children.elementAt(i) has the
         * name "foo" + namePath.elementAt(i).
         * 
         */
        Vector<String> namePath = new Vector<String>();

        /**
         * If this is a \A or \E decomposition, then this is the list of bound
         * identifiers.
         */
        Vector<FormalParamNode> quantIds = null;

        /**
         * If this is a \A or \E decomposition for a bounded quantifier (like \A
         * x \in S), then this is the list of bound identifiers.
         */
        Vector<ExprNode> quantBounds = null;

        /**
         * If this is a \A or \E decomposition for a bounded quantifier (like \A
         * x \in S), then this is the list of subexpression names for each of
         * the elements of quantBounds.
         */
        Vector<String> quantBoundsubexpNames = null;

        /**
         * True iff the Decomposition's children and quantBounds should be
         * primed.
         */
        boolean primed = false;

        /**
         * This is a deep clone only in that it clones the renaming and
         * definedOpRep fields. The other fields are strings, semantic nodes,
         * and values, which are (effectively) immutable as far as the command
         * is concerned.
         * 
         * @return
         */
        public Decomposition clone() {
            Decomposition result = new Decomposition();

            result.definedOpRep = null;
            if (this.definedOpRep != null) {
                result.definedOpRep = this.definedOpRep.clone();
            }

            result.renaming = null;
            if (this.renaming != null) {
                result.renaming = this.renaming.clone();
            }
            
            result.instantiationSubstitutionsD =
                        this.instantiationSubstitutionsD.clone() ;
            result.instantiatedNamePrefixD = 
                        this.instantiatedNamePrefixD ;            
            result.type = this.type;
            result.definedOp = this.definedOp;
            result.formalParams = this.formalParams;
            result.arguments = this.arguments;
            result.argNodes = this.argNodes;
            result.moduleName = this.moduleName;
            result.children = this.children;
            result.namePath = this.namePath;
            result.quantIds = this.quantIds;
            result.quantBounds = this.quantBounds;
            result.quantBoundsubexpNames = this.quantBoundsubexpNames;
            result.primed = this.primed;
            return result;
        }

        public String toString() {
            String val = "type: " + nodeSubTypeToString(this.type);
            if (definedOp != null) {
                val = val + "\ndefinedOp: " + this.definedOp;
                val = val + "\ndefinedOpRep: " + definedOpRep.toString();
            }
            val = val + "\nmoduleName: " + this.moduleName;
            val = val + "\nchildren: ";
            for (int i = 0; i < this.children.size(); i++) {
                val = val + "\nchildren[" + i + "]:\n "
                        + children.elementAt(i).toString();
            }
            // val = val + "\nchildren: " + this.children.toString();
            val = val + "\nnamePath: " + this.namePath.toString();
            if (quantIds != null) {
                val = val + "\nquantIds: ";
                for (int i = 0; i < this.quantIds.size(); i++) {
                    if (i != 0) {
                        val = val + ", ";
                    }
                    val = val + quantIds.elementAt(i).getName().toString();
                }
            }
            if (quantBounds != null) {
                for (int i = 0; i < this.quantBounds.size(); i++) {
                    val = val + "\nquantBounds[" + i + "]:\n "
                            + quantBounds.elementAt(i).toString();
                }
                val = val + "quantBoundsubexpNames: ";
                for (int i = 0; i < this.quantBounds.size(); i++) {
                    val = val + ((i == 0) ? "" : ", ")
                            + quantBoundsubexpNames.elementAt(i);
                }

            }
            val = val + "\nprimed: " + primed;
            return val;
        }
    }

    /**
     * Adds to `result' all symbols in scope for NodeRepresentation `node' that
     * are defined or declared in the current step by NEW assumptions. It can be
     * called only when `node' is in this.state.assumeReps, is a descendant of a
     * node in this.state.assumeReps, or is the goal.
     * 
     * @param result
     * @param node
     */
    private void addDeclaredSymbols(StringSet result,
            NodeRepresentation node) {
        Vector<NodeRepresentation> parentVec = node.getParentVector();
        // node.parentVector = null iff node is the goal, the case we
        // handle by simply setting parentVec to state.assumeReps.
        if (parentVec == null) {
            parentVec = this.state.assumeReps;
        }

        int i = 0;
        while ((i < parentVec.size()) && (parentVec.elementAt(i) != node)) {
            NodeRepresentation parent = parentVec.elementAt(i);
            if (parent.nodeType == NodeRepresentation.NEW_NODE) {
                result.add(parent.newId);
            }
            i++;
        }

        // If this isn't a top-level assumption (or the goal), call the method
        // on
        // its parent.
        if (parentVec != this.state.assumeReps) {
            // If parentVec != null, then node.parentNode should be
            // non-null--but just in case
            if (node.parentNode != null) {
                addDeclaredSymbols(result, node.parentNode);
            } else {
                System.out
                        .println("Bug found in NewDecomposeProofHandler.addDeclaredSymbols.");
            }
        }
    }

    /**
     * Adds to `prevDeclared' all top-level NEW symbols that occur after the
     * position of NodeRepresentation `nodeRepArg' or its ancestor in
     * assumpReps. And, if includeGoal = true, to all bound symbols in the goal.
     * It can be called only when `nodeRepArg' is in this.state.assumeReps, is a
     * descendant of a node in this.state.assumeReps, or is the goal.
     * 
     * @param prevDeclared
     * @param nodeRepArg
     * @param includeGoal
     */
    private void addSymbolsDeclaredLater(StringSet prevDeclared,
            NodeRepresentation nodeRepArg, boolean includeGoal) {
        // Set assumpRepNode to the NodeRepresentation and
        // set idx to the number such that assumpRepNode equals
        // assumpReps.elementAt(idx) and either equals or is an
        // ancestor of nodeRepArg.
        NodeRepresentation assumpRepNode = nodeRepArg;
        while (assumpRepNode.parentNode != null) {
            assumpRepNode = assumpRepNode.parentNode;
        }
        int idx = 0;
        while ((idx < this.state.assumeReps.size())
                && (this.state.assumeReps.elementAt(idx) != assumpRepNode)) {
            idx++;
        }
        if (idx == this.state.assumeReps.size()) {
            // This should be the goal, so there are no later declarations.
            return;
        }

        // Add to prevDeclared the set of all top-level NEW identifiers that
        // follow
        // assumpRepNode in state.assumeReps together with all the bound
        // identifiers
        // in the goal.
        for (int i = idx + 1; i < state.assumeReps.size(); i++) {
            NodeRepresentation anode = state.assumeReps.elementAt(i);
            if (anode.nodeType == NodeRepresentation.NEW_NODE) {
                prevDeclared.add(anode.newId);
            }
        }

        if (includeGoal) {
            FormalParamNode[] goalIdents = ResourceHelper
                    .getBoundIdentifiers((ExprNode) this.state.goalRep.semanticNode);
            for (int i = 0; i < goalIdents.length; i++) {
                prevDeclared.add(goalIdents[i].getName().toString());
            }
        }
    }

    /**
     * Converts a NodeRepresentation subType to a string. Used for debugging.
     * 
     * @param subType
     * @return
     */
    public static String nodeSubTypeToString(int subType) {
        String val = "?";
        switch (subType) {
        case NodeRepresentation.AND_TYPE:
            val = "AND_TYPE";
            break;
        case NodeRepresentation.OR_TYPE:
            val = "OR_TYPE";
            break;
        case NodeRepresentation.IMPLIES_TYPE:
            val = "IMPLIES_TYPE";
            break;
        case NodeRepresentation.FORALL_TYPE:
            val = "FORALL_TYPE";
            break;
        case NodeRepresentation.EXISTS_TYPE:
            val = "EXISTS_TYPE";
            break;
        case NodeRepresentation.SQSUB_TYPE:
            val = "SQSUB_TYPE";
            break;
//        case NodeRepresentation.MULTI_TYPE:
//            val = "MULTI_TYPE";
//            break;
        case NodeRepresentation.OTHER_TYPE:
            val = "OTHER_TYPE";
            break;
        }
        return val;
    }

    /**
     * Returns the NodeRepresentation subtype for an OpApplNode whose operator
     * name is opId.
     * 
     * @param opId
     * @return
     */
    // private static int operatorNameToNodeSubtype(UniqueString opId) {
    // String opName = opId.toString();
    // if ((opId == ASTConstants.OP_cl) || opName.equals("\\land")) {
    // return NodeRepresentation.AND_TYPE;
    // } else if ((opId == ASTConstants.OP_dl) || opName.equals("\\lor")) {
    // return NodeRepresentation.OR_TYPE;
    // } else if (opName.equals("=>")) {
    // return NodeRepresentation.IMPLIES_TYPE;
    // } else if ((opId == ASTConstants.OP_bf) || (opId == ASTConstants.OP_uf))
    // {
    // return NodeRepresentation.FORALL_TYPE;
    // } else if ((opId == ASTConstants.OP_be) || (opId == ASTConstants.OP_ue))
    // {
    // return NodeRepresentation.EXISTS_TYPE;
    // } else if (opId == ASTConstants.OP_sa) {
    // return NodeRepresentation.SQSUB_TYPE;
    // } else {
    // return NodeRepresentation.OTHER_TYPE;
    // }
    // }

    /**
     * This computes the decompose field of a NodeRepresentation.
     * 
     * @param sn
     * @param decomp
     *            The Decomposition from which the initial identifier renamings
     *            of the result are obtained.
     * @return
     */
    private Decomposition decompose(NodeRepresentation nodeRep,
            Decomposition decomp, boolean isAssumption) {
        SemanticNode sn = nodeRep.semanticNode;
        if (!(sn instanceof OpApplNode)) {
            return null;
        }

        OpApplNode node = (OpApplNode) sn;
        OpApplNode unprimedNode = node;

        Decomposition result = new Decomposition();
        if (decomp != null) {
            result.renaming.identifiers = (Vector<FormalParamNode>) decomp.renaming.identifiers
                    .clone();
            result.renaming.newNames = (Vector<String>) decomp.renaming.newNames
                    .clone();
        }

        // Check if primed expression.
        if (node.getOperator().getName() == ASTConstants.OP_prime) {
            if (!(node.getArgs()[0] instanceof OpApplNode)) {
                return null;
            }
            node = (OpApplNode) node.getArgs()[0];
            unprimedNode = node;
            result.primed = true;
        }

        // If nodeRep.isSubexpressionName is false (so it was not obtained by
        // decomposing a definition using subexpression names), then we
        // see if this is an operator definition we can handle.
        if ((!nodeRep.isSubexpressionName)
                && (node.getOperator().getKind() == ASTConstants.UserDefinedOpKind)) {
            // This is a user-defined operator
            OpDefNode definition = (OpDefNode) node.getOperator();
            String operatorName = definition.getName().toString();
            ExprNode opDef = definition.getBody();
            // LL-XXXXX  The following must be enhanced to create the necessary
            // data structures to deal with substitution in instantiated formulas.
            // However, for now, let's get things to work in the case when
            // the definition doesn't contain any of the instantiated parameters.
            // (we are inside decompose(nodeRep, decomp, isAssumption))
            //
            while (opDef instanceof SubstInNode) {
               opDef = ((SubstInNode) opDef).getBody();
            }

            if (opDef instanceof OpApplNode) {
                // This is a user-defined operator. We can handle it iff
                // the arguments are all single-line expressions.
                ExprOrOpArgNode[] args = node.getArgs();
                for (int i = 0; i < args.length; i++) {
                    SyntaxTreeNode stn = (SyntaxTreeNode) args[i].stn;
                    Location stnLoc = stn.getLocation();
                    if (stnLoc.beginLine() != stnLoc.endLine()) {
                        return null;
                    }
                }
                node = (OpApplNode) opDef;

                // We now set the definedOp and definedOpRep fields
                // iff we want to use subexpression names.
                result.moduleName = ((SyntaxTreeNode) node.stn).getLocation()
                        .source();
                // The following test is to determine if the definition should
                // be expanded by subexpression naming or by actual expansion.
                // (Initially, we don't deal with expansion of names from
                // another module.)
                result.definedOp = operatorName;
                result.definedOpRep = nodeRep.subNodeText(unprimedNode);
                result.formalParams = definition.getParams();
                result.arguments = new String[result.formalParams.length];
                result.argNodes = unprimedNode.getArgs();

                for (int i = 0; i < result.arguments.length; i++) {
                    result.arguments[i] = stringArrayToString(nodeRep
                            .subNodeText(((OpApplNode) unprimedNode).getArgs()[i]).nodeText);
                }
            } else {
                // This means that the definition is not an OpApplNode, which
                // I don't think is possible.
                return null;
            }
        }

        // Indicate exactly how it needs to be decomposed by setting
        // the type field and also:
        // - setting isAndOrOr true iff this is an infix /\ or \/
        // - setting isJunction true iff this is a bulleted disjunction
        // or conjunction.
        // - setting isQuantifier true iff this is a \A or \E.
        // - setting isBoundedQuantifier iff isQuantifier true and it's
        // a boundedquantifier.
        // Return null if it can't be decomposed.
        boolean isAndOrOr = false;
        boolean isJunction = false;
        boolean isQuantifier = false;
        boolean isBoundedQuantifier = false;

        // First check if the OpApplNode's operator is a defined or built-in
        // operator. If not, we can't decompose so we return null.
        if (!(node.getOperator() instanceof OpDefNode)) {
            return null;
        }
        UniqueString opId = ((OpDefNode) node.getOperator()).getName();
        String opName = opId.toString();
        // Note: experimentation reveals that /\ and \/ are parsed
        // with operator names "\\land" and "\\lor".
        if (((opId == ASTConstants.OP_cl) || opName.equals("\\land"))
                && ( (! isAssumption) || conjIsDecomposable(node))) {
            result.type = NodeRepresentation.AND_TYPE;
            if (opId == ASTConstants.OP_cl) {
                isJunction = true;
            } else {
                isAndOrOr = true;
            }
        } else if ((opId == ASTConstants.OP_dl) || opName.equals("\\lor")) {
            result.type = NodeRepresentation.OR_TYPE;
            if (opId == ASTConstants.OP_dl) {
                isJunction = true;
            } else {
                isAndOrOr = true;
            }
        } else if (opName.equals("=>")) {
            result.type = NodeRepresentation.IMPLIES_TYPE;
        } else if ((opId == ASTConstants.OP_bf) || (opId == ASTConstants.OP_uf)) {
            result.type = NodeRepresentation.FORALL_TYPE;
            isQuantifier = true;
            if (opId == ASTConstants.OP_bf) {
                isBoundedQuantifier = true;
            }
        } else if ((opId == ASTConstants.OP_be) || (opId == ASTConstants.OP_ue)) {
            result.type = NodeRepresentation.EXISTS_TYPE;
            isQuantifier = true;
            if (opId == ASTConstants.OP_be) {
                isBoundedQuantifier = true;
            }
        } else if (opId == ASTConstants.OP_sa) {
            result.type = NodeRepresentation.SQSUB_TYPE;
        } else {
            return null;
        }

        /**
         * Now set result.children and result.namePath.
         */
        if (isAndOrOr) {
            processAndOrOr(result, node, "", opName);
        } else if (isJunction) {
            SemanticNode[] juncts = node.getArgs();
            for (int i = 0; i < juncts.length; i++) {
                result.children.add(juncts[i]);
                result.namePath.add("!" + (i + 1));
            }
        } else if (isQuantifier) {
            // There is just a single child. Set it, and
            // set namePath to its namePath entry.
            result.children.add(node.getArgs()[0]);
            String namePath = "!(";
            result.quantIds = new Vector<FormalParamNode>();
            if (isBoundedQuantifier) {
                // Bounded Quantifier
                result.quantBounds = new Vector<ExprNode>();
                result.quantBoundsubexpNames = new Vector<String>();
                FormalParamNode[][] quantIdsArray = node
                        .getBdedQuantSymbolLists();
                ExprNode[] quantBounds = node.getBdedQuantBounds();
                for (int i = 0; i < quantIdsArray.length; i++) {
                    // We don't handle a quantifier bound of the form <<x, y>>
                    // \in S
                    if (node.isBdedQuantATuple()[i]) {
                        return null;
                    }
                    FormalParamNode[] quantIds = quantIdsArray[i];
                    for (int j = 0; j < quantIds.length; j++) {
                        result.quantIds.add(quantIds[j]);
                        // Note that we have to repeat the quantifier bound
                        // for x and y in \E x, y \in S : ...
                        result.quantBounds.add(quantBounds[i]);
                        result.quantBoundsubexpNames.add("!" + (i + 1));
                        if (!((i == 0) && (j == 0))) {
                            namePath = namePath + ",";
                        }
                        namePath = namePath + quantIds[j].getName().toString();
                    }
                }
            } else {
                // Unbounded Quantifier
                FormalParamNode[] quantIds = node.getUnbdedQuantSymbols();
                for (int i = 0; i < quantIds.length; i++) {
                    result.quantIds.add(quantIds[i]);
                    if (i != 0) {
                        namePath = namePath + ",";
                    }
                    namePath = namePath + quantIds[i].getName().toString();
                }

            }
            namePath = namePath + ")";
            result.namePath.add(namePath);

        } else if ((result.type == NodeRepresentation.IMPLIES_TYPE)
                || (result.type == NodeRepresentation.SQSUB_TYPE)) {
            result.children.add(node.getArgs()[0]);
            result.namePath.add("!1");
            result.children.add(node.getArgs()[1]);
            result.namePath.add("!2");
        }
        // System.out.println("Decomposition");
        // System.out.println(result.toString());
        return result;
    }

    /**
     * This method ssumes node represents a conjunction (either infix or bulleted list).
     * Returns true iff one of the conjuncts is either
     *   - a \E  or 
     *   - a disjunction and this.state.splitChosen() = false 
     * or a conjunction c for which conjIsDecomposable(c) is true.
     * 
     * It assumes that a conjunct that is a SubstInNode is not decomposable.
     * This should be valid because
     * This will have to be changed to allow decomposition of formulas imported
     * by instantiation.  LL-XXXXXX
     * 
     * @param node
     * @param allowOr
     * @return
     */
    private boolean conjIsDecomposable(OpApplNode node) {
        ExprOrOpArgNode[] conjuncts = node.getArgs();
        for (int i = 0; i < conjuncts.length; i++) {
            // To be decomposable, the conjunct must be an OpApplNode
            if (conjuncts[i] instanceof OpApplNode) {
                OpApplNode curNode = (OpApplNode) conjuncts[i];

                // if this is a user-defined operator application
                // must examine its definition.
                if ((curNode.getOperator().getKind() == ASTConstants.UserDefinedOpKind)
                        && ((OpDefNode) curNode.getOperator()).getBody() instanceof OpApplNode) {
                    curNode = (OpApplNode) ((OpDefNode) curNode.getOperator())
                            .getBody();
                }

                if (curNode.getOperator() instanceof OpDefNode) {
                    UniqueString opId = ((OpDefNode) curNode.getOperator())
                            .getName();
                    String opName = opId.toString();

                    if (   (   (! this.state.splitChosen())
                            && (   (opId == ASTConstants.OP_dl)
                                || opName.equals("\\lor")
                                || (opId == ASTConstants.OP_sa)))
                        || (opId == ASTConstants.OP_be)
                        || (opId == ASTConstants.OP_ue)
                        || (    (   (opId == ASTConstants.OP_cl) 
                                 || opName.equals("\\land")) 
                             && conjIsDecomposable(curNode))) {
                        return true;
                    }
                }
            } // end if instanceof OpApplNode
        }

        return false;
    }

    /**
     * Assumes node represents a conjunction (either infix or bulleted list).
     * Returns true iff one of the conjuncts is a a \E, or a
     * conjunction c for which conjContainsExists(c) is true.
     * 
     * It assumes that a conjunct that is a SubstInNode is not decomposable.
     * This will have to be changed to allow decomposition of formulas imported
     * by instantiation.
     * 
     * Note: This method obtained by cloning conjIsDecomposable.  A sensible 
     * implementation of the Decompose Proof command would combine them into
     * a single method that returns the type of decomposition possible.
     * 
     * @param node
     * @return
     */
    private boolean conjContainsExists(OpApplNode node) {
        ExprOrOpArgNode[] conjuncts = node.getArgs();
        for (int i = 0; i < conjuncts.length; i++) {
            // To be decomposable, the conjunct must be an OpApplNode
            if (conjuncts[i] instanceof OpApplNode) {
                OpApplNode curNode = (OpApplNode) conjuncts[i];

                // if this is a user-defined operator application
                // must examine its definition.
                if ((curNode.getOperator().getKind() == ASTConstants.UserDefinedOpKind)
                        && ((OpDefNode) curNode.getOperator()).getBody() instanceof OpApplNode) {
                    curNode = (OpApplNode) ((OpDefNode) curNode.getOperator())
                            .getBody();
                }

                if (curNode.getOperator() instanceof OpDefNode) {
                    UniqueString opId = ((OpDefNode) curNode.getOperator())
                            .getName();
                    String opName = opId.toString();

                    if (   (opId == ASTConstants.OP_be)
                        || (opId == ASTConstants.OP_ue)
                        || (   (   (opId == ASTConstants.OP_cl) 
                                || opName.equals("\\land")) 
                            && conjContainsExists(curNode))) {
                        return true;
                    }
                }
            } // end if instanceof OpApplNode
        }

        return false;
    }

    /**
     * Recursive procedure to set the children and namePath fields of a
     * Decomposition object for an infix /\ or \/ . It is based on the
     * observation that A /\ B /\ C is parsed as (A /\ B) /\ C (and similarly
     * for \/). It does the obvious depth-first dive into the left operand,
     * adding the entire node if it's not an op operation.
     * 
     * @param decomp
     *            The Decomposition object whose fields are being set.
     * @param node
     *            The node being decomposed.
     * @param namePathPrefix
     *            The prefix to be prepended to the constructed namePath entry.
     * @param op
     *            either "\\lor" or "\\land".
     */
    private static void processAndOrOr(Decomposition decomp, SemanticNode node,
            String namePathPrefix, String op) {
        if (!(node instanceof OpApplNode)) {
            decomp.children.add(node);
            decomp.namePath.add(namePathPrefix);
            return;
        }
        OpApplNode aonode = (OpApplNode) node;
        SymbolNode sym = aonode.getOperator();
        UniqueString opId = null;
        String opName = null;
        if (sym instanceof OpDefNode) {
            opId = ((OpDefNode) sym).getName();
            opName = opId.toString();
        }
        if ((opName == null) || (!opName.equals(op))) {
            decomp.children.add(node);
            decomp.namePath.add(namePathPrefix);
            return;
        }
        // This is an op infix operation, so recurse.
        processAndOrOr(decomp, aonode.getArgs()[0], namePathPrefix + "!1", op);
        decomp.children.add(aonode.getArgs()[1]);
        decomp.namePath.add(namePathPrefix + "!2");
        return;
    }

    /********************* MappingPairs and their methods *******************************/
    /**
     * Note: If the Decompose Proof command ever gets recoded, it would probably
     * be a good idea to do away with MappingPairs and replace them with
     * Insertions. See the comments for the Insertion class below.
     * 
     * A MappingPair contains two int-valued fields : `col' and `inc'.
     * 
     * A line-mapping is a mapping from column-numbers in a line of the
     * specification to positions in a string. It is represented by a vector V
     * of MappingPair objects such that V[0].col = 1 and i < j implies V[i].col
     * < V[j].col. Such an array represents the line-mapping M such that M(c)
     * equals c plus the sum of all V[i].inc such that V[i].col <= c.
     * 
     * Suppose NTR is a NodeTextRep that represents the text of a SemanticNode
     * SN after some substitutions for identifiers have been performed. Then
     * NTR.mapping[i] is the mapping M from character locations in the (i+1)st
     * line of the source text of SN (locations start at 1) to the corresponding
     * character position (starting from 0) in the string NTR.nodeText[i]. The
     * value of M(c) is the obvious position in the string if c is the location
     * of any character in the original source that does not lie within an
     * identifier that has been substituted for, or if c is the location of the
     * first character of an identifier that has been substituted for. Hence,
     * the restriction of M to all such character locations is monotone. If
     * character location c+i lies within an identifier starting at location c
     * that has been substituted for, then M(c+i) = M(c) + i. This implies that
     * M is not monotone on all character locations in the source if the string
     * substituted for an identifier has fewer characters than the identifier.
     * 
     * In order to preserve essential alignments after substitutions, it seems
     * to be necessary to understand how a vector V of MappingPair objects that
     * represents a line mapping is constructed. If V is a line mapping for a
     * line in a NodeTextRep for a source SemanticNode SN,
     * 
     * 
     * @author lamport
     * 
     */
    private static class MappingPair {
        int col;
        int inc;

        MappingPair(int c, int p) {
            col = c;
            inc = p;
        }

        public NewDecomposeProofHandler.MappingPair clone() {
            return new MappingPair(this.col, this.inc);

        }

        public String toString() {
            return "<" + col + ", " + inc + ">";
        }
    }

    /**
     * Returns the string position to which the line-mapping defined by
     * MappingPair vec maps the column col.
     * 
     * @param col
     * @param vec
     * @return
     */
    private int colToLoc(int col, Vector<MappingPair> vec) {
        int loc = col;
        for (int i = 0; (i < vec.size()) && (vec.elementAt(i).col <= col); i++) {
            loc = loc + vec.elementAt(i).inc;
        }
        return loc;
    }

    /**
     * Modify vec so the line mapping nl it represents is related to the
     * original line mapping ol by nl[c] = IF c < col THEN ol[c] ELSE ol[c] +
     * incr
     * 
     * @param col
     * @param incr
     * @param vec
     * @return
     */
    private static void adjustMappingPairVector(int col, int incr,
            Vector<MappingPair> vec) {
        // set i to the smallest value such that vec[i].col >= col, or i =
        // vec.size() if
        // there is none.
        int i;
        for (i = 0; (i < vec.size()) && (vec.elementAt(i).col < col); i++) {
        }

        if (i == vec.size()) {
            vec.add(new MappingPair(col, incr));
        } else if (vec.elementAt(i).col == col) {
            vec.elementAt(i).inc = vec.elementAt(i).inc + incr;
        } else {
            vec.insertElementAt(new MappingPair(col, incr), i);
        }
    }

    /**
     * Returns a vector the same length as vec whose elements are clones of the
     * elements of vec.
     * 
     * @param vec
     * @return
     */
    private static Vector<MappingPair> cloneMappingPairVector(
            Vector<MappingPair> vec) {
        Vector<MappingPair> result = new Vector<NewDecomposeProofHandler.MappingPair>();
        for (int i = 0; i < vec.size(); i++) {
            result.add(vec.elementAt(i).clone());
        }
        return result;
    }

    /************************* Insertions and their methods ***************************/
    /**
     * An Insertion object o represents the modification of a string in which a
     * sequence of o.oldLen characters at string position o.pos (counting from
     * 0) is replaced by a sequence of o.newLen characters. The position
     * newInsertPos(p, o) in the modified string corresponding to position p in
     * the original string is defined by
     * 
     * newInsertPos(p, o) == CASE p =< o.pos -> p [] o.pos < p < o.pos +
     * o.oldLen -> IF o.newLen = 1 THEN o.pos ELSE some value in
     * (o.pos+1)..(o.pos + o.newLen - 1) [] o.pos + o.oldLen =
     * < p * ->
     * p + (o.newLen - o.oldLen)
     * 
     * A sequence s of Insertion objects represents a sequence of such
     * modifications. The position newVecInsertPos(p, s) in the modified string
     * corresponding to the position p in the original string is defined by
     * 
     * newVecInsertPos(p, s) == IF s = << >> THEN p ELSE
     * newVecInsertPos(newInsertPos(p, Head(p)), Tail(p))
     * 
     * Insertions and these operations are used to preserve significant
     * indentation in TLA+ formulas after substitution. More precisely, suppose
     * L1 is a line and L0 is the line above L1 and closest to it such that the
     * position of the first non-blank character of L0 is =< the position of the
     * first non-blank character of L1. Suppose L0' and L1' are obtained from L0
     * and L1 by insertions described by the vectors V0 and V1. If p is the
     * position of the first non-blank character in L1, then
     * 
     * newVecInsertPos(p, V0) - newVecInsertPos(p, V1)
     * 
     * space characters must be added to the beginning of L1 to preserve the
     * indentation. (Adding negative characters means deletion.)
     * 
     * In this application, modifications are represented by vectors of
     * non-overlapping insertions. Thus, the non-deterministic choice in the
     * evaluation of newInsertPos occurs at most once in the evaluation of
     * newVecInsertPos.
     * 
     * Line mappings can be defined in terms of Insertion vectors as well by
     * MappingPair vectors. Insertions contain more information than
     * MappingPairs, which is why I had to introduce them. It would probably
     * have been better to use Insertions instead of MappingPairs from the
     * beginning. However, I don't feel like rewriting the code that uses them.
     * 
     * @author lamport
     * 
     */
    private static class Insertion {
        int pos;
        int oldLen;
        int newLen;

        /**
         * The obvious constructor.
         */
        private Insertion(int pos, int oldLen, int newLen) {
            this.pos = pos;
            this.oldLen = oldLen;
            this.newLen = newLen;
        }

        public String toString() {
            return "[pos: " + pos + ", oldLen: " + oldLen + ", newLen: "
                    + newLen + "]";
        }
    }

    /**
     * The new position corresponding to old position oldPos after the insertion
     * ins. See comments for the Insertion class.
     * 
     * @param oldPos
     * @param ins
     * @return
     */
    static int newInsertPos(int oldPos, Insertion ins) {
        if (oldPos <= ins.pos) {
            return oldPos;
        }
        if (oldPos < ins.pos + ins.oldLen) {
            // oldPos lies inside the text that was replaced.
            if (oldPos < ins.pos + ins.newLen) {
                // if oldPos lies inside the replacing text, return its value.
                return oldPos;
            } else {
                // if oldPos isn't inside the replacing text, then we have to
                // move it left. We might as well minimize indentation by moving
                // it as far left as we can without making it align with ins.pos
                // (which it didn't do initially).
                return ins.pos + ins.newLen - ins.oldLen;
            }
        } else {
            // oldPos is to the right of the replacing text.
            return oldPos + ins.newLen - ins.oldLen;
        }

    }

    /**
     * The new position corresponding to old position oldPos after the sequence
     * vec of insertions. See comments for the Insertion class.
     * 
     * @param oldPos
     * @param ins
     * @return
     */
    static int newVecInsertPos(int oldPos, Vector<Insertion> vec) {
        return innerNewVecInsertPos(oldPos, 0, vec);
    }

    /**
     * The recursive procedure that evaluates newVecInsertPos(oldPos, v) where v
     * is the vector of elements vec[idx], vec[idx+1], ...
     * 
     * @param oldPos
     * @param idx
     * @param vec
     * @return
     */
    static int innerNewVecInsertPos(int oldPos, int idx, Vector<Insertion> vec) {
        if (vec.size() <= idx) {
            return oldPos;
        } else {
            return innerNewVecInsertPos(
                    newInsertPos(oldPos, vec.elementAt(idx)), idx + 1, vec);
        }
    }

    /**
     * This method assumes that newTextRep was obtained from oldTextRep by
     * substitutions as are described by insVecArray, where insVecArray[i]
     * describes the changes that produced newTextRep.nodeText[i] from
     * oldTextRep.nodeText[i]. (The arrays newTextRep.nodeText,
     * oldTextRep.nodeText, and insVecArray must have the same length.) It
     * modifies newTextRep.mapping by adding and/or removing leading blanks to
     * maintain any alignment necessary to preserve the meaning of the formula.
     * This requires modifying newTextRep.mapping as well as
     * newTextRep.nodeText. I think there are just two essential kinds of
     * alignment that must be preserved.
     * 
     * - If a /\ or \/ that begins a line L1 is part of a con/disjunction list
     * beginning on line L0, then the /\ or \/ beginning L1 must remain aligned
     * with the corresponding /\ or \/ on L0.
     * 
     * - If a token t that begins a line L1 is part of a con/disjunction-list
     * item started by a /\ or \/ on line L0, then t must remain to the right of
     * that /\ or \/.
     * 
     * Here is the what the method does.
     * 
     * LET startingPos[i] == The position of the 1st non-blank character of
     * oldTextRep.node[i], or -1 if there is none. coveringLine[i] == LET S ==
     * {j \in 0..(i-1) : startingPos[j] \leq startingPos[i]} IN IF S = {} \/
     * startingPos[i] = -1 THEN -1 ELSE Maximum S newStartingPos[i] == IF
     * coveringLine[i] = -1 THEN startingPos[i] ELSE
     * newVecInsertPos(startingPos[i], insVecArray[coveringLine[i]]) addSpace[i]
     * == newStartingPos[i] - startingPos[i] ; For each i, add addSpace[i]
     * spaces to line i of newTextRep. (Adding a negative number of spaces means
     * deletion.)
     * 
     * @param oldTextRep
     * @param newTextRep
     * @param insVecArray
     */
    static void adjustIndentation(NodeTextRep oldTextRep,
            NodeTextRep newTextRep, Vector<Insertion>[] insVecArray) {
        int numOfLines = insVecArray.length;
        int[] startingPos = new int[numOfLines];

        for (int i = 0; i < numOfLines; i++) {
            // compute startingPos[i]
            String str = oldTextRep.nodeText[i];
            startingPos[i] = StringHelper.leadingSpaces(str);
            if (startingPos[i] == str.length()) {
                startingPos[i] = -1;
            }

            // compute coveringLine[i]
            int coveringLine;
            if (startingPos[i] == -1) {
                coveringLine = -1;
            } else {
                int j = i - 1;
                while ((j >= 0)
                        && ((startingPos[j] > startingPos[i]) || (startingPos[j] == -1))) {
                    j--;
                }
                coveringLine = j;
            }

            // Compute addSpace[i]
            int addSpace;
            if (coveringLine == -1) {
                addSpace = 0;
            } else {
                addSpace = newVecInsertPos(startingPos[i],
                        insVecArray[coveringLine]) - startingPos[i];
            }

            // Add or remove space
            str = newTextRep.nodeText[i];
            if (addSpace > 0) {
                newTextRep.nodeText[i] = StringHelper.copyString(" ", addSpace)
                        + str;
            } else if (addSpace < 0) {
                newTextRep.nodeText[i] = str.substring(-addSpace);
            }
            adjustMappingPairVector(1, addSpace, newTextRep.mapping[i]);
        }
    }

    /******************** Some Methods for String Arrays *****************************/
    /**
     * Returns the array of strings as a single string, with the obvious
     * line-breaks inserted.
     * 
     * @param A
     * @return
     */
    public static String stringArrayToString(String[] A) {
        if (A.length == 0) {
            return A[0];
        }
        String result = A[0];
        for (int i = 1; i < A.length; i++) {
            result = result + "\n" + A[i];
        }
        return result;
    }

    /**
     * Returns the array of strings as a single string, where the first line is
     * inserted at column indent (Java numbering, columns starting at 0).
     * 
     * @param A
     * @param indent
     * @return
     */
    public static String stringArrayToIndentedString(String[] A, int indent) {
        if (A.length == 0) {
            return A[0];
        }
        String result = A[0];
        for (int i = 1; i < A.length; i++) {
            result = result + "\n" + StringHelper.copyString(" ", indent)
                    + A[i];
        }
        return result;
    }

    /*
     * The following are the types of buttons in the window
     */
    public static final int MENU = 1;
    public static final int ACTION = 2;
    public static final int CHECK = 3;

    /*
     * The followingidentify the various menu buttons.
     */
    public static final int SHOW_CONTEXT_BUTTON = 3;
    public static final int PROVE_BUTTON = 2;
    public static final int BACK_BUTTON = 1;
    public static final int TEST_BUTTON = 99;

    /**
     * Used to set various parameters of a button
     * 
     * @param button
     * @param type
     *            The style type of the button.
     * @param text
     *            The button's text
     */
    private void setupMenuButton(Button button, int whichOne, String text) {
        button.addSelectionListener(new DecomposeProofButtonListener(this,
                new Integer(whichOne), MENU));
        // Image folderImg =
        // PlatformUI.getWorkbench().getSharedImages().getImage(ISharedImages.IMG_LCL_LINKTO_HELP);
        // String foo = ISharedImages.IMG_LCL_LINKTO_HELP ;
        // button.setImage(folderImg);
        button.setText(text);
        // button.setSize(100, button.getSize().y);
        GridData gridData = new GridData();
        gridData.horizontalIndent = 5;
        button.setLayoutData(gridData);
    }

    private void setupCheckButton(Button button, String text) {
        // There doesn't seem to be a need to set a listener on a checkbutton;
        // It can be read when some action button is pushed.
        // button.addSelectionListener(new DecomposeProofButtonListener(this,
        // button, CHECK)) ;
        button.setText(text);
        // button.setSize(100, button.getSize().y);
        GridData gridData = new GridData();
        gridData.horizontalIndent = 10;
        button.setLayoutData(gridData);
    }

    private void setupActionButton(Button button, NodeRepresentation nodeRep,
            String text) {
        button.setText(text);
        // button.setSize(30, button.getSize().y + 100);
        GridData gridData = new GridData();
        gridData.horizontalIndent = 15;
        gridData.verticalAlignment = SWT.TOP;
        button.setLayoutData(gridData);
        // Change made by LL for NewDecomposeProofHandler on 21 Aug 2014:
        // nodeRep.nodeRepPath() instead of nodeRep is the object
        // that is attached to the button, and whose value is in
        // DecomposeProofButtonListener.object when
        // DecomposeProofButtonListener.widgetSelected is executed as the
        // result of clicking on the button.
        button.addSelectionListener(new DecomposeProofButtonListener(this,
                nodeRep.nodeRepPath(), ACTION));
        button.setFont(JFaceResources.getFontRegistry().get(
                JFaceResources.TEXT_FONT));
        if (text.equals("  ")) {
            button.setEnabled(false);
        }
    }

    /**
     * The listener for buttons on the DecomposeProof window. The button type
     * tells what to do when clicked. Data identifying the button or what it
     * should do is in the object fiel.
     * 
     * @author lamport
     * 
     */
    public class DecomposeProofButtonListener extends SelectionAdapter
            implements SelectionListener {

        public Object execute(ExecutionEvent event) throws ExecutionException {
            // TODO Auto-generated method stub
            return null;
        }

        NewDecomposeProofHandler decomposeHandler;
        int type;
        Object object;

        public DecomposeProofButtonListener(NewDecomposeProofHandler dHandler,
                Object but, int tp) {
            super();
            decomposeHandler = dHandler;
            type = tp;
            object = but;
        }

        /**
         * Sent when selection occurs in the control. The default behavior is to
         * do nothing.
         * 
         * @param e
         *            an event containing information about the selection
         */
        public void widgetSelected(SelectionEvent e) {
            readButtons();
            switch (type) {
            case MENU:
                // System.out.println("MENU Click");
                int buttonId = ((Integer) object).intValue();
                switch (buttonId) {
                case BACK_BUTTON:
                    state = state.previousState;
                    raiseWindow();
                    break;
                case PROVE_BUTTON:
                    makeProof(null, false, true);
                    break;
                case SHOW_CONTEXT_BUTTON:
                    System.out.println("button is " + showContextButton.getSelection()) ;
                    readButtons();
                    raiseWindow();
                    break;
                case TEST_BUTTON:
                    windowShell = decomposeHandler.windowShell;
                    decomposeHandler.location = windowShell.getLocation();
                    windowShell.close();
                    if (windowShell != null) {
                        if (windowShell.isDisposed()) {
                            System.out.println("closing disposes of window");
                        } else {
                            windowShell.dispose();
                        }
                        if (windowShell == null) {
                            System.out.println("Closing nullifies");
                        }
                    }
                    raiseWindow();
                    break;
                }
                break;
            case ACTION:
                // Clone the current state
                DecompositionState newState = state.clone();
                newState.previousState = state;
                state = newState;
                state.hasChanged = true;
                NodeRepresentation nodeObj = pathToNodeRep((Vector<Integer>) object);
                // NodeRepresentation samenodeObj =
                // pathToNodeRep(nodeObj.nodeRepPath()) ;
                // if (nodeObj == samenodeObj) {
                // System.out.println("cool, man") ;
                // } else {
                // System.out.println( nodeObj.toString() + "\n doesn't equal\n"
                // +
                // samenodeObj.toString()) ;
                //
                // }
                if (nodeObj.nodeType == NodeRepresentation.OR_DECOMP) {
                    decomposeHandler.caseAction(nodeObj);
                    // this is the action that produces an or-split proof.
                } else {
                    switch (nodeObj.nodeSubtype) {
                    case NodeRepresentation.AND_TYPE:
                        decomposeHandler.andAction(nodeObj);
                        break;
                    case NodeRepresentation.OR_TYPE:
                        decomposeHandler.orAction(nodeObj);
                        break;
                    case NodeRepresentation.IMPLIES_TYPE:
                        decomposeHandler.impliesAction(nodeObj);
                        break;
                    case NodeRepresentation.FORALL_TYPE:
                        decomposeHandler.forAllAction(nodeObj);
                        break;
                    case NodeRepresentation.EXISTS_TYPE:
                        decomposeHandler.existsAction(nodeObj);
                        break;
                    case NodeRepresentation.SQSUB_TYPE:
                        decomposeHandler.sqsubAction(nodeObj);
                        break;
                    case NodeRepresentation.OTHER_TYPE:
                        break;
                    }
                }

                break;
            }
        }

        /**
         * Sent when default selection occurs in the control. The default
         * behavior is to do nothing.
         * 
         * @param e
         *            an event containing information about the default
         *            selection
         */
        public void widgetDefaultSelected(SelectionEvent e) {
            // System.out.println("widgetDefaultSelected called") ;
            widgetSelected(e);

        }

    }

    /**
     * This is a DisposeListener for the window that sets the editor to be
     * writable and sets the handler's `location' * field to the window's
     * current location, so it opens in the same place the next time the command
     * is issued.
     * 
     * @author lamport
     * 
     */
    class WindowDisposeListener implements DisposeListener {
        NewDecomposeProofHandler commandHandler;

        WindowDisposeListener(NewDecomposeProofHandler handler) {
            commandHandler = handler;

        }

        public void widgetDisposed(DisposeEvent e) {
            commandHandler.location = windowShell.getLocation();
            // The following method was deprecated because it was actually
            // possible to use it, so it had to be replaced by something
            // that requires a PhD in Eclipse to figure out how to use.
            commandHandler.editorIFile.setReadOnly(false);
        }
    }
    
// UP-DOWN ARROWS REMOVED
//    /**
//     * Listener for arrows to move /\ conjunctions up or down.
//     * 
//     * @author lamport
//     *
//     */
//    class ArrowSelectionListener implements SelectionListener {
//        int index;
//        int direction;
//        NewDecomposeProofHandler handler;
//
//        ArrowSelectionListener(int idx, int dir, NewDecomposeProofHandler han) {
//            index = idx;
//            direction = dir;
//            handler = han;
//        }
//
//        public void widgetSelected(SelectionEvent e) {
//
//            // Clone the current state, so can go back from an arrow operation.
//            DecompositionState newState = state.clone();
//            newState.previousState = state;
//            state = newState;
//
//            // SemanticNode node = handler.assumes.elementAt(index);
//            NodeRepresentation rep = handler.state.assumeReps.elementAt(index);
//            // handler.assumes.remove(index) ;
//            handler.state.assumeReps.remove(index);
//            int inc = (direction == SWT.DOWN) ? 1 : -1;
//            // handler.assumes.add(index + inc, node) ;
//            handler.state.assumeReps.add(index + inc, rep);
//            handler.raiseWindow();
//        }
//
//        public void widgetDefaultSelected(SelectionEvent e) {
//            widgetSelected(e);
//        }
//
//    }

    /**
     * A convenience method that returns the first line of a semantic node's
     * source in a module. I don't know what to do if the semantic node is
     * constructed and has no source.
     * 
     * @param nd
     * @return
     */
    static int getBeginLine(SemanticNode nd) {
        if (nd.stn == null) {
            System.out
                    .println("getBeginLine called on node with null stn field.");
            return -1;
        }
        return nd.stn.getLocation().beginLine();
    }

    /**
     * A convenience method that returns the first line of a semantic node's
     * source in a module. I don't know what to do if the semantic node is
     * constructed and has no source.
     * 
     * @param nd
     * @return
     */
    static int getEndLine(SemanticNode nd) {
        if (nd.stn == null) {
            System.out
                    .println("getEndLine called on node with null stn field.");
            return -1;
        }
        return nd.stn.getLocation().endLine();
    }

    /**
     * If nd is a step of a proof--that is, it is an element of the array
     * returned by NonLeafProofNode.getSteps()--then this returns the level
     * number of the proof, which is the i such that the step begins "<i>". A
     * little experimentation reveals that the parser turns "<+>" or "<*>" in
     * the source into "<i>" for the appropriate i.
     * 
     * This method must not be called if nd is a DefStepNode or InstanceNode,
     * since for an unnumbered step (which such a step is likely to be), there
     * is no way to find the level number. See the comments to the one place
     * where this method is called.
     * 
     * @param nd
     * @return
     */
    static int stepLevel(SemanticNode nd) {
        String stepStr = ((SyntaxTreeNode) nd.stn).getHeirs()[0].image
                .toString();
        String stepNum = stepStr.substring(stepStr.indexOf('<') + 1,
                stepStr.indexOf('>'));
        return Integer.valueOf(stepNum).intValue();
    }

    /**
     * Returns true if it may be necessary to put parentheses around the
     * expression represented by `node' in order to prime it. This is the case
     * if node is an OpApplNode whose operator is NOT a user-defined operator
     * with an identifier as its name (so it returns truen if the operator is
     * not in/prep/postfix) or if it's an OpApplNode with no arguments.
     * 
     * @param node
     * @return
     */
    static boolean primingNeedsParens(SemanticNode node) {
        if (!(node instanceof OpApplNode)) {
            return false;
        }
        if (((OpApplNode) node).getArgs().length == 0) {
            return false;
        }
        SymbolNode ops = ((OpApplNode) node).getOperator();
        if (ops instanceof OpDefNode) {
            OpDefNode odn = (OpDefNode) ops;
            return (odn.getKind() == ASTConstants.BuiltInKind)
                    || !StringHelper.isIdentifier(odn.getName().toString());
        } else {
            return false;
        }
    }

    /**
     * Returns true iff some module of the spec is unsaved. Code taken from
     * UIHelper.promptUserForDirtyModules. This is not optimal because it
     * returns true even if the dirty module is not a spec module, but that's
     * not worth worrying about.
     * 
     * @return
     */
    public boolean existDirtyModules() {
        final List<IEditorReference> dirtyEditors = new LinkedList<IEditorReference>();
        IEditorReference[] references = UIHelper.getActivePage()
                .getEditorReferences();
        if (references != null) {
            for (int i = 0; i < references.length; i++) {
                try {
                    if (references[i].isDirty()
                            && references[i].getEditorInput().getName()
                                    .endsWith(".tla")) {
                        dirtyEditors.add(references[i]);
                    }
                } catch (PartInitException e) {
                    Activator.getDefault().logError(
                            "Error getting unsaved resources.", e);
                }
            }
        }

        return (dirtyEditors.size() > 0);

    }
    
}

/**********************************
 * The following module provides a number of random test cases for the Decompose
 * Proof command.
 * 
 * ----------------- MODULE Test ------------------ EXTENDS Integers, TLAPS
 * 
 * Q3(a, b) == \E x \in Int : (x = a) /\ (x = b) Q2(a, b) == \E x \in Int : ((x
 * = a) /\ (x = b)) \/ Q3(a, b+1) Q1(a, b) == \E x \in Int : ((x = a) /\ (x =
 * b)) \/ Q2(a, b+1) THEOREM TT == \A y \in Int : Q1(y, 1) => (y = 1) \/ (y = 2)
 * \/ (y = 3)
 * 
 * THEOREM ASSUME NEW y \in Int, Q1(y, 1) PROVE (y = 1) \/ (y = 2) \/ (y = 3)
 * 
 * R3(b, a) == a = 3 \/ a = b R2(b, a) == a = 2 \/ \E x \in {b, a} : R3(x, a+1)
 * R1(a) == a = 1 \/ \E x \in {a} : R2(x, a+1) THEOREM TT2 == \A y \in {1, 2, 3}
 * : R1(y) => (y = 1)
 * 
 * VARIABLES A, B, C, D, E, F
 * 
 * T3 == \E x : D \/ E T2 == (C /\ A /\ T3) T1 == B /\ T2 THEOREM T1 => A /\ B
 * /\ C
 * 
 * S1 == A \/ (\E x \in {y_1 \in {44} : y_1 > 0} : x \in {44}) S1a == A \/ (\A x
 * \in {y_1 \in {44} : y_1 > 0} : x \in {44}) S1b == A \/ ({y_1 \in {44} : y_1 >
 * 0} = {x \in {44} : x > 0}) THEOREM ASSUME NEW x , NEW y_1, S1b PROVE \A x_1 :
 * FALSE
 * 
 * S2 == \E x \in {y \in {44} : y > 0} : x \in {44} S2a == \E x \in {y \in {44}
 * : y > 0} : x \in {44} S2b == \E x \in {y \in {44} : y > 0} : x \in {44}
 * THEOREM ASSUME NEW x, NEW y, S2, S2a, S2b, A \/ B PROVE FALSE
 * 
 * S4 == \E x \in {y \in {44} : y > 0} : x \in {44} S3 == (\E x \in {y \in {44}
 * : y > 0} : x \in {44}) \/ S4 THEOREM ASSUME NEW x, NEW y, NEW y_1, S3 PROVE
 * FALSE
 * 
 * U1 == \A x \in {y \in {44} : y > 0} : (x > 0) /\ A THEOREM ASSUME NEW x , NEW
 * y PROVE U1
 * 
 * U2 == \E x : A \/ \E x_1 : x = x_1 THEOREM ASSUME NEW x, U2 PROVE FALSE
 * 
 * THEOREM ASSUME \E x \in {1} : TRUE, A \/ \E x : FALSE PROVE \A x : TRUE
 * 
 * W3(a, b) == \E x : <<a, b>> \/ (x=1) W2(a) == \E x : W3(a, x) W1 == \E x :
 * W2(x) THEOREM W1 => \A x : FALSE
 * 
 * C3 == \E x : (x=2) \/ (x=3) C2 == \E x : \E y : C3 THEOREM (\E x : C2) =>
 * FALSE
 * 
 * C5(y) == y /\ (B \/ C) C4(x) == x /\ \E y : C5(y) /\ x THEOREM ASSUME NEW y,
 * (\E x : C4(x) /\ A) PROVE FALSE
 * 
 * C7(u, v) == \E y : <<u, v, y>> \/ (y=v) C6(a) == \E x : C7(a, x) THEOREM
 * C6(42) => FALSE
 * 
 * B2(a, b) == (a=1) \/ (b=1) B1(a) == \E y : B2(a, y) THEOREM (\E x : B1(x)) =>
 * FALSE
 * 
 * Bar(bb) == (bb \/ C) Foo(aaaa, bbbb) == Bar(aaaa) => bbbb \/ /\ aaaa
 * 
 * /\ bbbb => B
 * 
 * X(a, Op(_,_)) == \A x : Op(a, B) /\ a W(a) == (a \/ C) Z(a) == \E z \in {E} :
 * W(a) => \/ D \/ D
 * 
 * ABar(bb) == \E y , yy : (Z(C)
 * 
 * \/ D) AFoo(aaaa) == \E x : ( ABar(<<x, aaaa>>) ) THEOREM AFoo(44) => FALSE
 * 
 * Y == A \/ (Z(B) \/ D) AA == A BB == (\E yB, yBB \in {}, yBBB \in {} : B \/
 * (\E yC, yCCC : \E yCC : (C \/ (\E yD : D)))) ZZ == AA /\ BB ZZZ == A /\ (\E
 * yy : B)
 * 
 * THEOREM ZZ
 * 
 * THEOREM XYZ == ASSUME NEW AAAA , ZZ, NEW BBBB PROVE FALSE
 * 
 * THEOREM Y => FALSE
 * 
 * THEOREM ASSUME NEW ZZ1, NEW ZZ123456 PROVE Foo(ZZ1, ZZ123456)
 * 
 * CONSTANT Z77777 THEOREM Z(Z77777) => FALSE
 * 
 * THEOREM ASSUME A \/ B PROVE C
 * 
 * THEOREM ASSUME AFoo(F) PROVE FALSE
 * 
 * THEOREM ASSUME \E x : A \/ ABar(C) PROVE FALSE
 * 
 * 
 * THEOREM ASSUME Z(F) PROVE Foo(A, B)
 * 
 * THEOREM \A x \in 23 + 24 : A
 * 
 * THEOREM \A x \in 23 + 24, y \in E : A => Bar(11)
 * 
 * THEOREM X(22+33, Foo)
 * 
 * =====================================
 ************************************/


/*   The following module is a specification for code to enhance the 
     current module by allowing decomposition of operator applications
     whose arguments may span multiple lines.  It would replace the
     current method of performing substitions using MappingPair objects.


---------------------------- MODULE Substitution ----------------------------
(***************************************************************************)
(* This spec handles substitution under the assumption that when an        *)
(* expression e has been substituted for an identifier id, no later        *)
(* substitution will be performed within e.  However, one case arises in   *)
(* the Decompose Proof command in which this is not true: namely, when e   *)
(* itself is an identifier and a later substitution substitutes another    *)
(* identifier for it.  The NodeWithSubst object defined here is general    *)
(* enough to make that substitution easy to perform.  (Note that in this   *)
(* case, e lies on a single line.)                                         *)
(***************************************************************************)
(***************************************************************************)
(* A task that the DecomposeProof command must perform is to display to    *)
(* the user and insert into the spec formulas obtained from a formula F in *)
(* the spec by substituting expressions for identifiers.  One instance of  *)
(* this is replacing a formula Op(x+y+z) by the formula obtained from it   *)
(* by expanding the definition                                             *)
(*                                                                         *)
(*    Op(p) == expr                                                        *)
(*                                                                         *)
(* of Op.  This requires constructing a representation of the formula      *)
(* obtained from expr by substituting x+y+z for every instance of p in     *)
(* expr.  We write this substitution as p <- x+y+z.  However, note that p  *)
(* actually denotes a semantic node representing a declaration of the      *)
(* identifier "p", and the substitution is performed on an occurrence of   *)
(* that identifier that refers to that semantic node--not to any           *)
(* identifier "p" that that refers to a different semantic declaration     *)
(* node.                                                                   *)
(*                                                                         *)
(* Given the semantic node nd that represents expr, it's easy to construct *)
(* the semantic node produced by the substitution.  So, one way to perform *)
(* this task is to use a general procedure for "pretty-printing" a         *)
(* semantic node.  This is what TLAPS does.  However, our goal here is to  *)
(* maintain as much as possible the formatting of expr by the user.  So,   *)
(* this task will be performed by substituting the string "x+y+z" for all  *)
(* instances of the string "p" in the text of expr typed by the user.      *)
(* Those instances can be found using the semantic node nd for expr, from  *)
(* which all semantic nodes for instances of p can be found--since a       *)
(* semantic node points to the location of the user input corresponding to *)
(* that node.                                                              *)
(*                                                                         *)
(* This substitution task poses the following problems:                    *)
(*                                                                         *)
(* 1.  Suppose the definition of Op is                                     *)
(*                                                                         *)
(*     Op(p) == -p                                                         *)
(*                                                                         *)
(* Simply replacing "p" by "x+y+z" in the definition yields "-x+y+z"       *)
(* instead of the correct "-(x+y+z)".  We can solve this problem by always *)
(* putting parentheses around the expression being substituted, but it     *)
(* seems best to do this only when necessary.                              *)
(*                                                                         *)
(* 2.  Suppose now that expr is Op(x+y>z) and Op is defined by             *)
(*                                                                         *)
(*    Op(p) == p => /\ x=y                                                 *)
(*                  /\ y>4                                                 *)
(*                                                                         *)
(* Naive substitution would yield the expression                           *)
(*                                                                         *)
(*    x+y+z => /\ x=y                                                      *)
(*         /\ y>4                                                          *)
(*                                                                         *)
(* which is parsed as (x+y>z => /\ x=y) /\ (y>4), which is not equivalent  *)
(* to Op(x+y>z).                                                           *)
(*                                                                         *)
(* Another case in which substitution is needed is to avoid identifier     *)
(* conflict.  Suppose the expression `\A j : expr' is to be put into the   *)
(* spec in a location where the identifier j already has a meaning.  In    *)
(* that case j must be replaced as the quantifier variable and everywhere  *)
(* it occurs in expr by a new identifier.  (TLAPS uses a new identifier    *)
(* such as j_1, which seems like a good choice to use here.)               *)
(*                                                                         *)
(* Multiple substitutions may have to be done in an expression.  Clearly,  *)
(* if a operator has multiple arguments, or if both j and k have to be     *)
(* renamed in \A j, k : expr, then there will be substitutions for all the *)
(* arguments or all the renamed variables.  Such a multiple substitution   *)
(* poses no problem because in no matter what order the substitutions are  *)
(* done, the following is true:                                            *)
(*                                                                         *)
(*    Single-Substitution Property:  A substitution is never performed on  *)
(*    text that was inserted by a substitution.                            *)
(*                                                                         *)
(* However, this property is not true for all multiple substitutions--for  *)
(* example if we first perform the substitution p <- x+y+z and then the    *)
(* substitution y <- a-b in expr.  However, observe that the sequence of   *)
(* substitutions                                                           *)
(*                                                                         *)
(*    Substitute y <- a-b in Substitute p <- x+y>z in expr                 *)
(*                                                                         *)
(* is equivalent to the                                                    *)
(*                                                                         *)
(*    Substitute p <- x+(a-b)>z in Substitute y <- a-b in expr             *)
(*                                                                         *)
(* Those two substitutions satisfy the single-substitution property, no    *)
(* matter in which order they are performed because neither of the         *)
(* expressions being inserted by the substitutions contain either of the   *)
(* identifiers being substituted for.                                      *)
(*                                                                         *)
(* To maintain the single-substitution property, a sequences of            *)
(* substitutions                                                           *)
(*                                                                         *)
(*    Substitute p_1 <- exp_1 in Substitute p_2 <- exp_2 in                *)
(*        ...  p_n <- exp_n  Substitute expr                               *)
(*                                                                         *)
(* must satisfy the                                                        *)
(*                                                                         *)
(*    Hierarchical Substitution Property: The  p_i are all different, and  *)
(*    each p_j cannot occur in any expression exp_k with k < j.            *)
(*                                                                         *)
(* In that case, let                                                       *)
(*                                                                         *)
(*      xexp_1 == exp_1                                                    *)
(*      xexp_2 == Substitute p_1 <- xexp_1 in exp2                         *)
(*      xexp_3 == Substitute p_2 <- xexp_2                                 *)
(*                   in Substitute p_1 <- xexp_1 in exp_3                  *)
(*      ...                                                                *)
(*      xexp_n == Substitute p_(n-1) <- xexp_(n-1) in ... in exp_n         *)
(*                                                                         *)
(* and the result of the original sequence of substitutions is             *)
(*                                                                         *)
(*    Substitute p_1 <- xexp_1 in Substitute p_2 <- xexp_2 in              *)
(*        ...  p_n <- xexp_n  Substitute expr                              *)
(*                                                                         *)
(* The hierarchical substitution property implies that the substitutions   *)
(* in this sequence and all the substitutions in constructing the xexp_i   *)
(* satisfy the single-substitution property.                               *)
(*                                                                         *)
(* The hierarchical substitution property is maintained in the             *)
(* substitutions done by the DecomposeProof command for the following      *)
(* reason.  There are two types of substitutions performed:                *)
(*                                                                         *)
(* 1.  Replacing an operator use Op(e), where Op is defined by             *)
(*                                                                         *)
(*    Op(p) == expr                                                        *)
(*                                                                         *)
(* with the expression                                                     *)
(*                                                                         *)
(*    Substitute [p <- e] in expr                                          *)
(*                                                                         *)
(* This replacement is done only when Op(p) is the entire expression.      *)
(* Hence the expression cannot contain any identifiers declared in the     *)
(* resulting expression--or the parameters in the definitions of any any   *)
(* operator used in that expression.                                       *)
(*                                                                         *)
(* 2.  Replacing a declaration of an identifier in an expression by a      *)
(* brand new identifier.  This brand new identifier must be different from *)
(* (have a different semantic declaration node) than that of any           *)
(* identifier appearing in an expression that has already been substituted *)
(* for some identifier.                                                    *)
(***************************************************************************)

EXTENDS Integers, Sequences, FiniteSets, TLC

(***************************************************************************)
(* LOCATIONS.                                                              *)
(*                                                                         *)
(* A Location describes the line & column coordinates of the first and     *)
(* last characters of some semantic unit.  These coordinates are 1-based,  *)
(* the first line of a module being line 1 and the first column of a line  *)
(* being column 1.                                                         *)
(*                                                                         *)
(* A POSITION is a pair of positive integers representing line and column  *)
(* coordinates of a character.                                             *)
(***************************************************************************)
PosNat == Nat \ {0}

PairPrecedes(pair1, pair2) ==
  (*************************************************************************)
  (* True iff pair1 represents a position that precedes the position       *)
  (* represented by pair2.                                                 *)
  (*************************************************************************)
  \/ pair1[1] < pair2[1]
  \/ (pair1[1] = pair2[1]) /\ (pair1[1] < pair2[2])

PairPrecedesOrEq(pair1, pair2) == PairPrecedes(pair1, pair2) \/ (pair1 = pair2)

(***************************************************************************)
(* A Location is a record with fields:                                     *)
(*    bLine, bColumn : The position of the first character.                *)
(*    eLine, eColumn : The position of the last character.                 *)
(***************************************************************************)
Location == { loc \in [bLine : PosNat, bColumn : PosNat, 
                       eLine : PosNat, eColumn : PosNat] :
                PairPrecedesOrEq(<<loc.bLine, loc.bColumn>>, 
                                 <<loc.eLine, loc.eColumn>>) }

(***************************************************************************)
(* For some reason that I have forgotten, location loc1 is defined to      *)
(* precede location loc2 iff the end position of loc1 precedes OR EQUALS   *)
(* the beginning position of loc2.  In particular, a 1-character location  *)
(* precedes itself.                                                        *)
(***************************************************************************)
LocationPrecedes(loc1, loc2) == 
   PairPrecedesOrEq(<<loc1.eLine, loc1.eColumn>>, 
                    <<loc2.bLine, loc2.bColumn>>)

(***************************************************************************)
(* Note LocationContainedIn is defined so a location is contained in       *)
(* itself.                                                                 *)
(***************************************************************************)
LocationContainedIn(loc1, loc2) == 
  /\ PairPrecedesOrEq(<<loc2.bLine, loc2.bColumn>>, 
                      <<loc1.bLine, loc1.bColumn>>)
  /\ PairPrecedesOrEq(<<loc1.eLine, loc1.eColumn>>, 
                      <<loc2.bLine, loc2.bColumn>>)  

(***************************************************************************)
(* ++ is coordinate-wise addition of two positions.                        *)
(***************************************************************************)
pair1 ++ pair2 == <<pair1[1] + pair2[1], pair1[2] + pair2[2]>>

(***************************************************************************)
(* PosSum(f, i) == f[0] ++ f[1] ++ ...  ++ f[i] where                      *)
(* PosSum(f, -1) = <<0, 0>> .                                              *)
(***************************************************************************)
RECURSIVE PosSum(_, _)
PosSum(f, i) == IF i = -1 THEN <<0, 0>>
                          ELSE f[i] ++ PosSum(f, i-1)

(***************************************************************************)
(* We define the Max and Min of a set S of array indices, which will be    *)
(* non-negative integers.  Max of the empty set is defined to be -1; Min   *)
(* of the empty set is undefined.                                          *)
(***************************************************************************)
IndexMax(S) == IF S = {} THEN -1
                         ELSE CHOOSE x \in S : \A y \in S : x >= y
IndexMin(S) == CHOOSE x \in S : \A y \in S : x =< y

(***************************************************************************)
(* (Semantic) Nodes                                                        *)
(***************************************************************************)
IsSeq(s) == /\ Len(s) \in Nat
            /\ s = [i \in 1..Len(s) |-> s[i]]
  (*************************************************************************)
  (* True iff s is a sequence.                                             *)
  (*************************************************************************)

IsSeqOf(seq, IsElem(_)) ==
  (*************************************************************************)
  (* True iff seq is a sequence of elements e_i, with IsElem(e_i) true for *)
  (* all i.                                                                *)
  (*************************************************************************)
  /\ IsSeq(seq)
  /\ \A i \in 1..Len(seq) : IsElem(seq[i])

(***************************************************************************)
(* We define a JArray to be a function with domain 0..n for some integer   *)
(* n, which is the mathematical representation of a Java array.  We define *)
(* some operators on JArrays corresponding to operators on sequences.      *)
(* Note that an array of length 0 is the function whose domain is the      *)
(* empty set--the function that can be written << >>.                      *)
(***************************************************************************)
JArray(S) == {<< >>} \cup UNION {[0..n -> S] : n \in Nat}
JLen(A) == 1 + IndexMax(DOMAIN A)
JConcat(s, t) == [i \in 0 .. (JLen(s) + JLen(t)-1) |-> 
                    IF i < JLen(s) THEN s[i] ELSE t[i-JLen(s)]] 
JSubArray(A, m, n) ==
  (*************************************************************************)
  (* The JArray A[m], A[m+1], ...  , A[n].                                 *)
  (*************************************************************************)
  [i \in 0 .. n-m |-> A[i+m]]

IsJArray(A) == DOMAIN A = 0 .. IndexMax(DOMAIN A)

IsJArrayOf(A, S) == /\ IsJArray(A)
                    /\ \A x \in DOMAIN A : A[x] \in S

(***************************************************************************)
(* The operator StoJ maps from sequences to JArrays, and JtoS maps from    *)
(* JArrays to sequences.                                                   *)
(***************************************************************************)
StoJ(seq) == [i \in 0..(Len(seq)-1) |-> seq[i+1]]
JtoS(A) == [i \in 1..JLen(A) |-> A[i-1]]


(***************************************************************************)
(* Assume some set S of records, each element of which has a `children'    *)
(* field that is a sequence of elements of S called the node's children.   *)
(* The descendants of a node nd consists of it and its children and its    *)
(* children's children, and its children's children's children, etc.  The  *)
(* following defines Descendants(nd) to be the set of all descendants of   *)
(* nd.  Note that its possible for this set to be infinite if there is an  *)
(* infinite sequence seq of elements of S each of which is a child of the  *)
(* preceding one.  It's also possible for this set to be finite if there   *)
(* is such an infinite sequence seq--for example, if all the elements of   *)
(* the infinite sequence are the same.  To understand how this is          *)
(* possible, observe that if z is an infinite sequence of zeroes, then the *)
(* tail of z (obtained by removing the first zero in the sequence) equals  *)
(* z.                                                                      *)
(***************************************************************************)
Descendants(nd) ==
  LET RangeOfFcn(f) == {f[i] : i \in DOMAIN f}
      RECURSIVE D(_)
      D(n) == IF n.children = << >>
                   THEN {n}
                   ELSE {n} \cup
                          UNION {D(n.children[i]) 
                                   : i \in DOMAIN n.children}
  IN  D(nd)

(***************************************************************************)
(* Because TLC doesn't treat Strings as first-class sequences, we          *)
(* represent a String as an array of Chars, where a Char is a string of    *)
(* length 1.  Also, to simplify translation to Java, we use 0-based        *)
(* addressing of Chars in a String, and for vectors of Strings.  Note that *)
(* the empty string "" is the function whose domain is the empty set,      *)
(* which can be written as << >>.                                          *)
(***************************************************************************)
Char == {s \in STRING : Len(s) = 1}
String == UNION {[0..n -> Char] : n \in Nat \cup {-1}}
StringVector == UNION {[0..n -> String] : n \in Nat \cup {-1}}
IsString(s) == IsJArrayOf(s, Char)
IsStringVector(v) == /\ IsJArray(v)
                     /\ \A x \in DOMAIN v : IsString(v[x])

SpaceChar == " "
NSpaces(n) == [i \in 0..(n-1) |-> SpaceChar]

(***************************************************************************)
(* A node has nd has the following fields                                  *)
(*   uid : A unique number                                                 *)
(*   loc : A Location                                                      *)
(*   image : Like a StringVector, except its 0th line is numbered          *)
(*           nd.loc.bLine and its contents are the portion of the module   *)
(*           occupied by the text that produced the node.  (Enclosing      *)
(*           parentheses are not included in the image.                    *)
(*   children : The sequence of subnodes, ordered by their loc fields.     *)
(***************************************************************************)
RECURSIVE IsNode(_)
IsNode(nd) ==
   /\ nd = [uid |-> nd.uid, loc |-> nd.loc, image |-> nd.image, 
            children |-> nd.children]
   /\ /\ nd.uid \in Int
      /\ \A d1, d2 \in Descendants(nd) : (d1 # d2) => (d1.uid # d2.uid)
           \* uid's are unique.
   /\ nd.loc \in Location
   /\ /\ /\ DOMAIN nd.image = nd.loc.bLine .. nd.loc.eLine 
         /\ \A i \in DOMAIN nd.image : IsString(nd.image[i])
      /\ IF nd.loc.bLine = nd.loc.eLine 
           THEN JLen(nd.image[nd.loc.bLine]) = nd.loc.eColumn - nd.loc.bColumn + 1
           ELSE JLen(nd.image[nd.loc.eLine]) = nd.loc.eColumn
      /\ nd.image[nd.loc.bLine][1] # SpaceChar
      /\ nd.image[nd.loc.eLine][JLen(nd.image[nd.loc.eLine])-1] # SpaceChar
   /\ /\ IsSeqOf(nd.children, IsNode)
      /\ \A i \in DOMAIN nd.children :
            /\ LocationContainedIn(nd.children[i].loc, nd.loc)
            /\ (i = 1) => /\ nd.children[i].loc.bLine = nd.loc.bLine
                          /\ nd.children[i].loc.bColumn = nd.loc.bColumn
            /\ (i = Len(nd.children)) => /\ nd.children[i].loc.eLine = nd.loc.eLine
                                         /\ nd.children[i].loc.eColumn = nd.loc.eColumn
            /\ (i > 1) => LocationPrecedes(nd.children[i-1].loc, nd.children[i].loc)

IsIdentifier(nd) == /\ IsNode(nd)
                    /\ nd.children = << >>
                    /\ nd.loc.bLine = nd.loc.eLine           

(***************************************************************************)
(* A TLA+ semantic unit (such as an expression) will be represented (for   *)
(* display on the screen or insertion into a specification) by an array of *)
(* STRINGs, where the array is indexed by 0..i for some i in Nat.          *)
(***************************************************************************)

(***************************************************************************)
(* An insertion ins describes the replacement of a token node t, that is a *)
(* descendant of a semantic node nd, in the StringVector representing nd   *)
(* by a StringVector rep, where                                            *)
(*                                                                         *)
(*    ins.col = t.loc.bColumn                                              *)
(*    ins.oldLen = t.loc.eColumn - t.loc.bColumn + 1                       *)
(*    DOMAIN rep = 0..ins.linesAdded                                       *)
(*    newLen = JLen(rep[ins.linesAdded])                                   *)
(***************************************************************************)
Insertion == [col : Nat, oldLen : Nat, newLen : Nat, linesAdded : Nat]

(***************************************************************************)
(* A NodeWithSubst nws consists of the following fields                    *)
(*                                                                         *)
(*     node : Node -- The original node that was substituted into.         *)
(*                                                                         *)
(*     repr : StringVector -- The representation of the node after         *)
(*                            substitutions.                               *)
(*                                                                         *)
(*     startInc : Int \X Int --                                            *)
(*                  equals the pair <<ln, col>> such that                  *)
(*                    -- ln = -nws.node.loc.bLine                          *)
(*                    -- the position <<nws.node.loc.beginLine,            *)
(*                                      nws.node.loc.beginColumn>>         *)
(*                       in nws.node corresponds to nws.repr character     *)
(*                       nws.repr[0][nd.loc.beginColumn + col]             *)
(*                                                                         *)
(*     lineInc : JArray(Int \X Int) --                                     *)
(*                 -- JLen(nws.lineInc) equals                             *)
(*                       nws.node.loc.eLine - nws.loc.bLine + 1 and        *)
(*                 -- nws.lineInc[i] equals the pair <<ln, col>> such      *)
(*                    that the first descendant d of nws.node with         *)
(*                      d.loc.bLine + nws.startInc[1] = i                  *)
(*                   (or the expression substituted for d) begins in repr  *)
(*                   at character                                          *)
(*                     repr[i + lineInc[i][1]]                             *)
(*                            [d.loc.bColumn + lineInc[i][2]]              *)
(*                 Note that for each i \in DOMAIN lineInc,                *)
(*                   lines in                                              *)
(*                      (nws.lineInc[i] + 1)                               *)
(*                        .. (IF i+1 = JLen(lineInc)                       *)
(*                              THEN JLen(nws.repr) - 1                    *)
(*                              ELSE nws.lineInc[i+1] - 1)                 *)
(*                   consist of lines added to nws.node.image, where the   *)
(*                   last of those lines ends with tokens that were        *)
(*                   originally to the right of a replaced token that      *)
(*                   would have been on line nws.lineInc[i] had it not     *)
(*                   been replaced.                                        *)
(*                                                                         *)
(*     inserts : JArray(JArray(Insertion)) --                              *)
(*                  inserts[i] equals the Insertions that represent        *)
(*                  substitutions made to tokens t in                      *)
(*                  Descendants(nws.node) with                             *)
(*                     t.loc.bLine + startInc[1] = i                       *)
(*                  The elements ins of inserts[i] are ordered by ins.col. *)
(***************************************************************************)
IsNodeWithSubst(nws) ==
  /\ DOMAIN nws = {"node", "repr", "startInc", "lineInc", "inserts"}
  /\ IsNode(nws.node)
  /\ IsStringVector(nws.repr)
  /\ nws.startInc \in Int \X Int
  /\ IsJArrayOf(nws.lineInc, Int \X Int)
  /\ /\ IsJArray(nws.inserts)
     /\ \A x \in DOMAIN nws.inserts : IsJArrayOf(nws.inserts[x], Insertion)


LeadingSpaces(str) == 
  (*************************************************************************)
  (* The number of space characters at the beginning of String str.        *)
  (*************************************************************************)
  1 + IndexMax({i \in DOMAIN str : \A j \in 0..i : str[j] = SpaceChar})

AddSpaces(n, sv) ==
  (*************************************************************************)
  (* The String obtained by adding n SpaceChars to the beginning of String *)
  (* sv.  If n < 0, adding n Space characters means deleting -n            *)
  (* characters.                                                           *)
  (*************************************************************************) 
  [i \in 0..(JLen(sv)+n-1) |-> 
     IF n >= 0 THEN IF i < n THEN " " ELSE sv[i-n]
                             ELSE sv[i-n] ]
      
(***************************************************************************)
(* NodeToNodeWithSubst(nd) is the NodeWithSubst representing node nd after *)
(* no substitutions have been performed.                                   *)
(***************************************************************************)
NodeToNodeWithSubst(nd) == 
  LET Lines == 0..(nd.loc.eLine - nd.loc.bLine)
      image == [i \in Lines 
                       |-> IF i = 0 THEN AddSpaces(nd.loc.bColumn - 1, 
                                                   nd.image[nd.loc.bLine])
                                    ELSE nd.image[i + nd.loc.bLine]]
      BlankLines == {i \in Lines : \A j \in DOMAIN image[i] : image[i][j] = SpaceChar}
      trim == IndexMin({LeadingSpaces(image[i]) : i \in Lines \ BlankLines}) 
      trimVec(strVec) == [i \in 0..(JLen(strVec)-1-trim) |-> strVec[i+trim]]
      repr == [i \in Lines |-> IF i \in BlankLines THEN ""
                                                   ELSE trimVec(image[i])]
      
  IN  [node     |-> nd,
       repr     |-> repr,
       startInc |-> <<-nd.loc.bLine, -trim - 1>>,
       lineInc  |-> [j \in Lines |-> <<0, 0>>],
       inserts  |-> [j \in Lines |-> << >>] ]
  
(***************************************************************************)
(* ReprPos(pos, nws) is defined to be the pair <<i, j>> so that if nws is  *)
(* a NodeWithSubstitution and pos is a <<line number, column number>> pair *)
(* that represents a position in nws.node that does not lie within a token *)
(* that has been substituted for, then the character at position pos       *)
(* appears is at nws.repr[i][j].                                           *)
(***************************************************************************)
ReprPos(pos, nws) == 
   pos ++ nws.startInc
       ++ nws.lineInc[pos[1] + nws.startInc[1]]
       ++ LET inserts == nws.inserts[pos[1] + nws.startInc[1]]
              ipos == [i \in DOMAIN inserts |->
                        <<inserts[i].linesAdded,
                          inserts[i].newLen - inserts[i].oldLen>>]
          IN  PosSum(ipos,
                     IndexMax({i \in DOMAIN inserts :
                                inserts[i].col < pos[2]}))

(***************************************************************************)
(* The NodeWithSubstitution produced by replacing the token with Location  *)
(* tokLoc by the StringVector sVec in NodeWithSubstitution nws.  The       *)
(* expression in sVec is parenthesized iff parens = TRUE.                  *)
(***************************************************************************)
SubstForToken(tokLoc, sVec, nws, parens) == 
  LET (*********************************************************************)
      (* sV is sVec with parentheses added iff parens = TRUE               *)
      (*********************************************************************)
      sV == 
        (*******************************************************************)
        (* sVec with parentheses added iff parens = TRUE                   *)
        (*******************************************************************)
        IF parens
          THEN [[i \in DOMAIN sVec |->
                  [j \in 0..JLen(sVec[i]) |-> 
                     IF j = 0 THEN IF i = 0 THEN "(" ELSE " "
                              ELSE  sVec[i][j-1]]]
                  EXCEPT ![JLen(sVec)-1] = 
                             [j \in 0..JLen(@) |-> 
                                IF j = JLen(@) THEN ")" ELSE @[j]]]
          ELSE sVec
      insert == 
        (*******************************************************************)
        (* The Insertion describing the parameters of the substitution.    *)
        (*******************************************************************)
        [col        |-> tokLoc.bColumn, 
         oldLen     |-> tokLoc.eColumn - tokLoc.bColumn + 1,
         linesAdded |-> JLen(sV) - 1,
         newLen     |-> JLen(sV[JLen(sV) - 1])]

      beginPos == ReprPos(<<tokLoc.bLine, tokLoc.bColumn>>, nws)

      repr1 ==
        (*******************************************************************)
        (* nws.repr with the substitution of the first line of sV for the  *)
        (* token                                                           *)
        (*******************************************************************)
        [nws.repr EXCEPT 
           ![beginPos[1]] = 
              [i \in 0..(JLen(@)-1 + JLen(sV[0]) - insert.oldLen) |->
                 IF i < beginPos[2] THEN @[i]
                                    ELSE IF i < beginPos[2] + JLen(sV[0])
                                           THEN sV[0][i-beginPos[2]]
                                           ELSE @[i-JLen(sV[0])+insert.oldLen] ] ]                      

      repr2 ==
       (********************************************************************)
       (* repr2 with the substitutions made for the rest of the lines of   *)
       (* sV.                                                              *)
       (********************************************************************)
     IF JLen(sV) = 1 
       THEN repr1
       ELSE [i \in 0..(JLen(repr1) + JLen(sV) -2) |->
              CASE i < beginPos[1] -> repr1[i] 
                [] i = beginPos[1] -> 
                     JSubArray(repr1[i], 0, beginPos[2] + JLen(sV[0])-1)
                [] i \in (beginPos[1]+1) .. (beginPos[1] + JLen(sV)-2) ->
                     AddSpaces(beginPos[2], sV[i - beginPos[1]])   
                [] i = beginPos[1] + insert.linesAdded -> 
                        AddSpaces(beginPos[2], 
                                  JConcat(sV[JLen(sV)-1],
                                          JSubArray(repr1[beginPos[1]],
                                                    beginPos[2]+JLen(sV[0]),
                                                    JLen(repr1[beginPos[1]])-1)))
                [] OTHER ->  repr1[i-insert.linesAdded] ]
 
      affectedRepLines ==
        (*******************************************************************)
        (* The numbers of the contiguous set of lines in repr2 following   *)
        (* tokLoc's line that begin (have first non-space character) in    *)
        (* the same column or to the right of the first character in the   *)
        (* replaced token's representation in repr2.  These lines must be  *)
        (* shifted left or right to maintain the alignment if its tokens   *)
        (* with tokens that originally appeared to the right of the        *)
        (* replaced token.                                                 *)
        (*******************************************************************)
        {i \in (beginPos[1] + insert.linesAdded + 1) .. (JLen(repr2)-1) :
           \A j \in (beginPos[1] + insert.linesAdded + 1) .. i :
              LeadingSpaces(repr2[i]) >= beginPos[2]}

      repr ==
        (*******************************************************************)
        (* The repr component of the result, obtained by adding or         *)
        (* removing spaces to the lines of affectedRepLines.               *)
        (*******************************************************************)
        [i \in DOMAIN repr2 |->
           IF i \in affectedRepLines 
             THEN AddSpaces(insert.newLen - insert.oldLen, repr2[i])    
             ELSE repr2[i]]  
      
      insertIndex == tokLoc.bLine + nws.startInc[1]
        (*******************************************************************)
        (* The index in repr and lineInc at which the insertion is being   *)
        (* made.                                                           *)
        (*******************************************************************)
                 
      lineInc1 ==
        (*******************************************************************)
        (* nws.lineInc with line increments (first components) adjusted.   *)
        (*******************************************************************)
        [i \in DOMAIN nws.lineInc |->
           IF i =< insertIndex
             THEN nws.lineInc[i]
             ELSE [nws.lineInc[i] EXCEPT ![1] = @ + insert.linesAdded]]   

      affectedNodeLines ==
        (*******************************************************************)
        (* These are the numbers of lines in the domains of startInc and   *)
        (* lineInc that correspond to line numbers of repr that are in     *)
        (* affectedRepLines.                                               *)
        (*******************************************************************)
        {i \in DOMAIN lineInc1 :
          i + lineInc1[i][1] \in affectedRepLines}   
          
     lineInc ==
        (*******************************************************************)
        (* The lineInc component of the result, which equals lineInc1 with *)
        (* column increments (second components) adjusted to reflect the   *)
        (* spaces added or removed from lines in affectedNodeLines.        *)
        (*******************************************************************)
        [i \in DOMAIN lineInc1 |->
           IF i \in affectedNodeLines
             THEN [lineInc1[i] EXCEPT ![2] = @ + insert.newLen - insert.oldLen]
             ELSE lineInc1[i] ] 
     inserts ==
       (********************************************************************)
       (* The inserts component of the result, obtained by adding `insert' *)
       (* to nws.inserts[insertIndex].                                     *)
       (********************************************************************)
       LET ins == nws.inserts[insertIndex] \* nws.inserts[beginPos[1]]
           insertPos == IndexMax({i \in DOMAIN ins : ins[i].col < insert.col})
       IN  [i \in DOMAIN nws.inserts |->
             IF i = insertIndex 
               THEN [j \in 0 .. JLen(ins) |->
                      CASE j =< insertPos -> ins[j]
                        [] j = insertPos+1 -> insert     
                        [] OTHER -> ins[j-1] ] 
               ELSE nws.inserts[i]  ]
      
  IN [node     |-> nws.node,
      repr     |-> repr,
      startInc |-> nws.startInc,
      lineInc  |-> lineInc,
      inserts  |-> inserts]
----------------------------------------------------------------------------
(***************************************************************************)
(* Operators for writing test cases.                                       *)
(***************************************************************************)
(***************************************************************************)
(* S("abcd") is the String corresponding to "abcd".  SV(<<"abc", "def ",   *)
(* "g">>) is the StringVector corresponding to                             *)
(*     "abc\nde f\ng"                                                      *)
(***************************************************************************)
S(str) == 
  LET RECURSIVE seq(_)
      seq(s) == IF Len(s) = 0 THEN << >> ELSE <<SubSeq(s,1,1)>> \o seq(Tail(s))
  IN StoJ(seq(str))
SV(strSeq) == StoJ([i \in 1..Len(strSeq) |-> S(strSeq[i])])

JJtoSS(jaOfJa) == JtoS([i \in DOMAIN jaOfJa |-> JtoS(jaOfJa[i])])

(****************************************************************************
The expression bcd + ...  - hh in this "module"

   q == uu 
   foo == a + (bcdd + ef
                       g - hq) + ijk
   12345678901234567890123456789012345
****************************************************************************)
Module1 == SV(
<<
"q  == uu",
"foo == a + (bcdd + ef",
"                    g - hh) + ijk" >>)

node1 == 
 [uid |-> 1,
  loc |-> [bLine |-> 2, bColumn |-> 13, eLine |-> 3, eColumn |-> 25],
  image |-> 
  (2 :> S("bcdd + ef") @@ 3 :> 
        S("                    g - hh") ),
  children |-> << >>]

nws1 == NodeToNodeWithSubst(node1)
tokLoc1 == [bLine |-> 2, bColumn |-> 15, eLine |-> 2, eColumn |-> 16]
tokLoc1a == [bLine |-> 2, bColumn |-> 20, eLine |-> 2, eColumn |-> 20]
tokLoc1b == [bLine |-> 3, bColumn |-> 21, eLine |-> 3, eColumn |-> 21]
sub1 == SV(<<"xxx", "yyyy", "ZZZZZZ">>) \* for dd
sub1a == SV(<<"[222", "22]">>)   \* for e
sub1b == SV(<<"GGG", "GG">>)            \* for g

Subst1 == SubstForToken(tokLoc1, sub1, nws1, FALSE)
\*Subst1a == SubstForToken(tokLoc1a, sub1a, Subst1, FALSE)
\*Subst1b == SubstForToken(tokLoc1b, sub1b, Subst1a, FALSE)
Subst1b == SubstForToken(tokLoc1b, sub1b, Subst1, FALSE)
Subst1a == SubstForToken(tokLoc1a, sub1a, Subst1b, FALSE)
Result1x == JJtoSS(nws1.repr)
Result1 ==  JJtoSS(Subst1.repr)
Result1a ==  JJtoSS(Subst1a.repr)
Result1b ==  JJtoSS(Subst1b.repr)
(***************************************************************************)
(* The expression bcd + ...  - hh in this "module"                         *)
(*                                                                         *)
(*    q == uu                                                              *)
(*    foo == a + (bcd + ef - EF                                            *)
(*             g - hq) + ijk                                               *)
(*    123456789012345678901234567890                                       *)
(***************************************************************************)
Module2 == SV(
<<
"q  == uu",
"foo == a + (bcd + ef - EF",
"         g - hq) + ijk" >>)


node2 == 
 [uid |-> 1,
  loc |-> [bLine |-> 2, bColumn |-> 13, eLine |-> 3, eColumn |-> 15],
  image |-> 
  (2 :> S("bcd + ef - EF") @@ 3 :> S("         g - hq")),
  children |-> << >>]

nws2 == NodeToNodeWithSubst(node2)
tokLoc2 ==  [bLine |-> 2, bColumn |-> 19, eLine |-> 2, eColumn |-> 20] \* ef
tokLoc2b ==  [bLine |-> 2, bColumn |-> 13, eLine |-> 2, eColumn |-> 15] \*bcd

sub2a == SV(<<"x", "xxxx">>)
sub2b == SV(<<"Y","YYYY">>)
Subst2a == SubstForToken(tokLoc2, sub2a, nws2, FALSE)
Subst2b == SubstForToken(tokLoc2b, sub2b, Subst2a, FALSE)
Result2x == JJtoSS(nws2.repr)
Result2a == JJtoSS(Subst2a.repr)
Result2b == JJtoSS(Subst2b.repr)
(****************************************************************************
The expression b12345 + ...  - hh in this "module"

   q == uu 
   foo == a + (b12345 + ef
                    g - hq) + ijk
   12345678901234567890123456789012345
****************************************************************************)
Module3 == SV(
<<
"q  == uu",
"foo == a + (b12345 + ef",
"                 g - hh) + ijk" >>)

node3 == 
 [uid |-> 1,
  loc |-> [bLine |-> 2, bColumn |-> 13, eLine |-> 3, eColumn |-> 23],
  image |-> 
  (2 :> S("b12345 + ef") @@ 3 :> S("                 g - hq") ),
  children |-> << >>]

nws3 == NodeToNodeWithSubst(node3)
tokLoc3a == [bLine |-> 2, bColumn |-> 14, eLine |-> 2, eColumn |-> 18] \* 12345
tokLoc3b == [bLine |-> 2, bColumn |-> 22, eLine |-> 2, eColumn |-> 22] \* e
sub3a == SV(<<"XX", "XXXXX", "XXXXXXXXXXXX">>)
sub3b == SV(<<"YYYYY",  "YY">>)
\*Subst3a == SubstForToken(tokLoc3a, sub3a, nws3, TRUE)
\*Subst3b == SubstForToken(tokLoc3b, sub3b, Subst3a, TRUE)

Subst3b == SubstForToken(tokLoc3b, sub3b, nws3, FALSE)
Subst3a == SubstForToken(tokLoc3a, sub3a, Subst3b, FALSE)


Result3x == JJtoSS(nws3.repr)
Result3a == JJtoSS(Subst3a.repr)
Result3b == JJtoSS(Subst3b.repr)
=====

(***************************************************************************
NEED TO RECORD The mapping from coordinates in Node to 
coordinates in StringVector.
 ***************************************************************************)
RECURSIVE NTail(_, _)
NTail(n, seq) == IF n = 0 THEN seq ELSE NTail(n-1, Tail(seq))

StringVectorOfNode(nd) ==
  IF nd.loc.bLine = nd.loc.eLine
    THEN [i \in {0} |-> nd.image[nd.loc.bLine]]
    ELSE LET Lines == 0..(nd.loc.eLine - nd.loc.bLine)
             SVN == [i \in Lines 
                       |-> IF i = 0 THEN NSpaces(nd.loc.bColumn - 1) 
                                           \o nd.image[nd.loc.bLine]
                                    ELSE nd.image[i + nd.loc.bLine]]
             BlankLines == {i \in Lines : \A j \in 1..Len(SVN[i]) :
                                             SVN[i][j] = SpaceChar}
             LeadingSpaces(str) == SetMax({i \in DOMAIN str :
                                            \A j \in 1..i : str[j] = SpaceChar})
             trim == IndexMin({LeadingSpaces(SVN[i]) : i \in Lines \ BlankLines})   
         IN [i \in Lines |-> IF i \in BlankLines THEN ""
                                                 ELSE NTail(trim, SVN[i])]
        
=============================================================================
\* Modification History
\* Last modified Thu Aug 21 18:41:11 PDT 2014 by lamport
\* Created Fri Jul 04 17:30:53 PDT 2014 by lamport

*/