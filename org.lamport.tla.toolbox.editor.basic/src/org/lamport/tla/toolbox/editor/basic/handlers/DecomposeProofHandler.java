/**
 * Currently, this command is under construction and is not bound to the proper key or menu.
 * Instead, it is executed by typing Ctl+Shift+A.
 * 
 * A single object of this class is created and attached to the command.  Multiple
 * executions of the command use the same object, so data can be stored as (non-static)
 * fields of the object between executions of the command.
 * 
 */

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

    (A, B_1, C |= P) \/ ... \/ (A, B_n, C |= P)

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
A, H |= C by expanding definitions D_1, ...  , D_k.

Suppose that A, H |= C is then transformed to the equivalent
obligation  J, K, L |= C by expanding definitions E_1, ... , E_m
and introducing additional declarations NEW v_1, ... , NEW v_j,
where K has the form K_1, ... , K_n.  Then A |= P has the
proof

   <i> SUFFICES H, NEW v_1, ... , NEW v_j |= C
     BY DEF D_1, ... , D_k
   <i>1. K_1 |= C
     ...
   <i>n. K_n |= C
   <1> QED
     BY <i>1, ... , <i>n DEF E_1, ..., E_m

The transformation of A, H |= C to J, K, L |= C will be done in
two steps:

 1. Splitting conjunctions into separate assumptions.

 2. Performing the following transformations:

      \E x : S   ->  NEW x, S .

      NEW x, S_1 \/ ... \/ S_n  ->  
          (NEW x |= S_1) \/ ... \/ (NEW x |= S_n)


*********************************/

        /*
         * To figure out how to layout a nice popup, see 
         *    
         *    http://www.eclipse.org/articles/article.php?file=Article-Understanding-Layouts/index.html
         *    
         * to find out how to use GridLayout, and see ObligationsView.updateItem 
         * to see how to add things to a Composite nested inside other things.  
         * See also the ScrolledComposite method, which with luck will just be
         * a composite with scrollbars when needed.
         */

package org.lamport.tla.toolbox.editor.basic.handlers;

import java.io.File;
import java.io.IOException;
import java.util.LinkedList;
import java.util.List;
import java.util.Vector;

import org.eclipse.core.commands.AbstractHandler;
import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.core.commands.ExecutionException;
import org.eclipse.core.commands.IHandler;
import org.eclipse.core.resources.IFile;
import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.jface.resource.JFaceResources;
import org.eclipse.jface.text.BadLocationException;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.IRegion;
import org.eclipse.jface.text.TextSelection;
import org.eclipse.jface.viewers.ISelectionProvider;
import org.eclipse.swt.SWT;
import org.eclipse.swt.SWTError;
import org.eclipse.swt.browser.Browser;
import org.eclipse.swt.events.DisposeEvent;
import org.eclipse.swt.events.DisposeListener;
import org.eclipse.swt.events.SelectionAdapter;
import org.eclipse.swt.events.SelectionEvent;
import org.eclipse.swt.events.SelectionListener;
import org.eclipse.swt.graphics.Image;
import org.eclipse.swt.graphics.Point;
import org.eclipse.swt.layout.FillLayout;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Button;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Display;
import org.eclipse.swt.widgets.Label;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.swt.widgets.Text;
import org.eclipse.ui.IEditorReference;
import org.eclipse.ui.ISharedImages;
import org.eclipse.ui.PartInitException;
import org.eclipse.ui.PlatformUI;
import org.eclipse.ui.part.FileEditorInput;
import org.lamport.tla.toolbox.Activator;
//import org.lamport.tla.toolbox.doc.HelpButton;
import org.lamport.tla.toolbox.editor.basic.TLAEditor;
import org.lamport.tla.toolbox.editor.basic.util.EditorUtil;
import org.lamport.tla.toolbox.spec.Spec;
import org.lamport.tla.toolbox.spec.parser.IParseConstants;
import org.lamport.tla.toolbox.util.HelpButton;
import org.lamport.tla.toolbox.util.ResourceHelper;
import org.lamport.tla.toolbox.util.StringHelper;
import org.lamport.tla.toolbox.util.UIHelper;
import org.osgi.framework.Bundle;
import org.osgi.framework.FrameworkUtil;

import tla2sany.parser.SyntaxTreeNode;
import tla2sany.semantic.ASTConstants;
import tla2sany.semantic.AssumeProveNode;
import tla2sany.semantic.ExprNode;
import tla2sany.semantic.LeafProofNode;
import tla2sany.semantic.LevelNode;
import tla2sany.semantic.ModuleNode;
import tla2sany.semantic.NonLeafProofNode;
import tla2sany.semantic.OpApplNode;
import tla2sany.semantic.OpDefNode;
import tla2sany.semantic.ProofNode;
import tla2sany.semantic.SemanticNode;
import tla2sany.semantic.TheoremNode;
import tla2sany.st.Location;
import util.UniqueString;

/**
 * Notes:
 * 
 *   For expanding a definition that comes from a different file, use subexpression naming.
 *   
 *   When expanding a definition like Foo(Bar(a)), the "Bar(a)" is treated lik
 * @author lamport
 * 
 */
public class DecomposeProofHandler extends AbstractHandler implements IHandler {

    /***************************************************************
     * Fields holding information about the module, its source text,
     * the selected text, the selected step, and the theorem in
     * which it appears.
     ****************************************************************/
    /**
     * The document being edited.
     */
    private IDocument doc; 

    /**
     * The document as a string.
     */
    private String text; 

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
     * The step's proof which should be either null or a
     * LeafProofNode.
     */
    private  ProofNode proof;
    
    /**
     * If the step being proved is numbered <2>3,  then this equals 2.
     */
    private int proofLevel;
    
    /**
     * If the step is number <2>3, then this is "<2>3".  If the step is unnumbered,
     * as in <2>, or if it is the entire theorem, then this string is null.
     * 
     * Note that the SANY parser appears to replace <+> or <*> by
     * <n> for the appropriate number n, so the Toolbox doesn't have
     * to deal with <+> or <*>.
     */
    private String stepNumber;   
    
    /**
     * The column in which the step begins.  (Used for determining indentation of
     * the proof.
     */
    private int stepColumn;
    
    /**
     * The number of columns to the right of stepColumn to which the
     * created proof is to be indented.  It should be set from a 
     * preference.
     */
    int proofIndent = 2 ;
 
    /*************************************************************************
     * Fields that contain the current assumptions and goal.  
     * 
     * The data for the current assumptions are kept in vectors, the
     * i-th element containing data for the i-th assumption.  This is done
     * to make it easy to replace one assumption by several.  Other objects
     * contain pointers to these vectors, so once the vectors are
     * constructed by DecomposeProofHandler.execute, they can be modified
     * but must not be replaced by new vectors.
     *************************************************************************/
    /**
     * The semantic nodes for the current assumptions.
     */
    private Vector <SemanticNode> assumes ;
    
    /**
     * The NodeRepresentation objects for the current assumptions
     */
    private Vector <NodeRepresentation> assumeReps ; 
    
    private OpApplNode goal ;
    private NodeRepresentation goalRep ;
    
   
    // fields for displaying Decompose Proof window
    private Shell windowShell ;  // The shell of the Decompose Proof window
    private Point location = null ;  // The location at which window
                                     // should open.
    private TLAEditor editor;  // The editor from which window was raised.
    private IFile editorIFile ; // The IFile of the editor, used for making it read-only.
    
    /********************************************************
     * Fields representing the state of the decomposition
     ********************************************************/  
    /**
     * True iff some user action was performed that changed the obligation.
     */
    boolean changed;
    
    /**
     * If the user has done an \E split or an OR split on an assumption,
     * then this is the index of the assumption in assumes and assumeReps.
     * Otherwise, it equals -1.
     */
    int chosenSplit;
    
    /**
     * Once the user has performed an AND split on an assumption, then
     * another AND split can be performed only on one of the results of
     * that split.  The indices of the nodes in <code>assumes</code> and
     * <code>assumeReps</code> resulting from AND splits range from
     * andSplitBegin through andSplitEnd.  If no AND split has been performed,
     * then andSplitBegin and andSplitEnd equal -1.
     * 
     */
    int andSplitBegin;
    int andSplitEnd;
    
    /**
     * True iff the user has done something to change goal and/or set
     * of assumptions.  (This is used to disable the Replace option.)
     */
    private boolean hasChanged = false ;
    
    /**
     * True iff an action has been performed on an assumption--either
     * an AND-split, a \E-split, or an OR-split.  Such an action disables
     * actions on other assumptions.  Once an \E-split or an OR-split
     * has been performed, at most one assumption node can have actions 
     * performed on it.  After an AND-split, only AND-split nodes can
     * have enabled actions.
     */
    private boolean assumeHasChanged = false ;  

    /****************************************
     * Top Menu buttons.
     *****************************************/
    // The possible ways to distribute added assumptions in the proof are
    // - Put them in a SUFFICES step
    // - Put them in the ASSUMES clause of each step.
    // - Rewrite the original step.
    // I originally thought I'd allow all three, which required three
    // radio buttons. But I decided to disallow the third possibility,
    // so I needed only the single useSuffices check box.
    //
    //    // Radio buttons for how to rewrite proof:
    //    Button sufficesButton ; // Use SUFFICES step in proof
    //    Button rewriteButton ; // Rewrite step
    //    Button neitherButton ; // Use ASSUME/PROOF steps
    //
    //    // The value selected by the radiobuttons. Should initialize by preference
    // 
    //    private static final int SUFFICES_CHOSEN = 0 ;
    //    private static final int REWRITE_CHOSEN = 1 ;
    //    private static final int NEITHER_CHOSEN = 2 ;
    //    private int radioChoice = SUFFICES_CHOSEN ;
    
    /**
     * The useSufficesButton determines whether the created proof will
     * use an initial SUFFICES step to declare the newly created assumptions,
     * or if those assumptions will be put on each step of the proof in
     * an ASSUME/PROVE.
     */
    private boolean useSufficesValue = true;
    private Button useSufficesButton;  // 
    
    /**
     * The subexpressionButton determines if an occurrence of a user-defined
     * operator should be expanded by replacing it with its definition,
     * or by using subexpression names like Op(43)!2.  In the initial
     * implementation, definitions that come from a different module are
     * always expanded by using subexpression names.
     */
    private boolean subexpressionValue = true ; 
    private Button subexpressionButton ; 
    
            
    /**
     * Record the state of the top menu's check buttons.
     */
    private void readButtons() {
        useSufficesValue = useSufficesButton.getSelection() ;
        subexpressionValue = subexpressionButton.getSelection() ;
        // if (sufficesButton.getSelection()) {
        // radioChoice = SUFFICES_CHOSEN ;
        // return ;
        // }
        // if (rewriteButton.getSelection()) {
        // radioChoice = REWRITE_CHOSEN ;
        // return ;
        // }
        // radioChoice = NEITHER_CHOSEN ;
        // return ;
    }
    // private IRegion lineInfo; // The lineInfo for the current offset.

    
    public Object execute(ExecutionEvent event) throws ExecutionException {
        
        Shell topshell = UIHelper.getShellProvider().getShell() ;
        windowShell = new Shell(topshell, SWT.SHELL_TRIM) ; // | SWT.H_SCROLL); // SWT.RESIZE) ; // | SWT.V_SCROLL | SWT.H_SCROLL) ;
        windowShell.setText("Leslie's Test") ;
        Composite shell = windowShell; // new Composite(windowShell, SWT.NONE) ;
        GridLayout gridLayout = new GridLayout(2, false);
        shell.setLayout(gridLayout);
        // Set up the help button
        Button helpButton = HelpButton.helpButton(shell, "prover/test.html");
//        Button helpButton = new Button(shell, SWT.PUSH) ;
        Image helpImg = PlatformUI.getWorkbench().getSharedImages().getImage(ISharedImages.IMG_LCL_LINKTO_HELP);
        helpButton.setImage(helpImg);
        GridData gridData = new GridData();
        gridData.verticalAlignment = SWT.TOP;
        helpButton.setLayoutData(gridData);
        // Attach the listener to it
//        helpButton.addSelectionListener(new HelpButtonListener());
//        Bundle bundle = FrameworkUtil.getBundle(this.getClass());
        String url = HelpButton.baseURL; //bundle.getLocation() ;
        
        
        System.out.println("url:  " + url);
        String msgText = 
           "Please click on the `?' button on the left.\n\n" +
           "It will be obvious if it succeeds in doing what it should.\n\n" +
           "If it doesn't do what it should, please copy the following\n" +
           "text and send it to me.\n\n  |-" + url + "-|   \n\n"  +
           "Thanks,\n\nLeslie" ;
        Text text = new Text(shell, SWT.NONE+SWT.MULTI) ;
        text.setText(msgText);
        text.setFont(JFaceResources.getFontRegistry().get(
                JFaceResources.TEXT_FONT));
        text.setEnabled(true) ;
//        Label label = new Label(shell, SWT.BORDER) ;
//        label.setText(msgText);
        shell.pack() ;
        windowShell.update();
        windowShell.open();
        return null;
        
    }
    
    public class HelpButtonListener extends SelectionAdapter implements SelectionListener {

        public void widgetSelected(SelectionEvent e) {
            displayHTML();
        }
        
        public void widgetDefaultSelected(SelectionEvent e) {
            displayHTML();
        }

    }
    /**
     * The execute method is called when the user issues a DecomposeProof
     * command.
     *  
     * @see
     * org.eclipse.core.commands.IHandler#execute(org.eclipse.core.commands.
     * ExecutionEvent)
     */
    public Object realExecute(ExecutionEvent event) throws ExecutionException {

        /******************************************************************
         * Perform various checks to see if the command should be
         * executed, and possibly raise an error warning if it shouldn't. 
         *******************************************************************/
        // Do nothing if already executing command. 
        if (this.windowShell != null) {
            if (!this.windowShell.isDisposed()) {
                System.out.println("Command called when being executed.");
                return null;
            }
        }

        // Report an error if there are dirty modules.
        if (existDirtyModules())
        {
                MessageDialog
            .openError(UIHelper.getShellProvider().getShell(),  
                        "Decompose Proof Command",
                        "There is an unsaved module.");
            return null;
        }
        
        // Pop up an error if the spec is not parsed.
        Spec spec = Activator.getSpecManager().getSpecLoaded();
        if (spec == null || spec.getStatus() != IParseConstants.PARSED) {
                MessageDialog.openError(UIHelper.getShellProvider().getShell(),
                        "Decompose Proof Command",
                        "The spec status must be \"parsed\" to execute this command.");
                return null;
        }
         
        /*
         * The following text for finding the editor, document, selection, and
         * module is copied from other commands.
         */

        //gets the editor to which command applies
        editor = EditorUtil.getTLAEditorWithFocus();
        if (editor == null) {
            return null;
        }
        editorIFile = ((FileEditorInput) editor.getEditorInput()).getFile() ;
        if (editor.isDirty()) {
            MessageDialog.openError(UIHelper.getShellProvider().getShell(),
                    "Decompose Proof Command",
                    "The module is dirty; will replace by asking if it should be saved.");
            return null;
        }
        
        /**********************************************
         * Initialize the state of the decomposition.
         **********************************************/
        changed = false ;
        chosenSplit = -1;
        andSplitBegin = -1;
        andSplitEnd = -1 ;

        /*******************************************************************
         * Set the following fields:
         *    doc, text, selectionProvider, selection, offset, moduleNode.
         ******************************************************************/
        doc = editor.getDocumentProvider().getDocument(editor.getEditorInput());
        text = doc.get();
        selectionProvider = editor.getSelectionProvider();
        selection = (TextSelection) selectionProvider.getSelection();
        offset = selection.getOffset();

        // Get the module.
        String moduleName = editor.getModuleName();
        moduleNode = ResourceHelper.getModuleNode(moduleName);

        // selectedLocation is Location of selected region.
        Location selectedLocation = EditorUtil.getLocationAt(doc, offset,
                selection.getLength());

        /****************************************************
         * Set the `theorem' field.
         *****************************************************/
        TheoremNode[] allTheorems = moduleNode.getTheorems();
        theorem = null;
        int i = 0;
        String moduleFile = moduleNode.stn.getFilename() ;
        while ((theorem == null) & (i < allTheorems.length)) {
            if ( allTheorems[i].stn.getFilename()
                    .equals(moduleFile)
                 &&
                 EditorUtil.locationContainment(selectedLocation,
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

        /********************************************************************
         * Set the following fields:
         *   step, proofLevel, proof
         *********************************************************************/
        // NEED TO ADD CODE to compute a symbol table of all identifiers
        // that are defined by the context of the found step.
        // Things to check to find out how to do that
        //   classes: Context, SymbolTable
        //   SemanticHelper.getNewContext for generating a new Context from an
        //     existing module's context.  This context will have built-in
        //     operators, but they can be ignored by their OpDefNode's kind field.
        //   
        step = theorem;
        boolean notDone = true;
        proofLevel = -1 ;
        proof = step.getProof();
        while (notDone && (proof != null)
                && (proof instanceof NonLeafProofNode)) {
            LevelNode[] pfsteps = ((NonLeafProofNode) proof).getSteps();
            LevelNode foundLevelNode = null;
            i = 0;
            proofLevel = stepLevel(pfsteps[0]);
           while ((foundLevelNode == null) && (i < pfsteps.length)) {
                if (EditorUtil.locationContainment(selectedLocation,
                        pfsteps[i].stn.getLocation())) {
                    foundLevelNode = pfsteps[i];
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
  
        /*********************************
         * set stepNumber and stepColumn 
         *********************************/
        SyntaxTreeNode nd = (SyntaxTreeNode) step.stn;
        if (step == theorem) {
                stepNumber = null ;
        } else {
                stepNumber = nd.getHeirs()[0].image.toString();
                if (stepNumber.indexOf('>') == stepNumber.length()-1) {
                        stepNumber = null ;
                }
        }        
        stepColumn = nd.getLocation().beginColumn() ;
        
        /**************************************************************
         * Check that the step has either no proof or a leaf proof.
         *************************************************************/
        if ((proof != null) && !(proof instanceof LeafProofNode)) {
            MessageDialog.openError(UIHelper.getShellProvider().getShell(),
                    "Decompose Proof Command",
                    "You have selected a step that already has a non-leaf proof.");
            return null;
        }
        
        /**************************************************************
         * Set stepRep
         *************************************************************/
        try {
            stepRep = new NodeRepresentation(doc, step) ;
        } catch (BadLocationException e) {
            e.printStackTrace();
            System.out.println("threw exception");
        }
        
        /**************************************************************
         * Set assumes, assumesRep, goal, and goalRep
         *************************************************************/
        LevelNode thm = step.getTheorem();
        if (thm instanceof AssumeProveNode) {
            /**************************************************************
             * This is an ASSUME/PROVE.
             *************************************************************/
            SemanticNode[] assump = ((AssumeProveNode) thm).getAssumes();
            assumes = new Vector<SemanticNode>() ;
            assumeReps = new Vector<NodeRepresentation>();
            
            int rowOfLastNew = -1;
            for (i = 0; i < assump.length; i++) {
                /**************************************************************
                 * Loop invariant:
                 *   rowOfLastNew = n > -1 iff assumption i-1 is a NEW
                 *   statement that lies entirely on row n
                 *************************************************************/
                if (assump[i] instanceof AssumeProveNode) {
                    MessageDialog
                            .openError(UIHelper.getShellProvider().getShell(),
                                    "Decompose Proof Command",
                                    "Cannot decompose a step with a nested ASSUME/PROVE.");
                    return null;
                } 
                assumes.add(assump[i]);
                NodeRepresentation nodeRep = stepRep.subNode(assump[i], assumeReps, null) ;
                if (nodeRep.nodeType == NodeRepresentation.NEW_NODE) {
                    Location loc = nodeRep.semanticNode.stn.getLocation() ;
                    if (loc.beginLine() == loc.endLine()) {
                        if (loc.beginLine() == rowOfLastNew) {
                            assumeReps.elementAt(i-1).onSameLineAsNext = true ;
                        }
                        rowOfLastNew = loc.beginLine() ;
                    } else {
                        rowOfLastNew = -1;
                    }
                } else {
                    rowOfLastNew = -1;
                }
                assumeReps.add(nodeRep);
                
                goal = (OpApplNode) ((AssumeProveNode) thm).getProve();
                goalRep = stepRep.subNode(goal, null, null );
            }
            
        } else {
            /**************************************************************
             * This is not an ASSUME/PROVE, so have to set assumes and
             * assumesRep to null and check that this isn't something like a QED
             * step that the command doesn't handle.
             *************************************************************/
            assumes = null;
            assumeReps = null;
            goal = (OpApplNode) thm;
            UniqueString goalOpName = goal.getOperator().getName();

            // Abort if this is one of the following kinds of steps:
            // QED, HAVE, PICK, WITNESS, SUFFICES
            if ((goalOpName == ASTConstants.OP_qed)
                    || (goalOpName == ASTConstants.OP_pfcase)
                    || (goalOpName == ASTConstants.OP_have)
                    || (goalOpName == ASTConstants.OP_pick)
                    || (goalOpName == ASTConstants.OP_witness)
                    || (goalOpName == ASTConstants.OP_suffices)) {
                MessageDialog.openError(UIHelper.getShellProvider().getShell(),
                        "Decompose Proof Command",
                        "Cannot decompose this kind of step.");
                return null;
            }
            goalRep = stepRep.subNode(goal, null, null);
        }

        // The following code seems to be redundant.
        // The return null can never happen because that would have
        // caused a null return in the test at the beginning of the module
        // for whether the command was issued in the middle of executing
        // a DecomposeProof command.
//        if (this.windowShell != null)  {
//            if (this.windowShell.isDisposed()) {
//                // The following method was deprecated because it was actually possible to use
//                // it, so it had to be replaced by something that requires a PhD in Eclipse
//                // to figure out how to use.
//                editorIFile.setReadOnly(true) ;
//                raiseWindow("Decompose Proof") ;
//                
//            }
//            return null ;
//        }
        
        
//        System.out.println("parent null") ;
//        // This setReadOnly is a no-op.  Why???
//        EditorUtil.setReadOnly(editorIFile, true);
        
        /***************************************************************************
         * Make the editor read-only.
         ***************************************************************************/
        // The following method was deprecated because it was actually possible to use
        // it, so it had to be replaced by something that requires a PhD in Eclipse
        // to figure out how to use.
        editorIFile.setReadOnly(true) ;
        raiseWindow("newWindow") ;
        
        return null;
    }
    

    // Note: It looks like horizontalSpan doesn't apply to a Label or a Button
    // Probably have to put the label or Button inside a composite to do that.

    private void raiseWindow(String windowTitle) {
        // for testing
        // topshell = the Toolbox's shell
        Shell topshell = UIHelper.getShellProvider().getShell() ;
        windowShell = new Shell(topshell, SWT.SHELL_TRIM) ; // | SWT.H_SCROLL); // SWT.RESIZE) ; // | SWT.V_SCROLL | SWT.H_SCROLL) ;
        windowShell.setText(windowTitle) ;
        windowShell.addDisposeListener(new WindowDisposeListener(this)) ;
        Composite shell = new Composite(windowShell, SWT.NONE) ;
        GridLayout gridLayout = new GridLayout(3, false);
        shell.setLayout(gridLayout);
        
//        UIHelper.setHelp(shell, "definition_override_wizard");
        Composite topMenu = new Composite(shell,SWT.NONE) ;   
        gridLayout = new GridLayout(4, false);
        gridLayout.marginBottom = 0;
        topMenu.setLayout(gridLayout);        
        GridData gridData = new GridData() ;
        gridData.horizontalSpan = 3;
        topMenu.setLayoutData(gridData) ;
        
        // Display Help and Replace Step buttons. 
        // NEED TO ADD DISABLING OF Prove BUTTON
        Button helpButton = HelpButton.helpButton(topMenu, "prover/test.html") ;
//        HelpListener listener = new HelpListe
//        proveButton.addHelpListener(listener) ;
//        setupMenuButton(proveButton, PROVE_BUTTON, "Prove") ;
        Button replaceButton = new Button(topMenu, SWT.PUSH) ;
        setupMenuButton(replaceButton, TEST_BUTTON, "Replace Step") ;
        replaceButton.setEnabled(changed && (chosenSplit == -1) && (andSplitEnd == -1)) ;
        
        // Display checkbox to choose how to write proof.
        useSufficesButton = new Button(topMenu, SWT.CHECK);
        setupCheckButton(useSufficesButton, "Use SUFFICES") ;
        useSufficesButton.setSelection(useSufficesValue) ;
        
        // Display checkbox to choose whether to expand definitions with subexpression names.
        subexpressionButton = new Button(topMenu, SWT.CHECK);
        setupCheckButton(subexpressionButton, "Use subexpression names");
        subexpressionButton.setSelection(subexpressionValue) ;
        
        // /*
        // * Adds the radio buttons, which are a Composite.
        // */
        // Composite radio = new Composite(topMenu, SWT.BORDER) ;
        // GridLayout radioLayout = new GridLayout(6, false) ;
        // radio.setLayout(radioLayout) ;
        // Label radioLabel = new Label(radio, SWT.NONE) ;
        // radioLabel.setText("prove using:") ;
        // sufficesButton = new Button(radio, SWT.RADIO) ;
        // neitherButton = new Button(radio, SWT.RADIO) ;
        // rewriteButton = new Button(radio, SWT.RADIO) ;
        //
        // sufficesButton.setText("SUFFICES") ;
        // rewriteButton.setText("rewritten goal") ;
        // neitherButton.setText("ASSUME/PROVE steps") ;
        // switch (radioChoice) {
        // case SUFFICES_CHOSEN :
        // sufficesButton.setSelection(true) ;
        // rewriteButton.setSelection(false) ;
        // neitherButton.setSelection(false) ;
        // break ;
        // case REWRITE_CHOSEN :
        // sufficesButton.setSelection(false) ;
        // rewriteButton.setSelection(true) ;
        // neitherButton.setSelection(false) ;
        // break ;
        // case NEITHER_CHOSEN :
        // sufficesButton.setSelection(false) ;
        // rewriteButton.setSelection(false) ;
        // neitherButton.setSelection(true) ;
        // break ;
        // }
       
        /**************************************************************
         * Display the ASSUME Section
         **************************************************************/
        // Display the "ASSUME", which must be put in a 
        // composite because it spans multiple rows, and it appears
        // that a Label can't do that.
        Composite comp = new Composite(shell, SWT.NONE) ;
        GridLayout compLayout = new GridLayout(1, false) ;
        comp.setLayout(compLayout) ;       
        gridData = new GridData();
        gridData.horizontalSpan = 3;
        comp.setLayoutData(gridData);
        Label assumeLabel = new Label(comp, SWT.NONE);
        assumeLabel.setText("ASSUME");
        assumeLabel.setFont(JFaceResources.getFontRegistry().get(JFaceResources.HEADER_FONT));
        
        if (assumes != null) {
            /*************************************************************
             * Displaying  the assumptions.  
             * 
             * First, Set assumeWidth to the number of characters in the widest 
             * line among all the lines in the assumptions.
             **************************************************************/
            int assumeWidth = 0;
            for (int i = 0; i < assumes.size(); i++) {
                for (int j = 0; j < assumeReps.elementAt(i).nodeText.length; j++) {
                    assumeWidth = Math.max(assumeWidth,
                            assumeReps.elementAt(i).nodeText[j].length());
                }
            }
            
            /*************************************************************
             * Add the assumptions to the DecomposeProof window.
             *************************************************************/
            for (int i = 0 ; i < assumes.size(); i++) {
                
                /*************************************************************
                 * Add the button or blank area to the first column.
                 *************************************************************/
                String labelText =  null ;                      
                if (assumes.elementAt(i).getKind() == ASTConstants.OpApplKind) {
                        switch (assumeReps.elementAt(i).nodeSubtype) {
                        case NodeRepresentation.AND_TYPE:
                                labelText = "/\\";
                                break;
                        case NodeRepresentation.OR_TYPE:
                        case NodeRepresentation.SQSUB_TYPE:
                                labelText = "\\/";
                                break;
                        case NodeRepresentation.EXISTS_TYPE:
                                labelText = "\\E";
                                break;
                    default:
                        labelText = null ;
                        }
                }
                if (labelText != null) {
                    /*************************************************************
                     * Add a button
                     *************************************************************/
                    Button button = new Button(shell, SWT.PUSH);
                    setupActionButton(button, assumeReps.elementAt(i),
                            labelText);
                    if (((chosenSplit != -1) && (i != chosenSplit))
                            || (   (andSplitBegin != -1) 
                                && ((i < andSplitBegin) || (i > andSplitEnd)))) {
                        button.setEnabled(false);
                    }
                } else {
                    /*************************************************************
                     * Add a blank area.
                     *************************************************************/
                    comp = new Composite(shell, SWT.NONE);
                    gridLayout = new GridLayout(1, false);
                    comp.setLayout(gridLayout);
                    assumeLabel = new Label(comp, SWT.NONE);
                    assumeLabel.setText("  ");
                    gridData = new GridData();
                    gridData.horizontalIndent = 25;
                    comp.setLayoutData(gridData);
                }
                gridData = new GridData();
                gridData.verticalAlignment = SWT.TOP;
                assumeLabel.setLayoutData(gridData);
                
                // Add a spacer between the button and the formula
                comp = new Composite(shell, SWT.NONE);
                gridLayout = new GridLayout(1, false);
                comp.setLayout(gridLayout);                  
                comp.setSize(0, 5) ;
                
                /********************************************************************
                 * Add the text of the clause, preceded by appropriate up/down arrows
                 * for a node that comes from an AND-SPLIT.  
                 * Combine it with the next node if its onSameLineAsNext
                 * field is true (which implies it and the next node are NEW nodes.
                 ********************************************************************/
                comp = new Composite(shell, SWT.NONE);
                gridLayout = new GridLayout(3, false);
                comp.setLayout(gridLayout);   
                // Add arrow buttons if necessary
                if ((chosenSplit == -1) && (andSplitBegin <= i) && (i <= andSplitEnd)) {
                    Button arrowButton = new Button(comp, SWT.ARROW | SWT.UP);
                    gridData = new GridData();
                    gridData.verticalAlignment = SWT.TOP;
                    arrowButton.setLayoutData(gridData);
                    if (i == andSplitBegin) {
                        arrowButton.setEnabled(false);
                    }
                    arrowButton = new Button(comp, SWT.ARROW | SWT.DOWN);
                    gridData = new GridData();
                    gridData.verticalAlignment = SWT.TOP;
                    arrowButton.setLayoutData(gridData);
                    if (i == andSplitEnd) {
                        arrowButton.setEnabled(false);
                    }
                }
                

                assumeLabel = new Label(comp, SWT.NONE);
                String text = stringArrayToString(assumeReps.elementAt(i).nodeText) ;
                // Combine this with following NEW nodes if necessary
                while (assumeReps.elementAt(i).onSameLineAsNext) {
                    i++;
                    text = text + ", " + stringArrayToString(assumeReps.elementAt(i).nodeText) ;

                }
                assumeLabel.setText(text);
                // Set the font to be the editors main text font.
                assumeLabel.setFont(JFaceResources.getFontRegistry().get(
                                JFaceResources.TEXT_FONT));
                gridData = new GridData();
                // I have no idea why (undoubtedly a feature that no one has ever 
                // bothered to document), but the following statement did not have 
                // any effect before I added the new composite between the button
                // and it.  Now it can be used to add positive or negative space
                // to the left of the label.
                                gridData.horizontalIndent = 0 ;
                gridData.verticalAlignment = SWT.TOP;
                assumeLabel.setLayoutData(gridData);
                
                // Add a spacer between the items.
                if (i != assumeReps.size() - 1  ) {
//                                      comp = new Composite(shell, SWT.NONE);
//                                      comp.setSize(100,0) ;
                                        comp = new Composite(shell, SWT.NONE);
                                        comp.setLayout(compLayout);
                                        gridData = new GridData();
                                        gridData.horizontalSpan = 3;
                                        gridData.horizontalIndent = 30;
                                        comp.setLayoutData(gridData);
                                        gridLayout = new GridLayout(1, false) ;
                                    comp.setLayout(gridLayout);
                                    assumeLabel = new Label(comp, SWT.NONE) ;
                                    String dashes = StringHelper.copyString("  -", (assumeWidth+5)/3);
                                        assumeLabel.setText(dashes);
                                        assumeLabel.setFont(JFaceResources.getFontRegistry().get(
                                        JFaceResources.TEXT_FONT));

                                        // The following is one of many vain attempts to create a separator
                                        // of a given width. It works only if the following line begins with
                                        // a blank label, but not if it begins with a button.(?!)
                    //  assumeLabel = new Label(comp, SWT.SEPARATOR | SWT.HORIZONTAL);
                                        //
                                        // gridData = new GridData();
                                        // gridData.horizontalAlignment = GridData.FILL;
                                        // gridData.grabExcessHorizontalSpace = true;
                                        // gridData.minimumWidth = 500;
                                        // assumeLabel.setLayoutData(gridData) ;
                                       // comp.setSize(0,0) ;
                                        // System.out.println("Line " + i) ;
                }
            }
        }
        
        /**********************************************************
         *  Display the Goal
         **********************************************************/
        // Display the "PROVE", which must be put in a 
        // composite because it spans multiple rows, and it appears
        // that a Label can't do that.
        comp = new Composite(shell, SWT.NONE) ;
        compLayout = new GridLayout(1, false) ;
        comp.setLayout(compLayout) ;       
        gridData = new GridData();
        gridData.horizontalSpan = 3;
        comp.setLayoutData(gridData);
        assumeLabel = new Label(comp, SWT.NONE);
        assumeLabel.setText("PROVE");
        assumeLabel.setFont(JFaceResources.getFontRegistry().get(JFaceResources.HEADER_FONT));
        String labelText = null ;
        
        // isProver = true means clicking on the button produces the proof.
        boolean isProver = false ;
        // Set disable to disable the button, which should be done iff
        // decomposition of an assumption has been started and this is
        // an AND node.
        boolean disable = false;
        switch(goalRep.nodeSubtype) {
        case NodeRepresentation.AND_TYPE:
                        labelText = "/\\";
                        isProver = true ;
                        disable = (chosenSplit != -1) || (andSplitBegin != -1) ;
                        break;
        case NodeRepresentation.FORALL_TYPE:
                        labelText = "\\A";
                        break;  
        case NodeRepresentation.IMPLIES_TYPE:
                        labelText = "=>";
                        break;
        default:
                labelText = null ;
        }
        if (labelText != null) {
              Button goalButton = new Button(shell, SWT.PUSH) ;
              setupActionButton(goalButton, goalRep, labelText);
              goalButton.setEnabled(! disable) ;
                }
        else {
                assumeLabel = new Label(shell, SWT.NONE) ;
            assumeLabel.setText("  ") ;
        }
        
        // Add a spacer between the button and the formula
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
        assumeLabel.setText(stringArrayToString(goalRep.nodeText));
        gridData = new GridData();
        gridData.verticalAlignment = SWT.TOP;
        assumeLabel.setLayoutData(gridData);
        Display display = UIHelper.getCurrentDisplay();
        // The following sets the font to be the Toolbox editor's text font.
        assumeLabel.setFont(JFaceResources.getFontRegistry().get(
                        JFaceResources.TEXT_FONT));
        shell.pack() ;
        Point shellSize = shell.getSize() ;;
        windowShell.setSize(shellSize.x + 30, shellSize.y + 30) ;
        
        windowShell.update();
        if (this.location != null) {
            windowShell.setLocation(this.location) ;
        }
        windowShell.open();

        /***************************************************************************
         * For some reason, reraising the window seems to cause the editor to become
         * writable, so we make it read-only again.
         ***************************************************************************/
        // The following method was deprecated because it was actually possible to use
        // it, so it had to be replaced by something that requires a PhD in Eclipse
        // to figure out how to use.       
        editorIFile.setReadOnly(true);
    }
    
    
    void displayHTML() {
        Shell topshell = UIHelper.getShellProvider().getShell() ;
        Shell shell = new Shell(topshell, SWT.SHELL_TRIM) ;
        shell.setLayout(new FillLayout());
        Browser browser;
        try {
          browser = new Browser(shell, SWT.NONE);
    } catch (SWTError e) {
            System.out.println("Could not instantiate Browser: " + e.getMessage());
            shell.dispose();
            return;
    }
        
        Bundle bundle = FrameworkUtil.getBundle(this.getClass());
        String url = bundle.getLocation() ;
        System.out.println("What's going on");
        int idx = url.indexOf("reference:file:/");
        System.out.println("original url = " + url);
        if (idx == 0) {
            url = url.substring("reference:file:/".length()) ;
        }
        String url2 = url + "html/prover/test.html" ;
        String url1 = url ;
        idx = url.indexOf("org.lamport.tla.toolbox.editor.basic/") ;
        if (idx == url.length() - "org.lamport.tla.toolbox.editor.basic/".length()) {
            url1 = url.substring(0, idx) + 
              "org.lamport.tla.toolbox.doc/html/prover/test.html";
        }
    System.out.println(url1); // + ",  " + url2);
//    String html = "<BODY BGCOLOR=#ffffe4>" +
//                  "<PRE> this is some pre\n another line \n</PRE>" +
//                 "a b <i>c</i> d <font color=#ff00001>Large</font>" + 
//                 "</BODY>";
       browser.setUrl(url1) ;

//    browser.setText(html);
    shell.open();
    }
    
    /***************************************************************************
     * The action-button handlers
     ****************************************************************************/
    
    void andAction(NodeRepresentation nodeRep) {
       boolean isPrimed = false;
       boolean defExpanded = false;
       /**
        * Set conjuncts to the vector of conjunctions.
        */
       Vector<OpApplNode> conjunctions = new Vector<OpApplNode> () ;
       if (nodeRep.parentVector == null) {
           /**
            * This is a "prove by AND-split" operation.
            */
           // not yet implemented
           return ;
       } else {
           /**
            * This is an AND-SPLIT of an assumption, so nodeRep is assumeReps(i) 
            * node, and parentNode = null.  We set idx to i.
            */
           int idx = nodeRep.getParentIndex() ;
           
           
           
       }
       
    }
    
    /**
     * A NodeRepresentation object  describes the TLA+ source text
     * that produced a SemanticNode, after substitutions have been performed
     * for some identifiers.  It contains the following information:
     * <ul>
     * <li> The SemanticNode <code>node</code>.
     * 
     * <li> A String[] object <code>nodeText</code> that describes the source text 
     *      after substitutions have been performed.
     *      
     * <li> A mapping from <line, column> coordinates occurring in locations
     *      in the syntax tree of <code>node</code> to the corresponding
     *      positions in <code>nodeText</code>.  
     * </ul>
     * An OR-decomposition node represents a node that represents an assumption that has
     * been decomposed into a disjunction for a proof by cases.  Such a node has a
     * vector of children, which can include OR-decomposition nodes.
     * 
     * @author lamport
     *
     */
    public class NodeRepresentation {
        SemanticNode semanticNode ;
        
        /**
         * We represent the text of a TLA+ syntactic unit as a String array, each element
         * representing one line of the text with no end-of-line characters.
         * 
         * The text from the module that represents <code>node</code>, represented by
         * the array nodeText of strings  as follows.  Let S be the region of the module
         * that produces the node.  If S lies entirely on one line, then nodeText has length 1
         * and nodeText[0] = S.  Otherwise, suppose S lies on N lines.  Let B be the array with B[0]
         * containing the beginning of S up until the end of the first line, with
         * B[1], ... , B[n-1] containing the next n-2 lines of S, and with B[n] containing
         * the rest of S.  Then nodeText is the array obtained from B by possibly adding spaces to
         * the beginning of B[0] and possibly removing spaces from the beginning of
         * B[1], ... , B[n] so that there is at least one line of nodeText that does not begin with
         * a space and the formatting of the original text is maintained in nodeText.
         *  
         * @param document
         * @param semanticNode
         * @return
         */
        String[] nodeText ;
        
        // mapping defines the mapping from <line, column> coordinates
        // within the syntax tree of `node' to positions in nodeText,
        // where <ln, c> is mapped into the position mapping[j](c) in
        // string nodeText[j], where j = ln - node.stn.beginLine() 
        // (node.stn.beginLine() is the number of the line on which the
        // source text of `node' begins.  (See the comments on the
        // MappingPair class for a definition of mapping[j](c).
        Vector<MappingPair>[] mapping ;

        // If non-null, then originalOperator is the name of the
        // operator that was expanded to produce `node'.
        String originalOperator = null ;

        // The nodeType is the type of node.
        private static final int EXPR_NODE = 0  ; // An OpApplNode 
        private static final int NEW_NODE  = 1  ; // A NewSymbNode
        private static final int OR_DECOMP = 2  ; 
           // A node representing a decomposition into the disjunction of its children
           // Its node and nodeRep 
        private static final int PROOF_NODE = 4  ; 
          // The LeafProofNode of the step.  This may not be needed.
        private static final int OTHER_NODE = 5  ;        
        private int nodeType = 0 ;
        
        // An EXPR_NODE can have multiple subtypes, indicating what decomposition
        // can be applied.
        private static final int AND_TYPE     = 0 ;
        private static final int OR_TYPE      = 1 ;
        private static final int IMPLIES_TYPE = 2 ;
        private static final int FORALL_TYPE  = 3 ;
        private static final int EXISTS_TYPE  = 4 ;
        private static final int SQSUB_TYPE   = 5 ;  // An [A]_v expression
        private static final int OTHER_TYPE   = 99 ;  // anything else
        
        public int nodeSubtype = OTHER_TYPE ;
        
        /********************************************************************
         *  An OR-Split operation can be performed on a node of type EXPR_NODE 
         *  and subtype OR_TYPE.  This operation replaces the node with one
         *  of type OR_DECOMP, whose children field is a vector with one 
         *  element for each disjunct of the semanticNode's disjuncts, where
         *  children.elementAt(i) is a vector of length 1 containing a node
         *  of type EXPR_NODE for that disjunct.  Further operations on that
         *  node can turn children.elementAt(i) into a vector consisting of
         *  a sequence of NEW_NODE NodeRepresentation objects followed by
         *  an EXPR_NODE or OR_DECOMP node.  The `children' field is null
         *  for a node of type other than OR_DECOMP.
         *********************************************************************/
        Vector<Vector <NodeRepresentation>> children = null ;
        
        /********************************************************************
         * If this node has parentNode # null, then it equals 
         * n.children.elementAt(i).elementAt(j) for an OR_DECOMP node n,
         * where parentNode = n and parentVector = n.children.elementAt(i).
         * In this case, the node is of type EXPR_NODE, NEW_NODE, or
         * OR_DECOMP.
         * 
         * If this node has parentNode = null, then either
         * - it equals h.assumeReps.elementAt(j) for the DecomposeProofHandler
         *   object h, parentNode = null, and parentVector = assumeReps.
         * - parentVector = null and the node is the current goal.
         ********************************************************************/
        NodeRepresentation parentNode = null ;
        Vector<NodeRepresentation> parentVector = null ;
             
        /**
         * If parentVector is non-null, then the current node equals
         * parentVector.elementAt(getParentIndex()).  If parentVector
         * is null, then getParentIndex() equals -l.
         * 
         * @return
         */
        int getParentIndex() {
            if (parentVector == null) {
                return -1 ;
            }
            for (int i = 0; i < parentVector.size(); i++) {
                if (this == parentVector.elementAt(i)) {
                    return i;
                }
            }
            return -1;  // this shouldn't happen
        }
        
        /**
         * If parentNode is non-null (which implies parentVector is non-null),
         * and parentNode is an OR-SPLIT node, 
         * then parentVector = parentNode.children.elementAt(getParentVectorIndex).
         * 
         * @return
         */
        int getParentVectorIndex() {
            for (int i = 0; i < parentNode.children.size(); i++) {
                if (this.parentVector == parentNode.children.elementAt(i)) {
                    return i;
                }
            }
            return -1;  // this shouldn't happen

        }
        // State information about this clause.
        
        /**
         * True iff this assumption or goal was not in the original
         * step.
         */
        boolean isCreated = false;

        /**
         * True iff this is a NEW node that is to be displayed on the same
         * line as the next node, which is also a NEW node.  For nodes
         * that come from the step, this is true iff this and the next node
         * are NEW nodes that all appear entirely on the same line.  For added
         * NEW nodes, it will be true iff:
         * 
         *   - The NEW statement fits on a single line (meaning that it is NOT of
         *     the form NEW x \in S where S is a multi-line formula)
         *     
         *   - It and the next node come from the same \A or \E, as in the NEW x and 
         *     NEW y from \A x, y : ... 
         *     
         * A sequence of same-line NEWs will not all be put on the same line in the 
         * proof if its width plus proofIndent is greater than the module-editor right 
         * margin preference, which is obtained with
         * 
         *   Activator.getDefault().getPreferenceStore().getInt(
         *       EditorPreferencePage.EDITOR_RIGHT_MARGIN);
         */
        boolean onSameLineAsNext = false ;
        
// The following commented-out state information is deducible from the
//  handler object's state.
//        /**
//         * True if the action associated with this node is disabled
//         * because the user has performed an AND or OR or \E split on
//         * some other node.
//         * 
//         */
//        boolean isDisabled;
//        
//        /**
//         * True iff this node is the result of the user doing an AND 
//         * split on an assumption.
//         */
//        boolean fromAndSplit;
        
        
        /**
         * Create a NodeRepresentation for a subnode of this node.
         * 
         * @param sn  A subnode of this.node.
         * @return
         */
        NodeRepresentation subNode(SemanticNode sn, Vector <NodeRepresentation> vec,
                                     NodeRepresentation father) {
            
            NodeRepresentation result = new NodeRepresentation() ;
            result.parentNode = father;
            result.parentVector = vec ;
            result.semanticNode = sn ;
            // set beginId to be the index in this.nodeText representing the
            // first line of the source of SemanticNode node sn.
            int beginIdx =  getBeginLine(sn) - getBeginLine(this.semanticNode) ;
            result.nodeText = new String[getEndLine(sn) - getBeginLine(sn)+1];
            result.mapping = new Vector[result.nodeText.length] ;
            // Set beginCol to the column of the first token of sn.
            // Set beginPos to the position of the first token of sn in the string
            // this.result.nodeText[beginLine - 1] containing its text.
            int beginCol = sn.stn.getLocation().beginColumn() ;
            int beginPos = colToLoc(beginCol, this.mapping[beginIdx]);
            
            /*
             * Set the nodeText and mapping fields.
             */
            // Set result.nodeText[0] to the string containing the first
            // token and everything to its right in this.nodeText[...].
            // Set result.mapping[0] to the MappingVector obtained by
            // subtracting beginPos from all increments.           
            result.nodeText[0] = this.nodeText[beginIdx].substring(beginPos);
            Vector<MappingPair> mv = cloneMappingPairVector(this.mapping[beginIdx]) ;
            // Since we just removed beginPos characters to the left of beginCol, we should 
            // execute 
            adjustMappingPairVector(beginCol, -beginPos, mv) ;
            // but we'll do the adjustment by -beginPos later.
            result.mapping[0] = mv ;
           
            // Set result.nodeText[i] to a copy of this.nodeText[i+...] 
            //   and result.mapping[i] to a copy of this.mapping[i] for 
            //   all other lines of the subnode's text.
            // Set minPos = the minimum of beginPos and the smallest number
            //   of leading spaces of any subsequent line of result.nodeText
            int minPos = beginPos ;
            for (int i = 1; i < result.mapping.length; i++) {
                result.nodeText[i] = this.nodeText[i + beginIdx] ;
                minPos = Math.min(minPos, StringHelper.leadingSpaces(result.nodeText[i]));
                result.mapping[i] = new Vector<MappingPair>() ;
                for (int j = 0; j < this.mapping[i + beginIdx].size(); j++) {
                    result.mapping[i].add(this.mapping[i + beginIdx].elementAt(j).clone());
                }
            }
            
            // Remove the part of the last line of result.nodeText that doesn't
            // belong to the subnode
            result.nodeText[result.nodeText.length - 1] =
                   result.nodeText[result.nodeText.length - 1].
                     substring(0, colToLoc(sn.stn.getLocation().endColumn()+1, 
                               result.mapping[result.mapping.length-1])) ;
            
            // Add any necessary space at the beginning of result.nodeText[0]
            int spacesAddedToFirstLine = beginPos - minPos;
            result.nodeText[0] = StringHelper.copyString(" ", spacesAddedToFirstLine)
                              + result.nodeText[0];
            // Since we now have added spacesAddedToFirstLine, we  execute
            adjustMappingPairVector(beginCol, -spacesAddedToFirstLine, result.mapping[0]) ;

            // Trim any necessary space from the beginning of result.nodeText[i] for i > 0.
            for (int i = 1; i < result.nodeText.length; i++) {
                result.nodeText[i] = result.nodeText[i].substring(minPos);
                adjustMappingPairVector(1, minPos, result.mapping[i]) ;
            }

            
            /*
             *  Compute the type and subType fields.
             */
            switch (sn.getKind()){
            case ASTConstants.OpApplKind:
                result.nodeType = EXPR_NODE ;
                /* 
                 * Compute subType field.
                 */
                // Set nd to the expression we should look at to compute
                // the subType, which is the expression obtained from sn
                // by removing an application of ' and expanding user definitions.
                OpApplNode nd = exposeRelevantExpr((OpApplNode) sn) ;
                
                UniqueString opId = nd.getOperator().getName();
                String opName = opId.toString();
                // Note \: experimentation revelas that 
                //  \lor and \/ both yield operator name \lor, and
                // \land and /\ both yield operator name \land
                if ((opId == ASTConstants.OP_cl) || opName.equals("\\land")) {
                        result.nodeSubtype = AND_TYPE;
                } else if ((opId == ASTConstants.OP_dl) || opName.equals("\\lor")) {
                        result.nodeSubtype = OR_TYPE;
                } else if (opName.equals("=>")) {
                        result.nodeSubtype = IMPLIES_TYPE;
                } else if ((opId == ASTConstants.OP_bf) || (opId == ASTConstants.OP_uf)) {
                        result.nodeSubtype = FORALL_TYPE;
                } else if ((opId == ASTConstants.OP_be) || (opId == ASTConstants.OP_ue)) {
                        result.nodeSubtype = EXISTS_TYPE;
                } else if (opId == ASTConstants.OP_sa) {
                        result.nodeSubtype = SQSUB_TYPE;
                } else {
                        result.nodeSubtype = OTHER_TYPE;
                }
                break;
            case ASTConstants.NewSymbKind:
                result.nodeType = NEW_NODE;
                break;
            case ASTConstants.LeafProofKind:
                result.nodeType = PROOF_NODE;
                break;
            default:
                result.nodeType = OTHER_NODE ;
            }
            
//            OpDefNode odn = new OpDefNode(UniqueString.uniqueStringOf("foo")) ;
//            boolean isBuiltIn = odn.getKind() == ASTConstants.BuiltInKind ;
            return result ;
        }
        
        
        /**
         * This constructor is used to construct a NodeRepresentation
         * object for the entire selected step and its leaf proof (if any).
         * 
         * @param document The document of the editor 
         * @param node
         * @throws BadLocationException
         */
        NodeRepresentation(IDocument document, SemanticNode node)
                throws BadLocationException {
            this.semanticNode = node ;
            Location location = node.stn.getLocation();
            nodeText = new String[location.endLine() - location.beginLine() + 1] ;
            mapping = new Vector[nodeText.length] ;
            for (int i = 0; i < mapping.length; i++) {
                mapping[i] = new Vector<MappingPair>() ;
                mapping[i].add(new MappingPair(1, -1)) ;
            }
            if (location.beginLine() == location.endLine()) {
                IRegion thmregion = EditorUtil.getRegionOf(document,
                        node.stn.getLocation());
                String str = document.get(thmregion.getOffset(),
                        thmregion.getLength());
                nodeText[0] = str ;
                return ;
            }
           
            IRegion region = document
                    .getLineInformation(location.beginLine() - 1);
            nodeText[0] = document.get(
                    region.getOffset() + location.beginColumn() - 1,
                    region.getLength() - location.beginColumn() + 1);
            // minCol is the min of the beginning column of the first line (with
            // the first column numbered 0) and the smallest number of leading
            // spaces of any later line
            int minCol = location.beginColumn() - 1;
            for (int i = 1; i < nodeText.length; i++) {
                region = document.getLineInformation(location.beginLine() - 1
                        + i);
                nodeText[i] = document.get(region.getOffset(), region.getLength());
                minCol = Math.min(minCol, StringHelper.leadingSpaces(nodeText[i]));
            }

            // remove the rest of the last line that's not part of the token's
            // text
            nodeText[nodeText.length - 1] = nodeText[nodeText.length - 1]
                    .substring(0, location.endColumn());

            // Add any necessary space at the beginning of nodeText[0]
            int spacesAddedToFirstLine = location.beginColumn() - minCol - 1 ;
            nodeText[0] = StringHelper.copyString(" ", spacesAddedToFirstLine)
                              + nodeText[0];
            mapping[0].elementAt(0).inc = -minCol-1;
            
            
            // Trim any necessary space from the beginning of nodeText[i] for i > 0.
            for (int i = 1; i < nodeText.length; i++) {
                nodeText[i] = nodeText[i].substring(minCol);
                mapping[i].elementAt(0).inc = -1 - minCol ;
            }
            return ;
        }
        
        /**
         * Constructs an empty object
         */
        public NodeRepresentation() {
            // TODO Auto-generated constructor stub
        }

        public String toString() {
            String val = "" ;
            if (originalOperator != null) {
                val = "Original Operator: " + originalOperator + "\n" ;
            }
            val = val + "nodeText: |=\n" + stringArrayToString(nodeText) + "=|" ;
            for (int i = 0; i < mapping.length; i++) {
                val = val + "\n" + i + ":" ;
                for (int j = 0; j < mapping[i].size(); j++) {
                    val = val + "  " + mapping[i].elementAt(j).toString() ;
                }
            }
            
            return val ;
        }
    }
    
    /**
     * A MappingPair contains two int-valued fields : `col' and `inc'.
     *  
     * A line-mapping is a mapping from column-numbers in a line of
     * the specification to positions in a string.  It is represented
     * by a vector V of MappingPair objects such that V[0].col = 1 and
     * i < j implies V[i].col < V[j].col.  Such an array represents the
     * line-mapping M such that M(c) equals c plus the sum of all 
     * V[i].inc such that V[i].col <= c.
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
        
        public DecomposeProofHandler.MappingPair clone() {
            return new MappingPair(this.col, this.inc) ;
            
        }
        public String toString() {
            return "<" + col + ", " + inc + ">" ;
        }
    }
    
    /**
     * Returns the string position to which the line-mapping defined by MappingPair
     * vec maps the column col.
     * 
     * @param col
     * @param vec
     * @return
     */    
    private int colToLoc(int col, Vector<MappingPair> vec) {
        int loc = col ;
        for (int i = 0 ; (i < vec.size()) && (vec.elementAt(i).col <= col) ; i++) {
            loc = loc + vec.elementAt(i).inc ;
        }
        return loc ;
    }
    
    /**
     * Modify vec so the line mapping nl it represents is related to the original
     * line mapping ol by 
     *     nl[c] = IF c < col THEN ol[c] ELSE ol[c] + incr
     * @param col
     * @param incr
     * @param vec
     * @return
     */
    private static void adjustMappingPairVector(int col, int incr, Vector<MappingPair> vec) {
        // set i to the smallest value such that vec[i].col >= col, or i = vec.size() if
        // there is none.
        int i;
        for (i = 0; (i < vec.size()) && (vec.elementAt(i).col < col); i++) {
        }
        
        if (i == vec.size()) {
            vec.add(new MappingPair(col, incr)) ;
        } else if (vec.elementAt(i).col == col){
            vec.elementAt(i).inc = vec.elementAt(i).inc + incr ;
        } else {
            vec.insertElementAt(new MappingPair(col, incr), i) ;
        }
    }
    
    /**
     * Returns a vector the same length as vec whose elements are clones of the elements
     * of vec.
     * @param vec
     * @return
     */
    private static Vector<MappingPair> cloneMappingPairVector(Vector<MappingPair> vec) {
        Vector<MappingPair> result = new Vector<DecomposeProofHandler.MappingPair>() ;
        for (int i=0 ; i < vec.size(); i++) {
            result.add(vec.elementAt(i).clone()) ;
        }
        return result ;
    }
    
    public String stringArrayToString(String[] A) {
        if (A.length == 0) {
            return A[0] ;
        }
        String result = A[0] ;
        for (int i = 1; i < A.length; i++) {
            result = result + "\n" + A[i] ;
        }
        return result ;
        
    }

    /*
     * The following are the types of buttons in the window
     */
    public static final int MENU = 1 ;
    public static final int ACTION = 2 ;
    public static final int CHECK = 3 ;
    
    /*
     * The followingidentify the various menu buttons.
     */
    
    public static final int PROVE_BUTTON = 1 ;
    public static final int TEST_BUTTON = 99 ;
    /**
     * Used to set various parameters of a button
     * 
     * @param button
     * @param type  The style type of the button.
     * @param text  The button's text
     */
    private void setupMenuButton(Button button, int whichOne, String text) {
            button.addSelectionListener(new 
                DecomposeProofButtonListener(this, new Integer(whichOne), MENU)) ;
            Image folderImg = PlatformUI.getWorkbench().getSharedImages().getImage(ISharedImages.IMG_LCL_LINKTO_HELP);
            String foo = ISharedImages.IMG_LCL_LINKTO_HELP ;
             button.setImage(folderImg);
//            button.setText(text) ; 
//            button.setSize(100, button.getSize().y);
            GridData gridData = new GridData();
            gridData.horizontalIndent = 5 ;
            button.setLayoutData(gridData) ;
        }
    
    private void setupCheckButton(Button button, String text) {
        // There doesn't seem to be a need to set a listener on a checkbutton;
        // It can be read when some action button is pushed.
//        button.addSelectionListener(new DecomposeProofButtonListener(this, button, CHECK)) ;
        button.setText(text) ; 
//        button.setSize(100, button.getSize().y);
        GridData gridData = new GridData();
        gridData.horizontalIndent = 10 ;
        button.setLayoutData(gridData) ;
    }

    private void setupActionButton(Button button, NodeRepresentation nodeRep, String text) {
        button.setText(text) ; 
//        button.setSize(30, button.getSize().y + 100);
        GridData gridData = new GridData();
        gridData.horizontalIndent = 15 ;
        gridData.verticalAlignment = SWT.TOP;
        button.setLayoutData(gridData) ;
        button.addSelectionListener(new DecomposeProofButtonListener(this, nodeRep, ACTION)) ;
        button.setFont(JFaceResources.getFontRegistry().get(JFaceResources.TEXT_FONT));
        if (text.equals("  ")) {
                button.setEnabled(false);
        }
    }
    
    /**
     * The listener for buttons on the DecomposeProof window.  The button
     * type tells what to do when clicked.  Data identifying the button or what
     * it should do is in the object fiel.
     * 
     * @author lamport
     *
     */
    public class DecomposeProofButtonListener extends SelectionAdapter implements SelectionListener {

        public Object execute(ExecutionEvent event) throws ExecutionException {
            // TODO Auto-generated method stub
            return null;
        }
 
        DecomposeProofHandler decomposeHandler ;
        int type ;
        Object object ;
        public DecomposeProofButtonListener(DecomposeProofHandler dHandler, Object but, int tp) {
            super();
            decomposeHandler = dHandler ;
            type = tp ;
            object = but ;
        }
        
        /**
         * Sent when selection occurs in the control.
         * The default behavior is to do nothing.
         *
         * @param e an event containing information about the selection
         */
        public void widgetSelected(SelectionEvent e) {
            readButtons() ;
            switch (type) {
            case MENU:
                System.out.println("MENU Click");
                int buttonId = ((Integer) object).intValue() ;
                switch (buttonId) {
                case PROVE_BUTTON :
                    displayHTML();
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
                    raiseWindow("Re-opened window "
                            + decomposeHandler.location.toString());
                    break;
                }
                break;               
            case ACTION:
                // Any ACTION button causes a change.
                changed = true ;
                NodeRepresentation nodeObj = (NodeRepresentation) object ;
                switch (nodeObj.nodeSubtype) {
                case NodeRepresentation.AND_TYPE:
                   decomposeHandler.andAction(nodeObj) ;
                   break ;
                case NodeRepresentation.OR_TYPE:    
                   break ;
                case NodeRepresentation.IMPLIES_TYPE:
                   break ;
                case NodeRepresentation.FORALL_TYPE:
                   break ;
                case NodeRepresentation.EXISTS_TYPE:
                   break ;
                case NodeRepresentation.SQSUB_TYPE:
                   break ;
                case NodeRepresentation.OTHER_TYPE: 
                   break ;
                }
                
               
                System.out.println("ACTION Click");
                break ;
// There doesn't seem to be any need to put a listener on a check button.                
//            case CHECK:
//                Button but = (Button) object ;
//                System.out.println("status = " + but.getSelection()) ;
//                but.setEnabled(false) ;
            }
        }

        /**
         * Sent when default selection occurs in the control.
         * The default behavior is to do nothing.
         *
         * @param e an event containing information about the default selection
         */
        public void widgetDefaultSelected(SelectionEvent e) {
            System.out.println("widgetDefaultSelected called") ;
            widgetSelected(e) ;
             
        }
        
    }
    
    /**
     * This is a DisposeListener for the window that sets the editor to be writable
     * and sets the handler's `location' * field to the window's current location, 
     * so it opens in the same place the next time the command is issued.
     * 
     * @author lamport
     *
     */
    class  WindowDisposeListener implements DisposeListener {
        DecomposeProofHandler commandHandler;
        
        WindowDisposeListener(DecomposeProofHandler handler) {
            commandHandler = handler;
            
        }

        public void widgetDisposed(DisposeEvent e) {
            commandHandler.location = windowShell.getLocation() ;
            // The following method was deprecated because it was actually possible to use
            // it, so it had to be replaced by something that requires a PhD in Eclipse
            // to figure out how to use.
            commandHandler.editorIFile.setReadOnly(false) ;
        }
    }
    
    /**
     * A convenience method that returns the first line of a semantic node's
     * source in a module.  I don't know what to do if the semantic node is
     * constructed and has no source.
     *  
     * @param nd
     * @return
     */
    static int getBeginLine(SemanticNode nd) {
        if (nd.stn == null) {
            System.out.println("getBeginLine called on node with null stn field.") ;
            return -1 ;
        }
        return nd.stn.getLocation().beginLine() ;
    }

    /**
     * A convenience method that returns the first line of a semantic node's
     * source in a module.  I don't know what to do if the semantic node is
     * constructed and has no source.
     *  
     * @param nd
     * @return
     */
    static int getEndLine(SemanticNode nd) {
        if (nd.stn == null) {
            System.out.println("getEndLine called on node with null stn field.") ;
            return -1 ;
        }
        return nd.stn.getLocation().endLine() ;
    }
    
    /**
     *  If nd is a step of a proof--that is, it is an element of the array returned by
     *  NonLeafProofNode.getSteps()--then this returns the level number of the proof, which
     *  is the i such that the step begins "<i>".  A little experimentation reveals that
     *  the parser turns "<+>" or "<*>" in the source into "<i>" for the appropriate i.
     * @param nd
     * @return
     */
    static int stepLevel(SemanticNode nd) {
        String stepStr = ((SyntaxTreeNode) nd.stn).getHeirs()[0].image.toString() ;
        String stepNum = stepStr.substring(stepStr.indexOf('<')+1, stepStr.indexOf('>')) ;
        return Integer.valueOf(stepNum).intValue();
    }

    /**
     * Performs the following operation to extract the descendant of an expr node that
     * that should be examined to see if it's an implication, a conjunction, or whatever.
     * 
     *          nd := oan ;
     *          if nd = expr'  then nd := expr
     *          if nd = Op(...) where Op is a user-defined symbol
     *                              and expr is the body of its definition
     *            then nd := expr
     *          if nd = expr'  then nd := expr
     *          return nd
     *          
     * Note that the first and last if test can't both be true.
     * 
     * @param oan
     * @return
     */
    static OpApplNode exposeRelevantExpr(OpApplNode oan) {
        OpApplNode nd = oan;
        if (nd.getOperator().getName() == ASTConstants.OP_prime) {
            nd = (OpApplNode) nd.getArgs()[0];
        }
        if (nd.getOperator().getKind() == ASTConstants.UserDefinedOpKind) {
            ExprNode opDef = ((OpDefNode) nd.getOperator()).getBody();
            if (opDef instanceof OpApplNode) {
                nd = (OpApplNode) opDef;
            } else {
                return nd;
            }
        }
        if (nd.getOperator().getName() == ASTConstants.OP_prime) {
            nd = (OpApplNode) nd.getArgs()[0];
        }
        return nd;
    }
        
        /**
         * Returns true iff some module of the spec is unsaved.  Code
         * taken from UIHelper.promptUserForDirtyModules.  This is not optimal because
         * it returns true even if the dirty module is not a spec module, but that's
         * not worth worrying about.
         * 
         * @return
         */
        public boolean existDirtyModules()
    {
        final List<IEditorReference> dirtyEditors = new LinkedList<IEditorReference>();
        IEditorReference[] references = UIHelper.getActivePage().getEditorReferences();
        if (references != null)
        {
            for (int i = 0; i < references.length; i++)
            {
                try
                {
                    if (references[i].isDirty() && references[i].getEditorInput().getName().endsWith(".tla"))
                    {
                        dirtyEditors.add(references[i]);
                    }
                } catch (PartInitException e)
                {
                    Activator.getDefault().logError("Error getting unsaved resources.", e);
                }
            }
        }

        return (dirtyEditors.size() > 0) ;
       
    }

}
