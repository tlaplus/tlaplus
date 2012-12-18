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
A, H |= C by expanding definitions D_1, ... , D_k.

Suppose that A, H |= C is then transformed to the equivalent
obligation  J, K, L |= C by expanding definitions E_1, ... , E_m
and introducing additional declarations NEW v_1, ... , NEW v_j,
where K has the form K_1 \/ ... \/ K_n.  Then A |= P has the
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

import java.io.File;
import java.io.IOException;
import java.net.MalformedURLException;
import java.net.URISyntaxException;
import java.net.URL;
import java.util.AbstractSet;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;
import java.util.Vector;

import org.eclipse.core.commands.AbstractHandler;
import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.core.commands.ExecutionException;
import org.eclipse.core.commands.IHandler;
import org.eclipse.core.resources.IFile;
import org.eclipse.core.runtime.FileLocator;
import org.eclipse.core.runtime.Path;
import org.eclipse.core.runtime.Platform;
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

import pcal.exception.StringVectorToFileException;

import tla2sany.parser.SyntaxTreeNode;
import tla2sany.semantic.ASTConstants;
import tla2sany.semantic.AssumeProveNode;
import tla2sany.semantic.ExprNode;
import tla2sany.semantic.ExprOrOpArgNode;
import tla2sany.semantic.FormalParamNode;
import tla2sany.semantic.LeafProofNode;
import tla2sany.semantic.LevelNode;
import tla2sany.semantic.ModuleNode;
import tla2sany.semantic.NonLeafProofNode;
import tla2sany.semantic.OpApplNode;
import tla2sany.semantic.OpDefNode;
import tla2sany.semantic.ProofNode;
import tla2sany.semantic.SemanticNode;
import tla2sany.semantic.SubstInNode;
import tla2sany.semantic.SymbolNode;
import tla2sany.semantic.TheoremNode;
import tla2sany.st.Location;
import util.UniqueString;

/**
 * Notes:
 * 
 *   For expanding a definition that comes from a different file, use subexpression naming.
 *   
 *   When expanding a definition like Foo(exp), the expression exp is treated as an 
 *   uninterpreted string.  Thus, if Id(x) == x , then an AND-split cannot be done 
 *   on Id(A /\ B) 
 *   
 *   What should be done about splitting formulas with LET-INs?
 *   
 *   Note that decomposition has to do renaming of bound variables in two cases:
 *    - When a bound variable in a \E is split out to a NEW variable, it may
 *      conflict with bound variables or NEW variables below it in the obligation.
 *    - When a definition is expanded, its bound variables may conflict with
 *      identifiers that are defined or declared in the current context.
 *   
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
    
    private SemanticNode goal ;
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
    boolean hasChanged;
    
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
     * andSplitBegin through (including) andSplitEnd.  If no AND split has 
     * been performed, then andSplitBegin and andSplitEnd equal -1.
     * 
     */
    int andSplitBegin;
    int andSplitEnd;
    
    /**
     * True iff the user has done something to change goal and/or set
     * of assumptions.  (This is used to disable the Replace option.)
     * 
     * Redundant.
     */
    // private boolean hasChanged = false ;
    
    /**
     * True iff an action has been performed on an assumption--either
     * an AND-split, a \E-split, or an OR-split.  Such an action disables
     * actions on other assumptions.  Once an \E-split or an OR-split
     * has been performed, at most one assumption node can have actions 
     * performed on it.  After an AND-split, only AND-split nodes can
     * have enabled actions.
     */
    private boolean assumeHasChanged = false ;  
    
    /** 
     * The set of Ids of user-defined operations whose definitions 
     * were expanded in decomposing the assumptions.
     */
    private HashSet<String> assumeDefinitions = new HashSet<String> ();
    
    /** 
     * The set of Ids of user-defined operations whose definitions 
     * were expanded in decomposing the goal.
     */
    private HashSet<String> goalDefinitions = new HashSet<String> ();

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
     * 
     * Its initial value should probably be set by a preference.
     */
    private boolean useSufficesValue = true;
    private Button useSufficesButton;  // 
    
    /**
     * The subexpressionButton determines if an occurrence of a user-defined
     * operator should be expanded by replacing it with its definition,
     * or by using subexpression names like Op(43)!2.  In the initial
     * implementation, definitions that come from a different module are
     * always expanded by using subexpression names.
     * 
     * Its initial value should probably be set by a preference.
     */
    private boolean subexpressionValue = true ; 
    private Button subexpressionButton ; 
    
            
    /**
     * Record the state of the top menu's check buttons.
     */
    private void readButtons() {
        useSufficesValue = useSufficesButton.getSelection() ;
        subexpressionValue = subexpressionButton.getSelection() ;
    }
    // private IRegion lineInfo; // The lineInfo for the current offset.

    
    /**
     * TEST OF HELP BUTTON.  Rename this to execute for test.
     * @param event
     * @return
     * @throws ExecutionException
     */
    public Object testExecute(ExecutionEvent event) throws ExecutionException {
        /**
         * TESTING STUFF
         */
//        Bundle bundle = Platform.getBundle("org.lamport.tla.toolbox.doc");
//        URL fileURL = bundle.getEntry("html/prover/test.html");
//        File file = null;try {    
//           file = new File(FileLocator.resolve(fileURL).toURI());
//        } catch (URISyntaxException e1) {   
//            e1.printStackTrace();} catch (IOException e1) { 
//           e1.printStackTrace();}
//        System.out.println("url = " + file.getPath());
        /**
         * END TESTING STUFF
         */
        Shell topshell = UIHelper.getShellProvider().getShell() ;
        windowShell = new Shell(topshell, SWT.SHELL_TRIM) ; // | SWT.H_SCROLL); // SWT.RESIZE) ; // | SWT.V_SCROLL | SWT.H_SCROLL) ;
        windowShell.setText("Leslie's Test") ;
        Composite shell = windowShell; // new Composite(windowShell, SWT.NONE) ;
        GridLayout gridLayout = new GridLayout(2, false);
        shell.setLayout(gridLayout);
        // Set up the help button
        Button helpButton = HelpButton.helpButton(shell, "prover/prover.html");
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
        
//        Bundle bundle = FrameworkUtil.getBundle(this.getClass());
//        url = bundle.getLocation() ;
        
        
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
    
//    public class HelpButtonListener extends SelectionAdapter implements SelectionListener {
//
//        public void widgetSelected(SelectionEvent e) {
//            displayHTML();
//        }
//        
//        public void widgetDefaultSelected(SelectionEvent e) {
//            displayHTML();
//        }
//
//    }
    
    /**
     * THE REAL EXECUTE METHOD
     * 
     * The execute method is called when the user issues a DecomposeProof
     * command.
     *  
     * @see
     * org.eclipse.core.commands.IHandler#execute(org.eclipse.core.commands.
     * ExecutionEvent)
     */
    public Object execute(ExecutionEvent event) throws ExecutionException {

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
        hasChanged = false ;
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
                NodeRepresentation nodeRep = stepRep.subNodeRep(assump[i], assumeReps, null, null) ;
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
                
               goal = ((AssumeProveNode) thm).getProve();
               if (! (goal instanceof OpApplNode)) {
                   MessageDialog
                   .openError(UIHelper.getShellProvider().getShell(),  
                               "Decompose Proof Command",
                               "This step has a weird goal that cannot\n be processed.");
                   return null ;
               }
               
                goalRep = stepRep.subNodeRep(goal, null, null, null );
            }
            
        } else {
            /**************************************************************
             * This is not an ASSUME/PROVE, so have to set assumes and
             * assumesRep to null and check that this isn't something like a QED
             * step that the command doesn't handle.
             *************************************************************/
            assumes = null;
            assumeReps = null;
            if (! (thm instanceof OpApplNode)) {
                MessageDialog
                .openError(UIHelper.getShellProvider().getShell(),  
                            "Decompose Proof Command",
                            "This is a weird step that cannot\n be processed.");
                return null ;
            }
            goal = thm;
            UniqueString goalOpName = null ;
            if (goal instanceof OpApplNode) {
                goalOpName = ((OpApplNode) goal).getOperator().getName();
            }

            // Abort if this is one of the following kinds of steps:
            // QED, HAVE, PICK, WITNESS, SUFFICES
            if (       (goalOpName == null)
                    || (goalOpName == ASTConstants.OP_qed)
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
            goalRep = stepRep.subNodeRep(goal, null, null, null);
        }
//        if (goalRep.decomposition == null) {
//            System.out.println("null decomposition");
//        } else {
//            System.out.println("goalRep.decomposition:");
//            System.out.println(goalRep.decomposition.toString());
//        }
              
        
        /***************************************************************************
         * Make the editor read-only.
         ***************************************************************************/
        // The following method is deprecated because it is actually possible to use
        // it, so it has been replaced by something that requires a PhD in Eclipse
        // to figure out how to use.  The command 
        //
        //      EditorUtil.setReadOnly(editorIFile, true);
        //
        // that has worked in other places in the Toolbox code seems to work here
        // only occasionally.  This being modern 21st century code, I have the 
        // choice of reading 10^6 lines of code to figure out what is going on,
        // or doing what seems to work. 
        editorIFile.setReadOnly(true) ;
        raiseWindow() ;
        
        return null;
    }
    

    // Note: Experimentation seems to show that horizontalSpan doesn't apply to a Label 
    // or a Button, so I've been putting the Label or Button inside a composite to do that.
    private void raiseWindow() {
        // for testing
        // topshell = the Toolbox's shell
        if ((windowShell != null) && (!windowShell.isDisposed())) {
            location = windowShell.getLocation() ;
            windowShell.close();
            windowShell.dispose();
        }
        Shell topshell = UIHelper.getShellProvider().getShell() ;
        windowShell = new Shell(topshell, SWT.SHELL_TRIM) ; // | SWT.H_SCROLL); // SWT.RESIZE) ; // | SWT.V_SCROLL | SWT.H_SCROLL) ;
        windowShell.setText("Decompose Proof") ;
        windowShell.addDisposeListener(new WindowDisposeListener(this)) ;
        Composite shell = new Composite(windowShell, SWT.NONE) ;
        GridLayout gridLayout = new GridLayout(3, false);
        shell.setLayout(gridLayout);
        /**
         * Display the top-line window
         */
        // topMenu is a composite containing the stuff on the menu line.
        Composite topMenu = new Composite(shell,SWT.NONE) ;   
        gridLayout = new GridLayout(4, false);
        gridLayout.marginBottom = 0;
        topMenu.setLayout(gridLayout);        
        GridData gridData = new GridData() ;
        gridData.horizontalSpan = 3;
        topMenu.setLayoutData(gridData) ;
        
        // Display "Replace Step" button
        Button replaceButton = new Button(topMenu, SWT.PUSH) ;
        setupMenuButton(replaceButton, TEST_BUTTON, "Replace Step") ;
        replaceButton.setEnabled(hasChanged && (chosenSplit == -1) && (andSplitEnd == -1)) ;
        
        // Display "Use SUFFICES" checkbox.
        useSufficesButton = new Button(topMenu, SWT.CHECK);
        setupCheckButton(useSufficesButton, "Use SUFFICES") ;
        useSufficesButton.setSelection(useSufficesValue) ;

        // Display checkbox to choose whether to expand definitions with 
        // subexpression names.
        subexpressionButton = new Button(topMenu, SWT.CHECK);
        setupCheckButton(subexpressionButton, "Use subexpression names");
        subexpressionButton.setSelection(subexpressionValue) ;
        gridData = new GridData() ;
        gridData.horizontalAlignment = GridData.FILL;
        gridData.grabExcessHorizontalSpace = true ;
        subexpressionButton.setLayoutData(gridData) ;
        
        // Display Help button that should raise help page for this
        // dialog window.  I wish I knew how to move the button to
        // the right edge of the window.
        Button helpButton = HelpButton.helpButton(topMenu, "prover/test.html") ;
        gridData = new GridData() ;
        gridData.horizontalIndent = 20;
        helpButton.setLayoutData(gridData);
      
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
                // Need to test if assumes.elementAt(i) is null because created
                // NEW nodes have null semanticNode fields.
                if (    (assumes.elementAt(i) != null) 
                     && (assumes.elementAt(i).getKind() == ASTConstants.OpApplKind)) {
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
                    arrowButton.addSelectionListener(new ArrowSelectionListener (i, SWT.UP, this));
                    gridData = new GridData();
                    gridData.verticalAlignment = SWT.TOP;
                    arrowButton.setLayoutData(gridData);
                    if (i == andSplitBegin) {
                        arrowButton.setEnabled(false);
                    }
                    arrowButton = new Button(comp, SWT.ARROW | SWT.DOWN);
                    arrowButton.addSelectionListener(new ArrowSelectionListener (i, SWT.DOWN, this));
                    
                    gridData = new GridData();
                    gridData.verticalAlignment = SWT.TOP;
                    arrowButton.setLayoutData(gridData);
                    if (i == andSplitEnd) {
                        arrowButton.setEnabled(false);
                    }
                }
                

                assumeLabel = new Label(comp, SWT.NONE);
                String text = stringArrayToString(assumeReps.elementAt(i).primedNodeText()) ;
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
        assumeLabel.setText(stringArrayToString(goalRep.primedNodeText()));
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
        // See the comments on the following command where it is used in the execute 
        // method.
        editorIFile.setReadOnly(true);
    }
    
    
//   private void displayHTML() {
//        Shell topshell = UIHelper.getShellProvider().getShell() ;
//        Shell shell = new Shell(topshell, SWT.SHELL_TRIM) ;
//        shell.setLayout(new FillLayout());
//        Browser browser;
//        try {
//          browser = new Browser(shell, SWT.NONE);
//    } catch (SWTError e) {
//            System.out.println("Could not instantiate Browser: " + e.getMessage());
//            shell.dispose();
//            return;
//    }
//        
//        Bundle bundle = FrameworkUtil.getBundle(this.getClass());
//        String url = bundle.getLocation() ;
//        System.out.println("What's going on");
//        int idx = url.indexOf("reference:file:/");
//        System.out.println("original url = " + url);
//        if (idx == 0) {
//            url = url.substring("reference:file:/".length()) ;
//        }
//        String url2 = url + "html/prover/test.html" ;
//        String url1 = url ;
//        idx = url.indexOf("org.lamport.tla.toolbox.editor.basic/") ;
//        if (idx == url.length() - "org.lamport.tla.toolbox.editor.basic/".length()) {
//            url1 = url.substring(0, idx) + 
//              "org.lamport.tla.toolbox.doc/html/prover/test.html";
//        }
//    System.out.println(url1); // + ",  " + url2);
////    String html = "<BODY BGCOLOR=#ffffe4>" +
////                  "<PRE> this is some pre\n another line \n</PRE>" +
////                 "a b <i>c</i> d <font color=#ff00001>Large</font>" + 
////                 "</BODY>";
//       browser.setUrl(url1) ;
//
////    browser.setText(html);
//    shell.open();
//    }
//    
    /***************************************************************************
     * The action-button handlers
     ****************************************************************************/
    
    /**
     * The /\ action, both for a goal (which generates the proof) and
     * for an assumption (which splits the assumption).  
     * 
     * Precondition: if this is an AND-split of assumption assumeReps(i),
     * then either andSplitBegin = -1 or andSplitBegin \leq i \leq andSplitEnd.
     * 
     * @param nodeRep
     */
    void andAction(NodeRepresentation nodeRep) {
        boolean isPrimed = false;
        boolean defExpanded = false;
        /**
         * Set conjuncts to the vector of conjunctions.
         */
        Vector<OpApplNode> conjunctions = new Vector<OpApplNode>();
        if (nodeRep.parentVector == null) {
            /**
             * This is a "prove by AND-split" operation.
             */
            // not yet implemented
            System.out.println(stringArrayToString(createdAssumptions()));
            
            return;
        } else {
            /**
             * This is an AND-SPLIT of an assumption, so nodeRep equals
             * assumeReps(i) for some i and parentNode = null. We set idx to i,
             * and we set decomp to the Decomposition object.
             * 
             */
            int idx = nodeRep.getParentIndex();
            Decomposition decomp = nodeRep.decomposition;

            // Modify hasChanged, assumeHasChanged, and assumeDefinitions.
            hasChanged = true;
            assumeHasChanged = true;
            if (decomp.definedOp != null) {
                assumeDefinitions.add(decomp.definedOp);
            }

            // Remove this assumption and insert the split nodes in its place.
            // Set newSemanticNodes to the vector of new assumptions.
            Vector<SemanticNode> addedAssumps = decomp.children;
            this.assumes.remove(idx);
            this.assumeReps.remove(idx);
            for (int i = 0; i < addedAssumps.size(); i++) {
                // Call decompositionChildToNodeRep to construct the child's
                // NodeRepresentation.
                NodeRepresentation rep = decompositionChildToNodeRep(nodeRep,
                        i, this.assumeReps, null);
                this.assumes.add(idx + i, decomp.children.elementAt(i));
                this.assumeReps.add(idx + i, rep);

            }

            // Update andSplitBegin & andSplitEnd. Recall the precondition.
            if (andSplitBegin == -1) {
                andSplitBegin = idx;
                andSplitEnd = idx + addedAssumps.size() - 1;
            } else {
                andSplitEnd = andSplitEnd + addedAssumps.size() - 1;
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
        hasChanged = true;
        if (decomp.definedOp != null) {
            goalDefinitions.add(decomp.definedOp);
        }
        
        QuantifierDecomposition qdc = decomposeQuantifier(nodeRep, true) ;
        this.goalRep = qdc.body ;
        // I think that, once we start decomposing things, goal
        // may be used in calling primingNeedsParens
        this.goal = qdc.body.semanticNode ; 
        
        for (int i = 0; i < qdc.news.size(); i++) {
            this.assumeReps.add(qdc.news.elementAt(i)) ;
            this.assumes.add(qdc.news.elementAt(i).semanticNode) ;
        }
        raiseWindow();
    }
    
    void impliesAction(NodeRepresentation nodeRep) {
        Decomposition decomp = nodeRep.decomposition;
        hasChanged = true;
        if (decomp.definedOp != null) {
            goalDefinitions.add(decomp.definedOp);
        }
        
     // If this is within the subexpression-name expansion of a definition,
        // set NodeTextRep to the NodeTextRep that is the name of the formula
        // represented by nodeRep.
        NodeTextRep newNodeText = null;
        if ((decomp.definedOp != null)
               // && (subexpressionButton.getSelection()) // uncomment for def expansion
                ) {
            newNodeText = decomp.definedOpRep ;
        } else if (nodeRep.isSubexpressionName) {
            newNodeText = new NodeTextRep(nodeRep.nodeText, nodeRep.mapping);
        }
        
        NodeTextRep ntrep = null ;
        if (newNodeText != null) {
            ntrep = appendToNodeText(newNodeText, "!1") ;
        }
        NodeRepresentation nrep = nodeRep.subNodeRep(decomp.children.elementAt(0), 
                nodeRep.parentVector, nodeRep.parentNode, ntrep) ;
        nrep.isCreated = true;
        nrep.isPrimed = nrep.isPrimed || decomp.primed;
        nrep.isSubexpressionName = 
                nrep.isSubexpressionName || (decomp.definedOp != null);
        this.assumeReps.add(nrep) ;
        this.assumes.add(nrep.semanticNode);
          // I don't think the assumes vector is used after decomposition is
          // begun, but I'm not positive.
        
        ntrep = null ;
        if (newNodeText != null) {
            ntrep = appendToNodeText(newNodeText, "!2") ;
        }
        nrep = nodeRep.subNodeRep(decomp.children.elementAt(1), 
                nodeRep.parentVector, nodeRep.parentNode, ntrep) ;
        nrep.isCreated = true;
        nrep.isPrimed = nrep.isPrimed || decomp.primed;
        nrep.isSubexpressionName = 
                nrep.isSubexpressionName || (decomp.definedOp != null);
        this.goalRep = nrep;
        // I think that, once we start decomposing things, goal
        // may be used in calling primingNeedsParens
        
        this.goal = nrep.semanticNode ; 
        
        raiseWindow();
    }

    /**
     * Returns the NodeRepresentation for a child in nodeRep's decomposition when
     * nodeRep's formula is decomposed.
     * 
     * @param nodeRep  The NodeRepresentation whose decomposition child's representation
     *   is returned.
     * @param i  The index of the child in nodeRep's decomposition's children vector.
     * @param vec     The result's parentVector field.
     * @param father The result's parentNode field.
     * @return
     */
    NodeRepresentation decompositionChildToNodeRep(NodeRepresentation nodeRep, int i,  
            Vector <NodeRepresentation> vec, NodeRepresentation father) {
        // decomp is the nodeRep's decomposition
        Decomposition decomp = nodeRep.decomposition;
        
        // Set newNodeText to be null if the result's nodeText is to be obtained
        // from nodeText's semantic node.  Otherwise, set it to the appropriate
        // subexpression name.  
        NodeTextRep newNodeText = null;
        if ((decomp.definedOp != null) 
             // && this.subexpressionButton.getSelection() 
             // commented out because only expanding definitions by subexpression 
             // names for now.
             ){
            newNodeText = appendToNodeText(decomp.definedOpRep,
                    decomp.namePath.elementAt(i));
        } else if (nodeRep.isSubexpressionName) {
            newNodeText = appendToNodeText(new NodeTextRep(
                    nodeRep.nodeText, nodeRep.mapping),
                    decomp.namePath.elementAt(i));
        }
        
        // Call subNodeRep to construct the result.
        NodeRepresentation rep = nodeRep.subNodeRep(
                decomp.children.elementAt(i), nodeRep.parentVector, nodeRep.parentNode,
                newNodeText);
        // Set various fields whose values can be inferred from nodeRep and decomp.
        // Don't set rep.isCreated because don't want it set for an
        // AND-split of an assumption, unless that assumption came from
        // a split of the goal.
        //
        // rep.isCreated = true;
        rep.isPrimed = rep.isPrimed || decomp.primed;
        rep.isSubexpressionName = 
                nodeRep.isSubexpressionName || (decomp.definedOp != null);        
        return rep ;
    }
    
    /**
     * Since Java doesn't allow structs, this is a class whose sole purpose is
     * to provide a return type for the following method.  Its fields are
     * a vector of NodRepresentations that will be a vector of NEW nodes obtained from
     * a quantified expression, and a NodeRepresentation obtained from the body
     * of that expression.
    */
    static class QuantifierDecomposition {
        Vector<NodeRepresentation> news ;
        NodeRepresentation body ;
    }
    
    /**
     * Returns the NodeRepresentations of the nodes forming the decomposition
     * for a \A or \E split.  It assumes that the decomposition is
     * a \A or \E decomposition, so its quantIds field is not null.
     * The NodeRepresentations for the NEW assumptions are given a null
     * semanticNode field, since I don't think that field is ever used once
     * decomposition begins.  The isForAll argument is used to determine
     * whether the body's created field should be set true.
     * 
     * Must be enhanced to handle a decomposition that comes from a full expansion of
     * a defined operator.
     * 
     * @param decomp
     * @param isForAll  True iff this is called for a \A split
     * @return
     */
    QuantifierDecomposition decomposeQuantifier(NodeRepresentation nodeRep,
            boolean isForAll) {
        QuantifierDecomposition result = new QuantifierDecomposition();
        
        result.news  = new Vector<NodeRepresentation>() ;
        Decomposition decomp = nodeRep.decomposition;
        
        // If this is within the subexpression-name expansion of a definition,
        // set NodeTextRep to the NodeTextRep that is the name of the formula
        // represented by nodeRep.
        NodeTextRep newNodeText = null;
        if ((decomp.definedOp != null)
               // && (subexpressionButton.getSelection()) // uncomment for def expansion
                ) {
            newNodeText = decomp.definedOpRep ;
        } else if (nodeRep.isSubexpressionName) {
            newNodeText = new NodeTextRep(nodeRep.nodeText, nodeRep.mapping);
        }
        
        // We first compute the vector of NEW assumptions
        int lastLine = -1 ;
        for (int i = 0; i < decomp.quantIds.size(); i++) {
            // Loop invariant:
            //  lastRow != -1 iff /\ i > 0 
            //                    /\ \/ this is an unbounded quantifier
            //                       \/ the i-1st NEW fits entirely on line lastLine
            NodeRepresentation rep = new NodeRepresentation() ;
            rep.semanticNode = null ;
            rep.nodeType = NodeRepresentation.NEW_NODE;
            rep.isCreated = true ;
            rep.parentNode = nodeRep.parentNode ;
            if (nodeRep.parentVector != null) {
                rep.parentVector = nodeRep.parentVector ;
            } else {
                // nodeRep is the current goal and so the NEW assumptions
                // will become top-level assumptions and rep.parentVector
                // should be set to the DecomposeProofHandler's assumeRep
                // vector. 
                rep.parentVector = this.assumeReps ;
            }
            
            // set id to "NEW" plus the bound identifier
            NodeTextRep ntrep = new NodeTextRep() ;
            String id = "NEW " + decomp.quantIds.elementAt(i).getName().toString();
            
            // beginLine is set to the line containing the source if there is
            // no quantifier bound or the quantifier bound occupies a single line.
            // Otherwise, it is set to -1.
            int beginLine = ((SyntaxTreeNode) 
                    decomp.quantIds.elementAt(i).stn).getLocation().beginLine();
            if (decomp.quantBounds == null) {
                // Set ntrep to a trivial NodeTextRep representing a 
                // 1-line string with a standard mapping that should never
                // be used.
                ntrep.nodeText = new String[1] ;
                ntrep.nodeText[0] = id;
                ntrep.mapping = new Vector[1] ;
                ntrep.mapping[0] = new Vector<MappingPair> ();
                ntrep.mapping[0].addElement(new MappingPair(1, -1)) ;
            } else {
                // Set ntrep to be a NodeTextRep for the quantifier bound,
                // primed if decomp.primed or nodeRep.isPrimed is = true.
                if (newNodeText == null) {
                    // The bound is not a subexpression name.
                    ntrep = nodeRep.subNodeText(decomp.quantBounds.elementAt(i));
                    if (decomp.primed || nodeRep.isPrimed) {
                        if (primingNeedsParens(decomp.quantBounds.elementAt(i))) {
                            ntrep = prependToNodeText(appendToNodeText(ntrep, ")'"), "(");
                        } else {
                            ntrep = appendToNodeText(ntrep, "'") ;
                        }
                    }
                } else {
                    // The bound is a subexpression name.
                    String str = decomp.quantBoundsubexpNames.elementAt(i);
                    if (decomp.primed) {
                        str = str + "'" ;
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
            rep.nodeText = ntrep.nodeText ;
            rep.mapping  = ntrep.mapping ;
            result.news.add(rep) ;
            if ((beginLine != -1) && (beginLine == lastLine)) {
              result.news.elementAt(i-1).onSameLineAsNext = true ;
            }
            lastLine = beginLine ;
        }
        
        // We next compute the NodeRepresentation for the body of the quantified
        // expression.
        if (newNodeText != null) {
            // We are using subexpression names, so we append to newNodeText
            // the "!(id1, ... , idn)" needed to form the subexpression name
            // of the body.
            String str = "!(" ;
            for (int i = 0; i < decomp.quantIds.size(); i++) {
                if (i != 0) {
                    str = str + ", " ;
                }
                str = str + decomp.quantIds.elementAt(i).getName().toString();
            }
            str = str + ")";
            newNodeText = appendToNodeText(newNodeText, str);
        }
        result.body = nodeRep.subNodeRep(decomp.children.elementAt(0), 
                nodeRep.parentVector, nodeRep.parentNode, newNodeText) ;
        result.body.isCreated = isForAll;
        result.body.isPrimed = result.body.isPrimed || decomp.primed;
        result.body.isSubexpressionName = 
                nodeRep.isSubexpressionName || (newNodeText != null); 
        return result;
    }
    
    /**
     * Returns string array such that applying stringArrayToString to it
     * produces the text of a list of of assumptions in this.assumeReps 
     * for which the isCreated field equals true.
     */
    String[] createdAssumptions() {
        /** 
         * Sets vec to a vector of string arrays such that applying stringArrayToString to 
         * each of them produces the text of an assumption in this.assumeReps 
         * for which the isCreated field equals true--except that multiple
         * one-line NEW assumptions are combined into a single 1-line string array.
         */
        Vector<String[]> vec = new Vector<String[]>() ;
        for (int i = 0; i < this.assumeReps.size(); i++) {
            NodeRepresentation rep = assumeReps.elementAt(i) ;
           if (rep.isCreated) {
                String newDecls = null ;
                while (rep.onSameLineAsNext) {
                  if (newDecls != null) {
                      newDecls = newDecls + ", " ;
                  } else {
                      newDecls = "" ;
                  }
                  newDecls = newDecls + rep.nodeText[0];
                  i++ ;
                  rep = assumeReps.elementAt(i) ;
                }
                if (newDecls == null) {
                   vec.add(rep.primedNodeText()) ;
                } else {
                    vec.add(new String[] {newDecls + ", " + rep.nodeText[0]});                 
                }
            }
        }
        
        /**
         * Sets resVec to a single vector obtained by combining the elements
         * of vec, putting commas between them.
         */
        
        Vector<String> resVec = new Vector<String>();
        for (int i = 0; i < vec.size(); i++) {
            String[] strArray = vec.elementAt(i) ;
            for (int j = 0; j < strArray.length; j++) {
                String str = strArray[j] ;
                if ((j == strArray.length - 1) && (i != vec.size() - 1)) {
                    str = str + "," ;
                }
                resVec.add(str) ;
            }
        }
        
        // Convert resVec to the array result and return it.
        String[] result = new String[resVec.size()];
        for (int i = 0; i < result.length; i++) {
            result[i] = resVec.elementAt(i);
        }
        return result ;
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
        // I don't think this is needed.
        // String originalOperator = null ;

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
         * True iff this is a NEW assumption that was not in the original
         * obligation, or it is an ExprNode that was created by splitting
         * the goal. 
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
        
        /**
         * True iff the formula represented by this node has an implicit prime
         * that does not appear in the semanticNode or nodeText fields.
         */
        boolean isPrimed = false ;
        
        /**
         * If this is true, then the semanticNode field represents the expansion
         * of the subexpression name that appears in the nodeText field.  This means
         * that the node has been obtained by decomposing another node by expanding
         * a definition, so no further decomposition by expanding a definition
         * is possible.  (Using a subexpression name, it's impossible to name the
         * result of expanding a definition unless it's a LET definition inside
         * the current definition.  I'm not sure what should be done with LET definitions
         * inside assumptions or goals.)
         */
        boolean isSubexpressionName = false ;
        
        /**
         * The formula represented by this node was obtained by expanding
         * the definitions of all the identifiers in this array.
         * 
         * I don't think this is needed.
         */
        // String[] expandedDefs = new String[0];
        
        /**
         * Non-null iff the node can be decomposed as indicated by
         * the Decomposition object.
         */
        Decomposition decomposition = null ;
        
        /**
         * Create a NodeRepresentation for a subnode of this node.
         * 
         * @param sn  The subnode
         * @param vec The result's parentVector field.
         * @param father The result's parentNode field.
         * @param newNodeText If non-null, then the result's nodeText field is 
         *   to be set to this rather than the NodeTextRep representation of
         *   the semanticNode field. It will be non-null if the nodeText is to
         *   be set to a subexpression name, so set isSubexpressionName field
         *   true in that case.
         * @return
         */
        NodeRepresentation subNodeRep(SemanticNode sn, Vector <NodeRepresentation> vec,
                                     NodeRepresentation father, NodeTextRep setNodeText) {
            
            NodeRepresentation result = new NodeRepresentation() ;
            result.parentNode = father;
            result.parentVector = vec ;
            result.semanticNode = sn ;
            
            // Set the fields of the result that are inherited from the node it's
            // a subnode of.
            result.isPrimed = this.isPrimed;
            result.isSubexpressionName = this.isSubexpressionName;
            
            // If the original node came from splitting the
            // goal, then this node also came from splitting the
            // goal.
            result.isCreated = this.isCreated;
              
            NodeTextRep nodeTextRep = setNodeText;
            if (nodeTextRep == null ) {
              nodeTextRep = this.subNodeText(sn);
            } else {
                result.isSubexpressionName = true ;
            }
            result.nodeText = nodeTextRep.nodeText;
            result.mapping = nodeTextRep.mapping;
            
            /*
             *  Compute the type, subType, and decomposition fields an
             */
            switch (sn.getKind()){
            case ASTConstants.OpApplKind:
                result.nodeType = EXPR_NODE ;
                
                result.decomposition = decompose(result) ;
                if (result.decomposition == null) {
                    result.nodeSubtype = OTHER_TYPE;
                } else {
                    result.nodeSubtype = result.decomposition.type;
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
         * This is like subNodeRep except it returns only the fields contained
         * in a NodeText.  It is called by subNodeRep to set those fields.
         * 
         * @param sn
         * @return
         */
        NodeTextRep subNodeText(SemanticNode sn) {
            NodeTextRep result = new NodeTextRep();
//            result.semanticNode = sn ;
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
            adjustMappingPairVector(beginCol, spacesAddedToFirstLine, result.mapping[0]) ;

            // Trim any necessary space from the beginning of result.nodeText[i] for i > 0.
            for (int i = 1; i < result.nodeText.length; i++) {
                result.nodeText[i] = result.nodeText[i].substring(minPos);
                adjustMappingPairVector(1, -minPos, result.mapping[i]) ;
            }
            return result;
        }
        
        /**
         * If this.isPrimed is false, it just returns this.nodeText.  Otherwise,
         * it returns the primed version of this.nodeText.  It tries to be
         * clever and not put parentheses around the text if they're not needed.
         * Parentheses are not needed if isSubexpressionName is true, or
         * if primingNeedsParens(...) says they're not needed.
         */
        String[] primedNodeText() {
            if (!this.isPrimed) {
                return this.nodeText;
            }

            boolean needsParens = (!this.isSubexpressionName)
                    && primingNeedsParens(this.semanticNode);

            String[] result = this.nodeText.clone();
            if (needsParens) {
                result[0] = "(" + result[0];
                result[result.length - 1] = StringHelper
                        .trimEnd(result[result.length - 1]) + ")'";
            } else {
                result[result.length - 1] = StringHelper
                        .trimEnd(result[result.length - 1]) + "'";
            }
            return result;
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
//            if (originalOperator != null) {
//                val = "Original Operator: " + originalOperator + "\n" ;
//            }
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
     * A NodeTextRep object contains only the  nodeText, and mapping
     * fields of a NodeRepresentation object.  I should probably refactor
     * things so that instead of having those two fields, a NodeRepresentation
     * object contains a NodeText field
     */
    static class NodeTextRep {
//        SemanticNode semanticNode = null ;
        String[] nodeText = null ;
        Vector<MappingPair>[] mapping = null ;
        
        public NodeTextRep(String[] text, Vector<MappingPair>[] map) {
//            semanticNode = node ;
            nodeText = text;
            mapping = map ;
        }
        
        public NodeTextRep() {
            // TODO Auto-generated constructor stub
        }

        public NodeTextRep clone() {
            NodeTextRep result = new NodeTextRep() ;
            result.nodeText = new String[this.nodeText.length];
            for (int i = 0; i < result.nodeText.length; i++) {
                result.nodeText[i] = this.nodeText[i];
            }
            result.mapping = this.mapping.clone() ;
            return result ;
        }
        
        public String toString() {
            String val = "" ;
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
     * Returns a brand new NodeTextRep obtained thats equal to the nodeRep argument
     * except that the String str has been appended to the last line.
     * 
     * @param nodeRep
     * @param str
     * @return
     */
    static NodeTextRep appendToNodeText(NodeTextRep nodeRep, String str) {
        NodeTextRep result = nodeRep.clone();
        result.nodeText[result.nodeText.length - 1] = 
                result.nodeText[result.nodeText.length - 1] + str;
        return result;
    }
    
    static NodeTextRep prependToNodeText(NodeTextRep nodeRep, String str) {
        NodeTextRep result = nodeRep.clone();
        for (int i = 0; i < nodeRep.nodeText.length; i++) {
            if (i==0) {
               result.nodeText[0] = str + result.nodeText[0] ;
            } else {
               result.nodeText[i] = StringHelper.copyString(" ", str.length());
            }
            adjustMappingPairVector(1, str.length(), result.mapping[i]) ;
        }       
        return result;
    }
    
    
    /**
     * A Decomposition object describes the possible decomposition of
     * an assumption or goal.
     * 
     * @author lamport
     *
     */
    static class Decomposition {
        /**
         * The type of decomposition.  Its value is any of the first six 
         * possible nodeSubtype values of a NodeRepresentation object.
         * This is redundant information, since for any NodeRepresentation
         * object nd, nd.nodeSubtype should equal nd.decomposition.type
         * if nd.decomposition is non-null. 
         */
        int type ;
        
        /**
         * If non-null, then the decomposition is to be performed by
         * expanding the definition of this (user-defined) symbol.
         */
        String definedOp = null ;
        
        /**
         * If non-null, then this is the NodeTextRep representing the operator use
         * that is to be expanded.  E.g., it could represent source text such as
         * 
         *     Foo(a + b,
         *         c)
         */
        NodeTextRep definedOpRep = null ;
        
        /**
         * If definedOp is not null, then this is the name of the
         * module containing the node's definition.
         */
        String moduleName = null;
        
        /**
         * The nodes into which the assumption or goal is to be decomposed.
         */
        Vector<SemanticNode> children = new Vector<SemanticNode>() ;
        
        /**
         * If definedOp is the string "foo", then children.elementAt(i)
         * has the name "foo" + namePath.elementAt(i).
         * 
         */
        Vector<String> namePath = new Vector<String>() ;   
        
        /** 
         * If this is a \A or \E decomposition, then this is the list
         * of bound identifiers.
         */
        Vector<FormalParamNode> quantIds = null ;
        
        /**  
         * If this is a \A or \E decomposition for a bounded quantifier (like
         *   \A x \in S), then this is the list of bound identifiers.             
         */
        Vector<ExprNode> quantBounds = null ;
        
        /**  
         * If this is a \A or \E decomposition for a bounded quantifier (like
         *   \A x \in S), then this is the list of subexpression names for
         *   each of the elements of quantBounds.             
         */
        Vector<String> quantBoundsubexpNames = null ;
        
        
        /** True iff the Decomposition's children and  quantBounds should be primed. */
        boolean primed = false ;
       
        public String toString() {
            String val = "type: " + nodeSubTypeToString(this.type);
            if (definedOp != null) {
                val = val + "\ndefinedOp: " + this.definedOp;
                val = val + "\ndefinedOpRep: " + definedOpRep.toString();
            }
            val = val + "\nmoduleName: " + this.moduleName;
            val = val + "\nchildren: ";
            for (int i = 0; i < this.children.size(); i++) {
                val = val + "\nchildren[" + i + "]:\n " + 
                         children.elementAt(i).toString() ;
            }
//            val = val + "\nchildren: " + this.children.toString();
            val = val + "\nnamePath: " + this.namePath.toString();
            if (quantIds != null) {
                val = val + "\nquantIds: " ;
                for (int i = 0; i < this.quantIds.size(); i++) {
                   if (i!=0) {
                       val = val + ", ";
                   }
                   val = val + quantIds.elementAt(i).getName().toString();
                }
            }
            if (quantBounds != null) {
                for (int i = 0; i < this.quantBounds.size(); i++) {
                    val = val + "\nquantBounds[" + i + "]:\n " + 
                             quantBounds.elementAt(i).toString() ;
                }
                val = val + "quantBoundsubexpNames: ";
                for (int i = 0; i < this.quantBounds.size(); i++) {
                    val = val + ((i == 0)?"":", ") + 
                            quantBoundsubexpNames.elementAt(i) ;
                }
                
            }    
            val = val + "\nprimed: " + primed ;
            return val;
        }
    }
    
    /**
     * Converts a NodeRepresentation subType to a string.  Used
     * for debugging.
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
        case NodeRepresentation.OTHER_TYPE:
            val = "OTHER_TYPE";
            break;
        }
        return val;
    }
    
    /**
     * Returns the NodeRepresentation subtype for an OpApplNode whose
     * operator name is opId.
     * 
     * @param opId
     * @return
     */
    private static int operatorNameToNodeSubtype(UniqueString opId) {
        String opName = opId.toString();
        if ((opId == ASTConstants.OP_cl) || opName.equals("\\land")) {
            return NodeRepresentation.AND_TYPE;
        } else if ((opId == ASTConstants.OP_dl) || opName.equals("\\lor")) {
            return NodeRepresentation.OR_TYPE;
        } else if (opName.equals("=>")) {
            return NodeRepresentation.IMPLIES_TYPE;
        } else if ((opId == ASTConstants.OP_bf)
                || (opId == ASTConstants.OP_uf)) {
            return NodeRepresentation.FORALL_TYPE;
        } else if ((opId == ASTConstants.OP_be)
                || (opId == ASTConstants.OP_ue)) {
            return NodeRepresentation.EXISTS_TYPE;
        } else if (opId == ASTConstants.OP_sa) {
            return NodeRepresentation.SQSUB_TYPE;
        } else {
            return NodeRepresentation.OTHER_TYPE;
        }
    }
    
    /**
     * This computes the decompose field of a NodeRepresentation.  It does not
     * yet handle the decomposition of a defined operator except by using 
     * subexpression names.  Other than having to indicate substitute for parameters
     * in the definition, it needs to provide the information for extracting the
     * nodeText for the definition.  The problem is, that it has to be extracted
     * in the context of the module, not as a subnode of the node being expanded.
     * For this reason, at the moment definition expansion is all by subexpression
     * names.
     * 
     * @param sn
     * @return
     */
    private Decomposition decompose(NodeRepresentation nodeRep) {
        SemanticNode sn = nodeRep.semanticNode;
        if (!(sn instanceof OpApplNode)) {
            return null;
        }

        OpApplNode node = (OpApplNode) sn;
        OpApplNode unprimedNode = node;

        Decomposition result = new Decomposition();

        // Check if primed expression.
        if (node.getOperator().getName() == ASTConstants.OP_prime) {
            node = (OpApplNode) node.getArgs()[0];
            unprimedNode = node;
            result.primed = true;
        }

        // If nodeRep.isSubexpressionName is false (so it was not obtained by
        // decomposing a definition using subexpression names), then we
        // see if this is an operator definition we can handle.

        if ((!nodeRep.isSubexpressionName)
                && (node.getOperator().getKind() == ASTConstants.UserDefinedOpKind)) {
            String operatorName = ((OpDefNode) node.getOperator()).getName()
                    .toString();
            ExprNode opDef = ((OpDefNode) node.getOperator()).getBody();

            // If the definition comes from an INSTANCE, it may be a
            // SubstInNode. If so, we strip off the top-level SubstInNode
            // object(s).
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
                System.out.println(operatorName + " defined in module "
                        + result.moduleName);
                System.out.println("This module is: "
                        + moduleNode.getName().toString());
                // The following test is to determine if the definition should
                // be expanded by subexpression naming or by actual expansion.
                // (Initially, we don't deal with expansion of names from another
                // module.)  However, actual expansion is not yet implemented.
                //
                // if (subexpressionButton.getSelection()
                //      || !result.moduleName.equals(moduleNode.getName()
                //               .toString())) {
                    result.definedOpRep = nodeRep.subNodeText(unprimedNode);
                    result.definedOp = operatorName;
                // } // end of if

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
        if ((opId == ASTConstants.OP_cl) || opName.equals("\\land")) {
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
System.out.println("Decomposition");
System.out.println(result.toString());
        return result;
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
        UniqueString opId = ((OpDefNode) aonode.getOperator()).getName();
        String opName = opId.toString();

        if (!opName.equals(op)) {
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
     * Returns the array of strings as a single string, where the first line
     * is inserted at column indent (Java numbering, columns starting at 0).
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
            result = result + "\n" + StringHelper.copyString(" ", indent) + A[i];
        }
        return result;
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
//            Image folderImg = PlatformUI.getWorkbench().getSharedImages().getImage(ISharedImages.IMG_LCL_LINKTO_HELP);
//            String foo = ISharedImages.IMG_LCL_LINKTO_HELP ;
//             button.setImage(folderImg);
            button.setText(text) ; 
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
//                    displayHTML();
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
                // Any ACTION button causes a change.
                hasChanged = true ;
                NodeRepresentation nodeObj = (NodeRepresentation) object ;
                switch (nodeObj.nodeSubtype) {
                case NodeRepresentation.AND_TYPE:
                   decomposeHandler.andAction(nodeObj) ;
                   break ;
                case NodeRepresentation.OR_TYPE:    
                   break ;
                case NodeRepresentation.IMPLIES_TYPE:
                   impliesAction(nodeObj);
                   break ;
                case NodeRepresentation.FORALL_TYPE:
                   decomposeHandler.forAllAction(nodeObj) ;
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
    
    class ArrowSelectionListener implements SelectionListener {
        int index ;
        int direction ;
        DecomposeProofHandler handler ;
        
        ArrowSelectionListener(int idx, int dir, DecomposeProofHandler han) {
            index     = idx;
            direction = dir;
            handler   = han;
        }
        public void widgetSelected(SelectionEvent e) {
            SemanticNode node = handler.assumes.elementAt(index);
            NodeRepresentation rep = handler.assumeReps.elementAt(index);
            handler.assumes.remove(index) ;
            handler.assumeReps.remove(index);
            int inc = (direction == SWT.DOWN)?1:-1;
            handler.assumes.add(index + inc, node) ;
            handler.assumeReps.add(index + inc, rep) ;
            handler.raiseWindow();
        }

        public void widgetDefaultSelected(SelectionEvent e) {
            widgetSelected(e) ;
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
// No longer used.
//    static OpApplNode exposeRelevantExpr(OpApplNode oan) {
//        OpApplNode nd = oan;
//        if (nd.getOperator().getName() == ASTConstants.OP_prime) {
//            nd = (OpApplNode) nd.getArgs()[0];
//        }
//        if (nd.getOperator().getKind() == ASTConstants.UserDefinedOpKind) {
//            ExprNode opDef = ((OpDefNode) nd.getOperator()).getBody();
//            if (opDef instanceof OpApplNode) {
//                nd = (OpApplNode) opDef;
//            } else {
//                return nd;
//            }
//        }
//        if (nd.getOperator().getName() == ASTConstants.OP_prime) {
//            nd = (OpApplNode) nd.getArgs()[0];
//        }
//        return nd;
//    }
     
    /**
     * Returns true if it may be necessary to put parentheses around the
     * expression represented by `node' in order to prime it.  This is the
     * case if node is an OpApplNode whose operator is NOT a user-defined 
     * operator with an identifier as its name (so it's not in/prep/postfix).
     * 
     * @param node
     * @return
     */
    static boolean primingNeedsParens(SemanticNode node) {
        if (!(node instanceof OpApplNode)) {
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
