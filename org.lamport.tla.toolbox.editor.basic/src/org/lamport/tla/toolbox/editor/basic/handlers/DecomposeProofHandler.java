/**
 * Currently, this command is under construction and is not bound to the proper key or menu.
 * Instead, it is executed by typing Ctl+Shift+A.
 * 
 * A single object of this class is created and attached to the command.  Multiple
 * executions of the command use the same object, so data can be stored as (non-static)
 * fields of the object between executions of the command.
 * 
 */
package org.lamport.tla.toolbox.editor.basic.handlers;

import java.awt.Font;
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
import org.eclipse.swt.widgets.Display;
import org.eclipse.swt.widgets.Label;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.ui.part.FileEditorInput;
import org.lamport.tla.toolbox.editor.basic.TLAEditor;
import org.lamport.tla.toolbox.editor.basic.util.EditorUtil;
import org.lamport.tla.toolbox.util.ResourceHelper;
import org.lamport.tla.toolbox.util.StringHelper;
import org.lamport.tla.toolbox.util.UIHelper;

import tla2sany.semantic.ASTConstants;
import tla2sany.semantic.AssumeProveNode;
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


    private IDocument doc; // The document being edited.
    private String text; // The document as a string.
    private ISelectionProvider selectionProvider; //
    private TextSelection selection; // The current selection.
    private int offset; // The current offset.
    private ModuleNode moduleNode; // The module being edited.
    private TheoremNode theorem;// The theorem containing the selected step
    private TheoremNode step; // The step being decomposed.
    private NodeRepresentation stepRep; // the steps node representation;
    private  ProofNode proof;
    
    // The assumptions and goal
    private SemanticNode[] assumes ;
    private NodeRepresentation[] assumeReps ; // the assumptions NodeRepresentations 
    private OpApplNode goal ;
    private NodeRepresentation goalRep ;

    // fields for displaying Decompose Proof window
    private Shell windowShell ;  // The shell of the Decompose Proof window
    private Point location = null ;  // The location at which window
                                     // should open.
    private TLAEditor editor;  // The editor from which window was raised.
    private IFile editorIFile ; // The IFile of the editor, used for making it read-only.
    public boolean ignore = true ; // for producing a release without the handler doing anything.
    
    // buttons and stuff for the window
    // Radio buttons for how to rewrite proof: 
    Button sufficesButton ; //  Use SUFFICES step in proof
    Button rewriteButton ;  //  Rewrite step
    Button neitherButton ;  //  Use ASSUME/PROOF steps

    // The value selected by the radiobuttons.  Should initialize by preference
    private static final int SUFFICES_CHOSEN = 0 ;
    private static final int REWRITE_CHOSEN = 1 ;
    private static final int NEITHER_CHOSEN = 2 ;
    private int radioChoice = SUFFICES_CHOSEN ;
    
    private Button subexpressionButton ; // Determines how definitions are expanded
    private boolean subexpressionValue = false ; // should be initialized by preference
    
    // Some fields holding the state of the decomposition
    private boolean hasChanged = false ;       // true iff the user has done something
    private boolean assumeHasChanged = false ;  
            // true iff an action has been performed on an assumption. 
            // It is not set by an action that modifies the goal and creates a new
            // assumption.
    private int splitOrIdx = -1 ;  // If # -1, then assumption splitOrIdx has been OR-split.
            
    /**
     * Set radioChoice to indicate the currently selected radio button.
     * currently selected values ;
     */
    private void readButtons() {
        subexpressionValue = subexpressionButton.getSelection() ;
        if (sufficesButton.getSelection()) {
            radioChoice = SUFFICES_CHOSEN ;
            return ;
        }
        if (rewriteButton.getSelection()) {
            radioChoice = REWRITE_CHOSEN ;
            return ;
        }
        radioChoice = NEITHER_CHOSEN ;
        return ;
    }
    // private IRegion lineInfo; // The lineInfo for the current offset.

    /**
     * 
     */
    // public DecomposeProofHandler() {
    // // TODO Auto-generated constructor stub
    // }

    /*
     * (non-Javadoc)
     * 
     * @see
     * org.eclipse.core.commands.IHandler#execute(org.eclipse.core.commands.
     * ExecutionEvent)
     */
    public Object execute(ExecutionEvent event) throws ExecutionException {
        // TODO Auto-generated method stub
        
        // For a release without the handler doing anything.
//        if (ignore) {
//            return null ;
//       }

System.out.println("Decomposing Proof");

        // Do nothing if already executing command. 
        if (this.windowShell != null) {
            if (!this.windowShell.isDisposed()) {
                System.out.println("Command called when being executed.");
                return null;
            }
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
        
        
        doc = editor.getDocumentProvider().getDocument(editor.getEditorInput());
        text = doc.get();
        selectionProvider = editor.getSelectionProvider();
        selection = (TextSelection) selectionProvider.getSelection();
        offset = selection.getOffset();

        // Get the module.
        String moduleName = editor.getModuleName();
        ModuleNode moduleNode = ResourceHelper.getModuleNode(moduleName);

        // selectedLocation is Location of selected region.
        Location selectedLocation = EditorUtil.getLocationAt(doc, offset,
                selection.getLength());

        // Set theorem to  the THEOREM containing the selection
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

        // Set step to innermost step (or the theorem itself) containing
        // the selected region.
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
        proof = step.getProof();
        while (notDone && (proof != null)
                && (proof instanceof NonLeafProofNode)) {
            LevelNode[] pfsteps = ((NonLeafProofNode) proof).getSteps();
            LevelNode foundLevelNode = null;
            i = 0;
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
  
        // the step must have either no proof or a leaf proof.
        if ((proof != null) && !(proof instanceof LeafProofNode)) {
            MessageDialog.openError(UIHelper.getShellProvider().getShell(),
                    "Decompose Proof Command",
                    "You have selected a step that already has a non-leaf proof.");
            return null;
        }
        try {
            stepRep = new NodeRepresentation(doc, step) ;
            System.out.println((new NodeRepresentation(doc, step)).toString());
        } catch (BadLocationException e) {
            e.printStackTrace();
            System.out.println("threw exception");
        }
        LevelNode thm = step.getTheorem();
        if (thm instanceof AssumeProveNode) {
            SemanticNode[] assump = ((AssumeProveNode) thm).getAssumes();
            assumes = new SemanticNode[assump.length];
            assumeReps = new NodeRepresentation[assump.length];
            for (i = 0; i < assump.length; i++) {
                if (assump[i] instanceof AssumeProveNode) {
                    MessageDialog
                            .openError(UIHelper.getShellProvider().getShell(),
                                    "Decompose Proof Command",
                                    "Cannot decompose a step with a nested ASSUME/PROVE.");
                    return null;
                } 
//                else if (!(assump[i] instanceof OpApplNode)) {
//                    MessageDialog.openError(UIHelper.getShellProvider()
//                            .getShell(), "Decompose Proof Command",
//                            "Cannot handle assumption " + (i + 1) + ".");
//                    return null;
//                }
                assumes[i] =  assump[i];
                assumeReps[i] = stepRep.subNode(assumes[i]);
                goal = (OpApplNode) ((AssumeProveNode) thm).getProve();
                goalRep = stepRep.subNode(goal);
            }
            
        } else {
            assumes = null ;
            goal = (OpApplNode) thm ;
            UniqueString goalOpName = goal.getOperator().getName() ;
            
            // Abort if this is one of the following kinds of steps:
            //  QED, HAVE, PICK, WITNESS, SUFFICES
            if (   (goalOpName == ASTConstants.OP_qed)
                    || (goalOpName == ASTConstants.OP_pfcase)
                    || (goalOpName == ASTConstants.OP_have)
                    || (goalOpName == ASTConstants.OP_pick)
                    || (goalOpName == ASTConstants.OP_witness)
                    || (goalOpName == ASTConstants.OP_suffices)
               ) {
            	MessageDialog
                .openError(UIHelper.getShellProvider().getShell(),
                        "Decompose Proof Command",
                        "Cannot decompose this kind of step.");
        return null;
            }
            goalRep = stepRep.subNode(goal) ;
        }

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
        if (this.windowShell != null)  {
            if (this.windowShell.isDisposed()) {
                System.out.println("Parent disposed") ;
                // This setReadOnly is a no-op.  Why???
                // The following method was deprecated because it was actually possible to use
                // it, so it had to be replaced by something that requires a PhD in Eclipse
                // to figure out how to use.
                editorIFile.setReadOnly(true) ;
                raiseWindow("newWindow") ;
                
            }
            return null ;
        }
        
        
        System.out.println("parent null") ;
        // This setReadOnly is a no-op.  Why???
        EditorUtil.setReadOnly(editorIFile, true);
        
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
        windowShell.addDisposeListener(new DisposeListener() {            
            public void widgetDisposed(DisposeEvent e) {
                System.out.println("windowShell's disposeListener called");
                if (editor.isDirty()) {
                    System.out.println("Editor is dirty");
                }
                // The following method was deprecated because it was actually possible to use
                // it, so it had to be replaced by something that requires a PhD in Eclipse
                // to figure out how to use. 
                editorIFile.setReadOnly(false);
            }
        }) ;
        Composite shell = new Composite(windowShell, SWT.NONE) ;
        GridLayout gridLayout = new GridLayout(3, false);
        shell.setLayout(gridLayout);
        
        Composite topMenu = new Composite(shell,SWT.NONE) ;   
        gridLayout = new GridLayout(4, false);
        gridLayout.marginBottom = 0;
        topMenu.setLayout(gridLayout);        
        GridData gridData = new GridData() ;
        gridData.horizontalSpan = 3;
        topMenu.setLayoutData(gridData) ;
        
        Button closeButton = new Button(topMenu, SWT.PUSH) ;
        setupMenuButton(closeButton, TEST_BUTTON, "Refresh") ;
        Button closeButton2 = new Button(topMenu, SWT.PUSH) ;
        setupMenuButton(closeButton2, TEST_BUTTON, "Refresh2") ;
        
        // button to choose whether to expand definitions with subexpression names
        subexpressionButton = new Button(topMenu, SWT.CHECK);
        setupCheckButton(subexpressionButton, "Use subexpression names.");
        subexpressionButton.setSelection(subexpressionValue) ;
        
        // How to rewrite composite
        Composite radio = new Composite(topMenu, SWT.BORDER) ;
        GridLayout radioLayout = new GridLayout(6, false) ;
        radio.setLayout(radioLayout) ;
        Label radioLabel = new Label(radio, SWT.NONE) ;
        radioLabel.setText("prove using:") ;
        sufficesButton = new Button(radio, SWT.RADIO) ;
        neitherButton = new Button(radio, SWT.RADIO) ;
        rewriteButton = new Button(radio, SWT.RADIO) ;
        
        sufficesButton.setText("SUFFICES") ;
        rewriteButton.setText("rewritten goal") ;
        neitherButton.setText("ASSUME/PROVE steps") ;
        switch (radioChoice) {
        case SUFFICES_CHOSEN :
            sufficesButton.setSelection(true) ;
            rewriteButton.setSelection(false) ;
            neitherButton.setSelection(false) ;
            break ;
        case REWRITE_CHOSEN :
            sufficesButton.setSelection(false) ;
            rewriteButton.setSelection(true) ;
            neitherButton.setSelection(false) ;
            break ;
        case NEITHER_CHOSEN :
            sufficesButton.setSelection(false) ;
            rewriteButton.setSelection(false) ;
            neitherButton.setSelection(true) ;
            break ;
        }
       
        
        // Display the Assumptions        
        Label assumeLabel = new Label(shell, SWT.NONE);
        assumeLabel.setText("ASSUME");
        assumeLabel.setFont(JFaceResources.getFontRegistry().get(JFaceResources.HEADER_FONT));
        gridData = new GridData();
//        gridData.horizontalSpan = 3;
        new Label(shell, SWT.NONE) ;
        new Label(shell, SWT.NONE) ;
        
        assumeLabel.setLayoutData(gridData);
        
        if (assumes != null) {
            for (int i = 0 ; i < assumes.length; i++) {
            	String labelText = null ;        		
            	if (assumes[i].getKind() == ASTConstants.OpApplKind) {
            		switch (assumeReps[i].nodeSubtype) {
            		case NodeRepresentation.AND_TYPE:
            			labelText = "/\\";
            			break;
            		case NodeRepresentation.OR_TYPE:
            		case NodeRepresentation.SQSUB_TYPE:
            			labelText = "\\/";
            			break;
            		case NodeRepresentation.IMPLIES_TYPE:
            			labelText = "=>";
            			break;
            		case NodeRepresentation.EXISTS_TYPE:
            			labelText = "\\E";
            			break;
            	    default:
            	    	labelText = null ;
            		}
            	}
                if (labelText != null) {
            	      setupActionButton(new Button(shell, SWT.PUSH), assumeReps[i], labelText);
            		}
            	else {
            		assumeLabel = new Label(shell, SWT.NONE) ;
            	    assumeLabel.setText("  ") ;
            	}
            	gridData = new GridData();
                gridData.verticalAlignment = SWT.TOP;
                assumeLabel.setLayoutData(gridData);
                
                assumeLabel = new Label(shell, SWT.BORDER);
                assumeLabel.setText(stringArrayToString(assumeReps[i].nodeText));
                gridData = new GridData();
//                gridData.horizontalSpan = 2;
                new Label(shell, SWT.NONE) ;
//                new Label(shell, SWT.NONE) ;
                
                gridData.verticalAlignment = SWT.TOP;
                assumeLabel.setLayoutData(gridData);
                
            }
        }
        
        // Display the Goal
        assumeLabel = new Label(shell, SWT.NONE);
        assumeLabel.setText("PROVE");
        assumeLabel.setFont(JFaceResources.getFontRegistry().get(JFaceResources.HEADER_FONT));
        gridData = new GridData();
        gridData.horizontalSpan = 3;
        assumeLabel.setLayoutData(gridData);
        
        String labelText = null ;
        switch(goalRep.nodeSubtype) {
        case NodeRepresentation.AND_TYPE:
			labelText = "/\\";
			break;
        case NodeRepresentation.FORALL_TYPE:
			labelText = "\\A";
			break;	
        default:
	    	labelText = null ;
        }
        if (labelText != null) {
  	      setupActionButton(new Button(shell, SWT.PUSH), goalRep, labelText);
  		}
  	else {
  		assumeLabel = new Label(shell, SWT.NONE) ;
  	    assumeLabel.setText("  ") ;
  	}
//        assumeLabel = new Label(shell, SWT.NONE) ;
//        assumeLabel.setText(goal.getOperator().getName().toString()) ;
//        assumeLabel.setText(ASTConstants.kinds[goal.getKind()]) ;
//        gridData = new GridData();
//        gridData.verticalAlignment = SWT.TOP;
//        assumeLabel.setLayoutData(gridData);
        
        assumeLabel = new Label(shell, SWT.BORDER);
        assumeLabel.setText(stringArrayToString(goalRep.nodeText));
        gridData = new GridData();
        gridData.horizontalSpan = 2;
        gridData.verticalAlignment = SWT.TOP;
        assumeLabel.setLayoutData(gridData);
        Display display = UIHelper.getCurrentDisplay() ;
        // The following sets the font to be the Toolbox editor's text font.
        assumeLabel.setFont(JFaceResources.getFontRegistry().get(JFaceResources.TEXT_FONT));

/*  ---------- Garbage below
        new Button(shell, SWT.PUSH).setText("Wide Button 2");
        new Button(shell, SWT.PUSH).setText("Button 3");
        Button button4 = new Button(shell, SWT.PUSH) ;
        button4.setText("B4eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee"); 
        gridData = new GridData() ;
        gridData.verticalAlignment = SWT.TOP;
        button4.setLayoutData(gridData);

        
        Composite comp = new Composite(shell, SWT.NONE) ;
        GridLayout gl = new GridLayout(1, false);
        // no margin around the widget.
        gl.marginWidth = 0;
        gl.marginHeight = 0;
        comp.setLayout(gl);

        Label l1 = new Label(comp, SWT.NONE);
        l1.setText("Label1");
        Composite compInner = new Composite(comp, SWT.None) ;
        GridLayout gin = new GridLayout(2, false) ;
          gin.marginWidth = 0;
          gin.marginHeight = 0 ;
          compInner.setLayout(gin) ;
          gridData = new GridData() ;
          gridData.verticalAlignment = SWT.TOP;
          compInner.setLayoutData(gridData) ;          
          Button button7 = new Button(compInner, SWT.PUSH) ;
          button7.setText("B7") ;
          gridData = new GridData() ;
          gridData.verticalAlignment = SWT.TOP;
          button7.setLayoutData(gridData) ;       
          
        Label l2 = new Label(compInner, SWT.NONE);
        l2.setText("Label22\n22222"  + "\n22222222222222222222222222222\n" + 
                   "xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx" 
                );
        gridData = new GridData() ;
        gridData.verticalAlignment = SWT.TOP;
        l2.setLayoutData(gridData) ; 
        gridData = new GridData() ;
//        gridData.horizontalAlignment = SWT.LEFT;
//        gridData.grabExcessHorizontalSpace = true;
        gridData.verticalAlignment = SWT.TOP;
//        gridData.grabExcessVerticalSpace = true;
        comp.setLayoutData(gridData);
//        comp.setSize(comp.computeSize(SWT.DEFAULT, SWT.DEFAULT)) ;
//        sc2.setSize(comp.computeSize(SWT.DEFAULT, SWT.DEFAULT));
        
        
        
        Label l3 = new Label(shell, SWT.NONE) ;
        l3.setText("LabelLabel3");
        gridData = new GridData() ;
        gridData.verticalAlignment = SWT.FILL;
        l3.setLayoutData(gridData);
        

//        System.out.println("Shell.size = " + shell.getSize().toString());
//        System.out.println("parent.size = " + parent.getSize().toString());
        System.out.println("location = " + windowShell.getLocation().toString()) ;
        System.out.println("size = " + windowShell.getSize().toString()) ;
        System.out.println("location = " + topshell.getLocation().toString()) ;
        System.out.println("size = " + topshell.getSize().toString()) ;
*/
        shell.pack() ;
        Point shellSize = shell.getSize() ;;
        windowShell.setSize(shellSize.x + 30, shellSize.y + 30) ;
        
        windowShell.update();
        if (this.location != null) {
            windowShell.setLocation(this.location) ;
        }
        windowShell.open();
        
        
        System.out.println("closed") ;
        
    }
    
    /**
     * A NodeRepresentation object is describes the TLA+ source text
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
     *      
     * </ul>
     * 
     * 
     * @author lamport
     *
     */
    public class NodeRepresentation {
        SemanticNode node ;
        
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
         * @param node
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
        private static final int EXPR_NODE  = 0  ; // An OpApplNode that is not an OR_Node
        private static final int NEW_NODE   = 1  ; // A NewSymbNode
        private static final int DISJ_NODE  = 2  ; // A node representing a decomposition
                                                   // into the disjunction of its children
        private static final int EXISTS_NODE = 3 ; 
           // Represents a decomposition into \E of children[0].
           // This should not be the NodeRepresentation object for an assumption or goal,
           // but it could be an inner object, such as the \E x of the assumption
           //    \/ 1+1=2
           //    \/ \E x : 1+x = 3
        private static final int PROOF_NODE = 4  ; 
          // The LeafProofNode of the step.  This may not be needed.
        private static final int OTHER_NODE = 5  ;        
        private int nodeType ;
        
        // An EXPR_NODE can have multiple subtypes, indicating what decomposition
        // can be applied.
        private static final int AND_TYPE     = 0 ;
        private static final int OR_TYPE      = 1 ;
        private static final int IMPLIES_TYPE = 2 ;
        private static final int FORALL_TYPE  = 3 ;
        private static final int EXISTS_TYPE  = 4 ;
        private static final int SQSUB_TYPE   = 5 ;  // An [A]_v expression
        private static final int OTHER_TYPE   = 99 ;  // anything else
        
        public int nodeSubtype ;
        
        // children is the array of children of this object, if it has
        // any.  Otherwise it is null.  Only an OR node should have children.
        //
        // If the node is the child of a NodeRepresentation object,
        // then it equals parent.children[parentIdx]
        NodeRepresentation parent ;
        int parentIdx = -1;
        NodeRepresentation[] children ;
        
        /**
         * 
         * @param sn  A subnode of this.node.
         * @return
         */
        NodeRepresentation subNode(SemanticNode sn) {
            
            NodeRepresentation result = new NodeRepresentation() ;
            result.node = sn ;
            // set beginId to be the index in this.nodeText representing the
            // first line of the source of node sn.
            int beginIdx =  getBeginLine(sn) - getBeginLine(this.node) ;
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
            	// If this is a primed expression, we need to
            	// look at the argument of the prime operator.
            	// So we set nd to the OpApplNode to check.
            	OpApplNode nd = (OpApplNode) sn ;
            	if (nd.getOperator().getName() == ASTConstants.OP_prime) {
            		nd = (OpApplNode) nd.getArgs()[0] ;
            	}
            	
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
            this.node = node ;
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
     * The following are the types of buttons in the 
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
            button.setText(text) ; 
            button.setSize(100, button.getSize().y);
            GridData gridData = new GridData();
            gridData.horizontalIndent = 30 ;
            button.setLayoutData(gridData) ;
        }
    
    private void setupCheckButton(Button button, String text) {
        // There doesn't seem to be a need to set a listener on a checkbutton;
        // It can be read when some action button is pushed.
//        button.addSelectionListener(new DecomposeProofButtonListener(this, button, CHECK)) ;
        button.setText(text) ; 
//        button.setSize(100, button.getSize().y);
        GridData gridData = new GridData();
//        gridData.horizontalIndent = 30 ;
        button.setLayoutData(gridData) ;
    }

    private void setupActionButton(Button button, NodeRepresentation nodeRep, String text) {
    	button.setText(text) ; 
        button.setSize(30, button.getSize().y);
        GridData gridData = new GridData();
        gridData.horizontalIndent = 10 ;
        gridData.verticalAlignment = SWT.TOP;
        button.setLayoutData(gridData) ;
        button.addSelectionListener(new DecomposeProofButtonListener(this, nodeRep, ACTION)) ;
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
                
                            case ACTION:
                System.out.println("ACTION Click");
                break ;
            case CHECK:
                Button but = (Button) object ;
                System.out.println("status = " + but.getSelection()) ;
                but.setEnabled(false) ;
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

}
