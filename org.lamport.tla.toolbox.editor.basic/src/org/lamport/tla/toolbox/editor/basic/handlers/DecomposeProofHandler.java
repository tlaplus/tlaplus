/**
 * Currently, this command is under construction and is not bound to the proper key or menu.
 * Instead, it is executed by typing Ctl+Shift+A.
 */
package org.lamport.tla.toolbox.editor.basic.handlers;

import java.awt.MenuBar;
import java.util.Vector;

import org.eclipse.core.commands.AbstractHandler;
import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.core.commands.ExecutionException;
import org.eclipse.core.commands.IHandler;
import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.jface.resource.JFaceResources;
import org.eclipse.jface.text.BadLocationException;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.IRegion;
import org.eclipse.jface.text.TextSelection;
import org.eclipse.jface.viewers.ISelectionProvider;
import org.eclipse.swt.SWT;
import org.eclipse.swt.custom.ScrolledComposite;
import org.eclipse.swt.events.DisposeEvent;
import org.eclipse.swt.events.DisposeListener;
import org.eclipse.swt.events.SelectionAdapter;
import org.eclipse.swt.events.SelectionEvent;
import org.eclipse.swt.events.SelectionListener;
import org.eclipse.swt.graphics.Point;
import org.eclipse.swt.layout.FillLayout;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.layout.RowLayout;
import org.eclipse.swt.widgets.Button;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Label;
import org.eclipse.swt.widgets.Menu;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.swt.widgets.Text;
import org.lamport.tla.toolbox.Activator;
import org.lamport.tla.toolbox.editor.basic.TLAEditor;
import org.lamport.tla.toolbox.editor.basic.handlers.ShowDeclarationsHandler.ShowDeclarationsPopupDialog;
import org.lamport.tla.toolbox.editor.basic.util.EditorUtil;
import org.lamport.tla.toolbox.util.ResourceHelper;
import org.lamport.tla.toolbox.util.StringHelper;
import org.lamport.tla.toolbox.util.UIHelper;

import tla2sany.semantic.AssumeProveNode;
import tla2sany.semantic.LeafProofNode;
import tla2sany.semantic.LevelNode;
import tla2sany.semantic.ModuleNode;
import tla2sany.semantic.NonLeafProofNode;
import tla2sany.semantic.OpApplNode;
import tla2sany.semantic.ProofNode;
import tla2sany.semantic.SemanticNode;
import tla2sany.semantic.SymbolNode;
import tla2sany.semantic.TheoremNode;
import tla2sany.semantic.ThmOrAssumpDefNode;
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
    private  ProofNode proof;
    
    // The assumptions and 
    private OpApplNode[] assumes ;
    private OpApplNode goal ;

    // fields for displaying Decompose Proof window
    private Shell windowShell ;  // The shell of the Decompose Proof window
    private Point location = null ;  // The location at which window
                                     // should open.
    private TLAEditor editor;  // The editor from which window was raised.
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
System.out.println("Decomposing Proof");
//        String[] pathList = Activator.getSpecManager().getSpecLoaded().getTLALibraryPath();
//for (int i = 0; i < pathList.length; i++) {
//    System.out.println("item " + i + ": " + pathList[i]) ;
//}
        /*
         * The following text for finding the editor, document, selection, and
         * module are copied from other commands.
         */

        //gets the editor to which command applies
        editor = EditorUtil.getTLAEditorWithFocus();
        if (editor == null) {
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
        
        LevelNode thm = step.getTheorem();
        if (thm instanceof AssumeProveNode) {
            SemanticNode[] assump = ((AssumeProveNode) thm).getAssumes() ;
            assumes = new OpApplNode[assump.length] ;
            for (i = 0 ; i < assump.length; i++) {
                if (assump[i] instanceof AssumeProveNode) {
                    MessageDialog.openError(UIHelper.getShellProvider().getShell(),
                            "Decompose Proof Command",
                            "Cannot decompose a step with a nested ASSUME/PROVE.");
                    return null;
                } else if (!(assump[i] instanceof OpApplNode)) {
                    MessageDialog.openError(UIHelper.getShellProvider().getShell(),
                            "Decompose Proof Command",
                            "Cannot handle assumption " + (i+1) + ".");
                    return null;
                }
                assumes[i] = (OpApplNode) assump[i];
                
                // XXXXXXXXXXXXXXXXXx
                // change representation to have clauses an array with clauses[0] = goal
                // and clauses[1], ... the assumptions?
            }
            
        } else {
            System.out.println(thm.getClass().toString()) ;
        }
//        editor.setHighlightRange(thmregion.getOffset(), thmregion.getLength(), true) ;
        try {
            System.out.println((new NodeRepresentation(doc, step)).toString());
        } catch (BadLocationException e) {
            // TODO Auto-generated catch block
            e.printStackTrace();
            System.out.println("threw exception");
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
                raiseWindow("newWindow") ;
            }
            return null ;
        }
        System.out.println("parent null") ;
        raiseWindow("newWindow") ;
        return null;
    }
    


    private void raiseWindow(String windowTitle) {
        // for testing
        // topshell = the Toolbox's shell
        Shell topshell = UIHelper.getShellProvider().getShell() ;
        windowShell = new Shell(topshell, SWT.SHELL_TRIM) ; // | SWT.H_SCROLL); // SWT.RESIZE) ; // | SWT.V_SCROLL | SWT.H_SCROLL) ;
        windowShell.setText(windowTitle) ;
        windowShell.addDisposeListener(new DisposeListener() {
            
            public void widgetDisposed(DisposeEvent e) {
                // TODO Auto-generated method stub
                System.out.println("windowShell's disposeListener called");
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
        setupMenuButton(closeButton, "Refresh") ;
        Button closeButton2 = new Button(topMenu, SWT.PUSH) ;
        setupMenuButton(closeButton2, "Refresh2") ;
        
//        closeButton.setText("Close");
//        closeButton.addSelectionListener(new DecomposeProofButton(this, windowShell, DecomposeProofButton.MENU, "refresh")) ;
        
        Label assumeLabel = new Label(shell, SWT.NONE);
        assumeLabel.setText("ASSUME");
        assumeLabel.setFont(JFaceResources.getFontRegistry().get(JFaceResources.HEADER_FONT));
        gridData = new GridData();
        gridData.horizontalSpan = 3;
        assumeLabel.setLayoutData(gridData);
        
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
        shell.pack() ;

//        System.out.println("Shell.size = " + shell.getSize().toString());
//        System.out.println("parent.size = " + parent.getSize().toString());
        Point shellSize = shell.getSize() ;;
        windowShell.setSize(shellSize.x + 30, shellSize.y + 30) ;
        System.out.println("location = " + windowShell.getLocation().toString()) ;
        System.out.println("size = " + windowShell.getSize().toString()) ;
        System.out.println("location = " + topshell.getLocation().toString()) ;
        System.out.println("size = " + topshell.getSize().toString()) ;

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
            mapping[0].elementAt(0).inc = -spacesAddedToFirstLine;
            
            
            // Trim any necessary space from the beginning of nodeText[i] for i > 0.
            for (int i = 1; i < nodeText.length; i++) {
                nodeText[i] = nodeText[i].substring(minCol);
                mapping[i].elementAt(0).inc = -1 - minCol ;
            }
            return ;
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
    private class MappingPair {
        int col;
        int inc;
        MappingPair(int c, int p) {
            col = c;
            inc = p;
        }
        
        public String toString() {
            return "<" + col + ", " + inc + ">" ;
        }
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
    
    /**
     * Used to set various parameters of a button
     * 
     * @param button
     * @param type  The style type of the button.
     * @param text  The button's text
     */
    private void setupMenuButton(Button button, String text) {
            button.addSelectionListener(new DecomposeProofButtonListener(this, MENU)) ;
            button.setText(text) ; 
            button.setSize(100, button.getSize().y);
            GridData gridData = new GridData();
            gridData.horizontalIndent = 30 ;
            button.setLayoutData(gridData) ;
        }
    
    
    /**
     * The listener for buttons on the DecomposeProof window.  The button
     * type tells what to do when clicked.  Any data needed by the listener
     * must be put in fields of the DecomposeProofHandler object.
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
        
        public DecomposeProofButtonListener(DecomposeProofHandler dHandler, int tp) {
            super();
            decomposeHandler = dHandler ;
            type = tp ;
            
        }
        
        /**
         * Sent when selection occurs in the control.
         * The default behavior is to do nothing.
         *
         * @param e an event containing information about the selection
         */
        public void widgetSelected(SelectionEvent e) {
            switch (type) {
            case MENU:
                System.out.println("MENU Click");
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
            case ACTION:
                System.out.println("ACTION Click");
                break ;
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

}
