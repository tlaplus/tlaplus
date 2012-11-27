/**
 * Currently, this command is under construction and is not bound to the proper key or menu.
 * Instead, it is executed by typing Ctl+Shift+A.
 */
package org.lamport.tla.toolbox.editor.basic.handlers;

import java.awt.MenuBar;

import org.eclipse.core.commands.AbstractHandler;
import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.core.commands.ExecutionException;
import org.eclipse.core.commands.IHandler;
import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.IRegion;
import org.eclipse.jface.text.TextSelection;
import org.eclipse.jface.viewers.ISelectionProvider;
import org.eclipse.swt.SWT;
import org.eclipse.swt.custom.ScrolledComposite;
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
import org.lamport.tla.toolbox.editor.basic.TLAEditor;
import org.lamport.tla.toolbox.editor.basic.handlers.ShowDeclarationsHandler.ShowDeclarationsPopupDialog;
import org.lamport.tla.toolbox.editor.basic.util.EditorUtil;
import org.lamport.tla.toolbox.util.ResourceHelper;
import org.lamport.tla.toolbox.util.UIHelper;

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
 * @author lamport
 * 
 */
public class DecomposeProofHandler extends AbstractHandler implements IHandler {

    private IDocument doc; // The document being edited.
    private String text; // The document as a string.
    private ISelectionProvider selectionProvider; //
    private TextSelection selection; // The current selection.
    private int offset; // The current offset.
    private ModuleNode module; // The module being edited.
    private TheoremNode theorem;// The theorem containing the selected step
    private TheoremNode step; // The step being decomposed.

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

        /*
         * The following text for finding the editor, document, selection, and
         * module are copied from other commands.
         */
        TLAEditor editor;
        editor = EditorUtil.getTLAEditorWithFocus();
        // gets the editor to which command applies
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

        // Set theorem the THEOREM containing the selection
        TheoremNode[] allTheorems = moduleNode.getTheorems();
        theorem = null;
        int i = 0;
        while ((theorem == null) & (i < allTheorems.length)) {
            if (EditorUtil.locationContainment(selectedLocation,
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
        ProofNode proof = step.getProof();
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
        
        // for testing
        Shell topshell = UIHelper.getShellProvider().getShell() ;
          Shell parent = new Shell(topshell, SWT.SHELL_TRIM) ; // | SWT.H_SCROLL); // SWT.RESIZE) ; // | SWT.V_SCROLL | SWT.H_SCROLL) ;
          parent.setText("This is set by setText") ;
          Composite shell = new Composite(parent, SWT.NONE) ;
        GridLayout gridLayout = new GridLayout(3, false);
        shell.setLayout(gridLayout);
        new Button(shell, SWT.PUSH).setText("B1");
        new Button(shell, SWT.PUSH).setText("Wide Button 2");
        new Button(shell, SWT.PUSH).setText("Button 3");
        Button button4 = new Button(shell, SWT.PUSH) ;
        button4.setText("B4eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee"); 
        GridData gridData = new GridData() ;
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

        System.out.println("Shell.size = " + shell.getSize().toString());
        System.out.println("parent.size = " + parent.getSize().toString());
        Point shellSize = shell.getSize() ;;
        parent.setSize(shellSize.x + 30, shellSize.y + 30) ;
        parent.update();
        parent.open();
        
        System.out.println("closed") ;

        return null;
    }
}
