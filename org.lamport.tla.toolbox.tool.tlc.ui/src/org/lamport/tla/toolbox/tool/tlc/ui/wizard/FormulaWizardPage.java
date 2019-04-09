package org.lamport.tla.toolbox.tool.tlc.ui.wizard;

import org.eclipse.jface.text.Document;
import org.eclipse.jface.text.IDocumentPartitioner;
import org.eclipse.jface.text.ITextOperationTarget;
import org.eclipse.jface.text.source.SourceViewer;
import org.eclipse.jface.wizard.WizardPage;
import org.eclipse.swt.SWT;
import org.eclipse.swt.custom.StyledText;
import org.eclipse.swt.events.KeyEvent;
import org.eclipse.swt.events.KeyListener;
import org.eclipse.swt.events.ModifyEvent;
import org.eclipse.swt.events.ModifyListener;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Label;
import org.lamport.tla.toolbox.editor.basic.TLAEditorActivator;
import org.lamport.tla.toolbox.editor.basic.TLAFastPartitioner;
import org.lamport.tla.toolbox.editor.basic.TLAPartitionScanner;
import org.lamport.tla.toolbox.editor.basic.TLASourceViewerConfiguration;
import org.lamport.tla.toolbox.tool.tlc.ui.util.FormHelper;
import org.lamport.tla.toolbox.util.UIHelper;

/**
 * A page with a simple field for formula editing
 * @author Simon Zambrovski
 */
public class FormulaWizardPage extends WizardPage
{
    private SourceViewer sourceViewer;
    private Document document;
	private final String extendedDescription;
	private final String helpId;

    public FormulaWizardPage(String action, String description)
    {
        this(action, description, null, null);
    }
    
    public FormulaWizardPage(String action, String description, String extendedDescription, String helpId)
    {
        super("FormulaWizardPage");
        setTitle(action);
        setDescription(description);
        this.extendedDescription = extendedDescription;
        this.helpId = helpId;
    }

    /* (non-Javadoc)
     * @see org.eclipse.jface.dialogs.IDialogPage#createControl(org.eclipse.swt.widgets.Composite)
     */
    public void createControl(Composite parent)
    {
    	
        Composite container = new Composite(parent, SWT.NULL);
        GridLayout layout = new GridLayout(1, false);
        container.setLayout(layout);
        
        if (helpId != null) {
        	UIHelper.setHelp(container, helpId);
        }
        
		sourceViewer = FormHelper.createSourceViewer(container, SWT.BORDER | SWT.MULTI | SWT.H_SCROLL | SWT.V_SCROLL,
				new TLASourceViewerConfiguration());
		sourceViewer.getTextWidget().addKeyListener(new KeyListener() {
			@Override
			public void keyPressed(KeyEvent e) {
				if (isUndoKeyPress(e)) {
					sourceViewer.doOperation(ITextOperationTarget.UNDO);
				} else if (isRedoKeyPress(e)) {
					sourceViewer.doOperation(ITextOperationTarget.REDO);
				}
			}

			private boolean isRedoKeyPress(KeyEvent e) {
				return ((e.stateMask & SWT.CONTROL) > 0) && ((e.keyCode == 'y') || (e.keyCode == 'Y'));
			}

			private boolean isUndoKeyPress(KeyEvent e) {
				return ((e.stateMask & SWT.CONTROL) > 0) && ((e.keyCode == 'z') || (e.keyCode =='Z'));
			}

			@Override
			public void keyReleased(KeyEvent e) {
			}
		});

        // SWT.FILL causes the text field to expand and contract
        // with changes in size of the dialog window.
        GridData gd = new GridData(SWT.FILL, SWT.FILL, true, true);
        gd.heightHint = 200;
        gd.widthHint = 400;
        gd.grabExcessHorizontalSpace = true;
        gd.grabExcessVerticalSpace = true;

        StyledText control = sourceViewer.getTextWidget();
        control.addModifyListener(new ModifyListener() {

            public void modifyText(ModifyEvent e)
            {
                getContainer().updateButtons();
            }

        });
        control.setEditable(true);
        control.setLayoutData(gd);

    

        if (this.document == null)
        {
            this.document = new Document();
        }
		final IDocumentPartitioner partitioner = new TLAFastPartitioner(
				TLAEditorActivator.getDefault().getTLAPartitionScanner(), TLAPartitionScanner.TLA_PARTITION_TYPES);
		document.setDocumentPartitioner(TLAPartitionScanner.TLA_PARTITIONING, partitioner);
		partitioner.connect(document);
        sourceViewer.setDocument(this.getDocument());

        
        // Add extended description below source viewer if given.
        if (extendedDescription != null) {
        	final Label extendedLbl = new Label(container, SWT.WRAP);
        	extendedLbl.setText(extendedDescription);
			gd = new GridData(GridData.FILL_HORIZONTAL);
			gd.widthHint = 400; // same width as source viewer
			extendedLbl.setLayoutData(gd);
        }

        setControl(container);
    }

    public Document getDocument()
    {
        return this.document;
    }

    public void setDocument(Document document)
    {
        this.document = document;
    }

}
