package org.lamport.tla.toolbox.tool.tlc.ui.editor.page.results;

import java.util.concurrent.locks.Lock;
import java.util.concurrent.locks.ReentrantLock;

import org.eclipse.core.runtime.CoreException;
import org.eclipse.jface.resource.JFaceResources;
import org.eclipse.jface.text.Document;
import org.eclipse.jface.text.IDocument;
import org.eclipse.jface.text.IDocumentPartitioner;
import org.eclipse.jface.text.ITextOperationTarget;
import org.eclipse.jface.text.source.SourceViewer;
import org.eclipse.swt.SWT;
import org.eclipse.swt.custom.StyledText;
import org.eclipse.swt.events.KeyEvent;
import org.eclipse.swt.events.KeyListener;
import org.eclipse.swt.events.SelectionAdapter;
import org.eclipse.swt.events.SelectionEvent;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Button;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Label;
import org.eclipse.ui.forms.IManagedForm;
import org.eclipse.ui.forms.editor.FormEditor;
import org.eclipse.ui.forms.events.IExpansionListener;
import org.eclipse.ui.forms.widgets.FormToolkit;
import org.eclipse.ui.forms.widgets.Section;
import org.lamport.tla.toolbox.editor.basic.TLAEditorActivator;
import org.lamport.tla.toolbox.editor.basic.TLAFastPartitioner;
import org.lamport.tla.toolbox.editor.basic.TLAPartitionScanner;
import org.lamport.tla.toolbox.editor.basic.TLASourceViewerConfiguration;
import org.lamport.tla.toolbox.tool.tlc.model.Model;
import org.lamport.tla.toolbox.tool.tlc.output.data.ITLCModelLaunchDataPresenter;
import org.lamport.tla.toolbox.tool.tlc.output.data.TLCModelLaunchDataProvider;
import org.lamport.tla.toolbox.tool.tlc.output.source.TLCOutputSourceRegistry;
import org.lamport.tla.toolbox.tool.tlc.ui.TLCUIActivator;
import org.lamport.tla.toolbox.tool.tlc.ui.editor.ModelEditor;
import org.lamport.tla.toolbox.tool.tlc.ui.editor.page.BasicFormPage;
import org.lamport.tla.toolbox.tool.tlc.ui.editor.page.MainModelPage;
import org.lamport.tla.toolbox.tool.tlc.ui.editor.part.ValidateableSectionPart;
import org.lamport.tla.toolbox.tool.tlc.ui.util.DirtyMarkingListener;
import org.lamport.tla.toolbox.tool.tlc.ui.util.FormHelper;
import org.lamport.tla.toolbox.util.IHelpConstants;
import org.lamport.tla.toolbox.util.UIHelper;

/**
 * This class is in this package as part of historical situation in which its UI
 * facets were originally part of the 'Results' page; in some future world, this
 * class should probably be moved out of this package.
 */
public class EvaluateConstantExpressionPage extends BasicFormPage implements ITLCModelLaunchDataPresenter {
    public static final String ID = "evaluateConstantExpressionPage";
    
    /** Exists for making RCPTT tests nicer, hopefully **/
    public static String getTabTitle() {
    	return "Constant Expressions";
    }
   
	static BodyContentAssets createBodyContent(final Composite body, final FormToolkit toolkit, final int sectionFlags,
			final int textFieldFlags, final IExpansionListener expansionListener, final ModelEditor modelEditor) {
        // There is no description line for this section, so it is necessary to eliminate that bit in the style flags that
        // are passed in. If the bit were not changed to 0, an extra empty line would appear below the title.
		final Section section = FormHelper.createSpaceGrabbingSectionComposite(body, "Evaluate Constant Expression", "",
				toolkit, sectionFlags & ~Section.DESCRIPTION, expansionListener);
        GridData gd = new GridData();
        gd.horizontalAlignment = SWT.FILL;
        gd.verticalAlignment = SWT.FILL;
        gd.grabExcessHorizontalSpace = true;
        gd.grabExcessVerticalSpace = true;
        section.setLayoutData(gd);

        Composite resultArea = (Composite) section.getClient();
        GridLayout gl = new GridLayout(1, false);
        gl.marginHeight = 0;
        gl.marginWidth = 0;
        resultArea.setLayout(gl);

        final Composite expressionComposite = toolkit.createComposite(resultArea);
        gd = new GridData();
        gd.horizontalAlignment = SWT.FILL;
        gd.verticalAlignment = SWT.FILL;
        gd.grabExcessHorizontalSpace = true;
        gd.grabExcessVerticalSpace = true;
        gd.horizontalIndent = 0;
        gd.verticalIndent = 0;
        gd.minimumWidth = 360;
        expressionComposite.setLayoutData(gd);
        gl = new GridLayout(1, false);
        expressionComposite.setLayout(gl);

        final Composite labelToggleLine = toolkit.createComposite(expressionComposite);
        gd = new GridData();
        gd.horizontalAlignment = SWT.FILL;
        gd.grabExcessHorizontalSpace = true;
        gd.horizontalIndent = 0;
        gd.verticalIndent = 0;
        gd.minimumWidth = 360;
        labelToggleLine.setLayoutData(gd);
        gl = new GridLayout(2, false);
        labelToggleLine.setLayout(gl);
        
        Label l = toolkit.createLabel(labelToggleLine, "Expression: ");
		gd = new GridData();
		gd.horizontalAlignment = SWT.LEFT;
		gd.heightHint = l.computeSize(SWT.DEFAULT, SWT.DEFAULT).y;
		l.setLayoutData(gd);
		
		final Button b = new Button(labelToggleLine, SWT.CHECK);
		b.setText("No Behavior Spec");
		gd = new GridData();
		gd.horizontalAlignment = SWT.RIGHT;
		gd.heightHint = b.computeSize(SWT.DEFAULT, SWT.DEFAULT).y;
		gd.grabExcessHorizontalSpace = true;
		b.setLayoutData(gd);
		b.setSelection(modelEditor.modelIsConfiguredWithNoBehaviorSpec());
		b.addSelectionListener(new SelectionAdapter() {
			@Override
			public void widgetSelected(final SelectionEvent e) {
				final MainModelPage mmp = (MainModelPage)modelEditor.findPage(MainModelPage.ID);
				
				mmp.setNoBehaviorSpec(b.getSelection());
			}
		});
		
		
		final SourceViewer input = FormHelper.createFormsSourceViewer(toolkit, expressionComposite, textFieldFlags,
				new TLASourceViewerConfiguration());
		input.getTextWidget().addKeyListener(new KeyListener() {
			@Override
			public void keyPressed(KeyEvent e) {
				if (isUndoKeyPress(e)) {
					input.doOperation(ITextOperationTarget.UNDO);
				} else if (isRedoKeyPress(e)) {
					input.doOperation(ITextOperationTarget.REDO);
				}
			}

			private boolean isRedoKeyPress(KeyEvent e) {
				return ((e.stateMask & SWT.CONTROL) > 0) && ((e.keyCode == 'y') || (e.keyCode == 'Y'));
			}

			private boolean isUndoKeyPress(KeyEvent e) {
				return ((e.stateMask & SWT.CONTROL) > 0) && ((e.keyCode == 'z') || (e.keyCode =='Z'));
			}

			@Override
			public void keyReleased(KeyEvent e) { }
		});
        
        // Reminder that this layout data is for this text area within the expression composite within the result area
		gd = new GridData();
		gd.horizontalAlignment = SWT.FILL;
		gd.verticalAlignment = SWT.FILL;
		gd.grabExcessHorizontalSpace = true;
		gd.grabExcessVerticalSpace = true;
		gd.minimumWidth = 360;
		gd.minimumHeight = 80;
		input.getTextWidget().setLayoutData(gd);
		
		

        l = toolkit.createLabel(expressionComposite, "Value: ");
		gd = new GridData();
		gd.horizontalAlignment = SWT.LEFT;
		gd.heightHint = l.computeSize(SWT.DEFAULT, SWT.DEFAULT).y;
		l.setLayoutData(gd);
        final SourceViewer output = FormHelper.createFormsOutputViewer(toolkit, expressionComposite, textFieldFlags);
        // Reminder that this layout data is for this text area within the value composite within the result area
		gd = new GridData();
		gd.horizontalAlignment = SWT.FILL;
		gd.verticalAlignment = SWT.FILL;
		gd.grabExcessHorizontalSpace = true;
		gd.grabExcessVerticalSpace = true;
		gd.minimumWidth = 360;
		gd.minimumHeight = 80;
		output.getTextWidget().setLayoutData(gd);

        // We want this font to be the same as the input. If it was not set it would be the same as the font
        // in the module editor.
		input.getTextWidget().setFont(JFaceResources.getTextFont());
		output.getTextWidget().setFont(JFaceResources.getTextFont());
        // This is required to paint the borders of the text boxes it must be called on the direct parent of the widget
        // with a border. There is a call of this method in FormHelper.createSectionComposite, but that is called
        // on the section which is not a direct parent of the text box widget.
        toolkit.paintBordersFor(expressionComposite);
    	
    	return new BodyContentAssets(section, input, output, b);
    }
    

	private SourceViewer m_expressionInput;
	private SourceViewer m_expressionOutput;
	private ValidateableSectionPart m_validateableCalculatorSection;
	
	private Button m_toggleButton;

    private final Lock disposeLock = new ReentrantLock(true);

    /**
     * Constructs the page
     * 
     * @param editor
     */
	public EvaluateConstantExpressionPage(final FormEditor editor) {
        super(editor, ID, getTabTitle(), "icons/full/ece_page_" + IMAGE_TEMPLATE_TOKEN + ".png");
        helpId = IHelpConstants.EVALUATE_CON_EX_PAGE;
    }

	@Override
	protected void createBodyContent(IManagedForm managedForm) {
        final int sectionFlags = Section.TITLE_BAR | Section.TREE_NODE | Section.EXPANDED | SWT.WRAP;
        final int textFieldFlags = SWT.MULTI | SWT.V_SCROLL | SWT.READ_ONLY | SWT.FULL_SELECTION | SWT.WRAP;

        final FormToolkit toolkit = managedForm.getToolkit();
        final Composite body = managedForm.getForm().getBody();
        final GridLayout gl = new GridLayout();
        gl.marginHeight = 0;
        gl.marginWidth = 0;
        body.setLayout(gl);
        
		final BodyContentAssets bca = createBodyContent(body, toolkit, sectionFlags, textFieldFlags,
				getExpansionListener(), (ModelEditor)getEditor());
		m_expressionInput = bca.getExpressionInput();
		m_expressionOutput = bca.getExpressionOutput();
		m_toggleButton = bca.m_toggleButton;

		m_validateableCalculatorSection = new ValidateableSectionPart(bca.getSection(), this, SEC_EXPRESSION);
        // This ensures that when the part is made dirty, the model appears unsaved.
        managedForm.addPart(m_validateableCalculatorSection);

        // This makes the widget unsaved when text is entered.
        m_expressionInput.getTextWidget().addModifyListener(new DirtyMarkingListener(m_validateableCalculatorSection, false));

        getDataBindingManager().bindSection(m_validateableCalculatorSection, SEC_EXPRESSION, getId());
        getDataBindingManager().bindAttribute(Model.MODEL_EXPRESSION_EVAL, m_expressionInput, m_validateableCalculatorSection);
	}
    
	public void setNoBehaviorSpecToggleState(final boolean selected) {
		m_toggleButton.setSelection(selected);
	}
	
	public State getECEContent() {
		if (m_expressionInput != null) {
			return new State(m_expressionInput.getDocument(), m_expressionOutput.getTextWidget().getText(),
					m_toggleButton.getSelection());
		}
		
		return null;
	}
	
	public void setECEContent(final State state) {
		if (m_expressionInput == null) {
			TLCUIActivator.getDefault().logError("Can't set ECE content on null objects.");
		} else {
			m_expressionInput.setDocument(state.getInputDocument());
			m_expressionOutput.getTextWidget().setText(state.getOutputText());
			m_toggleButton.setSelection(state.getToggleState());
		}
	}
	
    /**
     * Gets the data provider for the current page
     */
    @Override
	public void loadData() throws CoreException {
		final TLCOutputSourceRegistry modelCheckSourceRegistry = TLCOutputSourceRegistry.getModelCheckSourceRegistry();
		final TLCModelLaunchDataProvider provider = modelCheckSourceRegistry.getProvider(getModel());
		if (provider != null) {
			provider.addDataPresenter(this);
		} else {
			// no data provider
			m_expressionOutput.getTextWidget().setText("");
		}
    	
		final Document document = new Document(getModel().getEvalExpression());
		final IDocumentPartitioner partitioner = new TLAFastPartitioner(
				TLAEditorActivator.getDefault().getTLAPartitionScanner(), TLAPartitionScanner.TLA_PARTITION_TYPES);
		document.setDocumentPartitioner(TLAPartitionScanner.TLA_PARTITIONING, partitioner);
		partitioner.connect(document);
		m_expressionInput.setDocument(document);
	}

    /**
     * Save data back to model
     */
	public void commit(boolean onSave) {
        final String expression = m_expressionInput.getDocument().get();
        getModel().unsavedSetEvalExpression(expression);

        super.commit(onSave);
    }

    /**
     * Dispose the page
     */
	public void dispose() {
		disposeLock.lock();
		try {
			final IManagedForm managedForm = getManagedForm();

			managedForm.removePart(m_validateableCalculatorSection);

			getDataBindingManager().unbindSectionAndAttribute(SEC_EXPRESSION);
			getDataBindingManager().unbindSectionFromPage(SEC_EXPRESSION, getId());

			final Model model = getModel();
			final TLCOutputSourceRegistry modelCheckSourceRegistry = TLCOutputSourceRegistry.getModelCheckSourceRegistry();
			// Do not initialize provider in dispose if it hasn't been initialized yet.
			if (modelCheckSourceRegistry.hasProvider(model)) {
				final TLCModelLaunchDataProvider provider = modelCheckSourceRegistry.getProvider(model);
				if (provider != null) {
					provider.removeDataPresenter(this);
				}
			}

			super.dispose();
		} finally {
			disposeLock.unlock();
		}
	}

    /**
     * {@inheritDoc}
     */
	@Override
	public void setFocus() {
		if ((m_expressionInput != null) && !m_expressionInput.getTextWidget().isDisposed()
										&& !m_expressionInput.getTextWidget().isFocusControl()) {
			final StyledText st = m_expressionInput.getTextWidget();
			final int caretOffset = st.getText().length();
			
			st.setFocus();
			
			/*
			 * We get a focus notification at least 3 times after TLC execution finishes, in which none of those times
			 * 	does the text widget believe itself focused. Further, the text widget gaining focus resets its caret
			 * 	offset to 0; so, nearly ubiquitously we end up with the caret offset position set invocation never
			 * 	sticking. We resort to this waiting-out-the-notification-storm ugly hack to get the caret set
			 *  to stick; were we getting more than 3 notifications, i would use a thread pool to gate proliferation
			 *  here.
			 */
			final Runnable ohSWT = () -> {
				try {
					Thread.sleep(75);
				} catch (Exception e) { }
				
				if (!st.isDisposed()) {
					st.getDisplay().asyncExec(() -> {
						if (!st.isDisposed()) {
							st.setCaretOffset(caretOffset);
						}
					});
				}
			};
			(new Thread(ohSWT)).start();
		}
	}

    /**
     * Will be called by the provider on data changes
     */
	public void modelChanged(final TLCModelLaunchDataProvider dataProvider, final int fieldId) {
        UIHelper.runUIAsync(() -> {
			// Acquire dispose lock prior to widget access. Using a single
			// lock just to serialize dispose and modelChange seems
			// overkill, but the wait-for graph becomes tricky with all the
			// background jobs going on (at least too tricky to get it
			// solved within an hour).
			disposeLock.lock();
			try {
				if (getPartControl().isDisposed()) {
					return;
				}
				if (fieldId == CONST_EXPR_EVAL_OUTPUT) {
					m_expressionOutput.getTextWidget().setText(dataProvider.getCalcOutput());
				}
			} finally {
				disposeLock.unlock();
			}
        });
    }

	
	static class BodyContentAssets {
		private final Section m_section;
		private final SourceViewer m_expressionInput;
		private final SourceViewer m_expressionOutput;
		private final Button m_toggleButton;
		
		BodyContentAssets(final Section s, final SourceViewer input, final SourceViewer output, final Button toggle) {
			m_section = s;
			m_expressionInput = input;
			m_expressionOutput = output;
			m_toggleButton = toggle;
		}
		
		Section getSection() {
			return m_section;
		}
		
		SourceViewer getExpressionInput() {
			return m_expressionInput;
		}
		
		SourceViewer getExpressionOutput() {
			return m_expressionOutput;
		}
		
		Button getToggleButton() {
			return m_toggleButton;
		}
	}
	
	static public class State {
		private final IDocument m_inputDocument;
		private final String m_outputText;
		private final boolean m_toggleState;
		
		State (final IDocument document, final String text, final boolean toggleState) {
			m_inputDocument = document;
			m_outputText = text;
			m_toggleState = toggleState;
		}

		public IDocument getInputDocument() {
			return m_inputDocument;
		}

		public String getOutputText() {
			return m_outputText;
		}

		public boolean getToggleState() {
			return m_toggleState;
		}
	}
}
