package org.lamport.tla.toolbox.tool.tlc.ui.editor.page;

import org.eclipse.core.runtime.CoreException;
import org.eclipse.jface.text.Document;
import org.eclipse.jface.text.source.SourceViewer;
import org.eclipse.swt.SWT;
import org.eclipse.swt.events.SelectionAdapter;
import org.eclipse.swt.events.SelectionEvent;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Button;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.eclipse.ui.forms.IManagedForm;
import org.eclipse.ui.forms.SectionPart;
import org.eclipse.ui.forms.editor.FormEditor;
import org.eclipse.ui.forms.events.ExpansionAdapter;
import org.eclipse.ui.forms.events.ExpansionEvent;
import org.eclipse.ui.forms.events.IExpansionListener;
import org.eclipse.ui.forms.widgets.FormToolkit;
import org.eclipse.ui.forms.widgets.Section;
import org.lamport.tla.toolbox.tool.tlc.ui.util.DirtyMarkingListener;
import org.lamport.tla.toolbox.tool.tlc.ui.util.FormHelper;
import org.lamport.tla.toolbox.tool.tlc.ui.util.IgnoringListener;
import org.lamport.tla.toolbox.util.IHelpConstants;

/**
 * Page to choose the specification formula 
 * @author Simon Zambrovski
 * @version $Id$
 * @deprecated
 */
public class BehaviorFormulaPage extends BasicFormPage
{

    public static final String ID = "BehaviorFormula";
    
    private SectionPart closedFormulaPart;
    private SectionPart initNextFairnessPart;

    private SourceViewer closedFormulaSource;

    private SourceViewer initFormulaSource;
    private SourceViewer nextFormulaSource;
    private SourceViewer fairnessFormulaSource;
    private Button initNextFairnessRadio;
    private Button closedFormulaRadio;

    public BehaviorFormulaPage(FormEditor editor)
    {
        super(editor, BehaviorFormulaPage.ID, "Behavior Formula");
        this.imagePath = "icons/full/loop_obj.gif";
        this.helpId = IHelpConstants.BEHAVIOR_FORMULA_MODEL_PAGE;
    }

    protected void createBodyContent(IManagedForm managedForm)
    {
        FormToolkit toolkit = managedForm.getToolkit();
        Composite parent = managedForm.getForm().getBody();

        closedFormulaRadio = toolkit.createButton(parent, "Use sigle formula", SWT.RADIO);

        // closed formula area
        Section closedFormulaComposite = FormHelper.createSectionComposite(parent, "Closed formula",
                "Specify the behavior by providing a single closed temporal formula.", toolkit, Section.DESCRIPTION
                        | Section.TITLE_BAR | Section.TWISTIE | Section.EXPANDED, getExpansionListener());

        Composite closedFormulaArea = (Composite) closedFormulaComposite.getClient();
        closedFormulaArea.setLayout(new GridLayout(1, false));

        // closed formula form part
        closedFormulaPart = new SectionPart(closedFormulaComposite);
        managedForm.addPart(closedFormulaPart);

        // listener for the part
        DirtyMarkingListener closedListener = new DirtyMarkingListener(closedFormulaPart, true);

        // closed formula source viewer
        closedFormulaSource = FormHelper.createSourceViewer(toolkit, closedFormulaArea, SWT.V_SCROLL | SWT.H_SCROLL);
        GridData gd = new GridData(GridData.FILL_HORIZONTAL);
        gd.heightHint = 80;
        closedFormulaSource.getTextWidget().setLayoutData(gd);
        closedFormulaSource.addTextListener(closedListener);

        initNextFairnessRadio = toolkit.createButton(parent, "Use separate formulas", SWT.RADIO);

        // section
        Section initNextFairnessComposite = FormHelper.createSectionComposite(parent, "Init, Next, Fairness",
                "Specify the behavior by providing the init, next actions and the fairness condition.", toolkit,
                Section.DESCRIPTION | Section.TITLE_BAR | Section.TWISTIE, getExpansionListener());
        Composite initNextFairnessArea = (Composite) initNextFairnessComposite.getClient();
        initNextFairnessArea.setLayout(new GridLayout(1, false));

        // part
        initNextFairnessPart = new SectionPart(initNextFairnessComposite);
        managedForm.addPart(initNextFairnessPart);

        // part listener
        DirtyMarkingListener initNextFairnessListener = new DirtyMarkingListener(initNextFairnessPart, true);

        // init
        initFormulaSource = FormHelper.createSourceViewer(toolkit, initNextFairnessArea, SWT.V_SCROLL | SWT.H_SCROLL);
        gd = new GridData(GridData.FILL_HORIZONTAL);
        gd.heightHint = 80;
        initFormulaSource.getTextWidget().setLayoutData(gd);
        initFormulaSource.addTextListener(initNextFairnessListener);

        // next
        nextFormulaSource = FormHelper.createSourceViewer(toolkit, initNextFairnessArea, SWT.V_SCROLL | SWT.H_SCROLL);
        gd = new GridData(GridData.FILL_HORIZONTAL);
        gd.heightHint = 80;
        nextFormulaSource.getTextWidget().setLayoutData(gd);
        nextFormulaSource.addTextListener(initNextFairnessListener);

        // fairness
        fairnessFormulaSource = FormHelper.createSourceViewer(toolkit, initNextFairnessArea, SWT.V_SCROLL
                | SWT.H_SCROLL);
        gd = new GridData(GridData.FILL_HORIZONTAL);
        gd.heightHint = 80;
        fairnessFormulaSource.getTextWidget().setLayoutData(gd);
        fairnessFormulaSource.addTextListener(initNextFairnessListener);

        MultiPartSelectionAdapter selectionAdapter = new MultiPartSelectionAdapter();
        // install selection adapters
        closedFormulaRadio.addSelectionListener(selectionAdapter);
        initNextFairnessRadio.addSelectionListener(selectionAdapter);

        dirtyPartListeners.add(selectionAdapter);
        dirtyPartListeners.add(initNextFairnessListener);
        dirtyPartListeners.add(closedListener);
    }
    
    

    /**
     * Load data from the model, or use defaults 
     */
    protected void loadData() throws CoreException
    {
        boolean isClosedFormula = getConfig().getAttribute(MODEL_BEHAVIOR_IS_CLOSED_SPEC_USED, MODEL_BEHAVIOR_IS_CLOSED_SPEC_USED_DEFAULT);
        
        // set up the radio buttons
        this.closedFormulaRadio.setSelection(isClosedFormula);
        this.initNextFairnessRadio.setSelection(!isClosedFormula);
        
        this.initNextFairnessPart.getSection().setExpanded(this.initNextFairnessRadio.getSelection());
        this.closedFormulaPart.getSection().setExpanded(this.closedFormulaRadio.getSelection());

        

        // closed spec
        String modelSpecification = getConfig().getAttribute(MODEL_BEHAVIOR_CLOSED_SPECIFICATION, EMPTY_STRING);
        Document closedDoc = new Document(modelSpecification);
        this.closedFormulaSource.setDocument(closedDoc);

        // init
        String modelInit = getConfig().getAttribute(MODEL_BEHAVIOR_SEPARATE_SPECIFICATION_INIT, EMPTY_STRING);
        Document initDoc = new Document(modelInit);
        this.initFormulaSource.setDocument(initDoc);

        // next
        String modelNext = getConfig().getAttribute(MODEL_BEHAVIOR_SEPARATE_SPECIFICATION_NEXT, EMPTY_STRING);
        Document nextDoc = new Document(modelNext);
        this.nextFormulaSource.setDocument(nextDoc);
        
        // fairness
        String modelFairness = getConfig().getAttribute(MODEL_BEHAVIOR_SEPARATE_SPECIFICATION_FAIRNESS, EMPTY_STRING);
        Document fairnessDoc = new Document(modelFairness);
        this.fairnessFormulaSource.setDocument(fairnessDoc);
    }

    
    
    /**
     * Commit the page content
     */
    public void commit(boolean onSave)
    {
        
        // closed formula
        String closedFormula = this.closedFormulaSource.getDocument().get();
        getConfig().setAttribute(MODEL_BEHAVIOR_CLOSED_SPECIFICATION, closedFormula);

        // init formula
        String initFormula = this.initFormulaSource.getDocument().get();
        getConfig().setAttribute(MODEL_BEHAVIOR_SEPARATE_SPECIFICATION_INIT, initFormula);

        // next formula
        String nextFormula = this.nextFormulaSource.getDocument().get();
        getConfig().setAttribute(MODEL_BEHAVIOR_SEPARATE_SPECIFICATION_NEXT, nextFormula);

        // fairness formula
        String fairnessFormula = this.fairnessFormulaSource.getDocument().get();
        getConfig().setAttribute(MODEL_BEHAVIOR_SEPARATE_SPECIFICATION_FAIRNESS, fairnessFormula);

        // mode 
        boolean isClosedSpecification = this.closedFormulaRadio.getSelection();
        getConfig().setAttribute(MODEL_BEHAVIOR_IS_CLOSED_SPEC_USED, isClosedSpecification);
        
        super.commit(onSave);
    }

    /**
     * Folds the section 
     */
    public IExpansionListener getExpansionListener()
    {
        return new ExpansionAdapter() {

            public void expansionStateChanged(ExpansionEvent e)
            {
                if (e.getSource() instanceof Section)
                {
                    Control sectionClient = ((Section) e.getSource());
                    if (sectionClient == closedFormulaPart.getSection())
                    {
                        closedFormulaPart.markDirty();
                        initNextFairnessPart.markDirty();
                        initNextFairnessPart.getSection().setExpanded(false);
                        closedFormulaRadio.setSelection(true);
                        initNextFairnessRadio.setSelection(false);
                    }

                    if (sectionClient == initNextFairnessPart.getSection())
                    {
                        closedFormulaPart.markDirty();
                        initNextFairnessPart.markDirty();
                        closedFormulaPart.getSection().setExpanded(false);
                        closedFormulaRadio.setSelection(false);
                        initNextFairnessRadio.setSelection(true);
                    }

                }

                // perform the form re-flow
                BehaviorFormulaPage.super.getExpansionListener().expansionStateChanged(e);
            }
        };
    }

    class MultiPartSelectionAdapter extends SelectionAdapter implements IgnoringListener
    {
        private boolean ignoreInput = true;

        public void widgetSelected(SelectionEvent e)
        {
            if (!ignoreInput)
            {
                closedFormulaPart.getSection().setExpanded(closedFormulaRadio.getSelection());
                initNextFairnessPart.getSection().setExpanded(initNextFairnessRadio.getSelection());
                closedFormulaPart.markDirty();
                initNextFairnessPart.markDirty();
            }
        }

        public void setIgnoreInput(boolean ignoreInput)
        {
            this.ignoreInput = ignoreInput;
        }
    }
}
