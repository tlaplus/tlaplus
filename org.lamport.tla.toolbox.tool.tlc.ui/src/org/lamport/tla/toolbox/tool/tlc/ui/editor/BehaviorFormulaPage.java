package org.lamport.tla.toolbox.tool.tlc.ui.editor;

import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IProgressMonitor;
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
import org.lamport.tla.toolbox.tool.tlc.launch.ui.IConfigurationConstants;
import org.lamport.tla.toolbox.tool.tlc.launch.ui.IConfigurationDefaultConstants;
import org.lamport.tla.toolbox.tool.tlc.ui.util.DirtyMarkingListener;
import org.lamport.tla.toolbox.tool.tlc.ui.util.FormHelper;
import org.lamport.tla.toolbox.tool.tlc.ui.util.IgnoringListener;
import org.lamport.tla.toolbox.util.IHelpConstants;

/**
 * Page to choose the specification formula 
 * @author Simon Zambrovski
 * @version $Id$
 */
public class BehaviorFormulaPage extends BasicFormPage implements IConfigurationConstants, IConfigurationDefaultConstants
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

        ignoringListeners.add(selectionAdapter);
        ignoringListeners.add(initNextFairnessListener);
        ignoringListeners.add(closedListener);

    }

    /**
     * 
     */
    protected void loadData() throws CoreException
    {
        
        String modelSpecification = getConfig().getAttribute(MODEL_SPECIFICATION, MODEL_SPECIFICATION_DEFAULT);
        
        Document closedDoc = new Document(modelSpecification);
        
        Document initDoc = new Document();
        Document nextDoc = new Document();
        Document fairnessDoc = new Document();

        closedFormulaRadio.setSelection(true);
        initNextFairnessRadio.setSelection(false);
        
        closedFormulaSource.setDocument(closedDoc);
        
        initFormulaSource.setDocument(initDoc);
        nextFormulaSource.setDocument(nextDoc);
        fairnessFormulaSource.setDocument(fairnessDoc);
    }

    
    

    protected void commit(boolean onSave)
    {
        // TODO
        String closedFormula = closedFormulaSource.getDocument().get();
        getConfig().setAttribute(MODEL_SPECIFICATION, closedFormula);
        
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
