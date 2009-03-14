package org.lamport.tla.toolbox.tool.tlc.ui.editor;

import org.eclipse.jface.text.Document;
import org.eclipse.jface.text.source.SourceViewer;
import org.eclipse.swt.SWT;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
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
import org.lamport.tla.toolbox.util.IHelpConstants;

/**
 * Page to choose the specification formula 
 * @author Simon Zambrovski
 * @version $Id$
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
        
        // enabling button
        toolkit.createButton(parent, "Use sigle formula", SWT.RADIO);

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

        // enabling button
        toolkit.createButton(parent, "Use separate formulas", SWT.RADIO);

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
        
        setInput();
        
        initNextFairnessListener.setIgnoreInput(false);
        closedListener.setIgnoreInput(false);
    }
    

    /**
     * 
     */
    private void setInput()
    {
        Document closedDoc = new Document();
        Document initDoc = new Document();
        Document nextDoc = new Document();
        Document fairnessDoc = new Document();

        closedFormulaSource.setDocument(closedDoc);

        initFormulaSource.setDocument(initDoc);
        nextFormulaSource.setDocument(nextDoc);
        fairnessFormulaSource.setDocument(fairnessDoc);
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
                    }

                    if (sectionClient == initNextFairnessPart.getSection())
                    {
                        closedFormulaPart.markDirty();
                        initNextFairnessPart.markDirty();
                        closedFormulaPart.getSection().setExpanded(false);
                    }

                }

                // perform the form re-flow
                BehaviorFormulaPage.super.getExpansionListener().expansionStateChanged(e);
            }
        };

    }
}
