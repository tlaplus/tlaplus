package org.lamport.tla.toolbox.tool.tlc.ui.editor;

import org.eclipse.jface.text.Document;
import org.eclipse.jface.text.source.SourceViewer;
import org.eclipse.swt.SWT;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.eclipse.ui.forms.editor.FormEditor;
import org.eclipse.ui.forms.events.ExpansionAdapter;
import org.eclipse.ui.forms.events.ExpansionEvent;
import org.eclipse.ui.forms.events.IExpansionListener;
import org.eclipse.ui.forms.widgets.FormToolkit;
import org.eclipse.ui.forms.widgets.Section;
import org.lamport.tla.toolbox.tool.tlc.ui.util.FormHelper;
import org.lamport.tla.toolbox.util.IHelpConstants;

/**
 * @author Simon Zambrovski
 * @version $Id$
 */
public class BehaviorFormulaPage extends BasicFormPage
{

    public static final String ID = "BehaviorFormula";
    private Section closedFormulaComposite;
    private Section initNextFairnessComposite;
    private SourceViewer closedFormulaSource;
    private SourceViewer initFormulaSource;
    private SourceViewer nextFormulaSource;
    private SourceViewer fairnessFormulaSource;

    public BehaviorFormulaPage(FormEditor editor)
    {
        super(editor, BehaviorFormulaPage.ID, "Behavior Formula");

        this.helpId = IHelpConstants.BEHAVIOR_FORMULA_MODEL_PAGE;
    }

    /* (non-Javadoc)
     * @see org.lamport.tla.toolbox.tool.tlc.ui.editor.BasicFormPage#createContent(org.eclipse.ui.forms.widgets.FormToolkit, org.eclipse.swt.widgets.Composite)
     */
    protected void createBodyContent(FormToolkit toolkit, Composite parent)
    {
        // enabling button
        toolkit.createButton(parent, "Use sigle formula", SWT.RADIO);
        
        // closed formula area
        closedFormulaComposite = FormHelper.createSectionComposite(parent,
                "Closed formula", "Specify the behavior by providing a single closed temporal formula.", toolkit, Section.DESCRIPTION
                        | Section.TITLE_BAR | Section.TWISTIE | Section.EXPANDED, getExpansionListener());
        
        Composite closedFormulaArea = (Composite) closedFormulaComposite.getClient();
        closedFormulaArea.setLayout(new GridLayout(1, false));

        closedFormulaSource = FormHelper.createSourceViewer(toolkit, closedFormulaArea, SWT.V_SCROLL | SWT.H_SCROLL);
        
        GridData gd = new GridData(GridData.FILL_HORIZONTAL);
        gd.heightHint = 80;
        closedFormulaSource.getTextWidget().setLayoutData(gd);

        // enabling button
        toolkit.createButton(parent, "Use separate formulas", SWT.RADIO);

        initNextFairnessComposite = FormHelper.createSectionComposite(parent,
                "Init, Next, Fairness", "Specify the behavior by providing the init, next actions and the fairness condition.", toolkit, Section.DESCRIPTION
                        | Section.TITLE_BAR | Section.TWISTIE, getExpansionListener());
        Composite initNextFairnessArea = (Composite) initNextFairnessComposite.getClient();
        initNextFairnessArea.setLayout(new GridLayout(1, false));

        // init
        initFormulaSource = FormHelper.createSourceViewer(toolkit, initNextFairnessArea, SWT.V_SCROLL | SWT.H_SCROLL);
        gd = new GridData(GridData.FILL_HORIZONTAL);
        gd.heightHint = 80;
        initFormulaSource.getTextWidget().setLayoutData(gd);

        // next
        nextFormulaSource = FormHelper.createSourceViewer(toolkit, initNextFairnessArea, SWT.V_SCROLL | SWT.H_SCROLL);
        gd = new GridData(GridData.FILL_HORIZONTAL);
        gd.heightHint = 80;
        nextFormulaSource.getTextWidget().setLayoutData(gd);

        // fairness
        fairnessFormulaSource = FormHelper.createSourceViewer(toolkit, initNextFairnessArea, SWT.V_SCROLL | SWT.H_SCROLL);
        gd = new GridData(GridData.FILL_HORIZONTAL);
        gd.heightHint = 80;
        fairnessFormulaSource.getTextWidget().setLayoutData(gd);
        
        setData();
    }

    /**
     * 
     */
    private void setData()
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
    public IExpansionListener getExpansionListener1()
    {
        return new ExpansionAdapter()
        {
            
            public void expansionStateChanged(ExpansionEvent e)
            {
                if (e.getSource() instanceof Section) 
                {
                    Control sectionClient = ((Section)e.getSource());
                    if (sectionClient == closedFormulaComposite) 
                    {
                        initNextFairnessComposite.setExpanded(false);    
                    }
                    
                    if (sectionClient == initNextFairnessComposite) 
                    {
                        closedFormulaComposite.setExpanded(false);
                    }
                    
                }

                // perform the form re-flow
                BehaviorFormulaPage.super.getExpansionListener().expansionStateChanged(e);
            }
        };
        
    }

    
}
