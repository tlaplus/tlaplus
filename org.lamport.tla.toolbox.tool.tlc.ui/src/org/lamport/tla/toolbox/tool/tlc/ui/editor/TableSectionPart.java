package org.lamport.tla.toolbox.tool.tlc.ui.editor;

import org.eclipse.jface.viewers.CheckboxTableViewer;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.swt.SWT;
import org.eclipse.swt.events.SelectionAdapter;
import org.eclipse.swt.events.SelectionEvent;
import org.eclipse.swt.events.SelectionListener;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Button;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Table;
import org.eclipse.ui.forms.IManagedForm;
import org.eclipse.ui.forms.SectionPart;
import org.eclipse.ui.forms.widgets.FormToolkit;
import org.lamport.tla.toolbox.tool.tlc.ui.editor.FormulaContentProvider.Formula;
import org.lamport.tla.toolbox.tool.tlc.ui.util.FormHelper;

/**
 * Section part with table and add and remove buttons
 * @author Simon Zambrovski
 * @version $Id$
 */
public class TableSectionPart extends SectionPart
{
    private CheckboxTableViewer tableViewer;

    private SelectionListener fSelectionListener = new SelectionAdapter() 
    {
        public void widgetSelected(SelectionEvent e)
        {
            Object source = e.getSource();
            if (source == buttonAdd)
            {
                doAdd();
            } else if (source == buttonRemove)
            {
                doRemove();
            }
        }
    };

    private Button buttonAdd;
    private Button buttonRemove;

    /**
     * 
     */
    public TableSectionPart(Composite composite, String title, String description, FormToolkit toolkit)
    {
        super(FormHelper.createSectionComposite(composite, title, description, toolkit));
    }

    public TableSectionPart(Composite composite, String title, String description, FormToolkit toolkit, int sectionFlags)
    {
        super(FormHelper.createSectionComposite(composite, title, description, toolkit, sectionFlags, null));
    }

    /**
     * Constructs the section content
     * @param toolkit
     */
    protected void sectionInitialize(FormToolkit toolkit)
    {
        GridData gd;

        Composite sectionArea = (Composite) getSection().getClient();
        sectionArea.setLayout(new GridLayout(2, false));

        Table table = toolkit.createTable(sectionArea, SWT.MULTI | SWT.CHECK | SWT.V_SCROLL | SWT.H_SCROLL);

        // The section grabs the entire space
        gd = new GridData(GridData.FILL_BOTH);
        gd.grabExcessVerticalSpace = true;
        getSection().setLayoutData(gd);

        // The table grabs the entire space
        gd = new GridData(GridData.FILL_BOTH);
        gd.grabExcessHorizontalSpace = true;
        gd.grabExcessVerticalSpace = true;
        // span for both buttons
        gd.verticalSpan = 2;

        table.setLayoutData(gd);
        table.setLinesVisible(false);
        table.setHeaderVisible(false);

        tableViewer = new CheckboxTableViewer(table);
        tableViewer.setContentProvider(new FormulaContentProvider());

        buttonAdd = toolkit.createButton(sectionArea, "Add", SWT.PUSH);
        buttonAdd.addSelectionListener(fSelectionListener);
        gd = new GridData();
        gd.verticalAlignment = SWT.TOP;
        gd.widthHint = 70;
        buttonAdd.setLayoutData(gd);

        buttonRemove = toolkit.createButton(sectionArea, "Remove", SWT.PUSH);
        buttonRemove.addSelectionListener(fSelectionListener);
        gd = new GridData();
        gd.verticalAlignment = SWT.TOP;
        gd.widthHint = 70;
        buttonRemove.setLayoutData(gd);
    }

    public void initialize(IManagedForm form)
    {
        super.initialize(form);
        sectionInitialize(form.getToolkit());
    }

    /**
     * Retrieves the table viewer
     * @return
     */
    public CheckboxTableViewer getTableViewer()
    {
        return tableViewer;
    }

    
    private void doRemove()
    {
        IStructuredSelection selection = (IStructuredSelection) tableViewer.getSelection();
        if (selection != null) 
        {
            tableViewer.remove(selection.toArray());
        }
    }

    private void doAdd()
    {
        Formula formula = new Formula("Added = 1");
        tableViewer.add(formula);
        tableViewer.setChecked(formula, true);
    }

}
