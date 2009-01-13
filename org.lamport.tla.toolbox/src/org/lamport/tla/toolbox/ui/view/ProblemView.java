package org.lamport.tla.toolbox.ui.view;

import java.util.Iterator;
import java.util.List;

import org.eclipse.jface.viewers.TableViewer;
import org.eclipse.swt.SWT;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.layout.RowLayout;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.ExpandBar;
import org.eclipse.swt.widgets.ExpandItem;
import org.eclipse.swt.widgets.Label;
import org.eclipse.ui.model.BaseWorkbenchContentProvider;
import org.eclipse.ui.model.WorkbenchLabelProvider;
import org.eclipse.ui.part.ViewPart;
import org.lamport.tla.toolbox.Activator;
import org.lamport.tla.toolbox.spec.Spec;
import org.lamport.tla.toolbox.spec.parser.problem.Problem;
import org.lamport.tla.toolbox.spec.parser.problem.ProblemContainer;

/**
 * Shows parse problems
 * 
 * @author zambrovski
 */
public class ProblemView extends ViewPart
{
    public static final String ID  = "toolbox.view.ProblemView";
    private ExpandBar          bar = null;

    public ProblemView()
    {
    }

    public void createPartControlTable(Composite parent)
    {

        TableViewer viewer = new TableViewer(parent, SWT.BORDER | SWT.MULTI | SWT.V_SCROLL);
        getSite().setSelectionProvider(viewer);
        viewer.getColumnProperties();
        viewer.setLabelProvider(new WorkbenchLabelProvider());
        viewer.setContentProvider(new BaseWorkbenchContentProvider());

        viewer.setInput(getProblemContainer());

    }

    public void createPartControl(Composite parent)
    {
        parent.getShell().setText("Parse Problems");
        bar = new ExpandBar(parent, SWT.V_SCROLL | SWT.BORDER);
        bar.setSpacing(8);

        ProblemContainer container = getProblemContainer();
        if (container != null)
        {
            List problems = container.getProblems(Problem.ALL);
            Iterator pIterator = problems.iterator();

            for (; pIterator.hasNext();)
            {
                Problem problem = (Problem) pIterator.next();

                Composite problemItem = new Composite(bar, SWT.LINE_SOLID);
                problemItem.setLayout(new RowLayout(SWT.VERTICAL));

                String[] lines = problem.message.split("\n");
                for (int i = 0; i < lines.length; i++)
                {
                    Label label = new Label(problemItem, SWT.INHERIT_DEFAULT);
                    label.setText(lines[i]);
                }

                ExpandItem item = new ExpandItem(bar, SWT.NONE, 0);
                item.setExpanded(true);
                item.setText("");
                item.setHeight(problemItem.computeSize(SWT.DEFAULT, SWT.DEFAULT).y);
                item.setControl(problemItem);

            }
        } // else no errors to display
    }

    public void createPartControlSWT(Composite parent)
    {
        Composite container;
        container = new Composite(parent, SWT.BORDER | SWT.V_SCROLL);
        container.setLayout(new GridLayout(1, true));
        container.setBackground(parent.getDisplay().getSystemColor(SWT.COLOR_WHITE));

        List problems = Activator.getSpecManager().getSpecLoaded().getParseProblems().getProblems(Problem.ALL);
        Iterator pIterator = problems.iterator();

        for (; pIterator.hasNext();)
        {
            Problem problem = (Problem) pIterator.next();

            Composite problemItem = new Composite(container, SWT.LINE_SOLID);
            problemItem.setLayout(new RowLayout(SWT.VERTICAL));

            String[] lines = problem.message.split("\n");
            for (int i = 0; i < lines.length; i++)
            {
                Label label = new Label(problemItem, SWT.INHERIT_DEFAULT);
                label.setText(lines[i]);
            }
        }

    }

    /*
     * (non-Javadoc)
     * @see org.eclipse.ui.part.WorkbenchPart#setFocus()
     */
    public void setFocus()
    {
        bar.setFocus();
    }

    /**
     * Retrieves the source of the problems to display
     * 
     * @return
     */
    private ProblemContainer getProblemContainer()
    {
        Spec spec = Activator.getSpecManager().getSpecLoaded();
        if (spec == null)
        {
            return null;
        } else
        {
            return spec.getParseProblems();
        }

    }
}
