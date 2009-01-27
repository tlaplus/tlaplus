package org.lamport.tla.toolbox.ui.view;

import java.util.Iterator;
import java.util.List;

import org.eclipse.swt.SWT;
import org.eclipse.swt.custom.StyleRange;
import org.eclipse.swt.custom.StyledText;
import org.eclipse.swt.layout.RowLayout;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Event;
import org.eclipse.swt.widgets.ExpandBar;
import org.eclipse.swt.widgets.ExpandItem;
import org.eclipse.swt.widgets.Listener;
import org.eclipse.ui.part.ViewPart;
import org.lamport.tla.toolbox.Activator;
import org.lamport.tla.toolbox.spec.Spec;
import org.lamport.tla.toolbox.spec.parser.problem.Problem;
import org.lamport.tla.toolbox.spec.parser.problem.ProblemContainer;
import org.lamport.tla.toolbox.util.AdapterFactory;

/**
 * Shows parse problems
 * @version $Id$
 * @author Simon Zambrovski
 */
public class ProblemView extends ViewPart
{
    public static final String ID = "toolbox.view.ProblemView";
    private ExpandBar bar = null;

    public ProblemView()
    {
    }

    /**
     * Creates the layout and fill it with data 
     */
    public void createPartControl(Composite parent)
    {
        parent.getShell().setText("TLA+ Parse Problems");

        bar = new ExpandBar(parent, SWT.V_SCROLL | SWT.BORDER);
        bar.setSpacing(8);


        
        ProblemContainer container = getProblemContainer();
        if (container != null)
        {
            List problems = container.getProblems(Problem.ALL);
            Iterator pIterator = problems.iterator();

            for (; pIterator.hasNext();)
            {
                final Problem problem = (Problem) pIterator.next();

                // listener
                Listener listener = new Listener() {

                    public void handleEvent(Event event)
                    {
                        System.out.println("Down on " + problem.location.moduleName);
/*
                        IEditorPart part = UIHelper.openEditor(OpenSpecHandler.TLA_EDITOR, new FileEditorInput((IFile) Activator.getSpecManager().getSpecLoaded().findModule(problem.location.moduleName)));
                        if (part instanceof IGotoMarker) 
                        {
                            // ((IGotoMarker)part).gotoMarker(null);
                        }
*/                        
                    }
                };

                // contents of the item
                Composite problemItem = new Composite(bar, SWT.LINE_SOLID);
                problemItem.setLayout(new RowLayout(SWT.VERTICAL));
                problemItem.addListener(SWT.MouseDown, listener);

                String[] lines = problem.message.split("\n");
                for (int i = 0; i < lines.length; i++)
                {
                    StyledText styledText = new StyledText(problemItem, SWT.INHERIT_DEFAULT);
                    styledText.setEditable(false);
                    styledText.setCursor(styledText.getDisplay().getSystemCursor(SWT.CURSOR_HAND));
                    styledText.setText(lines[i]);
                    styledText.addListener(SWT.MouseDown, listener);

                    if (isErrorLine(lines[i], problem))
                    {
                        StyleRange range = new StyleRange();
                        range.underline = true;
                        range.foreground = styledText.getDisplay().getSystemColor(SWT.COLOR_RED);
                        range.start = 0;
                        range.length = lines[i].length();
                        styledText.setStyleRange(range);
                    }

                    /*
                    Label label = new Label(problemItem, SWT.INHERIT_DEFAULT);
                    label.setText(lines[i]);
                    */
                }

                ExpandItem item = new ExpandItem(bar, SWT.NONE, 0);
                item.setExpanded(true);
                item.setText(AdapterFactory.getProblemTypeAsText(problem));
                item.setHeight(problemItem.computeSize(SWT.DEFAULT, SWT.DEFAULT).y);
                item.setControl(problemItem);
                item.addListener(SWT.MouseDown, listener);
            }
        } // else no errors to display
    }

    private boolean isErrorLine(String line, Problem problem)
    {
        return line.indexOf("module " + problem.location.moduleName) != -1;
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
