package org.lamport.tla.toolbox.tool.tlc.ui.wizard;

import org.eclipse.swt.SWT;
import org.eclipse.swt.layout.RowLayout;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Label;
import org.eclipse.swt.widgets.Text;

/**
 * @author Simon Zambrovski
 * @version $Id$
 */
public class LabeledListComposite
{
    Text[] fields;
    String[] values;
    
    public LabeledListComposite(Composite parent, String label, String[] values)
    {
        this.values = values;
        this.fields = new Text[values.length];
        initContent(parent, label);
    }

    /**
     * @param i 
     * @param parent 
     * 
     */
    private void initContent(Composite parent, String label)
    {
        Composite self = new Composite(parent, SWT.NONE);
        self.setLayout(new RowLayout(SWT.HORIZONTAL));
        
        Label l;
        
        l = new Label(self, SWT.NULL);
        l.setText(label + "(");

        for (int i = 0; i < fields.length; i++)
        {
            fields[i] = new Text(self, SWT.NONE);
            fields[i].setText(values[i]);
            if (i != fields.length - 1) 
            {
                l = new Label(self, SWT.NULL);
                l.setText(", ");
            }
        }
        
        l = new Label(self, SWT.NULL);
        l.setText(")");
    }
    
    public String[] getValues()
    {
        String[] result = new String[fields.length];
        
        for (int i = 0; i < fields.length; i++)
        {
            result[i] = fields[i].getText();
        }
        
        return result;
    }
}
