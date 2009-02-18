package org.lamport.tla.toolbox.ui.property;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;

import org.eclipse.jface.preference.FieldEditor;
import org.eclipse.jface.util.IPropertyChangeListener;
import org.eclipse.jface.util.PropertyChangeEvent;
import org.eclipse.swt.SWT;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.eclipse.ui.dialogs.PropertyPage;

/**
 * @author Simon Zambrovski
 * @version $Id$
 */
public abstract class GenericFieldEditorPropertyPage extends PropertyPage implements IPropertyChangeListener
{
    private List fields;
    private FieldEditor invalidFieldEditor;

    protected void initialize()
    {
        if (fields != null)
        {
            Iterator e = fields.iterator();
            while (e.hasNext())
            {
                FieldEditor fieldEditor = (FieldEditor) e.next();
                fieldEditor.setPage(this);
                fieldEditor.setPreferenceStore(getPreferenceStore());
                fieldEditor.load();
            }
        }
    }

    protected void addEditor(FieldEditor editor)
    {
        if (fields == null)
        {
            fields = new ArrayList();
        }
        fields.add(editor);
    }

    /*
     * @see org.eclipse.jface.preference.PreferencePage#createContents(org.eclipse.swt.widgets.Composite)
     */
    protected Control createContents(Composite parent)
    {
        Composite composite = new Composite(parent, SWT.NONE);
        GridLayout layout = new GridLayout();
        composite.setLayout(layout);
        GridData layoutData = new GridData(GridData.FILL);
        layoutData.grabExcessHorizontalSpace = true;
        composite.setLayoutData(layoutData);

        createFieldEditors(composite);
        
        initialize();
        
        
        return composite;
    }

    public abstract void createFieldEditors(Composite composite);

    /**  
     * The field editor preference page implementation of a <code>PreferencePage</code>
     * method loads all the field editors with their default values.
     */
    protected void performDefaults()
    {
        if (fields != null)
        {
            Iterator e = fields.iterator();
            while (e.hasNext())
            {
                FieldEditor pe = (FieldEditor) e.next();
                pe.loadDefault();
            }
        }
        // Force a recalculation of my error state.
        checkState();
        super.performDefaults();
    }

    /** 
     * The field editor preference page implementation of this 
     * <code>PreferencePage</code> method saves all field editors by
     * calling <code>FieldEditor.store</code>. Note that this method
     * does not save the preference store itself; it just stores the
     * values back into the preference store.
     *
     * @see FieldEditor#store()
     */
    public boolean performOk()
    {
        if (fields != null)
        {
            Iterator e = fields.iterator();
            while (e.hasNext())
            {
                FieldEditor pe = (FieldEditor) e.next();
                pe.store();
            }
        }
        return true;
    }

    /**
     * The field editor preference page implementation of this <code>IPreferencePage</code>
     * (and <code>IPropertyChangeListener</code>) method intercepts <code>IS_VALID</code> 
     * events but passes other events on to its superclass.
     */
    public void propertyChange(PropertyChangeEvent event)
    {

        if (event.getProperty().equals(FieldEditor.IS_VALID))
        {
            boolean newValue = ((Boolean) event.getNewValue()).booleanValue();
            // If the new value is true then we must check all field editors.
            // If it is false, then the page is invalid in any case.
            if (newValue)
            {
                checkState();
            } else
            {
                setInvalidFieldEditor((FieldEditor) event.getSource());
                setValid(newValue);
            }
        }
    }

    /**
     * Recomputes the page's error state by calling <code>isValid</code> for
     * every field editor.
     */
    protected void checkState()
    {
        boolean valid = true;
        setInvalidFieldEditor(null);
        // The state can only be set to true if all
        // field editors contain a valid value. So we must check them all
        if (fields != null)
        {
            int size = fields.size();
            for (int i = 0; i < size; i++)
            {
                FieldEditor editor = (FieldEditor) fields.get(i);
                valid = valid && editor.isValid();
                if (!valid)
                {
                    setInvalidFieldEditor(editor);
                    break;
                }
            }
        }
        setValid(valid);
    }

    /**
     * @param invalidFieldEditor the invalidFieldEditor to set
     */
    public void setInvalidFieldEditor(FieldEditor invalidFieldEditor)
    {
        this.invalidFieldEditor = invalidFieldEditor;
    }

    /**
     * @return the invalidFieldEditor
     */
    public FieldEditor getInvalidFieldEditor()
    {
        return invalidFieldEditor;
    }

}
