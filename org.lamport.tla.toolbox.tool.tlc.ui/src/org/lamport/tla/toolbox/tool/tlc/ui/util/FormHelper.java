package org.lamport.tla.toolbox.tool.tlc.ui.util;

import java.util.Arrays;
import java.util.Iterator;
import java.util.List;
import java.util.Vector;

import org.eclipse.jface.text.source.SourceViewer;
import org.eclipse.jface.text.source.SourceViewerConfiguration;
import org.eclipse.jface.viewers.CheckboxTableViewer;
import org.eclipse.swt.custom.StyledText;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.ui.forms.events.IExpansionListener;
import org.eclipse.ui.forms.widgets.FormToolkit;
import org.eclipse.ui.forms.widgets.Section;
import org.eclipse.ui.forms.widgets.TableWrapData;
import org.eclipse.ui.forms.widgets.TableWrapLayout;
import org.lamport.tla.toolbox.tool.tlc.model.Formula;

/**
 * @author Simon Zambrovski
 * @version $Id$
 */
public class FormHelper
{
    public static final int FORM_BODY_MARGIN_TOP = 12;
    public static final int FORM_BODY_MARGIN_BOTTOM = 12;
    public static final int FORM_BODY_MARGIN_LEFT = 6;
    public static final int FORM_BODY_MARGIN_RIGHT = 6;
    public static final int FORM_BODY_HORIZONTAL_SPACING = 20;
    public static final int FORM_BODY_VERTICAL_SPACING = 17;

    /**
     * Create TableWrapLayout for the whole page 
     * @param makeColumnsEqualWidth
     * @param numColumns
     * @return
     */
    public static TableWrapLayout createFormTableWrapLayout(boolean makeColumnsEqualWidth, int numColumns)
    {
        TableWrapLayout layout = new TableWrapLayout();

        layout.topMargin = FORM_BODY_MARGIN_TOP;
        layout.bottomMargin = FORM_BODY_MARGIN_BOTTOM;
        layout.leftMargin = FORM_BODY_MARGIN_LEFT;
        layout.rightMargin = FORM_BODY_MARGIN_RIGHT;

        layout.horizontalSpacing = FORM_BODY_HORIZONTAL_SPACING;
        layout.verticalSpacing = FORM_BODY_VERTICAL_SPACING;

        layout.makeColumnsEqualWidth = makeColumnsEqualWidth;
        layout.numColumns = numColumns;

        return layout;
    }

    /**
     * Create GridLayout for the whole page
     * @param makeColumnsEqualWidth
     * @param numColumns
     * @return
     */
    public static GridLayout createFormGridLayout(boolean makeColumnsEqualWidth, int numColumns)
    {
        GridLayout layout = new GridLayout();

        layout.marginTop = FORM_BODY_MARGIN_TOP;
        layout.marginBottom = FORM_BODY_MARGIN_BOTTOM;
        layout.marginLeft = FORM_BODY_MARGIN_LEFT;
        layout.marginRight = FORM_BODY_MARGIN_RIGHT;

        layout.horizontalSpacing = FORM_BODY_HORIZONTAL_SPACING;
        layout.verticalSpacing = FORM_BODY_VERTICAL_SPACING;

        layout.makeColumnsEqualWidth = makeColumnsEqualWidth;
        layout.numColumns = numColumns;

        return layout;
    }

    /**
     * Constructs a section and returns a section client composite
     * 
     * the section layout is TableWrapLayout
     * 
     * 
     * @param parent parent container for the section
     * @param title title of the section
     * @param description description of the section
     * @param toolkit toolkit to create the composite
     * @param sectionFlags parameters of the section
     * @param expansionListener 
     * @return a section client (the content container of the section)
     */
    public static Section createSectionComposite(Composite parent, String title, String description,
            FormToolkit toolkit, int sectionFlags, IExpansionListener expansionListener)
    {
        Section section = toolkit.createSection(parent, sectionFlags);

        TableWrapData td = new TableWrapData(TableWrapData.FILL_GRAB);
        td.grabHorizontal = true;
        section.setLayoutData(td);
        section.setText(title);
        section.setDescription(description);

        if (expansionListener != null)
        {
            section.addExpansionListener(expansionListener);
        }

        // create section client
        Composite sectionClient = toolkit.createComposite(section);
        TableWrapLayout layout = new TableWrapLayout();
        layout.numColumns = 1;
        sectionClient.setLayout(layout);
        section.setClient(sectionClient);

        // draw flat borders
        toolkit.paintBordersFor(sectionClient);
        return section;
    }

    /**
     * @see {@link FormHelper#createSectionComposite(String, String, FormToolkit, Composite, int)} 
     */
    public static Section createSectionComposite(Composite parent, String title, String description, FormToolkit toolkit)
    {
        return createSectionComposite(parent, title, description, toolkit, Section.DESCRIPTION | Section.TITLE_BAR,
                null);
    }

    /**
     * creates a source viewer with given parent, toolkit and flags
     * @param toolkit
     * @param parent
     * @param flags
     * @return
     */
    public static SourceViewer createSourceViewer(FormToolkit toolkit, Composite parent, int flags)
    {
        SourceViewer sourceViewer = new SourceViewer(parent, null, null, false, flags);
        sourceViewer.setData(FormToolkit.KEY_DRAW_BORDER, FormToolkit.TREE_BORDER);
        SourceViewerConfiguration configuration = new SourceViewerConfiguration();
        sourceViewer.configure(configuration);

        StyledText control = sourceViewer.getTextWidget();
        control.setData(FormToolkit.KEY_DRAW_BORDER, FormToolkit.TREE_BORDER);
        control.setEditable(true);
        toolkit.adapt(control, true, true);

        return sourceViewer;
    }

    /**
     * Reads the input (list of formulas) and returns a list of strings which can be serialized 
     * @param source - checkbox table viewer containing the formulas
     * @return
     */
    public static List getSerializedInput(CheckboxTableViewer source)
    {
        
        List formulas =  (List) source.getInput();
        Object[] checkedArray = source.getCheckedElements();
        
        if (formulas == null) 
        {
            return null;
        }
        
        Vector result = new Vector(formulas.size()); 
        List checked = Arrays.asList(checkedArray);
        
        
        Iterator formulaIterator = formulas.iterator();
        
        Formula formula;
        String entry;
        while(formulaIterator.hasNext())
        {
            formula = (Formula) formulaIterator.next();
            entry = ((checked.contains(formula)) ? "1" : "0") + formula.toString();
            result.add(entry);
        }
        
        return result;
    }

    /**
     * Performs the inverse operation to {@link FormHelper#getSerializedInput(CheckboxTableViewer)} 
     * Sets input of the checkbox table viewer read from the serialized list  
     */
    public static void setSerializedInput(CheckboxTableViewer source, List serializedInput)
    {
        Iterator serializedIterator = serializedInput.iterator();
        Vector checked = new Vector();
        Vector input = ((Vector)source.getInput());
        if (input == null) 
        {
            input = new Vector();
        }
        
        
        while (serializedIterator.hasNext()) 
        {
            String entry = (String) serializedIterator.next();
            Formula formula = new Formula(entry.substring(1));
            input.add(formula);
            if ("1".equals(entry.substring(0, 1))) 
            {
                checked.add(formula);
            }
        }
        source.setInput(input);
        source.setCheckedElements(checked.toArray());
    }

}
