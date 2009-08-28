package org.lamport.tla.toolbox.tool.tlc.ui.util;

import java.util.Arrays;
import java.util.Iterator;
import java.util.List;
import java.util.Vector;

import org.eclipse.jface.text.TabsToSpacesConverter;
import org.eclipse.jface.text.source.SourceViewer;
import org.eclipse.jface.text.source.SourceViewerConfiguration;
import org.eclipse.jface.viewers.CheckboxTableViewer;
import org.eclipse.jface.viewers.TableViewer;
import org.eclipse.swt.SWT;
import org.eclipse.swt.custom.StyledText;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Label;
import org.eclipse.swt.widgets.Text;
import org.eclipse.ui.forms.events.IExpansionListener;
import org.eclipse.ui.forms.widgets.FormToolkit;
import org.eclipse.ui.forms.widgets.Section;
import org.eclipse.ui.forms.widgets.TableWrapData;
import org.eclipse.ui.forms.widgets.TableWrapLayout;
import org.lamport.tla.toolbox.tool.tlc.model.Formula;
import org.lamport.tla.toolbox.tool.tlc.ui.TLCUIActivator;
import org.lamport.tla.toolbox.tool.tlc.util.ModelHelper;

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
     * creates a source viewer with given parent, toolkit and flags adopted to a form
     * @param toolkit
     * @param parent
     * @param flags
     * @return
     */
    public static SourceViewer createFormsSourceViewer(FormToolkit toolkit, Composite parent, int flags)
    {
        SourceViewer sourceViewer = createSourceViewer(parent, flags);
        sourceViewer.setData(FormToolkit.KEY_DRAW_BORDER, FormToolkit.TREE_BORDER);
        
        sourceViewer.getTextWidget().setData(FormToolkit.KEY_DRAW_BORDER, FormToolkit.TREE_BORDER);
        toolkit.adapt(sourceViewer.getTextWidget(), true, true);

        return sourceViewer;
    }

    /**
     * creates a forms-adopted read-only source viewer
     * @param toolkit
     * @param parent
     * @param flags
     * @return
     */
    public static SourceViewer createFormsOutputViewer(FormToolkit toolkit, Composite parent, int flags)
    {
        SourceViewer sourceViewer = createOutputViewer(parent, flags);
        sourceViewer.setData(FormToolkit.KEY_DRAW_BORDER, FormToolkit.TREE_BORDER);
        
        sourceViewer.getTextWidget().setData(FormToolkit.KEY_DRAW_BORDER, FormToolkit.TREE_BORDER);
        toolkit.adapt(sourceViewer.getTextWidget(), true, true);

        return sourceViewer;
    }

    
    /**
     * Creates the source viewer
     * @param parent
     * @param flags
     * @return
     */
    public static SourceViewer createOutputViewer(Composite parent, int flags)
    {
        SourceViewer sourceViewer = new SourceViewer(parent, null, null, false, flags);
        SourceViewerConfiguration configuration = new SourceViewerConfiguration();
        sourceViewer.configure(configuration);
        sourceViewer.setTabsToSpacesConverter(getTabToSpacesConverter());

        StyledText control = sourceViewer.getTextWidget();
        control.setFont(TLCUIActivator.getDefault().getOutputFont());
        control.setEditable(false);
        return sourceViewer;
    }

    
    /**
     * Creates the source viewer
     * @param parent
     * @param flags
     * @return
     */
    public static SourceViewer createSourceViewer(Composite parent, int flags)
    {
        SourceViewer sourceViewer = new SourceViewer(parent, null, null, false, flags);
        SourceViewerConfiguration configuration = new SourceViewerConfiguration();
        sourceViewer.configure(configuration);
        sourceViewer.setTabsToSpacesConverter(getTabToSpacesConverter());

        StyledText control = sourceViewer.getTextWidget();
        control.setWordWrap(true);
        control.setFont(TLCUIActivator.getDefault().getCourierFont());
        control.setEditable(true);
        return sourceViewer;
    }

    /**
     * Reads the input (list of formulas) and returns a list of strings which can be serialized 
     * @param source - viewer containing the formulas/assignments
     * @return
     */
    public static List getSerializedInput(TableViewer table)
    {
        if (table instanceof CheckboxTableViewer)
        {
            CheckboxTableViewer source = (CheckboxTableViewer) table;
            List formulas = (List) source.getInput();
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
            while (formulaIterator.hasNext())
            {
                formula = (Formula) formulaIterator.next();
                entry = ((checked.contains(formula)) ? "1" : "0") + formula.toString();
                result.add(entry);
            }

            return result;

        } else
        {
            List assignments = (List) table.getInput();
            if (assignments == null)
            {
                return null;
            }

            return ModelHelper.serializeAssignmentList(assignments);

        }

    }

    /**
     * Performs the inverse operation to {@link FormHelper#getSerializedInput(CheckboxTableViewer)} 
     */
    public static void setSerializedInput(TableViewer table, List serializedInput)
    {
        Vector input = ((Vector) table.getInput());
        if (input == null)
        {
            input = new Vector();
        }
        // handling Formulas
        if (table instanceof CheckboxTableViewer)
        {
            Iterator serializedIterator = serializedInput.iterator();
            Vector checked = new Vector();

            CheckboxTableViewer checkTable = (CheckboxTableViewer) table;
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
            checkTable.setInput(input);
            checkTable.setCheckedElements(checked.toArray());

        } else
        // handling Assignments
        {
            List deserializeAssignmentList = ModelHelper.deserializeAssignmentList(serializedInput);
            table.setInput(deserializeAssignmentList);
        }

    }

    /**
     * Retrieves the tab to spaces converter
     * @return
     */
    public static TabsToSpacesConverter getTabToSpacesConverter()
    {
        TabsToSpacesConverter converter = new TabsToSpacesConverter();
        converter.setNumberOfSpacesPerTab(4);
        return converter;
    }

    /**
     * Cuts the trailing \n \t and spaces
     * @param string
     * @return the string without trailing whitespaces
     */
    public static String trimTrailingSpaces(String string)
    {
        if (string == null) 
        {
            return null;
        } 
        for (int i = string.length() - 1; i >= 0; i--)
        {
            if (string.charAt(i) == '\t' || string.charAt(i) == ' ' || string.charAt(i) == '\n' || string.charAt(i) == '\r') 
            {
                continue;
            } else {
                string = string.substring(0, i + 1);
                return string;
            }
        }
        return string;
    }
    
    /**
     * Creates a text component with left-aligned text
     * @param title
     * @param parent
     * @param toolkit
     * @return
     */
    public static Text createTextLeft(String title, Composite parent, FormToolkit toolkit)
    {
        Label createLabel = toolkit.createLabel(parent, title);
        GridData gd = new GridData();
        createLabel.setLayoutData(gd);
        gd.verticalAlignment = SWT.TOP;
        Text text = toolkit.createText(parent, "");

        gd = new GridData(SWT.FILL, SWT.LEFT, true, false);
        gd.horizontalIndent = 30;
        gd.verticalAlignment = SWT.TOP;
        gd.horizontalAlignment = SWT.RIGHT;
        gd.minimumWidth = 150;
        text.setLayoutData(gd);

        return text;
    }

    
    /**
     * Returns true, if the string matches [A-Za-z0-9_]*[A-Za-z]{1}[A-Za-z0-9_]*
     * @param string
     * @return true, if the string consists of any nun-zero number letters, _ and digits but has at least one letter 
     */
    public static boolean isIdentifier(String string)
    {
        if (string == null || string.equals(""))
        {
            return false;
        }
        return string.matches("[A-Za-z0-9_]*[A-Za-z]{1}[A-Za-z0-9_]*");
    }
}
