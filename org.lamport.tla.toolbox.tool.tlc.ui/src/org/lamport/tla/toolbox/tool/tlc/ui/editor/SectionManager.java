package org.lamport.tla.toolbox.tool.tlc.ui.editor;

import java.util.Hashtable;

import org.eclipse.ui.forms.widgets.ExpandableComposite;

/**
 * @author Simon Zambrovski
 * @version $Id$
 */
public class SectionManager implements ISectionManager
{

    // sections array to be able to pre-expand them
    private Hashtable sections = new Hashtable(13);
    
    private Hashtable pages = new Hashtable(13);

    /* (non-Javadoc)
     * @see org.lamport.tla.toolbox.tool.tlc.ui.editor.ISectionManager#expandSection(int)
     */
    public void expandSection(String id)
    {
        ExpandableComposite section;
        if ((section = (ExpandableComposite) sections.get(id)) != null)
        {
            // System.out.println("Section to expand : " + id);
            if (!section.isExpanded()) 
            {
                section.setExpanded(true);
            }
        } else
        {
            throw new IllegalArgumentException("No section for id");
        }
    }

    /* (non-Javadoc)
     * @see org.lamport.tla.toolbox.tool.tlc.ui.editor.ISectionManager#expandSection(int)
     */
    public String getSectionPage(String id)
    {
        String pageId;
        if ((pageId = (String) pages.get(id)) != null)
        {
            return pageId;
        } else
        {
            throw new IllegalArgumentException("No page for id");
        }
    }

    /**
     * Adds a section to the manager
     * @param section
     * @param id
     * @param pageId
     */
    public void addSection(ExpandableComposite section, String id, String pageId)
    {
        // store the section
        sections.put(id, section);
        
        // store the page id
        pages.put(id, pageId);
    }
}
