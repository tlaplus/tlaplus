package org.lamport.tla.toolbox.tool.tlc.ui.editor;

import java.util.Hashtable;
import java.util.Vector;

import org.eclipse.ui.forms.widgets.ExpandableComposite;

/**
 * Takes care of section on pages
 * @author Simon Zambrovski
 * @version $Id$
 */
public class SectionManager implements ISectionManager
{
    private static final String[] EMPTY = new String[0];
    
    // sections array to be able to pre-expand them
    private Hashtable sections = new Hashtable(13);
    private Hashtable pages = new Hashtable(13);
    private Hashtable pageInverse = new Hashtable(13);

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
    public void enableSection(String id, boolean enabled)
    {
        ExpandableComposite section;
        if ((section = (ExpandableComposite) sections.get(id)) != null)
        {
            section.setEnabled(enabled);
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

        Vector sectionIds = (Vector) pageInverse.get(pageId);
        if (sectionIds == null)
        {
            sectionIds = new Vector();
            pageInverse.put(pageId, sectionIds);
        }
        
        sectionIds.add(id);
    }

    /**
     * Retrieves the section of the current page
     * @param pageId page id 
     * @return an array with sections or empty array
     */
    public String[] getSectionsForPage(String pageId)
    {
        Vector sectionIds = (Vector) pageInverse.get(pageId);
        if (sectionIds == null) 
        {
            return EMPTY;
        } else {
            return (String[]) sectionIds.toArray(new String[sectionIds.size()]);
        }
    }
}
