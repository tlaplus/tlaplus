package org.lamport.tla.toolbox.tool.tlc.ui.editor;

import java.util.Enumeration;
import java.util.Hashtable;
import java.util.Vector;

import org.eclipse.ui.forms.SectionPart;

/**
 * Takes care of section on pages, and attributes on sections
 * @author Simon Zambrovski
 * @version $Id$
 */
/**
 * @author Simon Zambrovski
 * @version $Id$
 */
/**
 * @author Simon Zambrovski
 * @version $Id$
 */
public class DataBindingManager implements ISectionConstants
{
    private static final String[] EMPTY = new String[0];

    // section parts containing the sections
    private Hashtable sectionParts = new Hashtable(13);
    // storage to retrieve the page for a section
    private Hashtable pageForSection = new Hashtable(13);
    // storage to retrieve sections on a given page
    private Hashtable sectionsForPage = new Hashtable(13);
    // storage to retrieve the section for a given attribute
    private Hashtable sectionForAttribute = new Hashtable(37);
    // storage to retrieve the viewer for a given attribute
    private Hashtable viewerForAttribute = new Hashtable(37);

    /** 
     * expands a section by given section id
     */
    public void expandSection(String id)
    {
        SectionPart part = (SectionPart) sectionParts.get(id);
        if (part == null)
        {
            throw new IllegalArgumentException("No section for id");
        }
        if (!part.getSection().isExpanded())
        {
            part.getSection().setExpanded(true);
        }
    }
    
    /**
     * Enables or disables all section on the current page
     * @param enabled 
     */
    public void setAllSectionsEnabled(String pageId, boolean enabled)
    {
        String[] sectionIds = getSectionsForPage(pageId);
        for (int i = 0; i < sectionIds.length; i++)
        {
            enableSection(sectionIds[i], enabled);
        }
    }

    /**
     * enables a section by given id
     */
    public void enableSection(String id, boolean enabled)
    {
        SectionPart part = (SectionPart) sectionParts.get(id);
        if (part == null)
        {
            throw new IllegalArgumentException("No section for id");
        }
        part.getSection().setEnabled(true);
    }

    /**
     * retrieves the id of the page the section is on
     */
    public String getSectionPage(String id)
    {
        String pageId;
        if ((pageId = (String) pageForSection.get(id)) != null)
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
    public void bindSection(SectionPart sectionPart, String id, String pageId)
    {
        // store the section
        sectionParts.put(id, sectionPart);

        // store the page id
        pageForSection.put(id, pageId);

        Vector sectionIds = (Vector) sectionsForPage.get(pageId);
        if (sectionIds == null)
        {
            sectionIds = new Vector();
            sectionsForPage.put(pageId, sectionIds);
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
        Vector sectionIds = (Vector) sectionsForPage.get(pageId);
        if (sectionIds == null)
        {
            return EMPTY;
        } else
        {
            return (String[]) sectionIds.toArray(new String[sectionIds.size()]);
        }
    }

    /**
     * Retrieves a section id if the attribute is found  
     * @param attributeName the id of the attribute
     * @return the id of the section, or <code>null</code> if not found
     */
    public String getSectionForAttribute(String attributeName)
    {
        return (String) sectionForAttribute.get(attributeName);
    }

    /**
     * Retrieves the section by id
     * @param sectionId
     * @return the section part, or <code>null</code> if not found
     */
    public SectionPart getSection(String sectionId)
    {
        return (SectionPart) sectionParts.get(sectionId);
    }

    
    
    /**
     * Bind an attribute name <code>attributeName</code> to the viewer <code>attributeViewer</code> location in the section part <code>sectionPart</code>
     * This method should be called after the section is bound to the section id and page using {@link DataBindingManager#bindSection(SectionPart, String, String)} method
     * @param attributeName
     * @param attributeViewer
     * @param sectionPart
     */
    public void bindAttribute(String attributeName, Object attributeViewer, SectionPart sectionPart)
    {
        // bind the viewer
        viewerForAttribute.put(attributeName, attributeViewer);
        // bind the section id
        Enumeration enumeration = sectionParts.keys();
        while (enumeration.hasMoreElements())
        {
            Object sectionId = enumeration.nextElement();
            SectionPart registeredPart = (SectionPart) sectionParts.get(sectionId);
            if (registeredPart.equals(sectionPart))
            {
                sectionForAttribute.put(attributeName, sectionId);
                break;
            }
        }
    }

    /**
     * Retrieves the viewer for given attribute
     * @param attributeName
     * @return the Viewer
     */
    public Object getAttributeControl(String attributeName)
    {
        return viewerForAttribute.get(attributeName);
    }

}
