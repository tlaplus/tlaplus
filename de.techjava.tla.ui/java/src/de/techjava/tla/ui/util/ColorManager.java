package de.techjava.tla.ui.util;

import java.util.Collection;
import java.util.HashMap;
import java.util.Iterator;
import java.util.Map;
import java.util.Vector;

import org.eclipse.jface.preference.IPreferenceStore;
import org.eclipse.jface.preference.PreferenceConverter;
import org.eclipse.swt.graphics.Color;
import org.eclipse.swt.graphics.RGB;
import org.eclipse.swt.widgets.Display;

/**
 * A toolkit providing cached syntax colors
 * @author Simon Zambrovski, <a href="http://simon.zambrovski.org">http://simon.zambrovski.org</a> 
 * @version $Id: ColorManager.java,v 1.1 2005/08/22 15:43:31 szambrovski Exp $
 */
public class ColorManager 
{
	private Map 				colorMap;
	private IPreferenceStore 	store;
    private Vector 				listeners = new Vector();

	public ColorManager(IPreferenceStore store) 
	{
		this.colorMap = new HashMap();
		this.store = store;
	}
	/**
	 * Reinitialize the color manager
	 */
	public void reInitialize()
	{
	    Collection colors = colorMap.keySet();
	    for (Iterator i = colors.iterator(); i.hasNext();)
	    {
	        String key = (String)i.next();
	        colorMap.put(key, (Color) colorMap.get(key));
	    }
	}
	/**
	 * Retrieves a color
	 * @param type
	 * @return
	 */
	public Color getColor(String type) 
	{
		if(colorMap == null) 
		{
			colorMap = new HashMap();
		}
		RGB prefColor = PreferenceConverter.getColor(store, type);
		Color color = null;
		if (colorMap.containsKey(type)
			&& (color = (Color) colorMap.get(type)).getRGB().equals(prefColor)) 
		{
			color = (Color) colorMap.get(type);
		} else {
			color = new Color(Display.getDefault(), prefColor);
			colorMap.put(type, color);
		}
		return color;
	}
	/**
	 * Disposes the colors
	 */
	public void dispose() {
		Collection colors = colorMap.values();
		for (Iterator iter = colors.iterator(); iter.hasNext();) 
		{
			Color color = (Color) iter.next();
			colorMap.remove(color);
			color.dispose();
		}
	}
	/**
	 * Initialize dolor defauls
	 */
	public void initializeDefaultPreferences()
	{
		PreferenceConverter.setDefault(store, ITLAEditorColorConstants.COMMENT,						ITLAEditorColorConstants.DEFAULT_COMMENT_COLOR);
		PreferenceConverter.setDefault(store, ITLAEditorColorConstants.COMMENT_MULTILINE,			ITLAEditorColorConstants.DEFAULT_COMMENT_MULTI_COLOR);
		PreferenceConverter.setDefault(store, ITLAEditorColorConstants.TEXT,						ITLAEditorColorConstants.DEFAULT_TEXT_COLOR);
		PreferenceConverter.setDefault(store, ITLAEditorColorConstants.RESERVED,					ITLAEditorColorConstants.DEFAULT_RESERVED_COLOR);
		PreferenceConverter.setDefault(store, ITLAEditorColorConstants.OPERATOR,					ITLAEditorColorConstants.DEFAULT_OPERATOR_COLOR);
		PreferenceConverter.setDefault(store, ITLAEditorColorConstants.CTX_INFORMATION_POPUP_BG,	ITLAEditorColorConstants.DEFAULT_CTX_INFORMATION_POPUP_BG);
		PreferenceConverter.setDefault(store, ITLAEditorColorConstants.IDENTIFIER,					ITLAEditorColorConstants.DEFAULT_IDENTIFIER);
		
		PreferenceConverter.setDefault(store, ITLAConsoleConstants.CONSOLE_PARSER_COLOR,			ITLAConsoleConstants.DEFAULT_CONSOLE_PARSER_COLOR);
		PreferenceConverter.setDefault(store, ITLAConsoleConstants.CONSOLE_CHECKER_COLOR,			ITLAConsoleConstants.DEFAULT_CONSOLE_CHECKER_COLOR);
		
		
	}
	/**
	 * Adds a listener to color manager
	 * the listener is informed if color setting are changed
	 * @param listener
	 */
	public void addColorManagerListener(IColorManagerListener listener)
	{
	    this.listeners.add(listener);
	}
	/**
	 * Adds a listener to color manager
	 * the listener is informed if color setting are changed
	 * @param listener
	 */
	public void removeColorManagerListener(IColorManagerListener listener)
	{
	    this.listeners.remove(listener);
	}
	/**
	 * Infor listeners about changes
	 */
	protected void fireColorManagerChangesOccured()
	{
	    for (Iterator i = listeners.iterator(); i.hasNext(); )
	    {
	        ((IColorManagerListener)i.next()).colorManagerChanged();
	    }
	}

}

/*
 * $Log: ColorManager.java,v $
 * Revision 1.1  2005/08/22 15:43:31  szambrovski
 * sf cvs init
 *
 * Revision 1.6  2004/10/24 23:12:14  sza
 * new colors for console added
 *
 * Revision 1.5  2004/10/23 16:10:35  sza
 * new colors
 *
 * Revision 1.4  2004/10/20 22:42:31  sza
 * editor improvements
 *
 * Revision 1.3  2004/10/13 19:30:26  sza
 * new colors
 *
 * Revision 1.2  2004/10/13 14:43:04  sza
 * operators added
 *
 * Revision 1.1  2004/10/12 16:21:38  sza
 * initial commit
 *
 * Revision 1.1  2004/10/12 09:55:11  sza
 * additions
 *
 * Revision 1.1  2004/10/06 01:02:29  sza
 * initial commit
 *
 * Revision 1.1  2004/10/06 00:59:04  sza
 * initial commit
 *
 *
 */