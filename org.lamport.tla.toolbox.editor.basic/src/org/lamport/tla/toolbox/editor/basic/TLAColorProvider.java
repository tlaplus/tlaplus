package org.lamport.tla.toolbox.editor.basic;

import java.util.HashMap;
import java.util.Iterator;
import java.util.Map;

import org.eclipse.swt.graphics.Color;
import org.eclipse.swt.graphics.RGB;
import org.eclipse.swt.widgets.Display;

/**
 * @author Simon Zambrovski
 * @version $Id$
 */
public class TLAColorProvider
{

    public static final RGB MULTI_LINE_COMMENT = new RGB(128, 0, 0);
    public static final RGB COMMENT = new RGB(128, 128, 0);
    public static final RGB KEYWORD = new RGB(0, 0, 128);

    // public static final RGB TYPE = new RGB(0, 0, 128);
    public static final RGB STRING = new RGB(0, 128, 0);
    public static final RGB DEFAULT = new RGB(0, 0, 0);
    
    /*
    public static final RGB JAVADOC_KEYWORD = new RGB(0, 128, 0);
    public static final RGB JAVADOC_TAG = new RGB(128, 128, 128);
    public static final RGB JAVADOC_LINK = new RGB(128, 128, 128);
    public static final RGB JAVADOC_DEFAULT = new RGB(0, 128, 128);
    */
    
    
    protected Map fColorTable = new HashMap(10);

    /**
     * Release all of the color resources held onto by the receiver.
     */
    public void dispose()
    {
        Iterator e = fColorTable.values().iterator();
        while (e.hasNext())
            ((Color) e.next()).dispose();
    }

    /**
     * Return the color that is stored in the color table under the given RGB
     * value.
     * 
     * @param rgb the RGB value
     * @return the color stored in the color table for the given RGB value
     */
    public Color getColor(RGB rgb)
    {
        Color color = (Color) fColorTable.get(rgb);
        if (color == null)
        {
            color = new Color(Display.getCurrent(), rgb);
            fColorTable.put(rgb, color);
        }
        return color;
    }
}
