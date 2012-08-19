package org.lamport.tla.toolbox.editor.basic;

import java.util.HashMap;
import java.util.Iterator;
import java.util.Map;

import org.eclipse.swt.graphics.Color;
import org.eclipse.swt.graphics.RGB;
import org.eclipse.swt.widgets.Display;

/**
 * Color provider
 * @author Simon Zambrovski
 * @version $Id$
 */
public class TLAColorProvider
{

    public static final RGB TLA_MULTI_LINE_COMMENT = new RGB(64, 64, 255);
    public static final RGB TLA_SINGLE_LINE_COMMENT = new RGB(0, 128, 64);
    
    // Added for PlusCal
    public static final RGB PCAL_KEYWORD = new RGB(175, 40, 10);


    public static final RGB TLA_KEYWORD = new RGB(128, 0, 128); 
    public static final RGB TLA_VALUE = new RGB(0, 0, 255); 
    public static final RGB TLA_DEFAULT = new RGB(0, 0, 0);
    public static final RGB CONTENT_ASSIST_BACKGROUNG = new RGB(150, 150, 0);
    
    
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
