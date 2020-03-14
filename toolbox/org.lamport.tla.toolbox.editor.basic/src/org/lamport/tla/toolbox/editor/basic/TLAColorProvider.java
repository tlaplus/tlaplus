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
 */
public class TLAColorProvider {
	public static final String CONTENT_ASSIST_BACKGROUND_KEY = "content_assist.background";
	public static final String DEFAULT_TEXT_KEY = "all.default";
	public static final String PCAL_KEYWORD_KEY = "pcal.keyword";
	public static final String TLA_KEYWORD_KEY = "tla.keyword";
	public static final String TLA_MULTI_LINE_COMMENT_KEY = "tla.comment.multiline";
	public static final String TLA_SINGLE_LINE_COMMENT_KEY = "tla.comment.single";
	public static final String TLA_VALUE_KEY = "tla.value";
	
	
	/** Colors for a light theme **/
    private static final RGB CONTENT_ASSIST_BACKGROUND_RGB = new RGB(150, 150, 0);
    private static final RGB DEFAULT_RGB = new RGB(0, 0, 0);
    private static final RGB PCAL_KEYWORD_RGB = new RGB(175, 40, 10);
    private static final RGB TLA_KEYWORD_RGB = new RGB(128, 0, 128); 
	private static final RGB TLA_MULTI_LINE_COMMENT_RGB = new RGB(64, 64, 255);
    private static final RGB TLA_SINGLE_LINE_COMMENT_RGB = new RGB(0, 128, 64);
    private static final RGB TLA_VALUE_RGB = new RGB(0, 0, 255); 

	/** Colors for a dark theme **/
    private static final RGB CONTENT_ASSIST_BACKGROUND_DARK_RGB = new RGB(150, 150, 0);
    private static final RGB DEFAULT_DARK_RGB = new RGB(3, 167, 226);
    private static final RGB PCAL_KEYWORD_DARK_RGB = new RGB(245, 115, 67);
    private static final RGB TLA_KEYWORD_DARK_RGB = new RGB(172, 226, 156); 
	private static final RGB TLA_MULTI_LINE_COMMENT_DARK_RGB = new RGB(245, 235, 191);
    private static final RGB TLA_SINGLE_LINE_COMMENT_DARK_RGB = new RGB(0, 207, 104);
    private static final RGB TLA_VALUE_DARK_RGB = new RGB(226, 200, 99); 
    
    private static final Map<String, RGB> COLOR_KEY_RGB_MAP;
    
    static {
    	COLOR_KEY_RGB_MAP = new HashMap<>();
    	
    	COLOR_KEY_RGB_MAP.put(getThemeContextualizedKey(CONTENT_ASSIST_BACKGROUND_KEY, false), CONTENT_ASSIST_BACKGROUND_RGB);
    	COLOR_KEY_RGB_MAP.put(getThemeContextualizedKey(DEFAULT_TEXT_KEY, false), DEFAULT_RGB);
    	COLOR_KEY_RGB_MAP.put(getThemeContextualizedKey(PCAL_KEYWORD_KEY, false), PCAL_KEYWORD_RGB);
    	COLOR_KEY_RGB_MAP.put(getThemeContextualizedKey(TLA_KEYWORD_KEY, false), TLA_KEYWORD_RGB);
    	COLOR_KEY_RGB_MAP.put(getThemeContextualizedKey(TLA_MULTI_LINE_COMMENT_KEY, false), TLA_MULTI_LINE_COMMENT_RGB);
    	COLOR_KEY_RGB_MAP.put(getThemeContextualizedKey(TLA_SINGLE_LINE_COMMENT_KEY, false), TLA_SINGLE_LINE_COMMENT_RGB);
    	COLOR_KEY_RGB_MAP.put(getThemeContextualizedKey(TLA_VALUE_KEY, false), TLA_VALUE_RGB);
    	
    	COLOR_KEY_RGB_MAP.put(getThemeContextualizedKey(CONTENT_ASSIST_BACKGROUND_KEY, true), CONTENT_ASSIST_BACKGROUND_DARK_RGB);
    	COLOR_KEY_RGB_MAP.put(getThemeContextualizedKey(DEFAULT_TEXT_KEY, true), DEFAULT_DARK_RGB);
    	COLOR_KEY_RGB_MAP.put(getThemeContextualizedKey(PCAL_KEYWORD_KEY, true), PCAL_KEYWORD_DARK_RGB);
    	COLOR_KEY_RGB_MAP.put(getThemeContextualizedKey(TLA_KEYWORD_KEY, true), TLA_KEYWORD_DARK_RGB);
    	COLOR_KEY_RGB_MAP.put(getThemeContextualizedKey(TLA_MULTI_LINE_COMMENT_KEY, true), TLA_MULTI_LINE_COMMENT_DARK_RGB);
    	COLOR_KEY_RGB_MAP.put(getThemeContextualizedKey(TLA_SINGLE_LINE_COMMENT_KEY, true), TLA_SINGLE_LINE_COMMENT_DARK_RGB);
    	COLOR_KEY_RGB_MAP.put(getThemeContextualizedKey(TLA_VALUE_KEY, true), TLA_VALUE_DARK_RGB);
    }
    
    private static String getThemeContextualizedKey(final String key, final boolean themeIsDark) {
    	return key + "_" + (themeIsDark ? "dunkel" : "hell");
    }
    
    
    private final Map<String, Color> keyColorMap;
    
    public TLAColorProvider() {
    	keyColorMap = new HashMap<>();
    }

    /**
     * Release all of the color resources held onto by the receiver.
     */
	public void dispose() {
		final Iterator<Color> e = keyColorMap.values().iterator();
        while (e.hasNext()) {
            e.next().dispose();
        }
    }
    
    /**
     * Return the color that is stored in the color table under, referenced by the supplied key, and the current
     * Toolbox theme (dark v. light.)
     * 
     * @param colorKey one of the public static String keys defined in this class
     * @return the color, adjusted for current theme, or null if the key provided is unknown to this class
     */
	public Color getColor(final String colorKey) {
		final String key = getThemeContextualizedKey(colorKey, TLAEditorActivator.getDefault().isCurrentThemeDark());
		Color color = keyColorMap.get(key);
		if (color == null) {
			final RGB rgb = COLOR_KEY_RGB_MAP.get(key);
			if (rgb != null) {
				color = new Color(Display.getCurrent(), rgb);
				keyColorMap.put(key, color);
			}
		}
		return color;
	}
}
