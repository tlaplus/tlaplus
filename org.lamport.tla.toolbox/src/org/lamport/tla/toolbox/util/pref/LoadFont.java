package org.lamport.tla.toolbox.util.pref;

import java.io.IOException;
import java.net.URL;

import org.eclipse.core.runtime.FileLocator;
import org.eclipse.core.runtime.Path;
import org.eclipse.swt.SWT;
import org.eclipse.swt.graphics.FontData;
import org.eclipse.swt.widgets.Display;
import org.lamport.tla.toolbox.Activator;

/**
 * Loads bundled fonts
 * 
 * @author pron
 */
public final class LoadFont {
	private LoadFont() {}
	
	// DejaVu License: http://dejavu-fonts.org/wiki/License
	public static final String TLAPLUS_FONT_NAME = "DejaVuSansMono";
	public static final String BOLD = "-Bold";
	public static final String ITALIC = "-Oblique";
	public static final String BOLD_ITALIC = "-BoldOblique";
	public static final String TYPE = "ttf";
	
	// How to set as default?
	// Answers may lie in:
	//     org.lamport.tla.toolbox.util.pref.PreferenceInitializer
	//     org.eclipse.ui.internal.themes.ColorsAndFontsPreferencePage
	//     org.eclipse.jface.resource.FontRegistry
	//     org.eclipse.ui.internal.themes.FontDefinition
	
	public static void loadTLAPlusFont() {
		final Display display = Display.getCurrent();

	    // Check if any of the fonts already exist in the system
	    final FontData[] fonts = display.getFontList(null, true);
	    boolean hasPlain = false;
	    boolean hasBold = false;
	    boolean hasItalic = false;
	    boolean hasBoldItalic = false;
	    for (FontData f : fonts) {
	    	if (f.getName().equals(TLAPLUS_FONT_NAME)) {
	    		if (f.getStyle() == SWT.NORMAL)
	    			hasPlain = true;
	    		if (f.getStyle() == SWT.BOLD)
	    			hasBold = true;
	    		if (f.getStyle() == SWT.ITALIC)
	    			hasItalic = true;
	    		if (f.getStyle() == (SWT.ITALIC | SWT.BOLD))
	    			hasBoldItalic = true;
	    	}
	    }
	    
	    // load fonts
	    if (!hasPlain) 
	    	loadFont(display, TLAPLUS_FONT_NAME + "." + TYPE);
	    if (BOLD != null && !hasBold) 
	    	loadFont(display, TLAPLUS_FONT_NAME + BOLD + "." + TYPE);
	    if (ITALIC != null && !hasItalic) 
	    	loadFont(display, TLAPLUS_FONT_NAME + ITALIC + "." + TYPE);
	    if (BOLD_ITALIC != null && !hasBoldItalic) 
	    	loadFont(display, TLAPLUS_FONT_NAME + BOLD_ITALIC + "." + TYPE);
	}
	
	private static void loadFont(Display display, String fileName) {
		// resolve font URL within the plug-in bundle (note, the font may be inside a JAR here)
	    final URL fontUrl = fontBundleUrl(fileName);
	    if (fontUrl == null) {
	    	Activator.getDefault().logWarning("Font " + fileName + " cannot be found in the plug-in.");
	    	return;
	    }

	    try {
	    	final URL fontFileURL = FileLocator.toFileURL(fontUrl);
	    	final String fontFilePath = new Path(fontFileURL.getPath()).toOSString();
	    	
	    	try {
	    		display.loadFont(fontFilePath);
	    		Activator.getDefault().logError("Font " + fileName + " has been loaded successfully from file " + fontFilePath);
	    	} catch  (Exception e) {
	    		Activator.getDefault().logError("Font " + fileName + " cannot be loaded from file " + fontFilePath);
	    	}
	    } catch (IOException e) {
	    	Activator.getDefault().logError("Font " + fileName + " cannot be loaded: " + e.getMessage());
	    }
	}
	
	private static URL fontBundleUrl(String fileName) {
		return Activator.getDefault().getBundle().getEntry("fonts/" + fileName);
	}
}
