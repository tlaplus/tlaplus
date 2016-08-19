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
	
	public static final String TLAPLUS_FONT_NAME = "IsabelleText";
	
	public static void loadTLAPlusFont() {
		Display display = Display.getCurrent();

	    // Check if any of the fonts already exist in the system
	    FontData[] fonts = display.getFontList(null, true);
	    boolean hasPlain = false;
	    boolean hasBold = false;
	    for (FontData f : fonts) {
	    	if (f.getName().equals(TLAPLUS_FONT_NAME)) {
	    		if (f.getStyle() == SWT.NONE)
	    			hasPlain = true;
	    		if (f.getStyle() == SWT.BOLD)
	    			hasBold = true;
	    	}
	    }
	    
	    // load fonts
	    if (!hasPlain) 
	    	loadFont(display, TLAPLUS_FONT_NAME + ".ttf");
	    if (!hasBold) 
	    	loadFont(display, TLAPLUS_FONT_NAME + "Bold.ttf");
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
