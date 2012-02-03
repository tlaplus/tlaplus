/*******************************************************************************
 * Copyright (c) 2007, 2009, 2012 IBM Corporation and others.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *     IBM Corporation - initial API and implementation
 *     Microsoft Corp. - Adoptions for TLA+ Toolbox
 *******************************************************************************/
package org.lamport.tla.toolbox.ui.preference;

import org.eclipse.core.runtime.Assert;
import org.eclipse.core.runtime.IAdaptable;
import org.eclipse.jface.dialogs.IDialogConstants;
import org.eclipse.jface.layout.PixelConverter;
import org.eclipse.jface.resource.JFaceResources;
import org.eclipse.swt.SWT;
import org.eclipse.swt.graphics.Font;
import org.eclipse.swt.graphics.Image;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Button;
import org.eclipse.swt.widgets.Combo;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Group;
import org.eclipse.swt.widgets.Label;
import org.eclipse.swt.widgets.Layout;
import org.eclipse.swt.widgets.Link;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.swt.widgets.Text;
import org.eclipse.ui.dialogs.PreferencesUtil;
import org.eclipse.ui.forms.widgets.ExpandableComposite;
import org.eclipse.ui.forms.widgets.SharedScrolledComposite;

public class SWTFactory {
	
	/**
	 * Returns a width hint for a button control.
	 */
	public static int getButtonWidthHint(Button button) {
		button.setFont(JFaceResources.getDialogFont());
		PixelConverter converter= new PixelConverter(button);
		int widthHint = converter.convertHorizontalDLUsToPixels(IDialogConstants.BUTTON_WIDTH);
		return Math.max(widthHint, button.computeSize(SWT.DEFAULT, SWT.DEFAULT, true).x);
	}
	
	/**
	 * Sets width and height hint for the button control.
	 * <b>Note:</b> This is a NOP if the button's layout data is not
	 * an instance of <code>GridData</code>.
	 * 
	 * @param	the button for which to set the dimension hint
	 */		
	public static void setButtonDimensionHint(Button button) {
		Assert.isNotNull(button);
		Object gd = button.getLayoutData();
		if (gd instanceof GridData) {
			((GridData)gd).widthHint = getButtonWidthHint(button);
			((GridData)gd).horizontalAlignment = GridData.FILL;
		}
	}
	
	/**
	 * Creates a check box button using the parents' font
	 * 
	 * @param parent the parent to add the button to
	 * @param label the label for the button
	 * @param image the image for the button 
	 * @param checked the initial checked state of the button
	 * @param hspan the horizontal span to take up in the parent composite
	 * @return a new checked button set to the initial checked state
	 */
	public static Button createCheckButton(Composite parent, String label, Image image, boolean checked, int hspan) {
		Button button = new Button(parent, SWT.CHECK);
		button.setFont(parent.getFont());
		button.setSelection(checked);
		if(image != null) {
			button.setImage(image);
		}
		if(label != null) {
			button.setText(label);
		}
		GridData gd = new GridData();
		gd.horizontalSpan = hspan;
		button.setLayoutData(gd);
		return button;
	}
	
	/**
	 * Creates and returns a new push button with the given
	 * label and/or image.
	 * 
	 * @param parent parent control
	 * @param label button label or <code>null</code>
	 * @param image image of <code>null</code>
	 * @return a new push button
	 */
	public static Button createPushButton(Composite parent, String label, Image image) {
		Button button = new Button(parent, SWT.PUSH);
		button.setFont(parent.getFont());
		if (image != null) {
			button.setImage(image);
		}
		if (label != null) {
			button.setText(label);
		}
		GridData gd = new GridData();
		button.setLayoutData(gd);
		SWTFactory.setButtonDimensionHint(button);
		return button;	
	}	

	/**
	 * Creates and returns a new push button with the given
	 * label and/or image.
	 * 
	 * @param parent parent control
	 * @param label button label or <code>null</code>
	 * @param image image of <code>null</code>
	 * @param fill the alignment for the new button
	 * @return a new push button
	 */
	public static Button createPushButton(Composite parent, String label, Image image, int fill) {
		Button button = new Button(parent, SWT.PUSH);
		button.setFont(parent.getFont());
		if (image != null) {
			button.setImage(image);
		}
		if (label != null) {
			button.setText(label);
		}
		GridData gd = new GridData(fill);
		button.setLayoutData(gd);
		SWTFactory.setButtonDimensionHint(button);
		return button;	
	}	
	
	/**
	 * Creates and returns a new radio button with the given
	 * label.
	 * 
	 * @param parent parent control
	 * @param label button label or <code>null</code>
	 * @return a new radio button
	 */
	public static Button createRadioButton(Composite parent, String label) {
		Button button = new Button(parent, SWT.RADIO);
		button.setFont(parent.getFont());
		if (label != null) {
			button.setText(label);
		}
		GridData gd = new GridData();
		button.setLayoutData(gd);
		SWTFactory.setButtonDimensionHint(button);
		return button;	
	}	
	
	/**
	 * Creates a new label widget
	 * 
	 * @param parent the parent composite to add this label widget to
	 * @param text the text for the label
	 * @param hspan the horizontal span to take up in the parent composite
	 * @return the new label
	 */
	public static Label createLabel(Composite parent, String text, int hspan) {
		Label l = new Label(parent, SWT.NONE);
		l.setFont(parent.getFont());
		if(text != null) {
			l.setText(text);
		}
		GridData gd = new GridData(GridData.FILL_HORIZONTAL);
		gd.horizontalSpan = hspan;
		gd.grabExcessHorizontalSpace = false;
		l.setLayoutData(gd);
		return l;
	}
	
	/**
	 * Creates a new label widget
	 * 
	 * @param parent the parent composite to add this label widget to
	 * @param text the text for the label
	 * @param font the font for the label
	 * @param hspan the horizontal span to take up in the parent composite
	 * @return the new label
	 */
	public static Label createLabel(Composite parent, String text, Font font, int hspan) {
		Label l = new Label(parent, SWT.NONE);
		l.setFont(font);
		if(text != null) {
			l.setText(text);
		}
		GridData gd = new GridData(GridData.FILL_HORIZONTAL);
		gd.horizontalSpan = hspan;
		l.setLayoutData(gd);
		return l;
	}
	
	/**
	 * Creates a new link widget
	 * 
	 * @param parent the parent composite to add this label widget to
	 * @param text the text for the label
	 * @param font the font for the label
	 * @param hspan the horizontal span to take up in the parent composite
	 * @return the new label
	 */
	public static Link createLink(Composite parent, String text, Font font, int hspan) {
		Link l = new Link(parent, SWT.UNDERLINE_LINK);
		l.setFont(font);
		l.setText(text);
		GridData gd = new GridData(GridData.BEGINNING, GridData.VERTICAL_ALIGN_CENTER, true, false, hspan, 1);
		l.setLayoutData(gd);
		return l;
	}
	
	public static Link createLink(Composite parent, String text, Font font, int hspan, int fill) {
		Link l = new Link(parent, SWT.UNDERLINE_LINK);
		l.setFont(font);
		l.setText(text);
		GridData gd = new GridData(fill);
		gd.horizontalSpan = hspan;
		l.setLayoutData(gd);
		return l;
	}

	
	/**
	 * Creates a wrapping label
	 * 
	 * @param parent the parent composite to add this label to
	 * @param text the text to be displayed in the label
	 * @param hspan the horizontal span that label should take up in the parent composite
	 * @param wrapwidth the width hint that the label should wrap at
	 * @return a new label that wraps at a specified width
	 */
	public static Label createWrapLabel(Composite parent, String text, int hspan, int wrapwidth) {
		Label l = new Label(parent, SWT.NONE | SWT.WRAP);
		l.setFont(parent.getFont());
		if(text != null) {
			l.setText(text);
		}
		GridData gd = new GridData(GridData.FILL_HORIZONTAL);
		gd.horizontalSpan = hspan;
		gd.widthHint = wrapwidth;
		l.setLayoutData(gd);
		return l;
	}
	
	/**
	 * Creates a wrapping label
	 * 
	 * @param parent the parent composite to add this label to
	 * @param text the text to be displayed in the label
	 * @param hspan the horizontal span that label should take up in the parent composite
	 * @return a new label that wraps at a specified width
	 */
	public static Label createWrapLabel(Composite parent, String text, int hspan) {
		Label l = new Label(parent, SWT.NONE | SWT.WRAP);
		l.setFont(parent.getFont());
		if(text != null) {
			l.setText(text);
		}
		GridData gd = new GridData(GridData.BEGINNING);
		gd.horizontalSpan = hspan;
		l.setLayoutData(gd);
		return l;
	}
	
	/**
	 * Creates a scrolled composite 
	 * 
	 * @param parent the parent to add to
	 * @param columns the number of columns for the composite
	 * @param hspan the horizontal span to take up in the parent
	 * @param marginwidth the width of the margins
	 * @param marginheight the height of the margins
	 * @return a new scrolled composite
	 */
	public static SharedScrolledComposite createScrolledComposite(Composite parent, int columns, int hspan, int marginwidth, int marginheight) {
		SharedScrolledComposite comp = new SharedScrolledComposite(parent, SWT.V_SCROLL | SWT.H_SCROLL) {};
		GridLayout layout = new GridLayout(columns, false);
		layout.marginHeight = marginheight;
		layout.marginWidth = marginwidth;
		comp.setLayout(layout);
		GridData gd = new GridData(GridData.FILL_BOTH);
		gd.horizontalSpan = hspan;
		comp.setLayoutData(gd);
		comp.setExpandHorizontal(true);
		comp.setExpandVertical(true);
		return comp;
	}
	
	/**
	 * Creates an ExpandibleComposite widget
	 * 
	 * @param parent the parent to add this widget to
	 * @param style the style for ExpandibleComposite expanding handle, and layout
	 * @param label the label for the widget
	 * @param hspan how many columns to span in the parent
	 * @param fill the fill style for the widget
	 * Can be one of <code>GridData.FILL_HORIZONAL</code>, <code>GridData.FILL_BOTH</code> or <code>GridData.FILL_VERTICAL</code>
	 * @return a new ExpandibleComposite widget
	 */
	public static ExpandableComposite createExpandibleComposite(Composite parent, String label, int hspan, int fill) {
		ExpandableComposite ex = new ExpandableComposite(parent, SWT.NONE, ExpandableComposite.TWISTIE | ExpandableComposite.CLIENT_INDENT);
		ex.setText(label);
		ex.setFont(JFaceResources.getFontRegistry().getBold(JFaceResources.DIALOG_FONT));
		GridData gd = new GridData(fill);
		gd.horizontalSpan = hspan;
		gd.grabExcessHorizontalSpace = true;
		ex.setLayoutData(gd);
		return ex;
	}
	
	/**
	 * Creates a new text widget 
	 * 
	 * @param parent the parent composite to add this text widget to
	 * @param hspan the horizontal span to take up on the parent composite
	 * @return the new text widget
	 * 
	 */
	public static Text createSingleText(Composite parent, int hspan) {
    	Text t = new Text(parent, SWT.SINGLE | SWT.BORDER);
    	t.setFont(parent.getFont());
    	GridData gd = new GridData(GridData.FILL_HORIZONTAL);
    	gd.horizontalSpan = hspan;
    	t.setLayoutData(gd);
    	return t;
    }
	
	/**
	 * Creates a new text widget 
	 * 
	 * @param parent the parent composite to add this text widget to
	 * @param style the style bits for the text widget
	 * @param hspan the horizontal span to take up on the parent composite
	 * @param fill the fill for the grid layout
	 * @return the new text widget
	 */
	public static Text createText(Composite parent, int style, int hspan, int fill) {
    	Text t = new Text(parent, style);
    	t.setFont(parent.getFont());
    	GridData gd = new GridData(fill);
    	gd.horizontalSpan = hspan;
    	t.setLayoutData(gd);
    	return t;
    }
	
	/**
	 * Creates a new text widget 
	 * 
	 * @param parent the parent composite to add this text widget to
	 * @param style the style bits for the text widget
	 * @param hspan the horizontal span to take up on the parent composite
	 * @return the new text widget
	 */
	public static Text createText(Composite parent, int style, int hspan) {
    	Text t = new Text(parent, style);
    	t.setFont(parent.getFont());
    	GridData gd = new GridData(GridData.FILL_HORIZONTAL);
    	gd.horizontalSpan = hspan;
    	t.setLayoutData(gd);
    	return t;
    }
	
	/**
	 * Creates a new text widget 
	 * 
	 * @param parent the parent composite to add this text widget to
	 * @param style the style bits for the text widget
	 * @param hspan the horizontal span to take up on the parent composite
	 * @param width the desired width of the text widget
	 * @param height the desired height of the text widget
	 * @param fill the fill style for the widget
	 * @return the new text widget
	 */
	public static Text createText(Composite parent, int style, int hspan, int width, int height, int fill) {
    	Text t = new Text(parent, style);
    	t.setFont(parent.getFont());
    	GridData gd = new GridData(fill);
    	gd.horizontalSpan = hspan;
    	gd.widthHint = width;
    	gd.heightHint = height;
    	t.setLayoutData(gd);
    	return t;
    }
	
	/**
	 * Creates a Group widget
	 * 
	 * @param parent the parent composite to add this group to
	 * @param text the text for the heading of the group
	 * @param columns the number of columns within the group
	 * @param hspan the horizontal span the group should take up on the parent
	 * @param fill the style for how this composite should fill into its parent
	 * @return the new group
	 */
	public static Group createGroup(Composite parent, String text, int columns, int hspan, int fill) {
    	Group g = new Group(parent, SWT.NONE);
    	g.setLayout(new GridLayout(columns, false));
    	g.setText(text);
    	g.setFont(parent.getFont());
    	GridData gd = new GridData(fill);
		gd.horizontalSpan = hspan;
    	g.setLayoutData(gd);
    	return g;
    }
	
	/**
	 * Creates a composite that uses the parent's font and has a grid layout
	 * 
	 * @param parent the parent to add the composite to
	 * @param columns the number of columns the composite should have
	 * @param hspan the horizontal span the new composite should take up in the parent
	 * @param fill the fill style of the composite {@link GridData}
	 * @return a new composite with a grid layout
	 */
	public static Composite createComposite(Composite parent, int columns, int hspan, int fill) {
		Composite g = new Composite(parent, SWT.NONE);
    	g.setLayout(new GridLayout(columns, false));
    	g.setFont(parent.getFont());
    	GridData gd = new GridData(fill);
		gd.horizontalSpan = hspan;
		gd.grabExcessHorizontalSpace = true;
    	g.setLayoutData(gd);
    	return g;
	}
	
	/**
	 * Creates a composite that uses the parent's font and has a grid layout
	 * 
	 * @param parent the parent to add the composite to
	 * @param font the font to use for this composite
	 * @param columns the number of columns the composite should have
	 * @param hspan the horizontal span the new composite should take up in the parent
	 * @param fill the fill style of the composite {@link GridData}
	 * @return a new composite with a grid layout
	 */
	public static Composite createComposite(Composite parent, Font font, int columns, int hspan, int fill) {
		Composite g = new Composite(parent, SWT.NONE);
    	g.setLayout(new GridLayout(columns, false));
    	g.setFont(font);
    	GridData gd = new GridData(fill);
		gd.horizontalSpan = hspan;
		gd.grabExcessHorizontalSpace = true;
    	g.setLayoutData(gd);
    	return g;
	}
	
	/**
	 * Creates a composite that uses the parent's font and has a grid layout
	 * 
	 * @param parent the parent to add the composite to
	 * @param columns the number of columns the composite should have
	 * @param hspan the horizontal span the new composite should take up in the parent
	 * @param fill the fill style of the composite {@link GridData}
	 * @param style the style of the composite
	 * @return a new composite with a grid layout
	 */
	public static Composite createComposite(Composite parent, int columns, int hspan, int fill, int style) {
		Composite g = new Composite(parent, style);
    	g.setLayout(new GridLayout(columns, false));
    	g.setFont(parent.getFont());
    	GridData gd = new GridData(fill);
		gd.horizontalSpan = hspan;
		gd.grabExcessHorizontalSpace = true;
    	g.setLayoutData(gd);
    	return g;
	}
	
	/**
	 * Creates a vertical spacer for separating components. If applied to a 
	 * <code>GridLayout</code>, this method will automatically span all of the columns of the parent
	 * to make vertical space
	 * 
	 * @param parent the parent composite to add this spacer to
	 * @param numlines the number of vertical lines to make as space
	 */
	public static void createVerticalSpacer(Composite parent, int numlines) {
		Label lbl = new Label(parent, SWT.NONE);
		GridData gd = new GridData(GridData.FILL_HORIZONTAL);
		Layout layout = parent.getLayout();
		if(layout instanceof GridLayout) {
			gd.horizontalSpan = ((GridLayout)parent.getLayout()).numColumns;
		}
		gd.heightHint = numlines;
		lbl.setLayoutData(gd);
	}
	
	/**
	 * Creates a horizontal spacer for separating components
	 * 
	 * @param comp
	 * @param numlines
	 */
	public static void createHorizontalSpacer(Composite comp, int numlines) {
		Label lbl = new Label(comp, SWT.NONE);
		GridData gd = new GridData(GridData.FILL_HORIZONTAL);
		gd.horizontalSpan = numlines;
		lbl.setLayoutData(gd);
	}
	
	/**
	 * Creates a Composite widget
	 * 
	 * @param parent the parent composite to add this composite to
	 * @param columns the number of columns within the composite
	 * @param hspan the horizontal span the composite should take up on the parent
	 * @param fill the style for how this composite should fill into its parent
	 * @param marginwidth the width of the margin to place on the sides of the composite (default is 5, specified by GridLayout)
	 * @param marginheight the height of the margin to place o the top and bottom of the composite
	 * @return the new composite
	 */
	public static Composite createComposite(Composite parent, int columns, int hspan, int fill, int marginwidth, int marginheight) {
		Composite g = new Composite(parent, SWT.NONE);
		GridLayout layout = new GridLayout(columns, false);
		layout.marginWidth = marginwidth;
		layout.marginHeight = marginheight;
		g.setLayout(layout);
		g.setFont(parent.getFont());
		GridData gd = new GridData(fill);
		gd.horizontalSpan = hspan;
		g.setLayoutData(gd);
		return g;
	}
	
	/**
	 * This method is used to make a combo box
	 * 
	 * @param parent the parent composite to add the new combo to
	 * @param style the style for the Combo
	 * @param hspan the horizontal span to take up on the parent composite
	 * @param fill how the combo will fill into the composite
	 * Can be one of <code>GridData.FILL_HORIZONAL</code>, <code>GridData.FILL_BOTH</code> or <code>GridData.FILL_VERTICAL</code>
	 * @param items the item to put into the combo
	 * @return a new Combo instance
	 */
	public static Combo createCombo(Composite parent, int style, int hspan, int fill, String[] items) {
		Combo c = new Combo(parent, style);
		c.setFont(parent.getFont());
		GridData gd = new GridData(fill);
		gd.horizontalSpan = hspan;
		c.setLayoutData(gd);
		if (items != null){
			c.setItems(items);
		}
		c.select(0);
		return c;
	}
	
	/**
	 * This method is used to make a combo box with a default fill style of GridData.FILL_HORIZONTAL
	 * 
	 * @param parent the parent composite to add the new combo to
	 * @param style the style for the Combo
	 * @param hspan the horizontal span to take up on the parent composite
	 * @param items the item to put into the combo
	 * @return a new Combo instance
	 */
	public static Combo createCombo(Composite parent, int style, int hspan, String[] items) {
		Combo c = new Combo(parent, style);
		c.setFont(parent.getFont());
		GridData gd = new GridData(GridData.FILL_HORIZONTAL);
		gd.horizontalSpan = hspan;
		c.setLayoutData(gd);
		if (items != null){
			c.setItems(items);
		}
		c.select(0);
		return c;
	}
	
	/**
	 * This method allows us to open the preference dialog on the specific page, in this case the perspective page
	 * 
	 * @param shell
	 * @param id the id of preference page to show
	 * @param page the actual page to show
	 */
	public static void showPreferencePage(Shell shell, String id, Object data) {
		PreferencesUtil.createPreferenceDialogOn(shell, id, new String[] {id}, data).open();
	}
	
	/**
	 * This method allows us to open a property page in the default platform dialog
	 * @param shell
	 * @param id
	 * @param element
	 * @param data
	 */
	public static void showPropertiesDialog(Shell shell, String id, IAdaptable element, Object data) {
		PreferencesUtil.createPropertyDialogOn(shell, element, id, new String[] {id}, data).open();
	}

}
