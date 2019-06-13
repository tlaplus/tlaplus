/*******************************************************************************
 * Copyright (c) 2019 Microsoft Research. All rights reserved. 
 *
 * The MIT License (MIT)
 * 
 * Permission is hereby granted, free of charge, to any person obtaining a copy 
 * of this software and associated documentation files (the "Software"), to deal
 * in the Software without restriction, including without limitation the rights
 * to use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies
 * of the Software, and to permit persons to whom the Software is furnished to do
 * so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all
 * copies or substantial portions of the Software. 
 * 
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS
 * FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR
 * COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN
 * AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION
 * WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 *
 * Contributors:
 *   Simon Zambrowski - initial API and implementation
 ******************************************************************************/
package org.lamport.tla.toolbox.tool.tlc.output.data;

import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeSet;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import org.eclipse.core.resources.IFile;
import org.eclipse.jface.resource.JFaceResources;
import org.eclipse.jface.text.IRegion;
import org.eclipse.jface.text.TextPresentation;
import org.eclipse.swt.SWT;
import org.eclipse.swt.custom.StyleRange;
import org.eclipse.swt.graphics.Color;
import org.eclipse.swt.graphics.RGB;
import org.lamport.tla.toolbox.tool.tlc.output.data.Representation.Grouping;
import org.lamport.tla.toolbox.tool.tlc.ui.util.IModuleLocatable;

import tla2sany.st.Location;
import tlc2.TLCGlobals;

public class CoverageInformationItem implements IModuleLocatable
{
    private final static String MOD = " of module ";
    private final static String COLON = ": ";
    private final static String AT = "at ";

    private String locationString;
    protected Location location;
    protected String modelName;
    protected long count;
    protected long cost;
    protected int layer;

    // Siblings are CII instances shown at the same editor region/location. 
	private final Set<CoverageInformationItem> siblings = new HashSet<>();
    // Children are CII instances corresponding to nested expressions. 
    private final Set<CoverageInformationItem> childs = new HashSet<>();
    // The parent is the CII instance this CII is a nested expressions of. 
    private CoverageInformationItem parent;
    private ActionInformationItem root;
	
	private boolean active = false;

	protected final Map<Representation, Color[]> representations = new HashMap<>();
	
    /**
     * Creates an simple item storing information about a coverage at a certain location
     * @param location
     * @param count
     * @param modelName the name of the model for which this is coverage information
     * @param module
     */

    protected CoverageInformationItem(Location location, long count, String modelName, int layer)
    {
        this.location = location;
        this.locationString = this.location.toString();
        this.count = count;
        this.modelName = modelName;
        assert layer > ActionInformationItem.actionLayer;
        this.layer = layer;
    }
    
    public CoverageInformationItem(Location location, long count, long cost, String modelName, int layer) {
    	this(location, count, modelName, layer);
    	this.cost = cost;
    }

    public CoverageInformationItem() {
	}

	public final String getModule()
    {
        return locationString.substring(locationString.indexOf(MOD) + MOD.length());
    }

    public final String getLocation()
    {
        return locationString.substring(0, locationString.indexOf(MOD));
    }
    
    public final boolean isInFile(IFile f) {
    	final String nameWithoutSuffix = f.getName().replace(".tla", "");
		return nameWithoutSuffix.equalsIgnoreCase(location.source());
    }

    public boolean includeInCounts() {
    	return true;
    }
    
    public long getCount()
    {
        return count;
    }

    public final long getCost() {
    	return cost;
    }

	public long getCountAndCost() {
		return count + cost;
	}    
	/**
	 * If two CCI are co-located (overlapping, nested, ...), the layer indicates
	 * which one is considered more important.
	 */
	public int getLayer() {
		return layer;
	}

    /**
     * Parses the coverage information item from a string
     * @param outputMessage
     * @param modelName the name of the model for which this is coverage information
     * @return
     */
    public static CoverageInformationItem parse(String outputMessage, String modelName)
    {

        // "  line 84, col 32 to line 85, col 73 of module AtomicBakery: 1012492"
        outputMessage = outputMessage.trim();
        
        final int layer = outputMessage.lastIndexOf(TLCGlobals.coverageIndent) + 1;
        
        int index = outputMessage.indexOf(COLON);
        return new CoverageInformationItem(Location.parseLocation(outputMessage.substring(layer, index)), Long
                .parseLong(outputMessage.substring(index + COLON.length())), modelName, layer);
    }
    
    public static CoverageInformationItem parseCost(String outputMessage, String modelName)
    {

        // "  line 84, col 32 to line 85, col 73 of module AtomicBakery: 1012492"
        outputMessage = outputMessage.trim();
        
		final Pattern pattern = Pattern.compile("^(\\|*?)(line .*): ([0-9]+):([0-9]+)$");
		final Matcher matcher = pattern.matcher(outputMessage);
		matcher.find();

		final int layer = matcher.group(1).length();
		final Location location = Location.parseLocation(matcher.group(2));
		final long count = Long.parseLong(matcher.group(3));
		final long cost= Long.parseLong(matcher.group(4));
       
		return new CoverageInformationItem(location, count, cost, modelName, layer);
    }

    /**
     * Parses coverage timestamp from the string  
     * @param outputMessage
     * @return
     */
    public static String parseCoverageTimestamp(String outputMessage)
    {
        return outputMessage.substring(outputMessage.lastIndexOf(AT) + AT.length());
    }

    /**
     * The {@link Location} in the module.
     * @return
     */
    public Location getModuleLocation()
    {
        return location;
    }

    /**
     * The name of the model.
     * 
     * @return
     */
    public String getModelName()
    {
        return modelName;
    }
 
    CoverageInformationItem setRoot(ActionInformationItem root) {
    	this.root = root;
    	return this;
    }
    
	CoverageInformationItem setSiblings(List<CoverageInformationItem> siblings) {
		this.siblings.clear();
		this.siblings.addAll(siblings);
		this.siblings.remove(this);
		return this;
	}
	
	boolean hasSiblings() {
		return !this.siblings.isEmpty();
	}
    
	public long getTotalCount() {
		return siblings.stream().mapToLong(CoverageInformationItem::getCount).sum() + getCount();
	}

	public long getTotalCost() {
		return siblings.stream().mapToLong(CoverageInformationItem::getCost).sum() + getCost();
	}

	public long getTotalCountAndCost() {
		return getTotalCost() + getTotalCount();
	}

	Collection<CoverageInformationItem> getChildren() {
		return childs;
	}

	CoverageInformationItem addChild(CoverageInformationItem child) {
		assert child != this;
		this.childs.add(child);
		
		assert child.parent == null;
		child.parent = this;
		
		child.root = this.root;
		
		return this;
	}

	CoverageInformationItem setLayer(int i) {
        assert layer > ActionInformationItem.actionLayer;
		this.layer = i;
		return this;
	}

	private IRegion region;

	public IRegion getRegion() {
		return this.region;
	}

	CoverageInformationItem setRegion(IRegion locationToRegion) {
		this.region = locationToRegion;
		return this;
	}

	protected boolean isRoot() {
		return false;
	}
	
	public boolean isActive() {
		return active;
	}

	protected StyleRange addStlye(StyleRange sr) {
		// no-op
		return sr;
	}

	public void style(final TextPresentation textPresentation, final Representation rep) {
		if (isRoot()) {
			style(textPresentation, true, rep);
		} else {
			style(textPresentation, false, rep);
		}
	}
	
	protected void style(final TextPresentation textPresentation, final boolean merge, final Representation rep) {
		if (!isRoot()) {
			final StyleRange rs = new StyleRange();
			
			// IRegion
			rs.start = region.getOffset();
			rs.length = region.getLength();
			
			// Background Color
			rs.background = rep.getColor(this, merge ? Grouping.COMBINED : Grouping.INDIVIDUAL);
			
			// Zero Coverage
			if ((rep == Representation.STATES_DISTINCT || rep == Representation.STATES) && !(this instanceof ActionInformationItem)) {
				rs.background = JFaceResources.getColorRegistry().get(ModuleCoverageInformation.GRAY);
				rs.borderStyle = SWT.NONE;
				rs.borderColor = null;
			} else if (rep != Representation.COST && rep.getValue(this, Grouping.INDIVIDUAL) == 0L) {
				rs.background = null;
				rs.borderStyle = SWT.BORDER_SOLID;
				rs.borderColor = JFaceResources.getColorRegistry().get(ModuleCoverageInformation.RED);
			}
			
			// Track active subtree
			rs.data = this; //mergeStyleRange does not merge rs.data, thus track active instead.
			active = true;
			
			textPresentation.mergeStyleRange(addStlye(rs));
		}
		for (CoverageInformationItem child : childs) {
			child.style(textPresentation, merge, rep);
		}
	}
	
	public void style(final TextPresentation textPresentation, final Color c, final Representation rep) {
		if (!isRoot()) {
			final StyleRange rs = new StyleRange();
			rs.start = region.getOffset();
			rs.length = region.getLength();
			rs.background = c;
			if ((rep == Representation.STATES_DISTINCT || rep == Representation.STATES) && !(this instanceof ActionInformationItem)) {
				rs.background = JFaceResources.getColorRegistry().get(ModuleCoverageInformation.GRAY);
				rs.borderStyle = SWT.NONE;
				rs.borderColor = null;
			} else if (rep != Representation.COST && rep.getValue(this, Grouping.INDIVIDUAL) == 0L) {
				rs.background = null;
				rs.borderStyle = SWT.BORDER_SOLID;
				rs.borderColor = JFaceResources.getColorRegistry().get(ModuleCoverageInformation.RED);
			}
			active = false;
			textPresentation.replaceStyleRange(addStlye(rs));
		}
		for (CoverageInformationItem child : childs) {
			child.style(textPresentation, c, rep);
		}
	}

	Color colorItem(TreeSet<Long> counts, final Representation rep) {
		int hue = ModuleCoverageInformation.getHue(rep.getValue(this, Grouping.INDIVIDUAL), counts);
		String key = Integer.toString(hue);
		if (!JFaceResources.getColorRegistry().hasValueFor(key)) {
			JFaceResources.getColorRegistry().put(key, new RGB(hue, .25f, 1f));
		}
		final Color color = JFaceResources.getColorRegistry().get(key);

		Color[] colors = new Color[2];
		colors[Grouping.INDIVIDUAL.ordinal()] = color;
		colors[Grouping.COMBINED.ordinal()] = color;
		representations.put(rep, colors);
		
		if (hasSiblings()) {
			// Aggregated color (might be identical to color).
			hue = ModuleCoverageInformation.getHue(rep.getValue(this, Grouping.COMBINED), counts);
			key = Integer.toString(hue);
			if (!JFaceResources.getColorRegistry().hasValueFor(key)) {
				JFaceResources.getColorRegistry().put(key, new RGB(hue, .25f, 1f));
			}
			Color aggregate = JFaceResources.getColorRegistry().get(key);

			colors = new Color[2];
			colors[Grouping.INDIVIDUAL.ordinal()] = color;
			colors[Grouping.COMBINED.ordinal()] = aggregate;
			representations.put(rep, colors);
			return aggregate;
		}
		
		return color;
	}

	public CoverageInformationItem getParent() {
		return parent;
	}
	
	public ActionInformationItem getRoot() {
		return root;
	}

	public boolean hasLocation() {
		return this.location != null;
	}

	public TreeSet<CoverageInformationItem> getLegend(final Representation rep) {
		return collectActive(new TreeSet<CoverageInformationItem>(rep.getComparator(Grouping.INDIVIDUAL)));
	}
	
	protected TreeSet<CoverageInformationItem> collectActive(final TreeSet<CoverageInformationItem> legend) {
		legend.add(this);
		for (CoverageInformationItem child : childs) {
			if (child.isActive()) {
				child.collectActive(legend);
			}
		}
		return legend;
	}
}
