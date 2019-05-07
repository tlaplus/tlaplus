package org.lamport.tla.toolbox.tool.tlc.ui.util;

import org.eclipse.swt.SWT;
import org.eclipse.swt.custom.SashForm;
import org.eclipse.swt.graphics.Point;
import org.eclipse.swt.widgets.Control;
import org.eclipse.ui.forms.events.ExpansionEvent;
import org.eclipse.ui.forms.events.IExpansionListener;
import org.eclipse.ui.forms.widgets.Section;

/**
 * There are a few scenarios in which we want the collapse of a section to force a neighboring component to expand into
 * 	that space. This class begins to address that.
 * 
 * <b>Note</b> this class presently only handles N-child SashForms and is only coded to handle those with vertical
 * 	layout.
 */
public class ExpandableSpaceReclaimer implements IExpansionListener {
	private static final double MINIMUM_SASH_PART_PERCENTAGE = 0.1;
	
	
	private final Section m_section;
	private final SashForm m_sashForm;
	
	private final int m_sectionIndex;
	private final int m_otherChildrenCount;
	
	private Point m_lastSectionSizeOnCollapse;
	
	/**
	 * An instance should be constructed only after all children have been added to the sash form.
	 * 
	 * @param s the section which we will listen for collapse and expansion on
	 * @param sf the sash form in which the section sits
	 * @throws IllegalArgumentException if the section is not one of the sash form's children
	 */
	public ExpandableSpaceReclaimer(final Section s, final SashForm sf) {
		m_section = s;
		m_sashForm = sf;
		
		final Control[] children = m_sashForm.getChildren();
		int index = -1;
		for (int i = 0; i < children.length; i++) {
			if (s == children[i]) {
				index = i;
				
				break;
			}
		}
		
		if (index == -1) {
			throw new IllegalArgumentException("Section could not be found in the sash form.");
		}
		
		m_sectionIndex = index;
		m_otherChildrenCount = children.length - 1;
		m_section.addExpansionListener(this);
		
		m_lastSectionSizeOnCollapse = null;
	}
	
	@Override
	public void expansionStateChanging(final ExpansionEvent ee) {
		if (!ee.getState()) {
			m_lastSectionSizeOnCollapse = m_section.getSize();
		}
	}

	@Override
	public void expansionStateChanged(final ExpansionEvent ee) {
		final Point sashFormSize = m_sashForm.getSize();
		final int totalSashConsumption = m_sashForm.getSashWidth() * m_otherChildrenCount;
		
		if (ee.getState()) { // => now expanded
			final Point desiredSize = (m_lastSectionSizeOnCollapse != null)
											? m_lastSectionSizeOnCollapse
											: m_section.computeSize(SWT.DEFAULT, SWT.DEFAULT, false);
			
			if (m_sashForm.getOrientation() == SWT.VERTICAL) {
				final int minimumHeight = (int)(MINIMUM_SASH_PART_PERCENTAGE * (double)sashFormSize.y);
				final int totalMinimumHeight = (minimumHeight  * m_otherChildrenCount) + totalSashConsumption;
				final double usableSashFormHeight = sashFormSize.y - totalSashConsumption;
				
				if (desiredSize.y < (sashFormSize.y - totalMinimumHeight)) {
					final double remainingHeight = usableSashFormHeight - desiredSize.y;
					final int[] weights = m_sashForm.getWeights();
					double sumOfOtherWeights = 0;
					
					for (int i = 0; i < weights.length; i++) {
						if (i != m_sectionIndex) {
							sumOfOtherWeights += weights[i];
						}
					}

					final double[] newHeights = new double[weights.length];
					int heightSum = 0;
					for (int i = 0; i < weights.length; i++) {
						if (i != m_sectionIndex) {
							final double percentage = (double)weights[i] / sumOfOtherWeights;
							newHeights[i] = (int)(percentage * remainingHeight);
							heightSum += newHeights[i];
						}
					}
					newHeights[m_sectionIndex] = usableSashFormHeight - heightSum;

					final int[] newWeights = new int[weights.length];
					for (int i = 0; i < weights.length; i++) {
						newWeights[i] = (int)(newHeights[i] * 100.0 / usableSashFormHeight);
					}
					
					m_sashForm.setWeights(newWeights);
				} // else let the user fend for themselves
			} else {
				final int minimumWidth = (int)(MINIMUM_SASH_PART_PERCENTAGE * (double)sashFormSize.x);
				final int totalMinimumWidth = (minimumWidth + m_sashForm.getSashWidth()) * m_otherChildrenCount;
				
				if (desiredSize.x < (sashFormSize.x - totalMinimumWidth)) {
					
				} // else let the user fend for themselves
			}
		} else {
			final Point sectionSize = m_section.getSize();
			final Point sectionClientSize = m_section.getClient().getSize();
			
			if (m_sashForm.getOrientation() == SWT.VERTICAL) {
				final double titleBarHeight = sectionSize.y - sectionClientSize.y;
				final double usableSashFormHeight = sashFormSize.y - (totalSashConsumption + titleBarHeight);
				final int[] weights = m_sashForm.getWeights();
				double sumOfOtherWeights = 0;
				
				for (int i = 0; i < weights.length; i++) {
					if (i != m_sectionIndex) {
						sumOfOtherWeights += weights[i];
					}
				}

				final double[] newHeights = new double[weights.length];
				for (int i = 0; i < weights.length; i++) {
					if (i != m_sectionIndex) {
						final double percentage = (double)weights[i] / sumOfOtherWeights;
						newHeights[i] = (int)(percentage * usableSashFormHeight);
					}
				}
				newHeights[m_sectionIndex] = (int)titleBarHeight;

				final int[] newWeights = new int[weights.length];
				for (int i = 0; i < weights.length; i++) {
					newWeights[i] = (int)(newHeights[i] * 100.0 / usableSashFormHeight);
				}
				
				m_sashForm.setWeights(newWeights);
			} else {
				
			}
		}
	}
}
