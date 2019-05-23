/*******************************************************************************
 * Copyright (c) 2018 Microsoft Research. All rights reserved. 
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
 *   Markus Alexander Kuppe - initial API and implementation
 ******************************************************************************/
package org.lamport.tla.toolbox.tool.tlc.output.data;

import java.util.Comparator;

import org.eclipse.jface.resource.JFaceResources;
import org.eclipse.swt.graphics.Color;

public enum Representation {
	
	INV, COST, INVCOST, STATES, STATES_DISTINCT;

	public static Object valuesNoStates() {
		final Representation[] values = new Representation[3];
		values[0] = INV;
		values[1] = COST;
		values[2] = INVCOST;
		return values;
	}

	public enum Grouping {
		INDIVIDUAL, COMBINED;
	}

	public String getToolTipText() {
		if (this == INV) {
			return "Invocations: %,d\nClick to jump to location %s.";
		} else if (this == COST) {
			return "Cost: %,d\nClick to jump to location %s.";
		} else if (this == INVCOST) {
			return "Inv + Cost: %,d\nClick to jump to location %s.";
		} else if (this == STATES) {
			return "States Generated: %,d\nClick to jump to location %s.";
		} else if (this == STATES_DISTINCT) {
			return "Distinct States: %,d\nClick to jump to location %s.";
		}
		return "";
	}
	
	public String toString() {
		if (this == INV) {
			return "Invocations";
		} else if (this == COST) {
			return "Cost";
		} else if (this == INVCOST) {
			return "Inv + Cost";
		} else if (this == STATES) {
			return "Generated States";
		} else if (this == STATES_DISTINCT) {
			return "Distinct States";
		}
		return "";
	}

	public long getValue(CoverageInformationItem item, Grouping grouping) {
		if (grouping == Grouping.COMBINED) {
			return getTotal(item);
		} else {
			return getValue(item);
		}
	}
	
	private long getValue(CoverageInformationItem item) {
		if (this == INV) {
			return item.getCount();
		} else if (this == COST) {
			return item.getCost();
		} else if (this == INVCOST) {
			return item.getCountAndCost();
		} else if (this == STATES) {
			return item.getCount();
		} else if (this == STATES_DISTINCT) {
			return item.getCost();
		}
		return 0L;
	}

	private long getTotal(CoverageInformationItem item) {
		if (this == INV) {
			return item.getTotalCount();
		} else if (this == COST) {
			return item.getTotalCost();
		} else if (this == INVCOST) {
			return item.getTotalCost() + item.getTotalCount();
		} else if (this == STATES) {
			return item.getTotalCount();
		} else if (this == STATES_DISTINCT) {
			return item.getTotalCost();
		}
		return 0L;
	}

	public Color getColor(CoverageInformationItem cii, final Grouping group) {
		final Color[] colors = cii.representations.get(this);
		if (colors != null) {
			return colors[group.ordinal()];
		}
		return JFaceResources.getColorRegistry().get(ModuleCoverageInformation.GRAY);
	}

	public Comparator<CoverageInformationItem> getComparator(Grouping grouping) {
		if (this == STATES) {
			return new Comparator<CoverageInformationItem>() {
				@Override
				public int compare(CoverageInformationItem o1, CoverageInformationItem o2) {
					return Long.compare(o1.getCount(), o2.getCount());
				}
			};
		} else if (this == STATES_DISTINCT) {
			return new Comparator<CoverageInformationItem>() {
				@Override
				public int compare(CoverageInformationItem o1, CoverageInformationItem o2) {
					return Long.compare(o1.getCost(), o2.getCost());
				}
			};
		}
		if (grouping == Grouping.COMBINED) {
			if (this == INV) {
				return new Comparator<CoverageInformationItem>() {
					@Override
					public int compare(CoverageInformationItem o1, CoverageInformationItem o2) {
						return Long.compare(o1.getTotalCount(), o2.getTotalCount());
					}
				};
			} else if (this == COST) {
				return new Comparator<CoverageInformationItem>() {
					@Override
					public int compare(CoverageInformationItem o1, CoverageInformationItem o2) {
						return Long.compare(o1.getTotalCost(), o2.getTotalCost());
					}
				};
			} else if (this == INVCOST) {
				return new Comparator<CoverageInformationItem>() {
					@Override
					public int compare(CoverageInformationItem o1, CoverageInformationItem o2) {
						return Long.compare(o1.getTotalCountAndCost(), o2.getTotalCountAndCost());
					}
				};
			}
		} else {
			if (this == INV) {
				return new Comparator<CoverageInformationItem>() {
					@Override
					public int compare(CoverageInformationItem o1, CoverageInformationItem o2) {
						return Long.compare(o1.getCount(), o2.getCount());
					}
				};
			} else if (this == COST) {
				return new Comparator<CoverageInformationItem>() {
					@Override
					public int compare(CoverageInformationItem o1, CoverageInformationItem o2) {
						return Long.compare(o1.getCost(), o2.getCost());
					}
				};
			} else if (this == INVCOST) {
				return new Comparator<CoverageInformationItem>() {
					@Override
					public int compare(CoverageInformationItem o1, CoverageInformationItem o2) {
						return Long.compare(o1.getCountAndCost(), o2.getCountAndCost());
					}
				};
			}
		}
		return new Comparator<CoverageInformationItem>() {
			@Override
			public int compare(CoverageInformationItem o1, CoverageInformationItem o2) {
				return 0;
			}
		};
	}
}
