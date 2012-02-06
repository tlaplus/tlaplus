/**
 * A Region represents a portion of the .tla file between two
 * Locations: begin and end.
 */

package pcal;

import java.io.Serializable;

import tla2sany.st.Location;

public class Region implements Serializable {

    /**
	 * @see TLAtoPCalMapping#serialVersionUID
	 */
	private static final long serialVersionUID = 5596444966456185518L;
	
	private PCalLocation begin ;
	private PCalLocation end ;

	/**
     * The simple constructor.
     * @param begin
     * @param end
     */
	public Region(PCalLocation begin, PCalLocation end) {
		this.begin = begin;
		this.end = end;
	}
	
	/**
	 * Constructs a region within a single line, from
	 * column bcol to column bcol+width;
	 * @param line
	 * @param bcol
	 * @param width
	 */
	public Region(int line, int bcol, int width)  {
		this.begin = new PCalLocation(line, bcol) ;
		this.end = new PCalLocation(line, bcol+width);
	}

	public PCalLocation getBegin() {
		return begin;
	}
	public void setBegin(PCalLocation begin) {
		this.begin = begin;
	}
	public PCalLocation getEnd() {
		return end;
	}
	public void setEnd(PCalLocation end) {
		this.end = end;
	}
	
	public String toString() {
//	  return "[begin |-> " + begin.toString() + ", end |-> "
//			   + end.toString() + "]";
	  if (this == null) {
	      return "null";
	  }
	  return "[" + begin.toString() + "-" + end.toString() + "]";
	}

	/* (non-Javadoc)
	 * @see java.lang.Object#hashCode()
	 */
	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + ((begin == null) ? 0 : begin.hashCode());
		result = prime * result + ((end == null) ? 0 : end.hashCode());
		return result;
	}

	/* (non-Javadoc)
	 * @see java.lang.Object#equals(java.lang.Object)
	 */
	@Override
	public boolean equals(Object obj) {
		if (this == obj)
			return true;
		if (obj == null)
			return false;
		if (getClass() != obj.getClass())
			return false;
		Region other = (Region) obj;
		if (begin == null) {
			if (other.begin != null)
				return false;
		} else if (!begin.equals(other.begin))
			return false;
		if (end == null) {
			if (other.end != null)
				return false;
		} else if (!end.equals(other.end))
			return false;
		return true;
	}

	public Location toLocation() {
		return new Location(begin.getLine() + 1, begin.getColumn() + 1,
				end.getLine() + 1, end.getColumn() + 1);
	}
}
