/**
 * A Region represents a portion of the .tla file between two
 * Locations: begin and end.
 */

package pcal;

public class Region {

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
}
