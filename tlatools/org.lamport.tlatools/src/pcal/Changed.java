/****************************************************************************
 * CLASS Changed                                                            * 
 * last modified on Wed 31 Aug 2005 at 13:18:17 UT by keith                 *
 ****************************************************************************/

package pcal;

import java.util.Vector;

public class Changed {
	/*
	 * A Changed object is used when generating the actions to keep track
	 * of how many times a variable has been set in the conjuncts produced
	 * so far.  It's an error if the variable has been set more than once.
	 * If it has been set once, then uses of it in expressions must be
	 * replaced by their primed versions.
	 * 
	 * The object has two fields: 
	 *   vars: a vector of variable names.  It is set to the vector
	 *         of all variables.
	 *   count: an array whose i-th element is the number of times the
	 *          i-th variable in vars has been changed.
	 */
    public int[] count; /* number times variable set */
    public Vector vars; /* list of variables */

    public Changed (Vector vars) {
	count = new int[vars.size()];
	this.vars = vars;
	for (int i = 0; i < count.length; i++)
	    count[i] = 0;
    }

    public Changed (Changed c) {
	vars = c.vars;
	count = new int[vars.size()];
	for (int i = 0; i < count.length; i++)
	    count[i] = c.count[i];
    }

    public String toString () {
	String s = "[";
	for (int i = 0; i < count.length; i++)
	    s = s
		+ ((i == 0) ? "" : ", ")
		+ ((String) vars.elementAt(i))
		+ " "
		+ count[i];
	s = s + "]";
	return s;
    }

    public int Size() {
	return count.length;
    }

    public boolean IsChanged(String s) {
	for (int i = 0; i < count.length; i++)
	    if (s.equals((String) vars.elementAt(i)))
		return (count[i] > 0);
	return false;
    }

    public void Merge (Changed  c) {
	PcalDebug.Assert(count.length == c.count.length);
	for (int i = 0; i < count.length; i++)
	    count[i] = (count[i] > c.count[i]) ? count[i] : c.count[i];
    }

    public int Set (String v) {
	for (int i = 0; i < count.length; i++)
	    if (v.equals((String) vars.elementAt(i)))
		return ++count[i];
	return 0;
    }

    /* String of vars whose change count is 0 */
    public String Unchanged () {
	String s = "";
	for (int i = 0; i < count.length; i++)
	    if (count[i] == 0)
		s = s
		    + ((s.length() == 0) ? "" : ", ")
		    + (String) vars.elementAt(i);
	return s;
    }

    /* String of vars that were changed in c but not in this */
    public String Unchanged (Changed c) {
	String s = "";
	for (int i = 0; i < count.length; i++)
	    if ((count[i] == 0) && c.count[i] > 0)
		s = s
		    + ((s.length() == 0) ? "" : ", ")
		    + (String) vars.elementAt(i);
	return s;
    }
  
    /* Vector of strings of vars whose change count is 0 */
    /* Each string is no longer than ch characters       */
    /* (except for vars whose length is over ch-1)       */
    /* This method is called only once, from             */
    /* GenLabeledStmt.                                   */
    public Vector Unchanged (int ch) {
	Vector sv = new Vector();
	String s = "";
	boolean haveOne = false;
	for (int i = 0; i < count.length; i++)
	    if (count[i] == 0) {
		String one = (String) vars.elementAt(i);
		if (haveOne) s = s + ", ";
		else haveOne = true;
		if (s.length() + one.length() > ch) {
		    if (s.length() > 0) sv.addElement(s);
		    s = one;
		}
		else s = s + one;
	    }
	if  (s.length() > 0) sv.addElement(s);
	return sv;
    }

    /* String of vars that were changed in c but not in this */
    /* Each string is no longer than ch characters           */
    /* (except for vars whose length is over ch-1)           */
    public Vector Unchanged (Changed c, int ch) {
	Vector sv = new Vector();
	String s = "";
	boolean haveOne = false;
	for (int i = 0; i < count.length; i++)
	    if ((count[i] == 0) && c.count[i] > 0) {
		String one = (String) vars.elementAt(i);
		if (haveOne) s = s + ", ";
		else haveOne = true;
		if (s.length() + one.length() > ch) {
		    if (s.length() > 0) sv.addElement(s);
		    s = one;
		}
		else s = s + one;
	    }
	if  (s.length() > 0) sv.addElement(s);
	return sv;
    }
  
    /* Number of vars whose change count is 0 */
    public int NumUnchanged () {
	int ct = 0;
	for (int i = 0; i < count.length; i++)
	    if (count[i] == 0) ct = ct + 1;
	return ct;
    }

    /* Number of vars that were changed in c but not in this */
    public int NumUnchanged (Changed c) {
	int ct = 0;

	for (int i = 0; i < count.length; i++)
	    if ((count[i] == 0) && c.count[i] > 0)
		ct = ct + 1;
	return ct;
    }
  
}
