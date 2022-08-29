/****************************************************************************
 * CLASS Changed                                                            * 
 * last modified on Wed 31 Aug 2005 at 13:18:17 UT by keith                 *
 ****************************************************************************/

package pcal;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

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
    public final int[] count; /* number times variable set */
    public final List<String> vars; /* list of variables */

    public Changed(final List<String> vars) {
        count = new int[vars.size()];
        this.vars = vars;
        Arrays.fill(count, 0);
    }

    public Changed(final Changed c) {
        vars = c.vars;
        count = new int[vars.size()];
        System.arraycopy(c.count, 0, count, 0, count.length);
    }

    public String toString() {
        final StringBuilder s = new StringBuilder("[");
        for (int i = 0; i < count.length; i++)
            s.append((i == 0) ? "" : ", ").append(vars.get(i)).append(" ").append(count[i]);
        s.append("]");
        return s.toString();
    }

    public int Size() {
        return count.length;
    }

    public boolean IsChanged(final String s) {
        for (int i = 0; i < count.length; i++)
            if (s.equals(vars.get(i)))
                return (count[i] > 0);
        return false;
    }

    public void Merge(final Changed c) {
        PcalDebug.Assert(count.length == c.count.length);
        for (int i = 0; i < count.length; i++)
            count[i] = Math.max(count[i], c.count[i]);
    }

    public int Set(final String v) {
        for (int i = 0; i < count.length; i++)
            if (v.equals(vars.get(i)))
                return ++count[i];
        return 0;
    }

    /* String of vars whose change count is 0 */
    public String Unchanged() {
        final StringBuilder s = new StringBuilder();
        for (int i = 0; i < count.length; i++)
            if (count[i] == 0)
                s.append((s.length() == 0) ? "" : ", ").append(vars.get(i));
        return s.toString();
    }

    /* String of vars that were changed in c but not in this */
    public String Unchanged(final Changed c) {
        final StringBuilder s = new StringBuilder();
        for (int i = 0; i < count.length; i++)
            if ((count[i] == 0) && c.count[i] > 0)
                s.append((s.length() == 0) ? "" : ", ").append(vars.get(i));
        return s.toString();
    }

    /* ArrayList of strings of vars whose change count is 0 */
    /* Each string is no longer than ch characters       */
    /* (except for vars whose length is over ch-1)       */
    /* This method is called only once, from             */
    /* GenLabeledStmt.                                   */
    public List<String> Unchanged(final int ch) {
        final List<String> sv = new ArrayList<>();
        StringBuilder s = new StringBuilder();
        boolean haveOne = false;
        for (int i = 0; i < count.length; i++)
            if (count[i] == 0) {
                final String one = vars.get(i);
                if (haveOne) s.append(", ");
                else haveOne = true;
                if (s.length() + one.length() > ch) {
                    if (s.length() > 0) sv.add(s.toString());
                    s = new StringBuilder(one);
                } else s.append(one);
            }
        if (s.length() > 0) sv.add(s.toString());
        return sv;
    }

    /* String of vars that were changed in c but not in this */
    /* Each string is no longer than ch characters           */
    /* (except for vars whose length is over ch-1)           */
    public List<String> Unchanged(final Changed c, final int ch) {
        final List<String> sv = new ArrayList<>();
        StringBuilder s = new StringBuilder();
        boolean haveOne = false;
        for (int i = 0; i < count.length; i++)
            if ((count[i] == 0) && c.count[i] > 0) {
                final String one = vars.get(i);
                if (haveOne) s.append(", ");
                else haveOne = true;
                if (s.length() + one.length() > ch) {
                    if (s.length() > 0) sv.add(s.toString());
                    s = new StringBuilder(one);
                } else s.append(one);
            }
        if (s.length() > 0) sv.add(s.toString());
        return sv;
    }

    /* Number of vars whose change count is 0 */
    public int NumUnchanged() {
        int ct = 0;
        for (final int j : count) if (j == 0) ct = ct + 1;
        return ct;
    }

    /* Number of vars that were changed in c but not in this */
    public int NumUnchanged(final Changed c) {
        int ct = 0;

        for (int i = 0; i < count.length; i++)
            if ((count[i] == 0) && c.count[i] > 0)
                ct = ct + 1;
        return ct;
    }

}
