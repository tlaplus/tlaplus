// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Last modified on Mon 30 Apr 2007 at  9:19:51 PST by lamport
//      modified on Tue Aug 22 16:03:24 PDT 2000 by yuanyu

package tlc2.module;

import tlc2.output.EC;
import tlc2.tool.EvalException;
import tlc2.value.ValueConstants;
import tlc2.value.Values;
import tlc2.value.impl.*;

import java.util.ArrayList;
import java.util.Hashtable;

public class TransitiveClosure implements ValueConstants {
    public static final long serialVersionUID = 20160822L;

    /* Implement the Warshall algorithm for transitive closure. */
    public static Value Warshall(final Value rel) {
        if (!(rel instanceof Enumerable)) {
            throw new EvalException(EC.TLC_MODULE_APPLYING_TO_WRONG_VALUE, new String[]{"TransitiveClosure",
                    "an enumerable set", Values.ppr(rel.toString())});
        }
        final int maxLen = 2 * rel.size();
        final boolean[][] matrix = new boolean[maxLen][maxLen];
        final ValueEnumeration elems = ((Enumerable) rel).elements();
        final ArrayList<Value> elemList = new ArrayList<>();
        final Hashtable<Value, Integer> fps = new Hashtable<>();
        int cnt = 0;
        Value elem;
        while ((elem = elems.nextElement()) != null) {
            final TupleValue tv = (TupleValue) elem.toTuple();
            if (tv == null || tv.size() != 2) {
                throw new EvalException(EC.TLC_MODULE_TRANSITIVE_CLOSURE, Values.ppr(elem.toString()));
            }
            final Value elem1 = tv.elems[0];
            final Value elem2 = tv.elems[1];
            int num1 = cnt;
            Integer num = fps.get(elem1);
            if (num == null) {
                fps.put(elem1, cnt);
                elemList.add(elem1);
                cnt++;
            } else {
                num1 = num;
            }
            int num2 = cnt;
            num = fps.get(elem2);
            if (num == null) {
                fps.put(elem2, cnt);
                elemList.add(elem2);
                cnt++;
            } else {
                num2 = num;
            }
            matrix[num1][num2] = true;
        }

        for (int y = 0; y < cnt; y++) {
            for (int x = 0; x < cnt; x++) {
                if (matrix[x][y]) {
                    for (int z = 0; z < cnt; z++) {
                        if (matrix[y][z])
                            matrix[x][z] = true;
                    }
                }
            }
        }

        final ValueVec newElems = new ValueVec();
        for (int i = 0; i < cnt; i++) {
            for (int j = 0; j < cnt; j++) {
                if (matrix[i][j]) {
                    final Value elem1 = elemList.get(i);
                    final Value elem2 = elemList.get(j);
                    final Value newElem = new TupleValue(elem1, elem2);
                    newElems.add(newElem);
                }
            }
        }
        return new SetEnumValue(newElems, false);
    }

}
