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
 *   Markus Alexander Kuppe - initial API and implementation
 ******************************************************************************/
package tlc2.tool.impl;

import tla2sany.semantic.ExprOrOpArgNode;
import tlc2.TLCGlobals;
import tlc2.tool.TLCState;
import tlc2.tool.coverage.CostModel;
import tlc2.util.Context;
import tlc2.util.IdThread;
import tlc2.value.IValue;

/*
Root Cause:
---------

1) [Values](https://github.com/tlaplus/tlaplus/blob/master/tlatools/src/tlc2/value/impl/Value.java) can be (deeply) nested.

1) Values transition through the following sequence of states:  New (instantiated), normalized, and fingerprinted.  Transitioning from one state to another is not thread-safe.  Non-technical speaking, a value is both the symbolic and the explicit entity.

2) Normalization of an (enumerable) value causes its elements to be sorted and duplicates to be removed.  It does not cause new elements to be  generated/enumerated. For example, normalizing the [SetPredValue](https://github.com/tlaplus/tlaplus/blob/master/tlatools/src/tlc2/value/impl/SetPredValue.java), corresponding to the expression ```tla { s \in SUBSET S : s # {} }```, causes ```S``` to be sorted and any duplicate elements to be removed.

3) Fingerprinting an enumerable value causes its elements to be explicitly enumerated.  For example, the SetPredValue from before causes all subsets ```s``` to be enumerated.

4) At startup, TLC eagerly evaluates zero-arity constant definitions and operators which involves creating values.  These values are normalized but not fingerprinted!  For example, the operator ```NonEmptySubsS == { s \in SUBSET S : s # {} }``` will be evaluated to a SetPredValue that is stored in the ```NonEmptySubsS``` node of the semantic graph.  We denote the set of values in the semantic graph with V<sub>SG</sub>.

5) Generating a [TLCState](https://github.com/tlaplus/tlaplus/blob/master/tlatools/src/tlc2/tool/TLCTrace.java) during the evaluation of the next-state relation, assigns newly created values to variables.  Before a TLCState is enqueued in the [StateQueue](https://github.com/tlaplus/tlaplus/blob/master/tlatools/src/tlc2/tool/queue/StateQueue.java), its values are fingerprinted.  Thus, values of TLCStates can safely be shared across [Workers](https://github.com/tlaplus/tlaplus/blob/master/tlatools/src/tlc2/tool/Worker.java).

Lets assume a spec with one variable ```x``` whose value - in all states - is some set.  Furthermore, let ```P``` be the property ```[](x \in NonEmptySubsS)```.  For simplicity reasons,  we assume:

1)  ```P``` is not checked on the initial states
2) Two Workers check next states simultaneously

Under these two assumptions, both Workers will race to enumerate (fingerprint) ```NonEmptySubsS```.

Note that the fact that we had to assume 1) and 2) explains why this race condition didn't surfaced earlier.  However, the assumptions are true in real-world executions of TLC.  For example, the evaluation of a more complex NonEmptySubsS, with a deeply nested hierarchy of values, may not require the evaluation of nested values in the initial states.

---------------

@xxyzzn came up with another scenario that might lead to the calculation of bogus fingerprints:

```tla
EXTENDS Integers, Sequences
VARIABLE x, y

Foo == { s \in SUBSET {1,2,3,4} : s # {} }

Init == x = << >> /\ y \in 1..2

Next == x' \in {<<i, Foo>> : i \in 1..2} /\ UNCHANGED y
```

Variable ```y``` only exists so that the state-graph has two initial states (sequentially generated).  A single initial state would restrict the first evaluation of Next to a single Worker (only a single initial state to dequeue from the ```StateQueue```) and thus fingerprinting cannot occur concurrently.

Attempted Fix A:
---------------------

[At startup](https://github.com/tlaplus/tlaplus/blob/63bab42e79e750b7ac033cfe7196d8f0b53e861e/tlatools/src/tlc2/tool/impl/SpecProcessor.java#L202-L281), (eagerly) fingerprint all values of V<sub>SG</sub>.

Problem: Not all values in V<sub>SG</sub> need not be fingerprinted to completely check a spec.  For some specs such as [CarTalkPuzzle](https://github.com/tlaplus/tlaplus/issues/361#issuecomment-543256201), this is even prohibitive because explicit enumeration is infeasible: TLC will hang at startup.

Deferring fingerprinting of V<sub>SG</sub> until after the assumptions have been checked, such as when the initial states are (atomically) generated, is no general solution.

Proposed Fix A:
--------------------

Properly synchronize values such that no race conditions are possible if two or more Workers enumerate them concurrently.  

Disadvantages:  
1) It creates a scalability bottleneck: Workers will content for the synchronized ```NonEmptySubs```on every state that is generated.
2) Engineering effort to correctly synchronize the Value type hierarchy without introducing dead-locks.

Proposed Fix B:
--------------------

For each worker, create a copy of V<sub>SG</sub> (technically borrows from the concept of  a ```ThreadLocal```).

Disadvantages:  
1) Requires a type check (and potentially cast) on every [lookup](https://github.com/tlaplus/tlaplus/blob/63bab42e79e750b7ac033cfe7196d8f0b53e861e/tlatools/src/tlc2/tool/impl/Spec.java#L448-L497) that occurrs during the [evaluation of the next-state relation](https://github.com/tlaplus/tlaplus/blob/63bab42e79e750b7ac033cfe7196d8f0b53e861e/tlatools/src/tlc2/tool/impl/Tool.java#L782-L814).  An optimization would be to [eventually](https://github.com/tlaplus/tlaplus/blob/63bab42e79e750b7ac033cfe7196d8f0b53e861e/tlatools/src/tlc2/tool/AbstractChecker.java#L496) garbage-collect the copies of V<sub>SG</sub> to at least skip the type cast once one copy is completely fingerprinted.
2) [Value#deepCopy](https://github.com/tlaplus/tlaplus/blob/63bab42e79e750b7ac033cfe7196d8f0b53e861e/tlatools/src/tlc2/value/IValue.java#L104)  - required to create the copies of V<sub>SG</sub> - is [broken for most value types](https://github.com/tlaplus/tlaplus/blob/63bab42e79e750b7ac033cfe7196d8f0b53e861e/tlatools/src/tlc2/value/impl/SubsetValue.java#L232) (can probably be fixed).
*/
public class WorkerValue {
	/*
	 * Demuxing is supposed to be called only once per sn/opDef whereas muxing is called many many times.
	 */    
    public static Object demux(final OpDefEvaluator spec, final ExprOrOpArgNode en) {
    	return demux(spec, en, CostModel.DO_NOT_RECORD);
    }

	/*
	 * Demuxing is supposed to be called only once per sn/opDef whereas muxing is called many many times.
	 */    
    public static Object demux(final OpDefEvaluator spec, final ExprOrOpArgNode en, final CostModel cm) {
        final IValue defVal = spec.eval(en, Context.Empty, TLCState.Empty, cm);
    	defVal.deepNormalize();
    	
    	if (defVal.mutates() && TLCGlobals.getNumWorkers() > 1) {
    		final IValue[] values = new IValue[TLCGlobals.getNumWorkers()];
    		values[0] = defVal;

    		for (int i = 1; i < values.length; i++) {
    			// Ideally, we could invoke IValue#deepCopy here instead of evaluating opDef again.  However,
    			// IValue#deepCopy doesn't create copies for most values.
    			values[i] = spec.eval(en, Context.Empty, TLCState.Empty, cm);
    			values[i].deepNormalize();
    		}
    		
    		return new WorkerValue(values);
    	} else {
    		return defVal;
    	}
    }
    
	public static Object mux(final Object result) {
		if (!(result instanceof WorkerValue)) {
			return result;
		}
		
		final WorkerValue vp = (WorkerValue) result;
		final Thread t = Thread.currentThread();
		if (t instanceof IdThread) {
			final IdThread w = (IdThread) t;
			return vp.values[w.myGetId()];
		} else {
			return vp.values[0];
		}
	}
	
	private final IValue[] values;

	private WorkerValue(IValue[] values) {
		this.values = values;
	}
}
