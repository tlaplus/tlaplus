// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Last modified on Mon 30 Apr 2007 at 13:21:10 PST by lamport
//      modified on Tue Aug 22 11:56:52 PDT 2000 by yuanyu

package tlc2.value.impl;

import java.util.ArrayList;
import java.util.List;
import java.util.function.Consumer;

public interface ValueEnumeration {
  /* Reset allows repeated use of this enumerator. */
  void reset();

  /* Return the next element if there is one. Otherwise return null. */
  Value nextElement();
  
	default List<Value> all() {
		final List<Value> values = new ArrayList<Value>();
		Value elem;
		while ((elem = nextElement()) != null) {
			values.add(elem);
		}
		return values;
	}

	default void forEach(final Consumer<? super Value> action) {
		Value elem;
		while ((elem = nextElement()) != null) {
			action.accept(elem);
		}
	}
	
	default SetEnumValue asSet() {
		final ValueVec vv = new ValueVec();
		Value elem;
		while ((elem = nextElement()) != null) {
			vv.addElement(elem);
		}
		return new SetEnumValue(vv, false);
	}
}
