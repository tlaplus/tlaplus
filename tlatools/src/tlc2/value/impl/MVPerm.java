// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Last modified on Mon 30 Apr 2007 at 13:42:27 PST by lamport
//      modified on Thu Nov 16 15:53:30 PST 2000 by yuanyu

package tlc2.value.impl;

import java.util.ArrayList;
import java.util.List;

import tlc2.value.IMVPerm;
import tlc2.value.IModelValue;
import tlc2.value.IValue;

public final class MVPerm implements IMVPerm {
  private final ModelValue[] elems;
  private int count;

  MVPerm() {
    this.elems = new ModelValue[ModelValue.mvs.length];
    this.count = 0;
  }

  public final boolean equals(Object obj) {
    if (obj instanceof MVPerm) {
      MVPerm perm = (MVPerm)obj;
      for (int i = 0; i < this.elems.length; i++) {
	if (this.elems[i] == null) {
	  if (perm.elems[i] != null) {
	    return false;
	  }
	}
	else if (!this.elems[i].equals(perm.elems[i])) {
	  return false;
	}
      }
      return true;
    }
    return false;
  }

  public final int hashCode() {
    int res = 0;
    for (int i = 0; i < this.elems.length; i++) {
      ModelValue mv = this.elems[i];
      if (mv != null) {
	res = 31*res + mv.val.hashCode();
      }
    }
    return res;
  }
  
  @Override
  public final int size() { return this.count; }

  @Override
  public final IValue get(IValue k) {
    return this.elems[((ModelValue) k).index];
  }

  @Override
  public final void put(IModelValue m1, IModelValue m2) {
	  ModelValue k = (ModelValue) m1;
	  ModelValue elem = (ModelValue) m2;
    if (!k.equals(elem) && this.elems[k.index] == null) {
      this.elems[k.index] = elem;
      this.count++;
    }
  }

  private final void put(int i, ModelValue elem) {
    if (this.elems[i] == null && elem != null) {
      this.elems[i] = elem;
      this.count++;
    }
  }
  
  @Override
  public final IMVPerm compose(IMVPerm perm) {
	  MVPerm res = new MVPerm();
    for (int i = 0; i < this.elems.length; i++) {
      ModelValue mv = this.elems[i];
      if (mv == null) {
	res.put(i, ((MVPerm) perm).elems[i]);
      }
      else {
	ModelValue mv1 = ((MVPerm) perm).elems[mv.index];
	if (mv1 == null) {
	  res.put(i, mv);
	}
	else if (!ModelValue.mvs[i].equals(mv1)) {
	  res.put(i, mv1);
	}
      }
    }
    return res;
  }
  
  /**
   * Consider caching if this method is used frequently; currently it is used once per instance per
   * 	execution of TLC, during initial state setup / expansion.
   * 
   * @return a {@code List} of all {@link ModelValue} instances held by this permutation.
   */
  public List<ModelValue> getAllModelValues() {
	  final List<ModelValue> values = new ArrayList<>();
	  
	  for (int i = 0; i < elems.length; i++) {
		  if (elems[i] != null) {
			  values.add(elems[i]);
		  }
	  }
	  
	  return values;
  }

  public final String toString() {
    StringBuffer sb = new StringBuffer("[");
    int i = 0;
    for (i = 0; i < this.elems.length; i++) {
      if (this.elems[i] != null) {
	sb.append(ModelValue.mvs[i].toString());
	sb.append(" -> ");
	sb.append(this.elems[i].toString());
	break;
      }
    }
    for (int j = i+1; j < this.elems.length; j++) {
      if (this.elems[j] != null) {
	sb.append(", ");
	sb.append(ModelValue.mvs[j].toString());
	sb.append(" -> ");
	sb.append(this.elems[j].toString());
      }
    }
    sb.append("]");    
    return sb.toString();
  }

}
