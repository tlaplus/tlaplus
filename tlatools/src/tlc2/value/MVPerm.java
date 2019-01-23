// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Last modified on Mon 30 Apr 2007 at 13:42:27 PST by lamport
//      modified on Thu Nov 16 15:53:30 PST 2000 by yuanyu

package tlc2.value;

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
  
  public final int size() { return this.count; }

  public final IValue get(IValue k) {
    return this.elems[((ModelValue) k).index];
  }

  @Override
  public final void put(ModelValue k, ModelValue elem) {
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
