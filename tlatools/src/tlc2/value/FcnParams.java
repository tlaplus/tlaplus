// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Last modified on Wed  4 Jul 2007 at 17:26:45 PST by lamport
//      modified on Sat Nov 13 11:14:54 PST 1999 by yuanyu

package tlc2.value;

import tla2sany.semantic.FormalParamNode;
import tlc2.output.EC;
import util.Assert;

public class FcnParams {
  public FormalParamNode[][] formals;  // array of formal params
  public boolean[] isTuples;      // true iff tuple param
  public Value[] domains;         // the bounds of the formals
  public int argLen;              // the number of arguments
  
  public FcnParams(FormalParamNode[][] formals, boolean[] isTuples, Value[] domains) {
    this.formals = formals;
    this.isTuples = isTuples;
    this.domains = domains;
    this.argLen = 0;
    for (int i = 0; i < formals.length; i++) {
      this.argLen += (isTuples[i]) ? 1 : formals[i].length;
    }
  }

  public final int length() { return this.argLen; }
  
  public final int size() {
    // int idx = 0; // SZ Feb 24, 2009: never read locally
    long sz = 1;
    for (int i = 0; i < this.domains.length; i++) {
      int sz1 = this.domains[i].size();
      if (!this.isTuples[i]) {
	int len1 = this.formals[i].length;
	for (int j = 1; j < len1; j++) {
	  sz *= sz1;
	  if (sz < -2147483648 || sz > 2147483647) {
	    Assert.fail(EC.TLC_MODULE_OVERFLOW, "the number of elements in:\n" +
			this.toString());
	  }
	}
      }
      sz *= sz1;
      if (sz < -2147483648 || sz > 2147483647) {
	Assert.fail(EC.TLC_MODULE_OVERFLOW, "the number of elements in:\n" +
		    this.toString());
      }
    }
    return (int)sz;
  }

  public final String toString() {
    StringBuffer sb = new StringBuffer();
    if (this.domains.length != 0) {
      FormalParamNode[] ids = this.formals[0];
      if (this.isTuples[0]) {
	sb.append("<<");
	if (ids.length != 0) sb.append(ids[0].getName());
	for (int j = 1; j < ids.length; j++) {
	  sb.append(", " + ids[j].getName());
	}
	sb.append(">>");	
      }
      else {
	sb.append(ids[0].getName());
      }
      sb.append(" \\in " + this.domains[0].toString());
    }
    for (int i = 1; i < this.domains.length; i++) {
      sb.append(", ");
      FormalParamNode[] ids = this.formals[i];
      if (this.isTuples[i]) {
	sb.append("<<");
	if (ids.length != 0) sb.append(ids[0].getName());
	for (int j = 1; j < ids.length; j++) {
	  sb.append(", " + ids[j].getName());
	}
	sb.append(">>");	
      }
      else {
	sb.append(ids[0].getName());
      }	
      sb.append(" \\in " + this.domains[i].toString());
    }
    return sb.toString();
  }

  public final ValueEnumeration elements() {
    if (this.argLen == 1) {
      if (!(this.domains[0] instanceof Enumerable)) {
	Assert.fail("The domains of formal parameters must be enumerable.");
      }
      return ((Enumerable)this.domains[0]).elements();
    }
    return new Enumerator();
  }

  final class Enumerator implements ValueEnumeration {
    private ValueEnumeration[] enums;
    private Value[] currentElems;
    
    public Enumerator() {
      this.enums = new ValueEnumeration[argLen];
      this.currentElems = new Value[argLen];
      int idx = 0;
      for (int i = 0; i < domains.length; i++) {
	if (!(domains[i] instanceof Enumerable)) {
	  Assert.fail("The domains of the parameters must be enumerable.");
	}
	if (isTuples[i]) {
	  this.enums[idx] = ((Enumerable)domains[i]).elements();
	  this.currentElems[idx] = this.enums[i].nextElement();
	  if (this.currentElems[idx] == null) {
	    this.enums = null;
	    this.currentElems = null;
	    return;
	  }
	  idx++;
	}
	else {
	  int maxIdx = idx + formals[i].length;
	  for (; idx < maxIdx; idx++) {
	    this.enums[idx] = ((Enumerable)domains[i]).elements();
	    this.currentElems[idx] = this.enums[idx].nextElement();
	    if (this.currentElems[idx] == null) {
	      this.enums = null;
	      this.currentElems = null;
	      return;
	    }
	  }
	}
      }
    }

    public final void reset() {
      if (this.enums != null) {
	for (int i = 0; i < this.enums.length; i++) {
	  this.enums[i].reset();
	  this.currentElems[i] = this.enums[i].nextElement();
	}
      }
    }

    public final Value nextElement() {
      if (this.enums == null) return null;
      Value[] elems = new Value[argLen];
      for (int i = 0; i < argLen; i++) {
	elems[i] = this.currentElems[i];
      }
      for (int i = 0; i < argLen; i++) {
	this.currentElems[i] = this.enums[i].nextElement();
	if (this.currentElems[i] != null) break;
	if (i == argLen - 1) {
	  this.enums = null;
	  this.currentElems = null;
	  break;
	}
	this.enums[i].reset();
	this.currentElems[i] = this.enums[i].nextElement();
      }
      return new TupleValue(elems);
    }
        
  }
  
}
