// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Last modified on Wed  4 Jul 2007 at 17:31:23 PST by lamport
//      modified on Thu Dec  6 21:46:34 PST 2001 by yuanyu

package tlc2.value;

import java.io.IOException;
import java.io.ObjectInputStream;
import java.io.ObjectOutputStream;

import tla2sany.semantic.FormalParamNode;
import tla2sany.semantic.SemanticNode;
import tla2sany.semantic.SymbolNode;
import tlc2.tool.EvalControl;
import tlc2.tool.EvalException;
import tlc2.tool.TLCState;
import tlc2.tool.Tool;
import tlc2.util.Context;
import util.Assert;

public class FcnLambdaValue extends Value implements Applicable {
  public FcnParams params;       // the function formals
  public SemanticNode body;      // the function body
  public ValueExcept[] excepts;  // the EXCEPTs
  public Tool tool;
  public Context con;
  public TLCState state;
  public TLCState pstate;
  public int control;
  public FcnRcdValue fcnRcd;

  /* Constructor */
  public FcnLambdaValue(FcnParams params, SemanticNode body, Tool tool,
			Context c, TLCState s0, TLCState s1, int control) {
    this.params = params;
    this.body = body;
    this.excepts = null;
    this.tool = tool;
    this.con = c;
    this.state = s0.copy();  // copy() added 12 Mar 2010 by Yuan Yu. 
    if (s1 != null) {        // see SetPredValue constructor.
        this.pstate = s1.copy(); 
    } else {
        this.pstate = null;
    }
    
    this.control = control;
    this.fcnRcd = null;
  }

  public FcnLambdaValue(FcnLambdaValue fcn) {
    this.params = fcn.params;
    this.body = fcn.body;
    this.excepts = fcn.excepts;
    this.tool = fcn.tool;
    this.con = fcn.con;
    this.state = fcn.state;
    this.pstate = fcn.pstate;
    this.control = fcn.control;
    this.fcnRcd = fcn.fcnRcd;
  }

  public final byte getKind() { return FCNLAMBDAVALUE; }

  public final void makeRecursive(SymbolNode fname) {
    this.con = this.con.cons(fname, this);
    this.control = EvalControl.setKeepLazy(this.control);
  }

  public final int compareTo(Object obj) {
    FcnRcdValue fcn = FcnRcdValue.convert(this);
    return fcn.compareTo(obj);
  }
  
  public final boolean equals(Object obj) {
    FcnRcdValue fcn = FcnRcdValue.convert(this);
    return fcn.equals(obj);
  }

  public final boolean member(Value elem) {
    Assert.fail("Attempted to check if the value:\n" + ppr(elem.toString()) +
		"\nis an element of the function " + ppr(this.toString()));
    return false;   // make compiler happy
  }

  public final boolean isFinite() {
    Assert.fail("Attempted to check if the function:\n" + ppr(this.toString()) +
		"\nis a finite set.");
    return false;   // make compiler happy
  }

  /* Apply this function to the arguments given by args.  */  
  public final Value apply(Value args, int control) throws EvalException {
    if (this.fcnRcd != null) {
      return this.fcnRcd.apply(args, control);
    }

    // First, find all the excepts that match args.
    Value res = null;
    int num = 0;
    ValueExcept[] excepts1 = null;
    if (this.excepts != null) {
      int exlen = this.excepts.length;
      for (int i = exlen-1; i >= 0; i--) {
	ValueExcept ex = this.excepts[i];
	Value arg = ex.current();
	boolean inExcept = true;
	inExcept = arg.equals(args);
	if (inExcept) {
	  if (ex.isLast()) { res = ex.value; break; }
	  if (excepts1 == null) excepts1 = new ValueExcept[exlen];
	  excepts1[num++] = new ValueExcept(ex, ex.idx+1);
	}
      }
    }

    // Second, evaluate the function application.
    if (res == null) {
      Context c1 = this.con;
      FormalParamNode[][] formals = this.params.formals;
      Value[] domains = this.params.domains;
      boolean[] isTuples = this.params.isTuples;
      int plen = this.params.length();
    
      if (plen == 1) {
	if (!domains[0].member(args)) {
	  Assert.fail("In applying the function\n" + Value.ppr(this.toString()) +
		      ",\nthe first argument is:\n" + Value.ppr(args.toString()) +
		      "\nwhich is not in its domain.\n");
	}
	if (isTuples[0]) {
	  FormalParamNode[] ids = formals[0];
	  TupleValue argVal = TupleValue.convert(args);
	  if (argVal == null) {
	    Assert.fail("In applying the function\n" + Value.ppr(this.toString()) +
			",\nthe first argument is:\n" + Value.ppr(args.toString()) +
			"\nwhich does not match its formal parameter.\n");
	  }
	  if (argVal.size() != ids.length) return null;
	  Value[] elems = argVal.elems;
	  for (int i = 0; i < ids.length; i++) {
	    c1 = c1.cons(ids[i], elems[i]);
	  }
	}
	else {
	  c1 = c1.cons(formals[0][0], args);
	}
      }
      else {
	TupleValue tv = TupleValue.convert(args);
	if (tv == null) {
	  Assert.fail("In applying the function\n" + Value.ppr(this.toString()) +
		      ",\nthe argument list is:\n" + Value.ppr(args.toString()) +
		      "\nwhich does not match its formal parameter.\n");
	}
	Value[] elems = tv.elems;
	int argn = 0;
	for (int i = 0; i < formals.length; i++) {
	  FormalParamNode[] ids = formals[i];
	  Value domain = domains[i];	  
	  if (isTuples[i]) {
	    if (!domain.member(elems[argn])) {
	      Assert.fail("In applying the function\n" + Value.ppr(this.toString()) +
			  ",\nthe argument number " + (argn+1) + " is:\n" +
			  Value.ppr(elems[argn].toString()) +
			  "\nwhich is not in its domain.\n");
	    }
	    TupleValue tv1 = TupleValue.convert(elems[argn++]);
	    if (tv1 == null || tv1.size() != ids.length) {
	      Assert.fail("In applying the function\n" + Value.ppr(this.toString()) +
			  ",\nthe argument number " + argn + " is:\n" +
			  Value.ppr(elems[argn-1].toString()) +
			  "\nwhich does not match its formal parameter.\n");
	    }
	    Value[] avals = tv1.elems;
	    for (int j = 0; j < ids.length; j++) {
	      c1 = c1.cons(ids[j], avals[j]);
	    }	  
	  }
	  else {
	    for (int j = 0; j < ids.length; j++) {
	      if (!domain.member(elems[argn])) {
		Assert.fail("In applying the function\n" + Value.ppr(this.toString()) +
			    ",\nthe argument number " + (argn+1) + " is:\n" +
			    Value.ppr(elems[argn].toString()) + "\nwhich is not in its domain.\n");
	      }
	      c1 = c1.cons(ids[j], elems[argn++]);
	    }
	  }
	}
      }
      res = this.tool.eval(this.body, c1, this.state, this.pstate, control);
    }
    
    // Finally, apply the matching excepts on the result.
    if (num == 0) return res;
    ValueExcept[] excepts2 = new ValueExcept[num];
    for (int i = 0; i < num; i++) {
      excepts2[num-1-i] = excepts1[i];
    }
    return res.takeExcept(excepts2);
  }

  /* This one does not seem to be needed anymore.  */
  public final Value apply(Value[] args, int control) throws EvalException {
    return this.apply(new TupleValue(args), control);
  }

  public final Value select(Value arg) {
    if (this.fcnRcd != null) {
      return this.fcnRcd.select(arg);
    }

    // First, find all the excepts that match arg.
    Value res = null;
    int num = 0;
    ValueExcept[] excepts1 = null;
    if (this.excepts != null) {
      int exlen = this.excepts.length;
      for (int i = exlen-1; i >= 0; i--) {
	ValueExcept ex = this.excepts[i];
	Value exArg = ex.current();
	boolean inExcept = exArg.equals(arg);
	if (inExcept) {
	  if (ex.isLast()) { res = ex.value; break; }
	  if (excepts1 == null) excepts1 = new ValueExcept[exlen];
	  excepts1[num++] = new ValueExcept(ex, ex.idx+1);
	}
      }
    }

    // Second, evaluate the function application.
    if (res == null) {
      Context c1 = this.con;
      FormalParamNode[][] formals = this.params.formals;
      Value[] domains = this.params.domains;
      boolean[] isTuples = this.params.isTuples;
      int plen = this.params.length();
    
      if (plen == 1) {
	if (!domains[0].member(arg)) return null;
	if (isTuples[0]) {
	  FormalParamNode[] ids = formals[0];
	  TupleValue argVal = TupleValue.convert(arg);
	  /*
	   * SZA: Changed from argVal.toString() to arg.toString() to prevent a NullPointerException
	   */
	  if (argVal == null) {
	    Assert.fail("In applying the function\n" + Value.ppr(this.toString()) +
			",\nthe first argument is:\n" + Value.ppr(arg.toString()) +
			"\nwhich does not match its formal parameter.\n");
	  }
	  if (argVal.size() != ids.length) return null;
	  Value[] elems = argVal.elems;
	  for (int i = 0; i < ids.length; i++) {
	    c1 = c1.cons(ids[i], elems[i]);
	  }
	}
	else {
	  c1 = c1.cons(formals[0][0], arg);
	}
      }
      else {
	TupleValue tv = TupleValue.convert(arg);
	if (tv == null) {
	  Assert.fail("In applying the function\n" + Value.ppr(this.toString()) +
		      ",\nthe argument list is:\n" + Value.ppr(arg.toString()) +
		      "\nwhich does not match its formal parameter.\n");
	}
	Value[] elems = tv.elems;
	int argn = 0;
	for (int i = 0; i < formals.length; i++) {
	  FormalParamNode[] ids = formals[i];
	  Value domain = domains[i];	  
	  if (isTuples[i]) {
	    if (!domain.member(elems[argn])) return null;
	    TupleValue tv1 = TupleValue.convert(elems[argn++]);
	    if (tv1 == null) {
	      Assert.fail("In applying the function\n" + Value.ppr(this.toString()) +
			  ",\nthe argument number " + argn + " is:\n" +
			  Value.ppr(elems[argn-1].toString()) +
			  "\nwhich does not match its formal parameter.\n");
	    }
	    if (tv1.size() != ids.length) return null;
	    Value[] avals = tv1.elems;
	    for (int j = 0; j < ids.length; j++) {
	      c1 = c1.cons(ids[j], avals[j]);
	    }	  
	  }
	  else {
	    for (int j = 0; j < ids.length; j++) {
	      if (!domain.member(elems[argn])) return null;
	      c1 = c1.cons(ids[j], elems[argn++]);
	    }
	  }
	}
      }
      res = this.tool.eval(this.body, c1, this.state, this.pstate, this.control);
    }
    
    // Finally, apply the matching excepts on the result.
    if (num == 0) return res;
    ValueExcept[] excepts2 = new ValueExcept[num];
    for (int i = 0; i < num; i++) {
      excepts2[num-1-i] = excepts1[i];
    }
    return res.takeExcept(excepts2);
  }
  
  /* This method returns a new function value by taking except. */
  public final Value takeExcept(ValueExcept ex) {
    if (ex.idx >= ex.path.length) return ex.value;
    
    if (this.fcnRcd != null) {
      return this.fcnRcd.takeExcept(ex);
    }
    FcnLambdaValue fcn = new FcnLambdaValue(this);
    if (this.excepts == null) {
      fcn.excepts = new ValueExcept[1];
      fcn.excepts[0] = ex;
    }
    else {
      int exlen = this.excepts.length;
      fcn.excepts = new ValueExcept[exlen+1];
      for (int i = 0; i < exlen; i++) {
	fcn.excepts[i] = this.excepts[i];
      }
      fcn.excepts[exlen] = ex;
    }
    return fcn;
  }

  /* This method returns a new function value by taking excepts. */
  public final Value takeExcept(ValueExcept[] exs) {
    if (this.fcnRcd != null) {
      return this.fcnRcd.takeExcept(exs);
    }
    FcnLambdaValue fcn = new FcnLambdaValue(this);
    int exslen = exs.length;
    if (exslen != 0) {
      int i = 0;
      for (i = exs.length-1; i >= 0; i--) {
	if (exs[i].idx >= exs[i].path.length) break;
      }
      if (i >= 0) {
	int xlen = exslen-i-1;
	fcn.excepts = new ValueExcept[xlen];
	System.arraycopy(exs, i+1, fcn.excepts, 0, xlen);
      }
      else if (this.excepts == null) {
	fcn.excepts = new ValueExcept[exslen];
	System.arraycopy(exs, 0, fcn.excepts, 0, exslen);
      }
      else {
	int len = this.excepts.length;
	fcn.excepts = new ValueExcept[len + exslen];
	System.arraycopy(this.excepts, 0, fcn.excepts, 0, len);
	System.arraycopy(exs, 0, fcn.excepts, len, exslen);
      }
    }
    return fcn;
  }

  public final Value getDomain() {
    if (this.fcnRcd != null) {
      return this.fcnRcd.getDomain();
    }
    int len = this.params.length();
    if (len == 1) {
      return this.params.domains[0];
    }
    Value[] sets = new Value[len];
    int dlen = this.params.domains.length;
    boolean[] isTuples = this.params.isTuples;
    int idx = 0;
    for (int i = 0; i < dlen; i++) {
      FormalParamNode[] formal = this.params.formals[i];
      Value domain = this.params.domains[i];
      if (isTuples[i]) {
	sets[idx++] = domain;
      }
      else {
	for (int j = 0; j < formal.length; j++) {
	  sets[idx++] = domain;
	}
      }
    }
    return new SetOfTuplesValue(sets);
  }
  
  public final int size() {
    if (this.fcnRcd == null) {
      return this.params.size();
    }
    return this.fcnRcd.size();
  }

  public final boolean isDefined() { return true; }

  public final Value deepCopy() {
    FcnLambdaValue fcn = new FcnLambdaValue(this);
    // A bug occured when printing a function whose domain is a Cartesian product because this.fcnRcd 
    // is null at this point.  On 5 Mar 2012, LL wrapped the following null test around the assignment.
    if (this.fcnRcd != null) {
       fcn.fcnRcd = (FcnRcdValue)this.fcnRcd.deepCopy();
    }
    return fcn;
  }

  public final boolean assignable(Value val) {
    return (val instanceof FcnLambdaValue);
  }

  private void readObject(ObjectInputStream ois)
  throws IOException, ClassNotFoundException {
    this.fcnRcd = (FcnRcdValue)ois.readObject();
  }

  private void writeObject(ObjectOutputStream oos) throws IOException {
    FcnRcdValue res = this.toFcnRcd();
    oos.writeObject(res);
  }
  
  public final boolean isNormalized() {
    if (this.fcnRcd == null) {
      return false;
    }
    return this.fcnRcd.isNormalized();
  }

  public final void normalize() {
    if (this.fcnRcd != null) {
      this.fcnRcd.normalize();
    }
  }

  public final FcnRcdValue toFcnRcd() {
    if (this.fcnRcd == null) {
      int sz = this.params.size();
      FormalParamNode[][] formals = this.params.formals;
      boolean[] isTuples = this.params.isTuples;
    
      Value[] domain = new Value[sz];
      Value[] values = new Value[sz];
      int idx = 0;
      ValueEnumeration Enum = this.params.elements();    
      Value arg;
      if (this.params.length() == 1) {
	while ((arg = Enum.nextElement()) != null) {
	  domain[idx] = arg;
	  Context c1 = this.con;
	  if (isTuples[0]) {
	    FormalParamNode[] ids = formals[0];
	    Value[] avals = ((TupleValue)arg).elems;
	    for (int j = 0; j < ids.length; j++) {
	      c1 = c1.cons(ids[j], avals[j]);
	    }
	  }
	  else {
	    c1 = c1.cons(formals[0][0], arg);
	  }
	  values[idx++] = this.tool.eval(this.body, c1, this.state, this.pstate, this.control);
	}
      }
      else {
	while ((arg = Enum.nextElement()) != null) {
	  domain[idx] = arg;
	  Value[] argList = ((TupleValue)arg).elems;
	  int argn = 0;
	  Context c1 = this.con;
	  for (int i = 0; i < formals.length; i++) {
	    FormalParamNode[] ids = formals[i];
	    if (isTuples[i]) {
	      Value[] avals = ((TupleValue)argList[argn++]).elems;
	      for (int j = 0; j < ids.length; j++) {
		c1 = c1.cons(ids[j], avals[j]);
	      }
	    }
	    else {
	      for (int j = 0; j < ids.length; j++) {
		c1 = c1.cons(ids[j], argList[argn++]);
	      }
	    }
	  }
	  values[idx++] = this.tool.eval(this.body, c1, this.state, this.pstate, this.control);
	}
      }
      this.fcnRcd = new FcnRcdValue(domain, values, false);
      if (this.excepts != null) {
	this.fcnRcd = (FcnRcdValue)fcnRcd.takeExcept(this.excepts);
      }
    }
    return this.fcnRcd;
  }
  
  /* The fingerprint methods.  */
  public final long fingerPrint(long fp) {
    FcnRcdValue fcn = FcnRcdValue.convert(this);
    return fcn.fingerPrint(fp);
  }

  public final Value permute(MVPerm perm) {
    FcnRcdValue fcn = FcnRcdValue.convert(this);    
    return fcn.permute(perm);
  }
  
  /* The string representation of this function.  */
  public final StringBuffer toString(StringBuffer sb, int offset) {
    if (expand || this.params == null) {
      try {
	Value val = FcnRcdValue.convert(this);
	return val.toString(sb, offset);
      }
      catch (Throwable e) { /*SKIP*/ }
    }
    sb.append("[" + this.params.toString());
    sb.append(" |-> <expression " + this.body + ">]");
    return sb;
  }

}
