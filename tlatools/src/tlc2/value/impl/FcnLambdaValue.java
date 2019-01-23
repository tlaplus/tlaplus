// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Last modified on Wed 12 Jul 2017 at 16:10:00 PST by ian morris nieves
//      modified on Wed  4 Jul 2007 at 17:31:23 PST by lamport
//      modified on Thu Dec  6 21:46:34 PST 2001 by yuanyu

package tlc2.value.impl;

import java.io.IOException;
import java.io.ObjectInputStream;
import java.io.ObjectOutputStream;

import tla2sany.semantic.FormalParamNode;
import tla2sany.semantic.SemanticNode;
import tla2sany.semantic.SymbolNode;
import tlc2.TLCGlobals;
import tlc2.tool.EvalControl;
import tlc2.tool.EvalException;
import tlc2.tool.FingerprintException;
import tlc2.tool.ITool;
import tlc2.tool.TLCState;
import tlc2.tool.coverage.CostModel;
import tlc2.util.Context;
import tlc2.value.IFcnLambdaValue;
import tlc2.value.IMVPerm;
import tlc2.value.IValue;
import tlc2.value.ValueEnumeration;
import tlc2.value.ValueExcept;
import tlc2.value.ValueOutputStream;
import tlc2.value.Values;
import util.Assert;
import util.UniqueString;

public class FcnLambdaValue extends Value implements Applicable, IFcnLambdaValue {
  public final FcnParams params;       // the function formals
  public final SemanticNode body;      // the function body
  public ValueExcept[] excepts;  // the EXCEPTs
  public final ITool tool;
  public Context con;
  public final TLCState state;
  public final TLCState pstate;
  public int control;
  public FcnRcdValue fcnRcd;

  /* Constructor */
  public FcnLambdaValue(FcnParams params, SemanticNode body, ITool tool,
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

  public FcnLambdaValue(FcnParams params, SemanticNode body, ITool tool,
	      Context c, TLCState s0, TLCState s1, int control, CostModel cm) {
	  this(params, body, tool, c, s0, s1, control);
	  this.cm = cm;
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
    try {
      this.con = this.con.cons(fname, this);
      this.control = EvalControl.setKeepLazy(this.control);
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

  public final int compareTo(Object obj) {
    try {
      FcnRcdValue fcn = (FcnRcdValue) this.toFcnRcd();
      return fcn.compareTo(obj);
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

  public final boolean equals(Object obj) {
    try {
      FcnRcdValue fcn = (FcnRcdValue) this.toFcnRcd();
      return fcn.equals(obj);
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

  public final boolean member(IValue elem) {
    try {
      Assert.fail("Attempted to check if the value:\n" + Values.ppr(elem.toString()) +
      "\nis an element of the function " + Values.ppr(this.toString()));
      return false;   // make compiler happy
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

  public final boolean isFinite() {
    try {
      Assert.fail("Attempted to check if the function:\n" + Values.ppr(this.toString()) +
      "\nis a finite set.");
      return false;   // make compiler happy
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

  /* Apply this function to the arguments given by args.  */
  public final IValue apply(IValue args, int control) throws EvalException {
    try {

      if (this.fcnRcd != null) {
        return this.fcnRcd.apply(args, control);
      }

      // First, find all the excepts that match args.
      IValue res = null;
      int num = 0;
      ValueExcept[] excepts1 = null;
      if (this.excepts != null) {
        int exlen = this.excepts.length;
        for (int i = exlen-1; i >= 0; i--) {
          ValueExcept ex = this.excepts[i];
          IValue arg = ex.current();
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
        IValue[] domains = this.params.domains;
        boolean[] isTuples = this.params.isTuples;
        int plen = this.params.length();

        if (plen == 1) {
          if (!domains[0].member(args)) {
            Assert.fail("In applying the function\n" + Values.ppr(this.toString()) +
            ",\nthe first argument is:\n" + Values.ppr(args.toString()) +
            "\nwhich is not in its domain.\n");
          }
          if (isTuples[0]) {
            FormalParamNode[] ids = formals[0];
            TupleValue argVal = (TupleValue) args.toTuple();
            if (argVal == null) {
              Assert.fail("In applying the function\n" + Values.ppr(this.toString()) +
              ",\nthe first argument is:\n" + Values.ppr(args.toString()) +
              "\nwhich does not match its formal parameter.\n");
            }
            if (argVal.size() != ids.length) return null;
            IValue[] elems = argVal.elems;
            for (int i = 0; i < ids.length; i++) {
              c1 = c1.cons(ids[i], elems[i]);
            }
          }
          else {
            c1 = c1.cons(formals[0][0], args);
          }
        }
        else {
          TupleValue tv = (TupleValue) args.toTuple();
          if (tv == null) {
            Assert.fail("In applying the function\n" + Values.ppr(this.toString()) +
                  ",\nthe argument list is:\n" + Values.ppr(args.toString()) +
                  "\nwhich does not match its formal parameter.\n");
          }
          IValue[] elems = tv.elems;
          int argn = 0;
          for (int i = 0; i < formals.length; i++) {
            FormalParamNode[] ids = formals[i];
            IValue domain = domains[i];
            if (isTuples[i]) {
              if (!domain.member(elems[argn])) {
                Assert.fail("In applying the function\n" + Values.ppr(this.toString()) +
                ",\nthe argument number " + (argn+1) + " is:\n" +
                Values.ppr(elems[argn].toString()) +
                "\nwhich is not in its domain.\n");
              }
              TupleValue tv1 = (TupleValue) elems[argn++].toTuple();
              if (tv1 == null || tv1.size() != ids.length) {
                Assert.fail("In applying the function\n" + Values.ppr(this.toString()) +
                ",\nthe argument number " + argn + " is:\n" +
                Values.ppr(elems[argn-1].toString()) +
                "\nwhich does not match its formal parameter.\n");
              }
              IValue[] avals = tv1.elems;
              for (int j = 0; j < ids.length; j++) {
                c1 = c1.cons(ids[j], avals[j]);
              }
            }
            else {
              for (int j = 0; j < ids.length; j++) {
                if (!domain.member(elems[argn])) {
                  Assert.fail("In applying the function\n" + Values.ppr(this.toString()) +
                        ",\nthe argument number " + (argn+1) + " is:\n" +
                        Values.ppr(elems[argn].toString()) + "\nwhich is not in its domain.\n");
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
    catch (RuntimeException | OutOfMemoryError e) {
      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

  /* This one does not seem to be needed anymore.  */
  public final IValue apply(IValue[] args, int control) throws EvalException {
    try {
      return this.apply(new TupleValue(args), control);
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

  public final IValue select(IValue arg) {
    try {

      if (this.fcnRcd != null) {
        return this.fcnRcd.select(arg);
      }

      // First, find all the excepts that match arg.
      IValue res = null;
      int num = 0;
      ValueExcept[] excepts1 = null;
      if (this.excepts != null) {
        int exlen = this.excepts.length;
        for (int i = exlen-1; i >= 0; i--) {
          ValueExcept ex = this.excepts[i];
          IValue exArg = ex.current();
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
        IValue[] domains = this.params.domains;
        boolean[] isTuples = this.params.isTuples;
        int plen = this.params.length();

        if (plen == 1) {
          if (!domains[0].member(arg)) return null;
          if (isTuples[0]) {
            FormalParamNode[] ids = formals[0];
            TupleValue argVal = (TupleValue) arg.toTuple();
            /*
             * SZA: Changed from argVal.toString() to arg.toString() to prevent a NullPointerException
             */
            if (argVal == null) {
              Assert.fail("In applying the function\n" + Values.ppr(this.toString()) +
              ",\nthe first argument is:\n" + Values.ppr(arg.toString()) +
              "\nwhich does not match its formal parameter.\n");
            }
            if (argVal.size() != ids.length) return null;
            IValue[] elems = argVal.elems;
            for (int i = 0; i < ids.length; i++) {
              c1 = c1.cons(ids[i], elems[i]);
            }
          }
          else {
            c1 = c1.cons(formals[0][0], arg);
          }
        }
        else {
          TupleValue tv = (TupleValue) arg.toTuple();
          if (tv == null) {
            Assert.fail("In applying the function\n" + Values.ppr(this.toString()) +
                  ",\nthe argument list is:\n" + Values.ppr(arg.toString()) +
                  "\nwhich does not match its formal parameter.\n");
          }
          IValue[] elems = tv.elems;
          int argn = 0;
          for (int i = 0; i < formals.length; i++) {
            FormalParamNode[] ids = formals[i];
            IValue domain = domains[i];
            if (isTuples[i]) {
              if (!domain.member(elems[argn])) return null;
              TupleValue tv1 = (TupleValue) elems[argn++].toTuple();
              if (tv1 == null) {
                Assert.fail("In applying the function\n" + Values.ppr(this.toString()) +
                ",\nthe argument number " + argn + " is:\n" +
                Values.ppr(elems[argn-1].toString()) +
                "\nwhich does not match its formal parameter.\n");
              }
              if (tv1.size() != ids.length) return null;
              IValue[] avals = tv1.elems;
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
    catch (RuntimeException | OutOfMemoryError e) {
      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

  /* This method returns a new function value by taking except. */
  public final IValue takeExcept(ValueExcept ex) {
    try {

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
    catch (RuntimeException | OutOfMemoryError e) {
      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

  /* This method returns a new function value by taking excepts. */
  public final IValue takeExcept(ValueExcept[] exs) {
    try {

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
    catch (RuntimeException | OutOfMemoryError e) {
      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

  public final IValue getDomain() {
    try {

      if (this.fcnRcd != null) {
        return this.fcnRcd.getDomain();
      }
      int len = this.params.length();
      if (len == 1) {
        return this.params.domains[0];
      }
      IValue[] sets = new IValue[len];
      int dlen = this.params.domains.length;
      boolean[] isTuples = this.params.isTuples;
      int idx = 0;
      for (int i = 0; i < dlen; i++) {
        FormalParamNode[] formal = this.params.formals[i];
        IValue domain = this.params.domains[i];
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
    catch (RuntimeException | OutOfMemoryError e) {
      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

  public final int size() {
    try {
      if (this.fcnRcd == null) {
        return this.params.size();
      }
      return this.fcnRcd.size();
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

  public final boolean isDefined() { return true; }

  public final IValue deepCopy() {
    try {
      FcnLambdaValue fcn = new FcnLambdaValue(this);
      // A bug occured when printing a function whose domain is a Cartesian product because this.fcnRcd 
      // is null at this point.  On 5 Mar 2012, LL wrapped the following null test around the assignment.
      if (this.fcnRcd != null) {
        fcn.fcnRcd = (FcnRcdValue)this.fcnRcd.deepCopy();
      }
      return fcn;
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

  public final boolean assignable(IValue val) {
    try {
      return (val instanceof FcnLambdaValue);
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

  private void readObject(ObjectInputStream ois) throws IOException, ClassNotFoundException {
    this.fcnRcd = (FcnRcdValue)ois.readObject();
  }

  private void writeObject(ObjectOutputStream oos) throws IOException {
    FcnRcdValue res = (FcnRcdValue) this.toFcnRcd();
    oos.writeObject(res);
  }

  public final boolean isNormalized() {
    try {
      if (this.fcnRcd == null) {
        return false;
      }
      return this.fcnRcd.isNormalized();
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

  public final IValue normalize() {
    try {
      if (this.fcnRcd != null) {
        this.fcnRcd.normalize();
      }
      return this;
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

  @Override
  public final void deepNormalize() {
	    try {
      if (fcnRcd == null) {
        if (excepts != null) {
          for (int i = 0; i < excepts.length; i++) {
            excepts[i].value.deepNormalize();
            for (int j = 0; j < excepts[i].path.length; j++) {
        excepts[i].path[j].deepNormalize();
            }
          }
        }
        IValue[] paramDoms = params.domains;
        for (int i = 0; i < paramDoms.length; i++) {
          paramDoms[i].deepNormalize();
        }
      }
      else {
        fcnRcd.deepNormalize();
      }
	    }
	    catch (RuntimeException | OutOfMemoryError e) {
	      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
	      else { throw e; }
	    }
  }

  @Override
  public final IValue toTuple() {
      if (this.params.length() != 1) return null;
      IValue dom = this.params.domains[0];
      SymbolNode var = this.params.formals[0][0];
      if (dom instanceof IntervalValue) {
        IntervalValue intv = (IntervalValue)dom;
        if (intv.low != 1) return null;
        IValue[] elems = new IValue[intv.high];
        for (int i = 1; i <= intv.high; i++) {
          Context c1 = this.con.cons(var, IntValue.gen(i));
          elems[i-1] = this.tool.eval(this.body, c1, this.state, this.pstate, this.control);
        }
        if (coverage) {cm.incSecondary(elems.length);}
        return new TupleValue(elems, cm);
      }
      else {
        SetEnumValue eSet = (SetEnumValue) dom.toSetEnum();
        if (eSet == null)
          Assert.fail("To convert a function of form [x \\in S |-> f(x)] " +
                "to a tuple, the set S must be enumerable.");
        eSet.normalize();
        int len = eSet.size();
        IValue[] elems = new IValue[len];
        for (int i = 0; i < len; i++) {
          IValue argVal = eSet.elems.elementAt(i);
          if (!(argVal instanceof IntValue)) return null;
          if (((IntValue)argVal).val != i + 1) return null;
          Context c1 = this.con.cons(var, argVal);
          elems[i] = this.tool.eval(this.body, c1, this.state, this.pstate, this.control);
        }
        cm.incSecondary(elems.length);
        return new TupleValue(elems, cm);
      }
  }

  @Override
  public final IValue toRcd() {
      FcnRcdValue fcn = (FcnRcdValue) this.toFcnRcd();
      if (fcn == null || fcn.domain == null) { return null; }
      fcn.normalize();
      UniqueString[] vars = new UniqueString[fcn.domain.length];
      for (int i = 0; i < fcn.domain.length; i++) {
        if (!(fcn.domain[i] instanceof StringValue)) {
          return null;
        }
        vars[i] = ((StringValue)fcn.domain[i]).getVal();
      }
      if (coverage) {cm.incSecondary(vars.length);}
      return new RecordValue(vars, fcn.values, fcn.isNormalized(), cm);
  }

  @Override
  public final IValue toFcnRcd() {
    try {

      if (this.fcnRcd == null) {
        int sz = this.params.size();
        FormalParamNode[][] formals = this.params.formals;
        boolean[] isTuples = this.params.isTuples;

        IValue[] domain = new IValue[sz];
        IValue[] values = new IValue[sz];
        int idx = 0;
        ValueEnumeration Enum = this.params.elements();
        IValue arg;
        if (this.params.length() == 1) {
          while ((arg = Enum.nextElement()) != null) {
            domain[idx] = arg;
            Context c1 = this.con;
            if (isTuples[0]) {
              FormalParamNode[] ids = formals[0];
              IValue[] avals = ((TupleValue)arg).elems;
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
            IValue[] argList = ((TupleValue)arg).elems;
            int argn = 0;
            Context c1 = this.con;
            for (int i = 0; i < formals.length; i++) {
              FormalParamNode[] ids = formals[i];
              if (isTuples[i]) {
                IValue[] avals = ((TupleValue)argList[argn++]).elems;
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
        if (coverage) {cm.incSecondary(sz);}
        this.fcnRcd = new FcnRcdValue(domain, values, false, cm);
        if (this.excepts != null) {
          this.fcnRcd = (FcnRcdValue)fcnRcd.takeExcept(this.excepts);
        }
      }
      return this.fcnRcd;

    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

	@Override
	public final void write(final ValueOutputStream vos) throws IOException {
		fcnRcd.write(vos);
	}
  
  /* The fingerprint methods.  */
  public final long fingerPrint(long fp) {
    try {
      IValue fcn = this.toFcnRcd();
      return fcn.fingerPrint(fp);
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

  public final IValue permute(IMVPerm perm) {
    try {
      IValue fcn = this.toFcnRcd();
      return fcn.permute(perm);
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

  /* The string representation of this function.  */
  public final StringBuffer toString(StringBuffer sb, int offset) {
    try {
      if (TLCGlobals.expand || this.params == null) {
        try {
          IValue val = this.toFcnRcd();
          return val.toString(sb, offset);
        }
        catch (Throwable e) { /*SKIP*/ }
      }
      sb.append("[" + this.params.toString());
      sb.append(" |-> <expression " + this.body + ">]");
      return sb;
    }
    catch (RuntimeException | OutOfMemoryError e) {
      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
      else { throw e; }
    }
  }

	@Override
	public final SemanticNode getBody() {
		return body;
	}
	
	@Override
	public final FcnRcdValue getRcd() {
		return fcnRcd;
	}

	@Override
	public FcnParams getParams() {
		return params;
	}

	@Override
	public Context getCon() {
		return con;
	}
}
