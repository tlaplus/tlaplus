// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Last modified on Mon 30 Apr 2007 at 13:26:42 PST by lamport
//      modified on Fri Jun 11 16:16:03 PDT 1999 by yuanyu

package tlc2.util;

import java.io.PrintWriter;
import java.util.Hashtable;

import util.WrongInvocationException;

public abstract class Sx {

  public static SxNil nil = new SxNil();

  private static Hashtable atomTbl = new Hashtable();
  private static int symCount = 0;  // Number of symbols returned by genSym().
  
  public static Sx cons(Sx a, Sx b) {
    return new SxPair(a, b);
  }

  public static Sx car(Sx a) {
    if (!(a instanceof SxPair)) {
        throw new WrongInvocationException("Car must be applied to cons.");
    }
    return ((SxPair)a).car;
  }

  public static Sx cdr(Sx a) {
    if (!(a instanceof SxPair)) {
        throw new WrongInvocationException("Cdr must be applied to cons.");
    }
    return ((SxPair)a).cdr;
  }
    
  public static Sx List(Sx a) { return cons(a, nil); }

  public static Sx List(Sx a, Sx b) {
    return cons(a, cons(b, nil));
  }

  public static Sx List(Sx a, Sx b, Sx c) {
    return cons(a, cons(b, cons(c, nil)));
  }

  public static Sx List(Sx a, Sx b, Sx c, Sx d) {
    return cons(a, cons(b, cons(c, cons(d, nil))));
  }

  public static Sx Append(Sx a, Sx b) {
    if (a == nil) return b;
    return cons(car(a), Append(cdr(a), b));
  }

  // Successive calls to genSym return distinct atoms.
  public static SxAtom genSym() {
    return Atom("F__" + (symCount++));
  }
  
  /* Returns true iff a is eq to an element of list p. */
  public static boolean memq(SxAtom a, Sx p) {
    while (p != nil) {
      if (a == car(p)) {
	return true;
      }
      else {
	p = cdr(p);
      }
    }
    return false;
  }
  
  public static SxAtom Atom(String st) {
    SxAtom res = (SxAtom)atomTbl.get(st);
    if (res == null) {
      res = new SxAtom(st);
      atomTbl.put(st, res);
    }
    return res;
  }

  public static Sx FromInt(int k) { return new SxInt(k); }
  
  public abstract void print(PrintWriter pw);
  
  public static class SxAtom extends Sx {
    public String st;
  
    private SxAtom(String st) { this.st = st; }

    public void print(PrintWriter pw) { pw.print(this.st); }
  }

  public static class SxInt extends Sx {
    public int val;
  
    public SxInt(int k) { this.val = k; }

    public void print(PrintWriter pw) { pw.print(this.val); }
  }

  public static class SxNil extends Sx {
    private SxNil() { /*SKIP*/ }

    public void print(PrintWriter pw) { pw.print("nil"); }
  }
  
  public static class SxPair extends Sx {
    public Sx car, cdr;
  
    public SxPair(Sx a, Sx b) {
      this.car = a;
      this.cdr = b;
    }

    public void print(PrintWriter pw) {
      pw.print("(");
      this.car.print(pw);
      Sx next = this.cdr;
      while (next instanceof SxPair) {
	pw.print(" ");
	((SxPair)next).car.print(pw);
	next = ((SxPair)next).cdr;
      }
      if (next != nil) { pw.print(" . "); next.print(pw); }
      pw.print(")");
    }
  }

}
