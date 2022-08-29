// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Last modified on Mon 30 Apr 2007 at 13:26:42 PST by lamport
//      modified on Fri Jun 11 16:16:03 PDT 1999 by yuanyu

package tlc2.util;

import util.WrongInvocationException;

import java.io.PrintWriter;
import java.util.Hashtable;

public abstract class Sx {

    public static final SxNil nil = new SxNil();

    private static final Hashtable<String, SxAtom> atomTbl = new Hashtable<>();
    private static int symCount = 0;  // Number of symbols returned by genSym().

    public static Sx cons(final Sx a, final Sx b) {
        return new SxPair(a, b);
    }

    public static Sx car(final Sx a) {
        if (a instanceof SxPair p) {
            return p.car;
        } else {
            throw new WrongInvocationException("Car must be applied to cons.");
        }

    }

    public static Sx cdr(final Sx a) {
        if (a instanceof SxPair p) {
            return p.cdr;
        } else {
            throw new WrongInvocationException("Cdr must be applied to cons.");
        }

    }

    public static Sx List(final Sx a) {
        return cons(a, nil);
    }

    public static Sx List(final Sx a, final Sx b) {
        return cons(a, cons(b, nil));
    }

    public static Sx List(final Sx a, final Sx b, final Sx c) {
        return cons(a, cons(b, cons(c, nil)));
    }

    public static Sx List(final Sx a, final Sx b, final Sx c, final Sx d) {
        return cons(a, cons(b, cons(c, cons(d, nil))));
    }

    public static Sx Append(final Sx a, final Sx b) {
        if (a == nil) return b;
        return cons(car(a), Append(cdr(a), b));
    }

    // Successive calls to genSym return distinct atoms.
    public static SxAtom genSym() {
        return Atom("F__" + (symCount++));
    }

    /* Returns true iff a is eq to an element of list p. */
    public static boolean memq(final SxAtom a, Sx p) {
        while (p != nil) {
            if (a == car(p)) {
                return true;
            } else {
                p = cdr(p);
            }
        }
        return false;
    }

    public static SxAtom Atom(final String st) {
        SxAtom res = atomTbl.get(st);
        if (res == null) {
            res = new SxAtom(st);
            atomTbl.put(st, res);
        }
        return res;
    }

    public static Sx FromInt(final int k) {
        return new SxInt(k);
    }

    public abstract void print(PrintWriter pw);

    public static class SxAtom extends Sx {
        public final String st;

        private SxAtom(final String st) {
            this.st = st;
        }

        @Override
        public void print(final PrintWriter pw) {
            pw.print(this.st);
        }
    }

    public static class SxInt extends Sx {
        public final int val;

        public SxInt(final int k) {
            this.val = k;
        }

        @Override
        public void print(final PrintWriter pw) {
            pw.print(this.val);
        }
    }

    public static class SxNil extends Sx {
        private SxNil() { /*SKIP*/ }

        @Override
        public void print(final PrintWriter pw) {
            pw.print("nil");
        }
    }

    public static class SxPair extends Sx {
        public final Sx car;
        public final Sx cdr;

        public SxPair(final Sx a, final Sx b) {
            this.car = a;
            this.cdr = b;
        }

        @Override
        public void print(final PrintWriter pw) {
            pw.print("(");
            this.car.print(pw);
            Sx next = this.cdr;
            while (next instanceof SxPair p) {
                pw.print(" ");
                p.car.print(pw);
                next = p.cdr;
            }
            if (next != nil) {
                pw.print(" . ");
                next.print(pw);
            }
            pw.print(")");
        }
    }

}
