// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Last modified on Sat 23 February 2008 at  9:52:47 PST by lamport
//      modified on Tue Jan  2 21:36:16 PST 2001 by yuanyu

package tlc2.module;

import tlc2.tool.EvalException;
import tlc2.tool.TLARegistry;
import tlc2.value.BoolValue;
import tlc2.value.IntValue;
import tlc2.value.IntervalValue;
import tlc2.value.ModelValue;
import tlc2.value.UserObj;
import tlc2.value.UserValue;
import tlc2.value.Value;
import tlc2.value.ValueConstants;

public class Naturals extends UserObj implements ValueConstants {

  static {
    TLARegistry.put("Plus", "+");
    TLARegistry.put("Minus", "-");
    TLARegistry.put("Times", "*");    
    TLARegistry.put("LT", "<");
    TLARegistry.put("LE", "\\leq");
    TLARegistry.put("GT", ">");
    TLARegistry.put("GEQ", "\\geq");
    TLARegistry.put("DotDot", "..");
    TLARegistry.put("Divide", "\\div");
    TLARegistry.put("Mod", "%");
    TLARegistry.put("Expt", "^");
  }
  
  private static Value SetNat = new UserValue(new Naturals());

  public static Value Nat() { return SetNat; }

  public static IntValue Plus(IntValue x, IntValue y) {
    int n1 = x.val;
    int n2 = y.val;
    int res = n1 + n2;
    if ((n1 < 0) == (n2 < 0) && (n2 < 0) != (res < 0)) {
      throw new EvalException("Overflow when computing " + n1 + "+" + n2);
    }
    return IntValue.gen(res);
  }

  public static IntValue Minus(IntValue x, IntValue y) {
    int n1 = x.val;
    int n2 = y.val;
    int res = n1 - n2;
    if ((n1 < 0) != (n2 < 0) && (n1 < 0) != (res < 0)) {
      throw new EvalException("Overflow when computing " + n1 + "-" + n2);
    }
    return IntValue.gen(res);
  }

  public static IntValue Times(IntValue x, IntValue y) {
    int n1 = x.val;
    int n2 = y.val;
    long res = n1 * n2;
    if (-2147483648 > res || res > 2147483647) {
      throw new EvalException("Overflow when computing " + n1 + "*" + n2);
    }
    return IntValue.gen((int)res);
  }

  public static BoolValue LT(Value x, Value y) {
    if (!(x instanceof IntValue)) {
      String msg = "The first argument of < must be an integer" +
	", but instead it is\n" + Value.ppr(x.toString());
      throw new EvalException(msg);
    }
    if (!(y instanceof IntValue)) {
      String msg = "The second argument of < must be an integer" +
	", but instead it is\n" + Value.ppr(y.toString());
      throw new EvalException(msg);
    }

    return (((IntValue)x).val < ((IntValue)y).val) ? ValTrue : ValFalse;
  }

  public static BoolValue LE(Value x, Value y) {
    if (!(x instanceof IntValue)) {
      String msg = "The first argument of <= must be an integer" +
	", but instead it is\n" + Value.ppr(x.toString());
      throw new EvalException(msg);
    }
    if (!(y instanceof IntValue)) {
      String msg = "The second argument of <= must be an integer" +
	", but instead it is\n" + Value.ppr(y.toString());
      throw new EvalException(msg);
    }
    
    return (((IntValue)x).val <= ((IntValue)y).val) ? ValTrue : ValFalse;
  }

  public static BoolValue GT(Value x, Value y) {
    if (!(x instanceof IntValue)) {
      String msg = "The first argument of > must be an integer" +
	", but instead it is\n" + Value.ppr(x.toString());
      throw new EvalException(msg);
    }
    if (!(y instanceof IntValue)) {
      String msg = "The second argument of > must be an integer" +
	", but instead it is\n" + Value.ppr(y.toString());
      throw new EvalException(msg);
    }

    return (((IntValue)x).val > ((IntValue)y).val) ? ValTrue : ValFalse;
  }

  public static BoolValue GEQ(Value x, Value y) {
    if (!(x instanceof IntValue)) {
      String msg = "The first argument of >= must be an integer" +
	", but instead it is\n" + Value.ppr(x.toString());
      throw new EvalException(msg);
    }
    if (!(y instanceof IntValue)) {
      String msg = "The second argument of >= must be an integer" +
	", but instead it is\n" + Value.ppr(y.toString());
      throw new EvalException(msg);
    }

    return (((IntValue)x).val >= ((IntValue)y).val) ? ValTrue : ValFalse;
  }

  public static IntervalValue DotDot(IntValue x, IntValue y) {
    return new IntervalValue(x.val, y.val);
  }

  public static IntValue Divide(IntValue x, IntValue y) {
    int n1 = x.val;
    int n2 = y.val;
    if (n2 == 0) {
      throw new EvalException("The second argument of \\div is 0.");
    }
    int q = n1 / n2;
    if ((q < 0) && (q*n2 != n1)) q--;
    return IntValue.gen(q);
  }

  public static IntValue Mod(IntValue x, IntValue y) {
    int n1 = x.val;
    int n2 = y.val;
    if (n2 <= 0) {
      String msg = "The second argument of % should be a positive" +
	" number; but instead it is:\n" + n2;
      throw new EvalException(msg);
    }
    int r = n1 % n2;
    return IntValue.gen(r < 0 ? (r+n2) : r);
  }

  public static IntValue Expt(IntValue x, IntValue y) {
    int n1 = x.val;
    int n2 = y.val;
    if (n2 < 0) {
      String msg = "The second argument of ^ should be a natural" +
	" number; but instead it is: " + n2;
      throw new EvalException(msg);
    }
    if (n2 == 0) {
      if (n1 == 0) {
	throw new EvalException("0^0 is undefined.");
      }
      return ValOne;
    }
    long res = n1;
    for (int i = 1; i < n2; i++) {
      res *= n1;
      if (res < -2147483648 || res > 2147483647) {
	throw new EvalException("Overflow when computing " + n1 + "^" + n2);
      }
    }
    return IntValue.gen((int)res);
  }

  public final int compareTo(Value val) {
    if (val instanceof UserValue) {
      if (((UserValue)val).userObj instanceof Naturals) {
	return 0;
      }
      if (((UserValue)val).userObj instanceof Integers) {
	return -1;
      }
    }
    if (val instanceof ModelValue) return 1;
    String msg = "Comparing Nat with the value\n" + Value.ppr(val.toString());
    throw new EvalException(msg);
  }

  public final boolean member(Value val) {
    if (val instanceof IntValue) return ((IntValue)val).val >= 0;
    if (val instanceof ModelValue) 
      return ((ModelValue) val).modelValueMember(this) ;
    throw new EvalException("Checking if the value:\n" + Value.ppr(val.toString()) +
			    "\nis an element of Nat.");
  }

  public final boolean isFinite() { return false; }
  
  public final StringBuffer toString(StringBuffer sb, int offset) {
    return sb.append("Nat");
  }
}
