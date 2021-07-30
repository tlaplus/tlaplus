package tlc2.value.impl;

import java.io.IOException;

import tlc2.tool.FingerprintException;
import tlc2.util.FP64;
import tlc2.value.IMVPerm;
import tlc2.value.IValue;
import tlc2.value.IValueOutputStream;
import tlc2.value.Values;
import util.Assert;

public class CharValue extends Value {
	
	public final char val;
	
	public CharValue(char val) { this.val = val; }

	@Override
	public final int compareTo(Object obj) {
	    try {
	        if (obj instanceof CharValue) {
	          return Character.compare(this.val, ((CharValue)obj).val);
	        }
	        if (!(obj instanceof ModelValue)) {
	          Assert.fail("Attempted to compare character " + Values.ppr(this.toString()) +
	          " with non-char:\n" + Values.ppr(obj.toString()), getSource());
	        }
	        return 1;
	      }
	      catch (RuntimeException | OutOfMemoryError e) {
	        if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
	        else { throw e; }
	      }
	}

    public final boolean equals(Object obj) {
	    try {
	      if (obj instanceof CharValue) {
	        return this.val == ((CharValue)obj).val;
	      }
	      if (!(obj instanceof ModelValue)) {
	        Assert.fail("Attempted to check equality of character " + Values.ppr(this.toString()) +
	        " with non-character:\n" + Values.ppr(obj.toString()), getSource());
	      }
	      return ((ModelValue) obj).modelValueEquals(this);
	    }
	    catch (RuntimeException | OutOfMemoryError e) {
	      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
	      else { throw e; }
	    }
	  }

	@Override
	public final boolean member(Value elem) {
	    try {
	        Assert.fail("Attempted to check if the value:\n" + Values.ppr(elem.toString()) +
	        "\nis an element of the char " + Values.ppr(this.toString()), getSource());
	        return false;  // make compiler happy
	      }
	      catch (RuntimeException | OutOfMemoryError e) {
	        if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
	        else { throw e; }
	      }
	}

	@Override
	public final boolean isFinite() {    
		try {
			Assert.fail("Attempted to check if the character " + Values.ppr(this.toString()) +
		    	        " is a finite set.", getSource());
		    return false;   // make compiler happy
		} catch (RuntimeException | OutOfMemoryError e) {
			if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
			else { throw e; }
		}
	}

	@Override
	public final int size() {
	    try {
	        Assert.fail("Attempted to compute the number of elements in the character " +
	        Values.ppr(this.toString()) + ".", getSource());
	        return 0;   // make compiler happy
	      }
	      catch (RuntimeException | OutOfMemoryError e) {
	        if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
	        else { throw e; }
	      }
	}

	@Override
	public final boolean isNormalized() { return true; }

	@Override
	public final Value normalize() { return this; }

	@Override
	public final boolean isDefined() { return true;	}

	@Override
	public final IValue deepCopy() { return this; }

	@Override
	public final StringBuffer toString(StringBuffer sb, int offset, boolean swallow) {
	    try {
	        return sb.append('\'').append(this.val).append('\'');
	        //return sb.append('"').append(this.val).append("\"[1]");
	      }
	    catch (RuntimeException | OutOfMemoryError e) {
	        if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
	        else { throw e; }
	      }
	}

	@Override
	public final byte getKind() { return CHARVALUE; }

	@Override
	public final Value takeExcept(ValueExcept ex) {
	    try {
	        if (ex.idx < ex.path.length) {
	          Assert.fail("Attempted to appy EXCEPT construct to the character " +
	          Values.ppr(this.toString()) + ".", getSource());
	        }
	        return ex.value;
	      }
	      catch (RuntimeException | OutOfMemoryError e) {
	        if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
	        else { throw e; }
	      }
	}

	@Override
	public final Value takeExcept(ValueExcept[] exs) {
	    try {
	        if (exs.length != 0) {
	          Assert.fail("Attempted to apply EXCEPT construct to the character " +
	          Values.ppr(this.toString()) + ".", getSource());
	        }
	        return this;
	      }
	      catch (RuntimeException | OutOfMemoryError e) {
	        if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
	        else { throw e; }
	      }
	}

	@Override
	final boolean assignable(Value val) {    
		try {
			return ((val instanceof CharValue) &&
	    	        this.val == ((CharValue)val).val);
		} catch (RuntimeException | OutOfMemoryError e) {
			if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
			else { throw e; }
		}
	}

	@Override
	public final IValue permute(IMVPerm perm) { return this; }

	@Override
	public final long fingerPrint(long fp) {
	    try {
	      fp = FP64.Extend(fp, CHARVALUE) ;
	      fp = FP64.Extend(fp, this.val) ;
	      return fp;
	    }
	    catch (RuntimeException | OutOfMemoryError e) {
	      if (hasSource()) { throw FingerprintException.getNewHead(this, e); }
	      else { throw e; }
	    }
	  }
	
	@Override
	public final boolean mutates() { return false; }

	@Override
	public final void write(IValueOutputStream vos) throws IOException {
		vos.writeByte(CHARVALUE);
		vos.writeInt(val); // TODO: potentially provide writeCharacter method
	}
}
