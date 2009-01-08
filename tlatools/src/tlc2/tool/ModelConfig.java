// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
// Last modified on Mon 30 Apr 2007 at 15:29:56 PST by lamport
//      modified on Thu Aug 23 17:46:39 PDT 2001 by yuanyu

package tlc2.tool;

import java.io.*;
import java.util.Hashtable;
import tla2sany.parser.*;
import util.Assert;
import tlc2.value.*;
import tlc2.util.*;

public class ModelConfig implements ValueConstants, Serializable {
  /* Get information from user's model configuration file.  */

  private static final String Constant = "CONSTANT";
  private static final String Constants = "CONSTANTS";
  private static final String Constraint = "CONSTRAINT";
  private static final String Constraints = "CONSTRAINTS";
  private static final String ActionConstraint = "ACTION_CONSTRAINT";
  private static final String ActionConstraints = "ACTION_CONSTRAINTS";
  private static final String Invariant = "INVARIANT";
  private static final String Invariants = "INVARIANTS";
  private static final String Init = "INIT";
  private static final String Next = "NEXT";
  private static final String View = "VIEW";  
  private static final String Symmetry = "SYMMETRY";
  private static final String Spec = "SPECIFICATION";
  private static final String Prop = "PROPERTY";  
  private static final String Props = "PROPERTIES";
  private static final String Type = "TYPE";
  private static final String TypeConstraint = "TYPE_CONSTRAINT";

  private Hashtable configTbl;
  private Hashtable overrides;  
  private Hashtable modConstants;
  private Hashtable modOverrides;
  private File configFile;

  public ModelConfig(String file) {
    this.configFile = new File(file);
    this.configTbl = new Hashtable();
    Vect temp = new Vect();    
    this.configTbl.put(Constant, temp);
    this.configTbl.put(Constants, temp);
    temp = new Vect();
    this.configTbl.put(Constraint, temp);
    this.configTbl.put(Constraints, temp);
    temp = new Vect();
    this.configTbl.put(ActionConstraint, temp);
    this.configTbl.put(ActionConstraints, temp);
    temp = new Vect();
    this.configTbl.put(Invariant, temp);
    this.configTbl.put(Invariants, temp);
    this.configTbl.put(Init, "");
    this.configTbl.put(Next, "");
    this.configTbl.put(View, "");
    this.configTbl.put(Symmetry, "");
    this.configTbl.put(Spec, "");
    temp = new Vect();
    this.configTbl.put(Prop, temp);
    this.configTbl.put(Props, temp);
    this.configTbl.put(Type, "");
    this.configTbl.put(TypeConstraint, "");

    this.modConstants = new Hashtable();
    this.modOverrides = new Hashtable();
    this.overrides = new Hashtable();
  }

  public synchronized final Vect getConstants() {
    return (Vect)this.configTbl.get(Constant);
  }

  public synchronized final Hashtable getModConstants() {
    return this.modConstants;
  }

  public synchronized final Hashtable getOverrides() {
    return this.overrides;
  }

  public synchronized final Hashtable getModOverrides() {
    return this.modOverrides;
  }
  
  public synchronized final Vect getConstraints() {
    return (Vect)this.configTbl.get(Constraint);
  }

  public synchronized final Vect getActionConstraints() {
    return (Vect)this.configTbl.get(ActionConstraint);
  }
  
  public synchronized final String getInit() {
    return (String)this.configTbl.get(Init);
  }

  public synchronized final String getNext() {
    return (String)this.configTbl.get(Next);
  }

  public synchronized final String getView() {
    return (String)this.configTbl.get(View);
  }

  public synchronized final String getSymmetry() {
    return (String)this.configTbl.get(Symmetry);
  }
  
  public synchronized final Vect getInvariants() {
    return (Vect)this.configTbl.get(Invariant);
  }

  public synchronized final String getSpec() {
    return (String)this.configTbl.get(Spec);
  }

  public synchronized final Vect getProperties() {
    return (Vect)this.configTbl.get(Prop);
  }

  public synchronized final String getType() {
    return (String)this.configTbl.get(Type);
  }

  public synchronized final String getTypeConstraint() {
    return (String)this.configTbl.get(TypeConstraint);
  }

  public static Token getNextToken(TLAplusParserTokenManager tmgr) {
    try {
      return tmgr.getNextToken();
    }
    catch (TokenMgrError e) {
      Token tt = new Token();
      tt.kind = TLAplusParserConstants.EOF;
      return tt;
    }
  }
  
  public final void parse() {
    Vect constants = (Vect)this.configTbl.get(Constant);
    Vect constraints = (Vect)this.configTbl.get(Constraint);
    Vect actionConstraints = (Vect)this.configTbl.get(ActionConstraint);    
    Vect invariants = (Vect)this.configTbl.get(Invariant);
    Vect props = (Vect)this.configTbl.get(Prop);
    try {
      FileInputStream fis = new FileInputStream(this.configFile);
      SimpleCharStream scs = new SimpleCharStream(fis, 1, 1);
      TLAplusParserTokenManager tmgr = new TLAplusParserTokenManager(scs, 2);

      Token tt = getNextToken(tmgr);
      while (tt.kind != TLAplusParserConstants.EOF) {
	String tval = tt.image;
	int loc = scs.getBeginLine();
	if (tval.equals(Init)) {
	  tt = getNextToken(tmgr);
	  if (tt.kind == TLAplusParserConstants.EOF) {
	    Assert.fail("TLC found an error in the configuration file at line " +
			loc + "\nThe keyword INIT was not followed by an identifier.\n");
	  }
	  String old = (String)this.configTbl.put(Init, tt.image);
	  if (old.length() != 0) {
	    Assert.fail("TLC found an error in the configuration file at line " +
			loc + "\nThe keyword INIT appeared twice.\n");
	  }
	  tt = getNextToken(tmgr);
	}
	else if (tval.equals(Next)) {
	  tt = getNextToken(tmgr);
	  if (tt.kind == TLAplusParserConstants.EOF) {
	    Assert.fail("TLC found an error in the configuration file at line " +
			loc + "\nThe keyword NEXT was not followed by an identifier.\n");
	  }
	  String old = (String)this.configTbl.put(Next, tt.image);
	  if (old.length() != 0) {
	    Assert.fail("TLC found an error in the configuration file at line " +
			loc + "\nThe keyword NEXT appeared twice.\n");
	  }
	  tt = getNextToken(tmgr);
	}
	else if (tval.equals(Spec)) {
	  tt = getNextToken(tmgr);
	  if (tt.kind == TLAplusParserConstants.EOF) {
	    Assert.fail("TLC found an error in the configuration file at line " +
			loc + "\nThe keyword SPECIFICATION was not followed by " +
			"an identifier.\n");
	  }
	  String old = (String)this.configTbl.put(Spec, tt.image);
	  if (old.length() != 0) {
	    Assert.fail("TLC found an error in the configuration file at line " +
			loc + "\nThe keyword SPECIFICATION appeared twice.\n");
	  }
	  tt = getNextToken(tmgr);
	}
	else if (tval.equals(View)) {
	  tt = getNextToken(tmgr);
	  if (tt.kind == TLAplusParserConstants.EOF) {
	    Assert.fail("TLC found an error in the configuration file at line " +
			loc + "\nThe keyword VIEW was not followed by an identifier.\n");
	  }
	  String old = (String)this.configTbl.put(View, tt.image);
	  if (old.length() != 0) {
	    Assert.fail("TLC found an error in the configuration file at line " +
			loc + "\nThe keyword VIEW appeared twice.\n");
	  }
	  tt = getNextToken(tmgr);
	}
	else if (tval.equals(Symmetry)) {
	  tt = getNextToken(tmgr);
	  if (tt.kind == TLAplusParserConstants.EOF) {
	    Assert.fail("TLC found an error in the configuration file at line " +
			loc + "\nThe keyword SYMMETRY was not followed by " +
			"an identifier.\n");
	  }
	  String old = (String)this.configTbl.put(Symmetry, tt.image);
	  if (old.length() != 0) {
	    Assert.fail("TLC found an error in the configuration file at line " +
			loc + "\nThe keyword SYMMETRY appeared twice.\n");
	  }
	  tt = getNextToken(tmgr);
	}
	else if (tval.equals(Type)) {
	  tt = getNextToken(tmgr);
	  if (tt.kind == TLAplusParserConstants.EOF) {
	    Assert.fail("TLC found an error in the configuration file at line " +
			loc + "\nThe keyword TYPE was not followed by an identifier.\n");
	  }
	  String old = (String)this.configTbl.put(Type, tt.image);
	  if (old.length() != 0) {
	    Assert.fail("TLC found an error in the configuration file at line " +
			loc + "\nThe keyword TYPE appeared twice.\n");
	  }
	  tt = getNextToken(tmgr);
	}
	else if (tval.equals(TypeConstraint)) {
	  tt = getNextToken(tmgr);
	  if (tt.kind == TLAplusParserConstants.EOF) {
	    Assert.fail("TLC found an error in the configuration file at line " +
			loc + "\nThe keyword TYPE-CONSTRAINT was not " +
			"followed by an identifier.\n");
	  }
	  String old = (String)this.configTbl.put(TypeConstraint, tt.image);
	  if (old.length() != 0) {
	    Assert.fail("TLC found an error in the configuration file at line " +
			loc + "\nThe keyword TYPE-CONSTRAINT appeared twice.\n");
	  }
	  tt = getNextToken(tmgr);
	}
	else if (tval.equals(Constant) || tval.equals(Constants)) {
	  while ((tt = getNextToken(tmgr)).kind != TLAplusParserConstants.EOF) {
	    if (this.configTbl.get(tt.image) != null) break;
	    Vect line = new Vect();
	    line.addElement(tt.image);
	    tt = getNextToken(tmgr);
	    if (tt.image.equals("<-")) {
	      tt = getNextToken(tmgr);
	      if (tt.image.equals("[")) {
		// This is a module override:
		tt = getNextToken(tmgr);
		if (tt.kind == TLAplusParserConstants.EOF) {
		  Assert.fail("TLC found an error in the configuration file at line " +
			      scs.getBeginLine() + ".\nExpect an identifier after <-[.\n");
		}
		String modName = tt.image;
		tt = getNextToken(tmgr);
		if (!tt.image.equals("]")) {
		  Assert.fail("TLC found an error in the configuration file at line " +
			      scs.getBeginLine() + ".\nIt was expecting ], but did not find one.\n");
		}
		tt = getNextToken(tmgr);
		if (tt.kind == TLAplusParserConstants.EOF) {
		  Assert.fail("TLC found an error in the configuration file at line " +
			      scs.getBeginLine() + ".\nExpect an identifier after <-[mod].\n");
		}
		Hashtable defs = (Hashtable)this.modOverrides.get(modName);
		if (defs == null) {
		  defs = new Hashtable();
		  this.modOverrides.put(modName, defs);
		}
		defs.put(line.elementAt(0), tt.image);
	      }
	      else {
		// This is a main module override:
		if (tt.kind == TLAplusParserConstants.EOF) {
		  Assert.fail("TLC found an error in the configuration file at line " +
			      scs.getBeginLine() + ".\nThe symbol <- was not followed by an " +
			      "identifier.\n");
		}
		this.overrides.put(line.elementAt(0), tt.image);
	      }
	    }
	    else {
	      if (tt.image.equals("(")) {
		while (true) {
		  tt = getNextToken(tmgr);
		  Value arg = this.parseValue(tt, scs, tmgr);
		  line.addElement(arg);
		  tt = getNextToken(tmgr);
		  if (!tt.image.equals(",")) break;
		}
		if (!tt.image.equals(")")) {
		  Assert.fail("TLC found an error in the configuration file at line " +
			      scs.getBeginLine());
		}
		tt = getNextToken(tmgr);
	      }
	      if (!tt.image.equals("=")) {
		Assert.fail("TLC found an error in the configuration file at line " +
			    scs.getBeginLine() + ".\nIt was expecting = or <- and didn't " +
			    "find it.\n");
	      }
	      tt = getNextToken(tmgr);
	      if (tt.image.equals("[")) {
		// This is a module specific override:
		tt = getNextToken(tmgr);
		if (tt.kind == TLAplusParserConstants.EOF) {
		  Assert.fail("TLC found an error in the configuration file at line " +
			      scs.getBeginLine() + ".\nExpect an identifier after =[.\n");
		}
		String modName = tt.image;
		tt = getNextToken(tmgr);
		if (!tt.image.equals("]")) {
		  Assert.fail("TLC found an error in the configuration file at line " +
			      scs.getBeginLine() + ".\nIt was expecting ], but did not find one.\n");
		}
		tt = getNextToken(tmgr);
		line.addElement(this.parseValue(tt, scs, tmgr));
		Vect mConsts = (Vect)this.modConstants.get(modName);
		if (mConsts == null) {
		  mConsts = new Vect();
		  this.modConstants.put(modName, mConsts);
		}
		mConsts.addElement(line);
	      }
	      else {
		// This is a main module override:
		line.addElement(this.parseValue(tt, scs, tmgr));
		constants.addElement(line);
	      }
	    }
	  }
	}
	else if (tval.equals(Invariant) || tval.equals(Invariants)) {
	  while ((tt = getNextToken(tmgr)).kind != TLAplusParserConstants.EOF) {
	    if (this.configTbl.get(tt.image) != null) break;
	    invariants.addElement(tt.image);
	  }
	}
	else if (tval.equals(Prop) || tval.equals(Props)) {
	  while ((tt = getNextToken(tmgr)).kind != TLAplusParserConstants.EOF) {
	    if (this.configTbl.get(tt.image) != null) break;
	    props.addElement(tt.image);
	  }
	}
	else if (tval.equals(Constraint) || tval.equals(Constraints)) {
	  while ((tt = getNextToken(tmgr)).kind != TLAplusParserConstants.EOF) {
	    if (this.configTbl.get(tt.image) != null) break;
	    constraints.addElement(tt.image);
	  }
	}
	else if (tval.equals(ActionConstraint) || tval.equals(ActionConstraints)) {
	  while ((tt = getNextToken(tmgr)).kind != TLAplusParserConstants.EOF) {
	    if (this.configTbl.get(tt.image) != null) break;
	    actionConstraints.addElement(tt.image);
	  }
	}
	else {
	  Assert.fail("TLC found an error in the configuration file at line " +
		      loc + ".\nIt was expecting a keyword and didn't find it.\n");
	}
      }
    }
    catch (IOException e) {
      Assert.fail("TLC encountered the following error when trying to read " +
		  "the configuration file " + this.configFile.getName() + ":\n" +
		  e.getMessage());
    }
  }

  private final Value parseValue(Token tt,
				 SimpleCharStream scs,
				 TLAplusParserTokenManager tmgr)
  throws IOException {
    if (tt.kind == TLAplusParserConstants.NUMBER_LITERAL) {
      int val = Integer.parseInt(tt.image);
      return IntValue.gen(val);
    }
    else if (tt.kind == TLAplusParserConstants.STRING_LITERAL) {
      String tval = tt.image;
      return new StringValue(tval.substring(1, tval.length()-1));
    }
    else if (tt.image.equals("TRUE")) {
      return ValTrue;
    }
    else if (tt.image.equals("FALSE")) {
      return ValFalse;
    }
    else if (tt.image.equals("{")) {
      ValueVec elems = new ValueVec();
      tt = getNextToken(tmgr);
      if (!tt.image.equals("}")) {
	while (true) {
	  Value elem = this.parseValue(tt, scs, tmgr);
	  elems.addElement(elem);
	  tt = getNextToken(tmgr);
	  if (!tt.image.equals(",")) break;
	  tt = getNextToken(tmgr);
	}
      }
      if (!tt.image.equals("}")) {
	Assert.fail("TLC found an error in the configuration file at line " +
		    scs.getBeginLine() + ".\nIt was expecting `}' but didn't find it.\n");
      }
      return new SetEnumValue(elems, false);
    }
    else if (tt.kind != TLAplusParserConstants.EOF) {
      return ModelValue.make(tt.image);
    }
    Assert.fail("TLC found an error in the configuration file at line " +
		scs.getBeginLine() + ".\nIt was expecting a value, but didn't find it.\n");
    return null;   // make compiler happy
  }

  public static void main(String[] args) {
    try {
      FileInputStream fis = new FileInputStream(args[0]);
      SimpleCharStream scs = new SimpleCharStream(fis, 1, 1);    
      TLAplusParserTokenManager tmgr = new TLAplusParserTokenManager(scs, 2);

      Token t = getNextToken(tmgr);
      while (t.kind != 0) {
	System.err.println(t);
	t = getNextToken(tmgr);
      }
    }
    catch (Exception e) { System.err.println(e.getMessage()); }
  }
  
}
