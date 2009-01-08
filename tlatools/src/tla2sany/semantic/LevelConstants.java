// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
package tla2sany.semantic;

import java.util.HashSet;

public interface LevelConstants {

  static final int ConstantLevel = 0;
  static final int VariableLevel = 1;
  static final int ActionLevel   = 2;
  static final int TemporalLevel = 3;

  static final int MinLevel      = 0;
  static final int MaxLevel      = 3;

  static final Integer[] Levels = {new Integer(ConstantLevel),
				   new Integer(VariableLevel),
				   new Integer(ActionLevel),
				   new Integer(TemporalLevel)};
  
  static final HashSet EmptySet = new HashSet();
  static final SetOfLevelConstraints EmptyLC = new SetOfLevelConstraints();
  static final SetOfArgLevelConstraints EmptyALC = new SetOfArgLevelConstraints();
}

