// Copyright (c) 2003 Compaq Corporation.  All rights reserved.
// Portions Copyright (c) 2003 Microsoft Corporation.  All rights reserved.
package tla2sany.semantic;

import java.util.HashSet;

public interface LevelConstants {

    int ConstantLevel = 0;
    int VariableLevel = 1;
    int ActionLevel = 2;
    int TemporalLevel = 3;

    int MinLevel = 0;
    int MaxLevel = 3;

    Integer[] Levels = {ConstantLevel,
            VariableLevel,
            ActionLevel,
            TemporalLevel};

    HashSet<?> EmptySet = new HashSet<>();
    SetOfLevelConstraints EmptyLC = new SetOfLevelConstraints();
    SetOfArgLevelConstraints EmptyALC = new SetOfArgLevelConstraints();
}

