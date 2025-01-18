--------------------------- MODULE RecordsTest ------------------------------
EXTENDS Semantics
CONSTANT (* ID: c *) c
VARIABLE (* ID: v *) v

THEOREM ConstantRecord == IsLevel([
    x |-> IsLevel(RefersTo(c, "c"), ConstantLevel),
    y |-> IsLevel(RefersTo(c, "c"), ConstantLevel)
  ],
  ConstantLevel
)

THEOREM ConstantRecordSet == IsLevel([
    x : IsLevel(RefersTo(c, "c"), ConstantLevel),
    y : IsLevel(RefersTo(c, "c"), ConstantLevel)
  ],
  ConstantLevel
)

THEOREM VariableRecord == IsLevel([
    x |-> IsLevel(RefersTo(v, "v"), VariableLevel),
    y |-> IsLevel(RefersTo(c, "c"), ConstantLevel)
  ],
  VariableLevel
)

THEOREM VariableRecordSet == IsLevel([
    x : IsLevel(RefersTo(v, "v"), VariableLevel),
    y : IsLevel(RefersTo(c, "c"), ConstantLevel)
  ],
  VariableLevel
)

THEOREM ActionRecord == IsLevel([
    x |-> IsLevel(RefersTo(v, "v")', ActionLevel),
    y |-> IsLevel(RefersTo(c, "c"), ConstantLevel)
  ],
  ActionLevel
)

THEOREM ActionRecordSet == IsLevel([
    x : IsLevel(RefersTo(v, "v")', ActionLevel),
    y : IsLevel(RefersTo(c, "c"), ConstantLevel)
  ],
  ActionLevel
)

THEOREM TemporalRecord == IsLevel([
    x |-> IsLevel([]RefersTo(v, "v"), TemporalLevel),
    y |-> IsLevel(RefersTo(c, "c"), ConstantLevel)
  ],
  TemporalLevel
)

=============================================================================
