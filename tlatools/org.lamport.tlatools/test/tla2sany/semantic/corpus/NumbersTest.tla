--------------------------- MODULE NumbersTest ------------------------------
EXTENDS Semantics, Naturals, Integers, Reals

ASSUME IsLevel(12345, ConstantLevel)
ASSUME IsLevel(12345.67890, ConstantLevel)
ASSUME IsLevel(\b01010101, ConstantLevel)
ASSUME IsLevel(\B10101010, ConstantLevel)
ASSUME IsLevel(\o01234567, ConstantLevel)
ASSUME IsLevel(\O76543210, ConstantLevel)
ASSUME IsLevel(\h01234, ConstantLevel)
ASSUME IsLevel(\h56789, ConstantLevel)
ASSUME IsLevel(\habcdef, ConstantLevel)
ASSUME IsLevel(\H98765, ConstantLevel)
ASSUME IsLevel(\H43210, ConstantLevel)
ASSUME IsLevel(\HFEDCBA, ConstantLevel)

ASSUME IsLevel(Nat, ConstantLevel)
ASSUME IsLevel(Int, ConstantLevel)
ASSUME IsLevel(Real, ConstantLevel)

=============================================================================

