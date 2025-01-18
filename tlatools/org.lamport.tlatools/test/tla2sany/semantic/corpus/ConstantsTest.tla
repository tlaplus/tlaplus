-------------------------- MODULE ConstantsTest -----------------------------
EXTENDS Semantics
CONSTANT
  (* ID: x *) x,
  (* ID: y *) y,
  (* ID: z *) z

ASSUME RefersTo(x, "x")
ASSUME RefersTo(y, "y")
ASSUME RefersTo(z, "z")
ASSUME IsLevel(x, ConstantLevel)
ASSUME IsLevel(y, ConstantLevel)
ASSUME IsLevel(z, ConstantLevel)

CONSTANTS
  (* ID: f *) f(_, _),
  (* ID: + *) _+_,
  (* ID: ^+ *) _^+

ASSUME RefersTo(f(1, 1), "f")
ASSUME RefersTo(1 + 1, "+")
ASSUME RefersTo(1^+, "^+")
ASSUME IsLevel(f(1, 1), ConstantLevel)
ASSUME IsLevel(1 + 1, ConstantLevel)
ASSUME IsLevel(1^+, ConstantLevel)

=============================================================================
