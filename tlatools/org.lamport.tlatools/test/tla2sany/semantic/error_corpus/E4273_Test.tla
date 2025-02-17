This test looks at higher-order operator parameters when given parameters of
indeterminate level. The "apply" function simply applies its second parameter
as the first parameter of the higher-order operator parameter F. There is no
information about the level of x, or the level constraints of F, until they
are actually used. This is in contrast to a case where the argument to F has
known level just from the context of the apply operator itself - for example,
using F(v) instead of F(x) would clearly require F be able to accept a
parameter of variable level or above. Here, cross-checking needs to be done
to see whether the actual value bound to x violates the constraints of the
operator bound to F, at the point of use. In the case below it should trigger
a level-checking error preventing a double-prime expression.
---- MODULE E4273_Test ----
VARIABLE v
apply(F(_), x) == F(x)
op == apply(', v')
====

