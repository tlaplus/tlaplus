INSTANCE operator definitions cannot be referred to by themselves; instead,
operator applications must refer to a specific definition within the imported
module, like import!def.
---- MODULE E4203_Test ----
import == INSTANCE Naturals
op == import
====

