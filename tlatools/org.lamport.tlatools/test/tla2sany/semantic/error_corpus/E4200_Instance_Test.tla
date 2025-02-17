One of the most basic errors there is: referring to an undefined symbol.
---- MODULE E4200_Instance_Test ----
---- MODULE Inner ----
====
import == INSTANCE Inner
op == import!DoesNotExist
====

