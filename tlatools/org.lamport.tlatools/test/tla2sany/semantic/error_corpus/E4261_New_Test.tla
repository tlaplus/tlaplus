The @ symbol has special syntactic meaning and cannot be used as an
ordinary declared identifier, so it cannot be declared by NEW.
---- MODULE E4261_New_Test ----
THEOREM ASSUME NEW CONSTANT @
        PROVE TRUE
====
