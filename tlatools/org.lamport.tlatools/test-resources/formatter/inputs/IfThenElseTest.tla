---- MODULE IfThenElseTest ----
EXTENDS Naturals

VARIABLE x, y

Init == x = 0 /\ y = 0

Next == x' = IF x < 100 THEN x + 1 ELSE 0
     /\ y' = IF y > 5 THEN y - 1 ELSE y + 2

Nested == x' = IF x < 5 THEN IF y > 3 THEN x + y ELSE x - y ELSE 0

====