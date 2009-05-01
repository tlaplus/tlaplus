--------------- MODULE test33  -------------

(* Test of large sets of functions *)

EXTENDS TLC, Naturals

VARIABLE x

Init == /\ Print(<<"Computing", 7^6, "States">>, TRUE)
        /\ x \in [1..6 -> 1..7]   

Next == UNCHANGED x

Inv ==  TRUE
=========================================

Works for 7^6 = 117649 states on dix in     43.049u   3.729s  1:16.97 60.7%  
                                           (1529 states/sec)
Works for 6^7 = 279936 states on dix in    113.333u  19.494s  3:37.24 61.1%
                                           (1289 states/sec)
works for 7^7 = 823543 states on rowdy in  655.835u 158.050s 11:03.11 122.7%
                                           (1242 states/sec)
Doesn't work for 7^7 = 823543 states on dix
