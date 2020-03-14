--------------- MODULE test17 -------------

(* Test of handling of handling expressions with primes. *)

EXTENDS TLC, Naturals, Sequences

VARIABLE x, y

Init == /\ Print("There should be two distinct states", TRUE)
        /\ x = 1
        /\ y = 1

f[i \in Nat ] == x'+ x + 2*i
g == [i \in {x'} |-> x+i]


Foo(a) == a' = x+1

Inv == TRUE

TNext == 
  /\ x' = x+1
  /\ x' = 2
  /\ \/ UNCHANGED y

     \/ /\ Print("Starting Test 1", TRUE)
        /\ y' = IF x' = 2 
                  THEN 1 
                   ELSE Assert(FALSE, "Failed Test 1")

     \/ /\ Print("Starting Test 2", TRUE)
        /\ IF x' = 2 
             THEN y' = 1 
             ELSE Assert(FALSE, "Failed Test 2")

     \/ /\ Print("Starting Test 3", TRUE)
        /\ x' # 2
        /\ Assert(FALSE, "Failed Test 3")

     \/ /\ Print("Starting Test 4", TRUE)
        /\ ~(\E i \in {x'} : i = 2)
        /\ Assert(FALSE, "Failed Test 4")

     \/ /\ Print("Starting Test 5", TRUE)
        /\ ~ (\A i \in {x'} : i = 2)
        /\ Assert(FALSE, "Failed Test 5")

     \/ /\ Print("Starting Test 6", TRUE)
        /\ (CHOOSE i \in {x'} : TRUE) # 2
        /\ Assert(FALSE, "Failed Test 6")

     \/ /\ Print("Starting Test 7", TRUE)
        /\ 2 \notin {x'}
        /\ Assert(FALSE, "Failed Test 7")

     \/ /\ Print("Starting Test 8", TRUE)
        /\ {i \in {x'} : TRUE} # {2}
        /\ Assert(FALSE, "Failed Test 8")

     \/ /\ Print("Starting Test 9", TRUE)
        /\ {i' : i \in {x'}} # {2}
        /\ Assert(FALSE, "Failed Test 9")

     \/ /\ Print("Starting Test 10", TRUE)
        /\ {2} \notin SUBSET {x'}
        /\ Assert(FALSE, "Failed Test 10")

     \/ /\ Print("Starting Test 11", TRUE)
        /\ {2} # UNION {{x'}, {}}
        /\ Assert(FALSE, "Failed Test 11")

     \/ /\ Print("Starting Test 12", TRUE)
        /\ f[1] # 5
        /\ Assert(FALSE, "Failed Test 12")

     \/ /\ Print("Starting Test 13", TRUE)
        /\ f[x'] # 7
        /\ Assert(FALSE, "Failed Test 13")

     \/ /\ Print("Starting Test 14", TRUE)
        /\ [f EXCEPT ![x'] = x'+x+3][2] # 6
        /\ Assert(FALSE, "Failed Test 14")

     \/ /\ Print("Starting Test 15", TRUE)
        /\ [f EXCEPT ![2] = x'+x+3][x'] # 6
        /\ Assert(FALSE, "Failed Test 15")

     \/ /\ Print("Starting Test 16", TRUE)
        /\ [{x'-1} -> {x'}] # {<<2>>}
        /\ Assert(FALSE, "Failed Test 16")

     \/ /\ Print("Starting Test 17", TRUE)
        /\ [{x',x} -> {x'}] # {<<2, 2>>}
        /\ Assert(FALSE, "Failed Test 17")

     \/ /\ Print("Starting Test 18", TRUE)
        /\ [{x',x} -> {x}] # {<<1, 1>>}
        /\ Assert(FALSE, "Failed Test 18")

     \/ /\ Print("Starting Test 19", TRUE)
        /\ x'=2 => x'=3
        /\ Assert(FALSE, "Failed Test 19")

     \/ /\ Print("Starting Test 20", TRUE)
        /\ CASE x'= x+1 -> FALSE
             [] x'# x+1 -> TRUE
        /\ Assert(FALSE, "Failed Test 20")

     \/ /\ Print("Starting Test 21", TRUE)
        /\ DOMAIN g # {2}
        /\ Assert(FALSE, "Failed Test 21")

     \/ /\ Print("Starting Test 22", TRUE)
        /\ g[2] # 3
        /\ Assert(FALSE, "Failed Test 22")

     \/ /\ Print("Starting Test 23", TRUE)
        /\ CASE x' # 2 -> Assert(FALSE, "Failed Test 23")
             [] x' = 2 -> y' = 1

     \/ /\ Print("Starting Test 24", TRUE)
        /\ ~Foo(x)
        /\ Assert(FALSE, "Failed Test 24")

     \/ /\ Print("Starting Test 25", TRUE)
        /\ ~Foo(x)
        /\ Assert(FALSE, "Failed Test 25")


Next == TNext \/ UNCHANGED <<x, y>>
=========================================
