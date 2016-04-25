----------------------------- MODULE April25 -----------------------------
EXTENDS Integers

CONSTANT S

VARIABLE x

Init == x \in S

Next == x' \in S

Spec == Init /\ [][Next]_x

(* 
   There exists (at least) an element e in S for which variable x in all
   suffixes of all behaviors is never assigned e. Prefixes can be anything.
   There can be other elements in S which show a different behavior
   (even though this should not be the case as the spec declares S to
   be symmetric).
   
   A counterexample - to such a liveness claim - is an infinite suffix path
   with the property that x gets assigned e. This assignment can occur 1 to
   N times within the infinite suffix path. Any SCC is an infinite suffix
   path.
   
   Assume S={a,b}:
   
   This behavior satisfies Live with e bound to b (in Omega notation)
   ... > (x=a)^w
   
   Conversely, this behavior satisfies Live with e bound to a 
   ... > (x=b)^w
   
   Thus, the only infinite path that violates Live is where x is assigned
   both elements of the set S. This behavior violates Live for both 
   values a and b.
   ... > (x=a > x=b)^w
   
   Under no symmetry and S consisting out of two elements, the corresponding
   behavior graph - which shows the above violation - has two nodes. The two
   nodes are strongly connected. TLC searches the behavior graph for an SCC
   whose disjunct of all action predicates (arc labels) - indicating whether
   x' # x for one of the values of S - evaluates to true (satisfied).
   See April25NoSymmetry.dot for an illustration. The illustration omits
   self loops as they are irrelevant in this context.
   
   TLC generates two initial states (x=a and x=b) and for each, explores
   its successor states. The successors are (x=a > x=b) and for (x=b > x=a).
   Thus, the action predicate x'=e is evaluated for element a and b.
   
   
   With symmetry declared on S, the behavior graph collapses to a single
   node. This node represents both states x=a and x=b (which is indicated by
   its label in April25WithSymmetry.dot). Consequently, TLC only generates
   one successor state (either x=a or x=b) and thus only evaluates the
   action predicate for one element of S and adds its corresponding arc
   in the behavior graph. Let the initial state be x=a, its successor then
   is x=b. The symmetric counterpart x=b > x=a - as intended by declaring
   symmetry reduction - is never generated and no arc added to the behavior
   graph. TLC cannot find the liveness violation. 
*)
Live == \E e \in S : <>[][x # e]_x
=============================================================================
