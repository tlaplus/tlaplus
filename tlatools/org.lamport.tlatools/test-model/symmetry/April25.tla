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
   (even though this is not be the case when the spec/model declares S
   to be symmetric).
   
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
   whose path dissatisfies all action predicates (arc labels) - indicating
   whether x' # x for each of the values of S evaluates to true.
   See April25NoSymmetry.dot for an illustration. The illustration omits
   self loops as they are irrelevant in this context.
   
   TLC generates two initial states (x=a and x=b) and for each, explores
   its successor states. The successors for x=a are {x=a, x=b} and for x=b
   {x=b, x=a}. Thus, the action predicate x'=e is evaluated for element
   a *and* b.
   
   Gen_init = {x=a, x=b}
   Gen_succ(x=a) = {x=a, x=b}
   Gen_succ(x=b) = {x=a, x=b}
   Arcs_sat = {x=a -> x=b, x=b -> x=a}
   
   
   With symmetry declared on S, the behavior graph is reduced to a single
   node. This node is logically equivalent to all states of the symmetry
   set (which is indicated by the label in April25WithSymmetry.dot).
   Consequently, TLC only generates successor states for a single element
   of the symmetry set. Thus, it evaluates the action predicate for the
   chosen element of S only and just adds its corresponding arcs to the
   behavior graph.
   
   Let the initial state for which successor states are generated be x=a.
   Its successors are x=a and x=b. TLC therefore only adds the arc
   x=a -> x=b to the behavior graph which satisfies the action predicate
   for (-[x#a]_x).
   
   Gen_init = {x=a, x=b}
   Gen_succ(x=a) = {x=a, x=b}
   Gen_succ(x=b) never explored due to symmetry of x=a and x=b.
   Arcs_sat = {x=a -> x=b}
*)
Live == \E e \in S : <>[][x # e]_x
=============================================================================
