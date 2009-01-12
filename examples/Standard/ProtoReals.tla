----------------------------- MODULE ProtoReals ----------------------------- 
EXTENDS Peano

IsModelOfReals(R, Plus, Times, Leq) == 
  LET IsAbelianGroup(G, Id, _+_) == 
        /\ Id \in G
        /\ \A a, b \in G : a + b \in G
        /\ \A a \in G : Id + a = a
        /\ \A a, b, c \in G : (a + b) + c = a + (b + c)
        /\ \A a \in G : \E minusa \in G : a + minusa = Id
        /\ \A a, b \in G : a + b = b + a
     (**********************************************************************)
     (* Plus and Times are functions and Leq is a set, but it's more       *)
     (* convenient to turn them into the infix operators +, *, and \leq    *)
     (**********************************************************************)
      a + b    == Plus[a, b]
      a * b    == Times[a, b]
      a \leq b == <<a, b>> \in Leq
  IN  /\ Nat \subseteq R
      /\ \A n \in Nat : Succ[n] = n + Succ[Zero]
      /\ IsAbelianGroup(R, Zero, +)
      /\ IsAbelianGroup(R \ {Zero}, Succ[Zero], *)
      /\ \A a, b, c \in R : a * (b + c) = (a * b) + (a * c) 
      /\ \A a, b \in R : /\ (a \leq b) \/ (b \leq a)
                         /\ (a \leq b) /\ (b \leq a) <=> (a = b)
      /\ \A a, b, c \in R : /\ (a \leq b) /\ (b \leq c) => (a \leq c)
                            /\ (a \leq b) => 
                                 /\ (a + c) \leq (b + c)
                                 /\ (Zero \leq c) => (a * c) \leq (b * c)
      /\ \A S \in SUBSET R :
           LET SBound(a) == \A s \in S : s \leq a
           IN  (\E a \in R : SBound(a)) => 
                  (\E sup \in R : /\ SBound(sup) 
                                  /\ \A a \in R : SBound(a) => (sup\leq a))

THEOREM \E R, Plus, Times, Leq : IsModelOfReals(R, Plus, Times, Leq)
-----------------------------------------------------------------------------
RM == CHOOSE RM : IsModelOfReals(RM.R, RM.Plus, RM.Times, RM.Leq)

Real  == RM.R
-----------------------------------------------------------------------------
Infinity == CHOOSE x : x \notin Real
MinusInfinity == CHOOSE x : x \notin Real \cup {Infinity}

a + b == RM.Plus[a, b]

a * b == RM.Times[a, b]

a \leq b == CASE (a \in Real) /\ (b \in Real) -> <<a, b>> \in RM.Leq
              [] (a = Infinity) /\ (b \in Real \cup {MinusInfinity})  -> FALSE
              [] (a \in Real  \cup {MinusInfinity}) /\ (b = Infinity) -> TRUE
              [] (a = b) -> TRUE

a - b == CASE (a \in Real) /\ (b \in Real)  -> CHOOSE c \in Real : c + b = a
           [] (a \in Real) /\ (b = Infinity)      -> MinusInfinity
           [] (a \in Real) /\ (b = MinusInfinity) -> Infinity 

a / b == CHOOSE c \in Real : a = b * c

Int  == Nat \cup {Zero - n : n \in Nat}
-----------------------------------------------------------------------------
a ^ b == 
  LET RPos == {r \in Real \ {Zero} : Zero \leq r}
      exp  == CHOOSE f \in [(RPos \X Real) \cup (Real \X RPos) 
                                   \cup ((Real \ {Zero}) \X Int) -> Real] :
               /\ \A r \in Real :
                    /\ f[r, Succ[Zero]] = r
                    /\ \A m, n \in Int : (r # Zero) => 
                                           (f[r, m+n] = f[r, m] * f[r, n])
               /\ \A r \in RPos :
                    /\ f[Zero, r] = Zero
                    /\ \A s, t \in Real : f[r, s*t] = f[f[r, s], t]
                    /\ \A s, t \in RPos : (s \leq t) => (f[r,s] \leq f[r,t])
  IN  exp[a, b]
=============================================================================


