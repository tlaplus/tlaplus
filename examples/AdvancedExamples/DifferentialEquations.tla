----------------------- MODULE DifferentialEquations ------------------------
LOCAL INSTANCE Reals
LOCAL INSTANCE Sequences
LOCAL PosReal == {r \in Real : r > 0}
LOCAL OpenInterval(a, b) == {s \in Real : a < s /\ s < b}
LOCAL Nbhd(r,e) ==  OpenInterval(r-e, r+e)
LOCAL IsFirstDeriv(df, f) ==
        /\ df \in [DOMAIN f -> Real]
        /\ \A r \in DOMAIN f : 
              \A e \in PosReal :
                 \E d \in PosReal : 
                    \A s \in Nbhd(r,d) \ {r} :
                        (f[s] - f[r])/(s - r) \in Nbhd(df[r], e)

LOCAL IsDeriv(n, df, f) == 
  LET IsD[k \in 0..n,  g \in [DOMAIN f -> Real]] ==
         IF k = 0 
           THEN g = f
           ELSE \E gg \in [DOMAIN f -> Real] : /\ IsFirstDeriv(g, gg)
                                               /\ IsD[k-1, gg]
  IN  IsD[n, df]

Integrate(D, a, b, InitVals) ==
  LET n == Len(InitVals)
      gg == CHOOSE g : 
              \E e \in PosReal : 
                 /\ g \in [0..n -> [OpenInterval(a-e, b+e) -> Real]]
                 /\ \A i \in 1..n : /\ IsDeriv(i, g[i], g[0])
                                    /\ g[i-1][a] = InitVals[i]
                 /\ \A r \in OpenInterval(a-e, b+e) :
                        D[ <<r>> \o [i \in 1..(n+1) |-> g[i-1][r]] ] = 0
  IN  [i \in 1..n |-> gg[i-1][b]]
=============================================================================



