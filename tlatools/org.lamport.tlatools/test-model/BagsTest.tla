---------------------------- MODULE BagsTest ----------------------------
EXTENDS Bags, TLC, Integers

CONSTANT C

strings == {"a","b","c","d","e","f","g","h","i","j","k","l","m","n","o"}

s == {"a","b","c"}

a == <<>>
b == <<1,2,3>>
c == <<2,3,4>>
d == <<1,1,1>>
e == 1 :> 1
f == 2 :> 1
g == [x \in {1,2,3} |-> x * x]
h == [a |-> 3, b |-> 2, c |-> 1]

ASSUME(EmptyBag = <<>>)

\* IsABag
ASSUME(IsABag(a))
ASSUME(IsABag(b))
ASSUME(IsABag(c))
ASSUME(IsABag(d))
ASSUME(IsABag(e))
ASSUME(IsABag(f))
ASSUME(IsABag(g))
ASSUME(IsABag(h))

ASSUME(IsABag(SetToBag({})))

t == <<0>>
u == 2 :> -1
v == <<1,0>>
w == <<0,1>>
x == <<0,0,0>>
y == <<-1,-2,-3>>
z == <<"a","b","c">>

ASSUME(~IsABag(t))
ASSUME(~IsABag(u))
ASSUME(~IsABag(v))
ASSUME(~IsABag(w))
ASSUME(~IsABag(x))
ASSUME(~IsABag(y))
ASSUME(~IsABag(z)) \* With the standard module TLC fails with "Cannot decide if element "a" is element of Nat"

ASSUME(\A bool \in BOOLEAN : ~IsABag(bool))
ASSUME(~IsABag(C))  

\* BagCardinality
ASSUME(BagCardinality(a) = 0)
ASSUME(BagCardinality(b) = 6)
ASSUME(BagCardinality(c) = 9)
ASSUME(BagCardinality(d) = 3)
ASSUME(BagCardinality(e) = 1)
ASSUME(BagCardinality(f) = 1)
ASSUME(BagCardinality(g) = (1*1+2*2+3*3))
ASSUME(BagCardinality(h) = 6)

ASSUME(BagCardinality(<<1>>) = 1)
ASSUME(BagCardinality(<<1,3>>) = 4)

\* BagIn
ASSUME(\A elem \in 1..10: ~BagIn(elem, a))
ASSUME(\A elem \in 1..3: BagIn(elem, b))
ASSUME(\A elem \in 4..10: ~BagIn(elem, b))
ASSUME(\A dom \in DOMAIN c: BagIn(dom, c))
ASSUME(\A dom \in DOMAIN d: BagIn(dom, d))
ASSUME(\A dom \in DOMAIN e: BagIn(dom, e))
ASSUME(\A dom \in DOMAIN f: BagIn(dom, f))
ASSUME(\A dom \in DOMAIN f: BagIn(dom, f))
ASSUME(\A dom \in DOMAIN g: BagIn(dom, g))
ASSUME(\A dom \in DOMAIN h: BagIn(dom, h))
ASSUME(\A str \in (strings \ DOMAIN h): ~BagIn(str, h))
ASSUME(\A elem \in s : BagIn(elem, SetToBag(s)))


\* SetToBag and BagToSet
Codomain(fun) == {fun[i] : i \in DOMAIN fun}  
ASSUME(SetToBag(s) = [elem \in s |-> 1])
ASSUME(DOMAIN SetToBag(s) = s)
ASSUME(Codomain(SetToBag(s)) = {1})
ASSUME(BagToSet(SetToBag(s)) = s)

ASSUME(BagToSet(a) = {})
ASSUME(BagToSet(b) = DOMAIN b)
ASSUME(BagToSet(c) = DOMAIN c)
ASSUME(BagToSet(d) = DOMAIN d)
ASSUME(BagToSet(e) = {1})
ASSUME(BagToSet(f) = {2})
ASSUME(BagToSet(g) = DOMAIN g)
ASSUME(BagToSet(h) = s)


\* CopiesIn
ASSUME(\A str \in strings: CopiesIn(str, a) = 0)

ASSUME(\A dom \in DOMAIN b: CopiesIn(dom, b) = b[dom])
ASSUME(\A elem \in 5..10: CopiesIn(elem, b) = 0)
ASSUME(\A dom \in DOMAIN c: CopiesIn(dom, c) = c[dom])
ASSUME(\A elem \in 5..10: CopiesIn(elem, c) = 0)
ASSUME(\A dom \in DOMAIN d: CopiesIn(dom, d) = d[dom])
ASSUME(\A elem \in 5..10: CopiesIn(elem, d) = 0)

ASSUME(CopiesIn(1, e) = 1)
ASSUME(CopiesIn(2, f) = 1)
ASSUME(CopiesIn(1, f) = 0)
ASSUME(CopiesIn(1, 1 :> 0) = 0)
ASSUME(CopiesIn(2, 2 :> -1) = -1)

ASSUME(\A dom \in DOMAIN g: CopiesIn(dom, g) = dom * dom)

ASSUME(CopiesIn("a", h) = 3)
ASSUME(CopiesIn("b", h) = 2)
ASSUME(CopiesIn("c", h) = 1)
ASSUME(\A str \in (strings \ DOMAIN h): CopiesIn(str, h) = 0)

ASSUME(\A aelem \in s: CopiesIn(aelem, [elem \in s |-> 42]) = 42)
ASSUME(\A aelem \in s: CopiesIn(aelem, [elem \in s |-> 0]) = 0)


\* (+)
ASSUME(EmptyBag (+) EmptyBag = EmptyBag)
ASSUME(a (+) a = a)
ASSUME(b (+) b = <<2,4,6>>)
ASSUME(b (+) EmptyBag = b)
ASSUME(c (+) c = <<4,6,8>>)
ASSUME(d (+) d = <<2,2,2>>)
ASSUME(e (+) e = <<2>>)
ASSUME(b (+) c = c (+) b)
ASSUME(b (+) c = <<3,5,7>>)
ASSUME(h (+) h = [a |-> 6, b |-> 4, c |-> 2])
ASSUME([c |-> 3, d |-> 2, e |-> 1] (+) h = [a |-> 3, b |-> 2, c |-> 4, d |-> 2, e |-> 1])


\* (-)
ASSUME(a (-) a = a)
ASSUME(b (-) b = EmptyBag)
ASSUME(b (-) EmptyBag = b)
ASSUME(c (-) c = EmptyBag)
ASSUME(d (-) d = EmptyBag)
ASSUME(e (-) e = EmptyBag)
ASSUME(b (-) c = b (-) c)
ASSUME(b (-) c = EmptyBag)
ASSUME(c (-) b = <<1,1,1>>)
ASSUME([c |-> 3, d |-> 2, e |-> 1] (-) h = [c |-> 2, d |-> 2, e |-> 1])
ASSUME((1:>1) (-) EmptyBag = <<1>>)


\* BagUnion
ASSUME(BagUnion({a,a}) = a)
ASSUME(BagUnion({b,b}) = b)
ASSUME(BagUnion({c,c}) = c)
ASSUME(BagUnion({d,d}) = d)
ASSUME(BagUnion({e,e}) = e)
ASSUME(BagUnion({f,f}) = f)
ASSUME(BagUnion({g,g}) = g)
ASSUME(BagUnion({h,h}) = h)
ASSUME(BagUnion({h,h,[c |-> 3, d |-> 2, e |-> 1]}) = h (+) [c |-> 3, d |-> 2, e |-> 1])
ASSUME(BagUnion({a,b,c,d}) = <<4,6,8>>)
ASSUME(BagUnion({EmptyBag, EmptyBag}) = <<>>)
ASSUME(BagUnion({[a |-> 3, b |-> 2, c |-> 1],[c |-> 3, d |-> 2, e |-> 1]}) = [a |-> 3, b |-> 2, c |-> 4, d |-> 2, e |-> 1])
ASSUME(BagUnion({1 :> 2, 2 :> 2, 3 :> 3}) = (1 :> 2) (+) (2 :> 2) (+) (3 :> 3))
ASSUME(BagUnion({<<>>, <<1,1,1>>, <<1,2,3,4>>}) = (1:>2 @@ 2:>3 @@ 3:>4 @@ 4:>4))


\* \sqsubseteq
ASSUME((a \sqsubseteq a) = TRUE)
ASSUME((a \sqsubseteq b) = TRUE)
ASSUME((a \sqsubseteq c) = TRUE)
ASSUME((a \sqsubseteq d) = TRUE)
ASSUME((b \sqsubseteq b) = TRUE)
ASSUME((c \sqsubseteq c) = TRUE)
ASSUME((h \sqsubseteq [a |-> 3]) = FALSE)
ASSUME((h \sqsubseteq [a |-> 3, b |-> 2]) = FALSE)
ASSUME(([a |-> 3] \sqsubseteq h) = TRUE)
ASSUME(([a |-> 3, b |-> 2] \sqsubseteq h) = TRUE)
ASSUME(([a |-> 3, c |-> 1] \sqsubseteq h) = TRUE)
ASSUME(([b |-> 2, c |-> 1] \sqsubseteq h) = TRUE)
ASSUME((h \sqsubseteq h) = TRUE)


\* BagOfAll
ASSUME(BagOfAll(LAMBDA elem : elem, a) = a)
ASSUME(BagOfAll(LAMBDA elem : TRUE, a) = a)
ASSUME(BagOfAll(LAMBDA elem : elem, h) = h)
ASSUME(BagOfAll(LAMBDA elem : TRUE, h) = TRUE :> 6)
ASSUME(BagOfAll(LAMBDA elem : IF elem = "a" THEN "b" ELSE elem, [a |-> 3, b |-> 2, c |-> 1]) = [b |-> 5, c |-> 1])


\* SubBag
\* Module overwrite does not overwrite SubBag

\* A dummy spec to make TLC run model checking as required by BagsTest.java.
Spec == [][TRUE]_<<>>

=============================================================================
