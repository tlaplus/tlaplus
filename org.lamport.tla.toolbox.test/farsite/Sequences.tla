---- MODULE Sequences ----
(*`^\addcontentsline{toc}{section}{Sequences}^'*)

EXTENDS Stubs,Naturals
(* Should be LOCAL INSTANCE *)

(*Defn*)Seq(S)==UNION{[1..n->S]:n \in Nat}

(*Defn*)BSeq(s,n)==UNION{[1..i->s]:i \in 0..n}

(*Defn*)Len(s)==CHOOSE n \in Nat:DOMAIN s=(1..n)

(*Defn*)s \o t==
  [i \in 1..(Len(s)+Len(t))|->IF i \leq Len(s)THEN s[i]ELSE t[(i-Len(s))]]

(*Defn*)Append(s,e)==[i \in 1..(Len(s)+1)|->IF i \leq Len(s)THEN s[i]ELSE e]

(*Defn*)Head(s)==s[1]

(*Defn*)Tail(s)==[i \in 1..(Len(s)-1)|->s[(i+1)]]

(*Defn*)SubSeq(s,m,n)==[i \in 1..(1+n-m)|->s[(i+m-1)]]

(* 

<Definition>
	SelectSeq(s, Test(_)) == 
	LET
		F[i \in 0..Len(s)] == 
			IF i = 0
			THEN
				\langle \rangle
			ELSE IF Test(s[i])
			THEN
				Append(F[i-1], s[i])
			ELSE
				F[i-1]
	IN
		F[Len(s)]
</Definition>

TODO:  The parser cannot currently handle second-order operators.

 *)
====
