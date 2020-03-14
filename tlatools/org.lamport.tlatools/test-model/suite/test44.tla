--------------- MODULE test44  -------------

(* Test of operator precedence and associativity . *)

EXTENDS TLC, Integers, Sequences

VARIABLE x

Init == x = 1


Next ==  x' = x
         

a | b == <<a, b>>
a || b == <<a, b>>
a & b == <<a, b>>
a && b == <<a, b>>
a $ b == <<a, b>>
a $$ b == <<a, b>>
a ?? b == <<a, b>>
a %% b == <<a, b>>
a ## b == <<a, b>>
a ++ b == <<a, b>>
a -- b == <<a, b>>
a ** b == <<a, b>>
a (+) b == <<a, b>>
a (-) b == <<a, b>>
a (.) b == <<a, b>>

a (\X) b == <<a, b>>         

\* a \otimes b == <<a, b>> 
a \uplus b == <<a, b>>
a \sqcap b == <<a, b>>
a \sqcup b == <<a, b>>
a \star b == <<a, b>>
a \bigcirc b == <<a, b>>
a \bullet b == <<a, b>>

a ... b == <<a, b>>
a // b == <<a, b>>
a ^^ b == <<a, b>>
a !! b == <<a, b>>
a |- b == <<a, b>>
a |= b == <<a, b>>
a -| b == <<a, b>>
a =| b == <<a, b>>

a <: b == <<a, b>> 


a := b == <<a, b>>
a ::= b == <<a, b>>
a (/) b == <<a, b>>
\* a \oslash b == <<a, b>> 
a \wr b == <<a, b>>
a \prec b == <<a, b>>
a \succ b == <<a, b>>
a \preceq b == <<a, b>>
a \succeq b == <<a, b>>
a \sim b == <<a, b>>
a \simeq b == <<a, b>>
a \ll b == <<a, b>>
a \gg b == <<a, b>>
a \asymp b == <<a, b>>
a \subset b == <<a, b>>
a \supset b == <<a, b>>
a \supseteq b == <<a, b>>
a \approx b == <<a, b>>
a \cong b == <<a, b>>
a \sqsubset b == <<a, b>>
a \sqsupset b == <<a, b>>
a \sqsubseteq b == <<a, b>>
a \sqsupseteq b == <<a, b>>
a \doteq b == <<a, b>>
a \propto b == <<a, b>>


Inv ==
        /\ IF (3 - 2 - 1) = 0
             THEN Print("Test 1 OK", TRUE)
             ELSE Assert(FALSE, "Test 1 Failed")

        /\ IF 1 | 2 | 3 = <<<<1, 2>>, 3>>
             THEN Print("Test 2 OK", TRUE)
             ELSE Assert(FALSE, "Test 2 Failed")

        /\ IF 1 || 2 || 3 = <<<<1, 2>>, 3>>
             THEN Print("Test 3 OK", TRUE)
             ELSE Assert(FALSE, "Test 3 Failed")

        /\ IF 1 & 2 & 3 = <<<<1, 2>>, 3>>
             THEN Print("Test 4 OK", TRUE)
             ELSE Assert(FALSE, "Test 4 Failed")

        /\ IF 1 && 2 && 3 = <<<<1, 2>>, 3>>
             THEN Print("Test 5 OK", TRUE)
             ELSE Assert(FALSE, "Test 5 Failed")

        /\ IF 1 $ 2 $ 3 = <<<<1, 2>>, 3>>
             THEN Print("Test 6 OK", TRUE)
             ELSE Assert(FALSE, "Test 6 Failed")

        /\ IF 1 $$ 2 $$ 3 = <<<<1, 2>>, 3>>
             THEN Print("Test 7 OK", TRUE)
             ELSE Assert(FALSE, "Test 7 Failed")

        /\ IF 1 ?? 2 ?? 3 = <<<<1, 2>>, 3>>
             THEN Print("Test 8 OK", TRUE)
             ELSE Assert(FALSE, "Test 8 Failed")

        /\ IF TRUE
             THEN Print("Test 9 OK", TRUE)
             ELSE Assert(FALSE, "Test 9 Failed")

        /\ IF 1 %% 2 %% 3 = <<<<1, 2>>, 3>>
             THEN Print("Test 10 OK", TRUE)
             ELSE Assert(FALSE, "Test 10 Failed")

        /\ IF 1 ## 2 ## 3 = <<<<1, 2>>, 3>>
             THEN Print("Test 11 OK", TRUE)
             ELSE Assert(FALSE, "Test 11 Failed")

        /\ IF 1 ++ 2 ++ 3 = <<<<1, 2>>, 3>>
             THEN Print("Test 12 OK", TRUE)
             ELSE Assert(FALSE, "Test 12 Failed")

        /\ IF 1 -- 2 -- 3 = <<<<1, 2>>, 3>>
             THEN Print("Test 13 OK", TRUE)
             ELSE Assert(FALSE, "Test 13 Failed")

        /\ IF 1 ** 2 ** 3 = <<<<1, 2>>, 3>>
             THEN Print("Test 14 OK", TRUE)
             ELSE Assert(FALSE, "Test 14 Failed")

        /\ IF 1 (+) 2 (+) 3 = <<<<1, 2>>, 3>>
             THEN Print("Test 15 OK", TRUE)
             ELSE Assert(FALSE, "Test 15 Failed") 

        /\ IF 1 (-) 2 (-) 3 = <<<<1, 2>>, 3>>
             THEN Print("Test 16 OK", TRUE)
             ELSE Assert(FALSE, "Test 16 Failed") 

        /\ IF 1 (.) 2 (.) 3 = <<<<1, 2>>, 3>>
             THEN Print("Test 17 OK", TRUE)
             ELSE Assert(FALSE, "Test 17 Failed") 

        /\ IF 1 (\X) 2 (\X) 3 = <<<<1, 2>>, 3>>
             THEN Print("Test 18 OK", TRUE)
             ELSE Assert(FALSE, "Test 18 Failed")

        /\ IF 1 \oplus 2 \oplus 3 = <<<<1, 2>>, 3>>
             THEN Print("Test 19 OK", TRUE)
             ELSE Assert(FALSE, "Test 19 Failed")

        /\ IF 1 \ominus 2 \ominus 3 = <<<<1, 2>>, 3>>
             THEN Print("Test 20 OK", TRUE)
             ELSE Assert(FALSE, "Test 20 Failed")

        /\ IF 1 \odot 2 \odot 3 = <<<<1, 2>>, 3>>
             THEN Print("Test 21 OK", TRUE)
             ELSE Assert(FALSE, "Test 21 Failed")

        /\ IF 1 \otimes 2 \otimes 3 = <<<<1, 2>>, 3>>
             THEN Print("Test 22 OK", TRUE)
             ELSE Assert(FALSE, "Test 22 Failed")

        /\ IF 1 \uplus 2 \uplus 3 = <<<<1, 2>>, 3>>
             THEN Print("Test 23 OK", TRUE)
             ELSE Assert(FALSE, "Test 23 Failed")


        /\ IF 1 \sqcap 2 \sqcap 3 = <<<<1, 2>>, 3>>
             THEN Print("Test 24 OK", TRUE)
             ELSE Assert(FALSE, "Test 24 Failed")

        /\ IF 1 \sqcup 2 \sqcup 3 = <<<<1, 2>>, 3>>
             THEN Print("Test 25 OK", TRUE)
             ELSE Assert(FALSE, "Test 25 Failed")

        /\ IF 1 \star 2 \star 3 = <<<<1, 2>>, 3>>
             THEN Print("Test 26 OK", TRUE)
             ELSE Assert(FALSE, "Test 26 Failed")

        /\ IF <<1>> \o <<2>> \o <<3>> = <<1, 2, 3>>
             THEN Print("Test 27 OK", TRUE)
             ELSE Assert(FALSE, "Test 27 Failed")

        /\ IF 1 \bigcirc 2 \bigcirc 3 = <<<<1, 2>>, 3>>
             THEN Print("Test 28 OK", TRUE)
             ELSE Assert(FALSE, "Test 28 Failed")

        /\ IF 1 \bullet 2 \bullet 3 = <<<<1, 2>>, 3>>
             THEN Print("Test 29 OK", TRUE)
             ELSE Assert(FALSE, "Test 29 Failed")

        /\ IF 1 ... 2 = <<1, 2>>
             THEN Print("Test 30 OK", TRUE)
             ELSE Assert(FALSE, "Test 30 Failed")

        /\ IF 1 // 2 = <<1, 2>>
             THEN Print("Test 31 OK", TRUE)
             ELSE Assert(FALSE, "Test 31 Failed")

        /\ IF 1 ^^ 2 = <<1, 2>>
             THEN Print("Test 32 OK", TRUE)
             ELSE Assert(FALSE, "Test 32 Failed")

        /\ IF 1 !! 2 = <<1, 2>>
             THEN Print("Test 33 OK", TRUE)
             ELSE Assert(FALSE, "Test 33 Failed")

        /\ IF (1 |- 2) = <<1, 2>>
             THEN Print("Test 34 OK", TRUE)
             ELSE Assert(FALSE, "Test 34 Failed")

        /\ IF (1 |= 2) = <<1, 2>>
             THEN Print("Test 35 OK", TRUE)
             ELSE Assert(FALSE, "Test 35 Failed")

        /\ IF (1 -| 2) = <<1, 2>>
             THEN Print("Test 36 OK", TRUE)
             ELSE Assert(FALSE, "Test 36 Failed")

        /\ IF (1 =| 2) = <<1, 2>>
             THEN Print("Test 37 OK", TRUE)
             ELSE Assert(FALSE, "Test 37 Failed")

        /\ IF 1 <: 2 = <<1, 2>>
             THEN Print("Test 38 OK", TRUE)
             ELSE Assert(FALSE, "Test 38 Failed")

        /\ IF TRUE
             THEN Print("Test 39 OK", TRUE)
             ELSE Assert(FALSE, "Test 39 Failed")

        /\ IF (1 := 2) = <<1, 2>>
             THEN Print("Test 40 OK", TRUE)
             ELSE Assert(FALSE, "Test 40 Failed")

        /\ IF (1 ::= 2) = <<1, 2>>
             THEN Print("Test 41 OK", TRUE)
             ELSE Assert(FALSE, "Test 41 Failed")

        /\ IF 1 (/) 2 = <<1, 2>>
             THEN Print("Test 42 OK", TRUE)
             ELSE Assert(FALSE, "Test 42 Failed") 

        /\ IF 1 \oslash 2 = <<1, 2>> 
             THEN Print("Test 43 OK", TRUE)
             ELSE Assert(FALSE, "Test 43 Failed")

        /\ IF 1 \wr 2 = <<1, 2>>
             THEN Print("Test 44 OK", TRUE)
             ELSE Assert(FALSE, "Test 44 Failed")

        /\ IF (1 \prec 2) = <<1, 2>>
             THEN Print("Test 45 OK", TRUE)
             ELSE Assert(FALSE, "Test 45 Failed")

        /\ IF (1 \succ 2) = <<1, 2>>
             THEN Print("Test 46 OK", TRUE)
             ELSE Assert(FALSE, "Test 46 Failed")

        /\ IF (1 \preceq 2) = <<1, 2>>
             THEN Print("Test 47 OK", TRUE)
             ELSE Assert(FALSE, "Test 47 Failed")

        /\ IF (1 \succeq 2) = <<1, 2>>
             THEN Print("Test 48 OK", TRUE)
             ELSE Assert(FALSE, "Test 48 Failed")

        /\ IF (1 \sim 2) = <<1, 2>>
             THEN Print("Test 49 OK", TRUE)
             ELSE Assert(FALSE, "Test 49 Failed")

        /\ IF (1 \simeq 2) = <<1, 2>>
             THEN Print("Test 50 OK", TRUE)
             ELSE Assert(FALSE, "Test 50 Failed")

        /\ IF (1 \ll 2) = <<1, 2>>
             THEN Print("Test 51 OK", TRUE)
             ELSE Assert(FALSE, "Test 51 Failed")

        /\ IF (1 \gg 2) = <<1, 2>>
             THEN Print("Test 52 OK", TRUE)
             ELSE Assert(FALSE, "Test 52 Failed")

        /\ IF (1 \asymp 2) = <<1, 2>>
             THEN Print("Test 53 OK", TRUE)
             ELSE Assert(FALSE, "Test 53 Failed")

        /\ IF (1 \subset 2) = <<1, 2>>
             THEN Print("Test 54 OK", TRUE)
             ELSE Assert(FALSE, "Test 54 Failed")

        /\ IF (1 \supset 2) = <<1, 2>>
             THEN Print("Test 55 OK", TRUE)
             ELSE Assert(FALSE, "Test 55 Failed")

        /\ IF (1 \supseteq 2) = <<1, 2>>
             THEN Print("Test 56 OK", TRUE)
             ELSE Assert(FALSE, "Test 56 Failed")

        /\ IF (1 \approx 2) = <<1, 2>>
             THEN Print("Test 57 OK", TRUE)
             ELSE Assert(FALSE, "Test 57 Failed")

        /\ IF (1 \cong 2) = <<1, 2>>
             THEN Print("Test 58 OK", TRUE)
             ELSE Assert(FALSE, "Test 58 Failed")

        /\ IF (1 \sqsubset 2) = <<1, 2>>
             THEN Print("Test 59 OK", TRUE)
             ELSE Assert(FALSE, "Test 59 Failed")

        /\ IF (1 \sqsupset 2) = <<1, 2>>
             THEN Print("Test 60 OK", TRUE)
             ELSE Assert(FALSE, "Test 60 Failed")

        /\ IF (1 \sqsubseteq 2) = <<1, 2>>
             THEN Print("Test 61 OK", TRUE)
             ELSE Assert(FALSE, "Test 61 Failed")

        /\ IF (1 \sqsupseteq 2) = <<1, 2>>
             THEN Print("Test 62 OK", TRUE)
             ELSE Assert(FALSE, "Test 62 Failed")

        /\ IF (1 \doteq 2) = <<1, 2>>
             THEN Print("Test 63 OK", TRUE)
             ELSE Assert(FALSE, "Test 63 Failed")

        /\ IF (1 \propto 2) = <<1, 2>>
             THEN Print("Test 64 OK", TRUE)
             ELSE Assert(FALSE, "Test 64 Failed")

        /\ IF << <<1, 2>>, 3 >> = 1 & 2 ... 3
             THEN Print("Test 65 OK", TRUE)
             ELSE Assert(FALSE, "Test 65 Failed")


        /\ IF << <<1, 2>>, 3 >> = 1 && 2 ... 3
             THEN Print("Test 66 OK", TRUE)
             ELSE Assert(FALSE, "Test 66 Failed")


        /\ IF << <<1, 2>>, 3 >> = 1 ** 2 ... 3
             THEN Print("Test 67 OK", TRUE)
             ELSE Assert(FALSE, "Test 67 Failed")

        /\ IF << <<1, 2>>, 3 >> = 1 // 2 ... 3
             THEN Print("Test 68 OK", TRUE)
             ELSE Assert(FALSE, "Test 68 Failed")

        /\ IF << <<1, 2>>, 3 >> = 1 ^^ 2 ... 3
             THEN Print("Test 69 OK", TRUE)
             ELSE Assert(FALSE, "Test 69 Failed")

        /\ IF << <<1, 2>>, 3 >> = 1 (/) 2 ... 3
             THEN Print("Test 70 OK", TRUE)
             ELSE Assert(FALSE, "Test 70 Failed")  

        /\ IF << <<1, 2>>, 3 >> =  1 (.) 2 ... 3
             THEN Print("Test 71 OK", TRUE)
             ELSE Assert(FALSE, "Test 71 Failed")  

        /\ IF << <<1, 2>>, 3 >> = 1 \star 2 ... 3
             THEN Print("Test 72 OK", TRUE)
             ELSE Assert(FALSE, "Test 72 Failed")

        /\ IF << <<1, 2>>, 3 >> =  1 \bigcirc  2 ... 3
             THEN Print("Test 73 OK", TRUE)
             ELSE Assert(FALSE, "Test 73 Failed")

        /\ IF << <<1, 2>>, 3 >> =  1 \bullet 2 ... 3
             THEN Print("Test 74 OK", TRUE)
             ELSE Assert(FALSE, "Test 74 Failed")


        /\ IF << <<1, 2>>, 3 >> = (1 $ 2 \sim 3)
             THEN Print("Test 75 OK", TRUE)
             ELSE Assert(FALSE, "Test 75 Failed") 


        /\ IF << <<1, 2>>, 3 >> = (1 $$ 2 \simeq 3)
             THEN Print("Test 76 OK", TRUE)
             ELSE Assert(FALSE, "Test 76 Failed") 


        /\ IF << <<1, 2>>, 3 >> = (1 $ 2 \gg 3)
             THEN Print("Test 77 OK", TRUE)
             ELSE Assert(FALSE, "Test 77 Failed") 

        /\ IF << <<1, 2>>, 3 >> = (1 -- 2 ++ 3)
             THEN Print("Test 78 OK", TRUE)
             ELSE Assert(FALSE, "Test 78 Failed")

        /\ IF << <<1, 2>>, 3 >> = (1 -- 2 <: 3)
             THEN Print("Test 79 OK", TRUE)
             ELSE Assert(FALSE, "Test 79 Failed") 


        /\ IF << <<1, 2>>, 3 >> = (1 !! 2 \ll 3)
             THEN Print("Test 80 OK", TRUE)
             ELSE Assert(FALSE, "Test 80 Failed") 

        /\ IF << <<1, 2>>, 3 >> =  1 (-) 2 (+) 3
             THEN Print("Test 81 OK", TRUE)
             ELSE Assert(FALSE, "Test 81 Failed") 

        /\ IF << <<1, 2>>, 3 >> = (1 ++ 2 |- 3)
             THEN Print("Test 82 OK", TRUE)
             ELSE Assert(FALSE, "Test 82 Failed")

        /\ IF << <<1, 2>>, 3 >> = 1 (.) 2 (-) 3
             THEN Print("Test 83 OK", TRUE)
             ELSE Assert(FALSE, "Test 83 Failed")  

        /\ IF << <<1, 2>>, 3 >> = (1 \bullet 2 \prec 3)
             THEN Print("Test 84 OK", TRUE)
             ELSE Assert(FALSE, "Test 84 Failed")

        /\ IF << <<1, 2>>, 3 >> = (1 \uplus 2 \approx 3)
             THEN Print("Test 85 OK", TRUE)
             ELSE Assert(FALSE, "Test 85 Failed")


        /\ IF << <<1, 2>>, 3 >> = (1 ++ 2 \sim 3)
             THEN Print("Test 86 OK", TRUE)
             ELSE Assert(FALSE, "Test 86 Failed")

        /\ IF << <<1, 2>>, 3 >> = (1 (/) 2 (-) 3)
             THEN Print("Test 87 OK", TRUE)
             ELSE Assert(FALSE, "Test 87 Failed")  



Constraint == TRUE
=========================================

<< {"..."},         "Infix", <<P.dotdot,   P.dotdot>>,   "none" >>,
<< {"//"},          "Infix", <<P.times,    P.times>>,    "none" >>,
<< {"^^"},          "Infix", <<P.exponent, P.exponent>>, "none" >>,
<< {"!!"},          "Infix", <<P.dotdot,   P.times>>,    "none" >>,
<< {"|-"},          "Infix", <<P.equals,   P.equals>>,   "none" >>,
<< {"|="},          "Infix", <<P.equals,   P.equals>>,   "none" >>,
<< {"-|"},          "Infix", <<P.equals,   P.equals>>,   "none" >>,
<< {"=|"},          "Infix", <<P.equals,   P.equals>>,   "none" >>,
<< {"<:"},          "Infix", <<P.colongt,  P.colongt>>,  "none" >>,
<< {":>"},          "Infix", <<P.colongt,  P.colongt>>,  "none" >>,
<< {":="},          "Infix", <<P.equals,   P.equals>>,   "none" >>,
<< {"::="},         "Infix", <<P.equals,   P.equals>>,   "none" >>,
<< {"(/)", "\oslash"}, "Infix", <<P.times, P.times>>, "none"  >>,
<< {"\wr"},             "Infix", <<P.dotdot, P.exponent>>, "none" >>,
<< {"\prec"},           "Infix", <<P.equals, P.equals>>,   "none" >>,
<< {"\succ"},           "Infix", <<P.equals, P.equals>>,   "none" >>,
<< {"\preceq"},         "Infix", <<P.equals, P.equals>>,   "none" >>,
<< {"\succeq"},         "Infix", <<P.equals, P.equals>>,   "none" >>,
<< {"\sim"},            "Infix", <<P.equals, P.equals>>,   "none" >>,
<< {"\simeq"},          "Infix", <<P.equals, P.equals>>,   "none" >>,
<< {"\ll"},             "Infix", <<P.equals, P.equals>>,   "none" >>,
<< {"\gg"},             "Infix", <<P.equals, P.equals>>,   "none" >>,
<< {"\asymp"},          "Infix", <<P.equals, P.equals>>,   "none" >>,
<< {"\subset"},         "Infix", <<P.equals, P.equals>>,   "none" >>,
<< {"\supset"},         "Infix", <<P.equals, P.equals>>,   "none" >>,
<< {"\supseteq"},       "Infix", <<P.equals, P.equals>>,   "none" >>,
<< {"\approx"},         "Infix", <<P.equals, P.equals>>,   "none" >>,
<< {"\cong"},           "Infix", <<P.equals, P.equals>>,   "none" >>,
<< {"\sqsubset"},       "Infix", <<P.equals, P.equals>>,   "none" >>,
<< {"\sqsupset"},       "Infix", <<P.equals, P.equals>>,   "none" >>,
<< {"\sqsubseteq"},     "Infix", <<P.equals, P.equals>>,   "none" >>,
<< {"\sqsupseteq"},     "Infix", <<P.equals, P.equals>>,   "none" >>,
<< {"\doteq"},          "Infix", <<P.equals, P.equals>>,   "none" >>,
<< {"\propto"},         "Infix", <<P.equals, P.equals>>,   "none" >>




