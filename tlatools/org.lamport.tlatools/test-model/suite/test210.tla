\* This module is meant to produce parsing errors when evaluating any
\* subexpression reference ref in an expression of the form ref <=>
\* ILLEGAL and any label labeling "ILLEGAL"


-------------------- MODULE test210 --------------
ILLEGAL == FALSE
LEGAL   == TRUE

ASSUME assump == /\ lab :: LEGAL
                 /\ TRUE

AssDef == /\ assump!lab <=> LEGAL
          /\ assump!1   <=> LEGAL

THEOREM foo == ASSUME  NEW x \in labx :: LEGAL,
                       NEW y \in laby :: LEGAL,
                       labz :: LEGAL,
                       ASSUME TRUE PROVE  labi :: LEGAL
                       PROVE labu :: LEGAL
<1>1. ASSUME  LEGAL,
              NEW q \in labx :: LEGAL,
              NEW r \in laby :: LEGAL
              PROVE /\ foo!3 <=> LEGAL
                    /\ foo!labz  <=> LEGAL
                    /\ foo!5 <=> LEGAL
                    /\ foo!labu  <=> LEGAL
                    /\ foo!labi  <=> LEGAL
  BY <1>1!labx <=> LEGAL, <1>1!laby <=> LEGAL, <1>1!4 <=> LEGAL,
     foo!4!2 <=> LEGAL, foo!4!1 <=> LEGAL

<1>1a. /\ <1>1!labx <=> LEGAL
       /\ <1>1!laby <=> ILLEGAL
       /\ <1>1!1    <=> LEGAL
       /\ <1>1!4    <=> ILLEGAL

<1>2. SUFFICES ASSUME  NEW q \in labx :: LEGAL,
                       TRUE,
                       NEW r \in laby :: LEGAL,
                       ASSUME lab1 :: LEGAL,
                              NEW a \in lab2 :: LEGAL,
                              NEW b \in lab3 :: ILLEGAL
                       PROVE lab4 :: ILLEGAL
                PROVE /\ foo!3 <=> LEGAL
                      /\ foo!labz  <=> LEGAL
                      /\ foo!5 <=> LEGAL
                      /\ foo!labu  <=> LEGAL
        
<1>2a. /\ <1>2!laby <=> LEGAL
       /\ <1>2!labx <=> LEGAL
       /\ <1>2!lab1 <=> LEGAL
       /\ <1>2!lab2 <=> LEGAL
       /\ <1>2!1!5 <=> LEGAL
       /\ <1>2!1!5!2  <=> LEGAL
       /\ <1>2!2    <=> ILLEGAL

<1>3. SUFFICES 1 = 2

<1>4. QED

Bar == /\ foo!labx <=> LEGAL
       /\ foo!laby <=> ILLEGAL
       /\ foo!labi <=> ILLEGAL
       /\ foo!labu <=> ILLEGAL
       /\ foo!3    <=> ILLEGAL
==================

CONSTANT x
THEOREM TRUE
<1>1. x = 1
<1>4. QED
================
<2>21 bar == 1 foobar == 2
<2>31 foo
  BY DEF <2>21
(****
<2>22 WITNESS TRUE
<2>32 <2>22
<2>23 TAKE x \in {}
<2>33 <2>23
<2>24 PICK y \in {} : TRUE
<2>34 <2>24
<2>25 CASE TRUE
<2>35 <2>25
*****)
<2>3 QED
  <3>1 TRUE\* <2>3
     BY <2>31
  <3>2 QED
=================
VARIABLE y
Foo(x) == INSTANCE Test1 
LOCAL fcn[x \in {}] == x
USE MODULE Test, MODULE Test1 DEFS (* MODULE Test, *) MODULE Test1, Foo
Bar == Foo(1)!-(1, 2)
================================

THEOREM ASSUME ASSUME P PROVE
        PROVE  P
BY Foo \* DEFS Foo

THEOREM foo7 == TRUE
 <0>1. TRUE
 <*>.... <0>1
     <007>1. TRUE
     <07>2. QED
 <000>3 QED

=================
\* Foo == <1>1 
THEOREM foobar == TRUE
<*>1. TRUE
PROOF
 <+>1. TRUE
   <+> TRUE
   <*>11. TRUE
   <*>12 TRUE
   <2>13. TRUE
   <2>14 TRUE 
   <2>2a TRUE
   <*>2 <2>2a
   <*>3. TRUE
   <*> QED
 <*>2. QED
<0>4. TRUE
<0>1a <0>4
<0>2. QED

THEOREM foo == ASSUME CONSTANT a,
                     VARIABLE c,
                      STATE b
               PROVE  TRUE
PROOF
<+>1. TRUE
       PROOF <+>a. TRUE
             <1>3. TRUE
             <*> Test == <1>a

             <1>4. QED
              <+> <1>3
              <2> QED
<0>... QED

AXIOM TRUE

THEOREM ASSUME CONSTANT a,
               CONSTANT b \in {} ,
               VARIABLE c,
               STATE d,
               ACTION e,
               TEMPORAL f
        PROVE  e = e

THEOREM ASSUME NEW a,
               NEW CONSTANT b \in {} ,
               NEW VARIABLE c,
               NEW STATE d,
               NEW ACTION e,
               NEW TEMPORAL f
        PROVE  TRUE

OBVIOUS

THEOREM TRUE
OMITTED

THEOREM TRUE
PROOF OBVIOUS

THEOREM TRUE
PROOF OMITTED

a+b == <<a, b>>

THEOREM TRUE
BY TRUE DEF +

THEOREM TRUE
BY TRUE DEFS +

THEOREM TRUE
PROOF BY TRUE DEFS +



THEOREM TRUE
<1>ab.... TRUE
  PROOF
  <33>0 TRUE
        BY <1>ab
  <33>1 HAVE ~ (TRUE /\ <33>0)
  <33>2 TAKE Id, Id1
  <33>3 TAKE Id4 \in {1}, <<Id2, Id3>> \in {2}
  <33>123 FooBar == <<Id, Id1, Id4, Id2, Id3>>
  <33>4 WITNESS {1} \cup <33>1!1!1!2
  <33>5 WITNESS {1} \in {2}, {3}
  <33>-... PICK x : ~ FALSE
          <+>*.   PICK y \in {1} : ~ FALSE
          <*>* QED
  <33>7 PICK y \in {1} : <33>5!1!1 + <33>3!1
    PROOF <*>1... TRUE
          <*>2.... USE <*>1, <33>5, <33>7!1!1, <33>7!(42)!<< DEF +

          <*>3 QED
  <33>7a Foo == << <33>7!(1)!<< , <33>7!>> >>
  <33>8 PICK z \in {1}, <<y1, z1>> \in {2} : ~ FALSE
  <33>9 PICK w, u : <<1, 2, 3>>
    <34>* DEFINE A == <<x, y, z, y1, z1>>
    <34>*. B == A!1
           C == A
    <34> QED
  <33>44 DEFINE A == <<x, y, z, y1, z1, w, u>>
  <33>*. B == <33>9!(1,2)!3
  <33>. BBC(Op(_,_)) == Op(1,2)
        DD == BBC(<33>9!@)
  <33>22 ASSUME TRUE PROVE FALSE
  <33>  BBB == \A xxxx \in {} : TRUE
  <33>14. INSTANCE Test1
  <*>  AA == INSTANCE Test1
  <*>a ASSUME FALSE PROVE TRUE 
  <33>b CASE TRUE /\ <33>22!1
  <33>c SUFFICES TRUE
  <33>. SUFFICES ASSUME FALSE PROVE TRUE
  <33>2a. QED
<1>14 HAVE <<1, 2, 3>>
<1>14a havedef == <1>14!1!3
<*> TAKE Id7 \in {1}
<*> WITNESS {1} \in {2}
<*> PICK x2 \in {1}, y2 \in {2} : ~ FALSE
   <+> PICK x3, y3 : ~ FALSE
   <*>*. DEFINE A2 == 1
   <*>2 B2 == 17
   <*> ASSUME FALSE PROVE TRUE 
   <*> CASE TRUE
   <*> TRUE
   <*> SUFFICES ASSUME FALSE PROVE TRUE
   <2> QED
<1>... DEFINE A == 1
<1> B == 17
<1> INSTANCE Test1 WITH x <- 27
<1> AA == INSTANCE Test2 WITH B <- 1
<1>3. QED

===============================

\* Foo == \A x , y, z : TRUE
\* Bar == \A x \in {}, y, z \in {}, <<u, v>> \in {} : TRUE
\* Inst(a) == INSTANCE Test1
\* Foo == Inst(7)!Bar1
THEOREM Thm2 == TRUE
 <1>2 QED
       PROOF USE <1>2
             QED
====================
 PROOF 
\* DEFINE Def1 == TRUE
 USE Thm2!:  \* DEF Thm2 , Inst!Bar2
\* Def2 == TRUE
 QED
\*   PROOF USE Def1 DEFS Def2
\*         QED
=================================
THEOREM Thm3 == FALSE
 PROOF DEFINE A == B
       PROVE /\ TRUE
             /\ 1=1
         BY Thm2
       QED
==========================================================
THEOREM 1
 PROOF QED
       PROOF OBVIOUS
=================================================
=============================================================================

BY [.]
USE DEF FALSE
HIDE 
<1>abc FALSE
      BY MODULE M DEF MODULE M, 2 [.]
A == B
DEFINE F == INSTANCE M
A[x \in S] == B
INSTANCE M
<1>2. QED
(********
  PROOF ASSUME TRUE PROVE FALSE
          <1>1. TRUE
          <1>2. QED
        HAVE TRUE
        QED
********)
=============================================================================
