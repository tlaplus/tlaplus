------------------------------- MODULE test219 ------------------------------ 
\* Test of use of labels from instantiated theorems, and repeat
\* test of some instantiations

EXTENDS TLC , Integers

I(x) == INSTANCE test219a WITH C <- 4  
J == INSTANCE test219a WITH C <- 4  
INSTANCE test219a WITH C <- 4 

LOCAL K(x) == INSTANCE test219a WITH C <- 4  
LOCAL L == INSTANCE test219a WITH C <- 4  


ASSUME J!Thm2!lab3
ASSUME I(55)!Thm2!lab3
ASSUME L!Thm2!lab3
ASSUME K(55)!Thm2!lab3
ASSUME Thm2!lab3


ASSUME Op(Foo, 9) 

ASSUME Thm2!lab3

ASSUME Bar

ASSUME Op(Foo, 9)!lab(1,2,3)!label2 = Op(Foo, 9)!lab(1,2,3)!:!++(9, 4) 
ASSUME OOp1(SOp1, 2) = 2
ASSUME OOp2(SOp1b!@, 2, 3) = 5
ASSUME OOp2(SOp1c!@!c, 2, 3) = 2 * 3
ASSUME OOp3(SOp1d!@!c, 2, 3, 4) = 2 * 3 + 4
ASSUME Op1(2)!(3)!2!1 = 2 + 4*3 + 6
ASSUME Op1(2)!(3)!2!Op1a(4) = 16 + 6
ASSUME Op3(Op1!@!2!Op1a, 2, 3, 4) = 22
ASSUME COp(1, 2)!(3)!++(4, 5) = {2,1, 3, 4, 5}
ASSUME COp(1, 2)!(3) = <<1, {99, 1, 2, 3} >>
ASSUME COp(1, 2)!(3)!1 = <<1, {99, 1, 2, 3} >>
ASSUME COp(1, 2)!(3)!1!>> = {99, 1, 2, 3}
ASSUME OOp5(COp!@!++, 1, 2, 3, 4, 5) = {2,1, 3, 4, 5}
ASSUME COp(1, 2)!lab(3)!:!++(4, 5) = {2,1, 3, 4, 5}
ASSUME Inst!Foo(1, 2, 3, 4, 5) = {2,1, 3, 4, 5}
ASSUME Inst!Bar(3)!>> = 3
ASSUME Inst!Bar2(3)!>> = 3
ASSUME Inst!Bar3!>> = 2
ASSUME Inst!Bar4(1)!(2)!<< = 2
ASSUME Inst!Bar4(1)!(2)!>> = 1
ASSUME Inst!Bar4(1)!lab(2)!<< = 2
ASSUME Inst!Bar4(1)!lab(2)!>> = 1
ASSUME OOp2(Inst!Bar4!@!<<, 1, 2) = 2
ASSUME OOp2(Inst!Bar4!@!>>, 1, 2) = 1
ASSUME OOp2(Inst!Bar4!lab!<<, 1, 2) = 2
ASSUME OOp2(Inst!Bar4!lab!>>, 1, 2) = 1
ASSUME Inst!Bar5(1)!lab(2)!:!++(3, 4) = <<1, 3, 4, 2>>
ASSUME Inst!Bar5(1)!(2)!++(3, 4) = <<1, 3, 4, 2>>
ASSUME OOp4(Inst!Bar5!lab!:!++, 1, 2, 3, 4) = <<1, 3, 4, 2>>
ASSUME Inst2(COp!@!++)!Foo(1, 2, 3, 4, 5) = {2,1, 3, 4, 5}
ASSUME COp2(1,2)!lab(3)!:!++(9,10)!lab(11) = 30
ASSUME COp2(1,2)!(3)!++(9,10)!lab(11) = 30
ASSUME COp2(1,2)!lab(3)!:!++(9,10)!(11) = 30
ASSUME OOp6(COp2!lab!:!++!lab, 1, 2, 3, 9, 10, 11) = 30
ASSUME OOp6(COp2!@!++!lab, 1, 2, 3, 9, 10, 11) = 30
ASSUME OOp6(COp2!lab!:!++!@, 1, 2, 3, 9, 10, 11) = 30
ASSUME Def1!2 = 2
ASSUME Def2!(14)!<< = 14
ASSUME Def3!2!1 = 2
ASSUME Def3!(1, 2)!<< = 1
ASSUME Def4!<<!<<!2 = {2}
ASSUME Def5!>> = 3
ASSUME Def5!<<[4] = 5
ASSUME Def5!<<!1!>> = 10
ASSUME Def6!1[3] = 4
ASSUME Def7!1 = 3
ASSUME Def7!2 = "a"
ASSUME Def8!2 = 2
ASSUME Def9!2 = 2
ASSUME Def10!2 = 2
ASSUME Def11!3!1 = 3

ASSUME L!Op(Foo, 9)!lab(1,2,3)!label2 = Op(Foo, 9)!lab(1,2,3)!:!++(9, 4) 
ASSUME L!OOp1(SOp1, 2) = 2
ASSUME L!OOp2(SOp1b!@, 2, 3) = 5
ASSUME L!OOp2(SOp1c!@!c, 2, 3) = 2 * 3
ASSUME L!OOp3(SOp1d!@!c, 2, 3, 4) = 2 * 3 + 4
ASSUME L!Op1(2)!(3)!2!1 = 2 + 4*3 + 6
ASSUME L!Op1(2)!(3)!2!Op1a(4) = 16 + 6
ASSUME L!Op3(Op1!@!2!Op1a, 2, 3, 4) = 22
ASSUME L!COp(1, 2)!(3)!++(4, 5) = {2,1, 3, 4, 5}
ASSUME L!COp(1, 2)!(3) = <<1, {99, 1, 2, 3} >>
ASSUME L!COp(1, 2)!(3)!1 = <<1, {99, 1, 2, 3} >>
ASSUME L!COp(1, 2)!(3)!1!>> = {99, 1, 2, 3}
ASSUME L!OOp5(COp!@!++, 1, 2, 3, 4, 5) = {2,1, 3, 4, 5}
ASSUME L!COp(1, 2)!lab(3)!:!++(4, 5) = {2,1, 3, 4, 5}
ASSUME L!Inst!Foo(1, 2, 3, 4, 5) = {2,1, 3, 4, 5}
ASSUME L!Inst!Bar(3)!>> = 3
ASSUME L!Inst!Bar2(3)!>> = 3
ASSUME L!Inst!Bar3!>> = 2
ASSUME L!Inst!Bar4(1)!(2)!<< = 2
ASSUME L!Inst!Bar4(1)!(2)!>> = 1
ASSUME L!Inst!Bar4(1)!lab(2)!<< = 2
ASSUME L!Inst!Bar4(1)!lab(2)!>> = 1
ASSUME L!OOp2(Inst!Bar4!@!<<, 1, 2) = 2
ASSUME L!OOp2(Inst!Bar4!@!>>, 1, 2) = 1
ASSUME L!OOp2(Inst!Bar4!lab!<<, 1, 2) = 2
ASSUME L!OOp2(Inst!Bar4!lab!>>, 1, 2) = 1
ASSUME L!Inst!Bar5(1)!lab(2)!:!++(3, 4) = <<1, 3, 4, 2>>
ASSUME L!Inst!Bar5(1)!(2)!++(3, 4) = <<1, 3, 4, 2>>
ASSUME L!OOp4(Inst!Bar5!lab!:!++, 1, 2, 3, 4) = <<1, 3, 4, 2>>
ASSUME L!Inst2(COp!@!++)!Foo(1, 2, 3, 4, 5) = {2,1, 3, 4, 5}
ASSUME L!COp2(1,2)!lab(3)!:!++(9,10)!lab(11) = 30
ASSUME L!COp2(1,2)!(3)!++(9,10)!lab(11) = 30
ASSUME L!COp2(1,2)!lab(3)!:!++(9,10)!(11) = 30
ASSUME L!OOp6(COp2!lab!:!++!lab, 1, 2, 3, 9, 10, 11) = 30
ASSUME L!OOp6(COp2!@!++!lab, 1, 2, 3, 9, 10, 11) = 30
ASSUME L!OOp6(COp2!lab!:!++!@, 1, 2, 3, 9, 10, 11) = 30
ASSUME L!Def1!2 = 2
ASSUME L!Def2!(14)!<< = 14
ASSUME L!Def3!2!1 = 2
ASSUME L!Def3!(1, 2)!<< = 1
ASSUME L!Def4!<<!<<!2 = {2}
ASSUME L!Def5!>> = 3
ASSUME L!Def5!<<[4] = 5
ASSUME L!Def5!<<!1!>> = 10
ASSUME L!Def6!1[3] = 4
ASSUME L!Def7!1 = 3
ASSUME L!Def7!2 = "a"
ASSUME L!Def8!2 = 2
ASSUME L!Def9!2 = 2
ASSUME L!Def10!2 = 2
ASSUME L!Def11!3!1 = 3

ASSUME I(55)!Op(Foo, 9)!lab(1,2,3)!label2 = Op(Foo, 9)!lab(1,2,3)!:!++(9, 4) 
ASSUME I(55)!OOp1(SOp1, 2) = 2
ASSUME I(55)!OOp2(SOp1b!@, 2, 3) = 5
ASSUME I(55)!OOp2(SOp1c!@!c, 2, 3) = 2 * 3
ASSUME I(55)!OOp3(SOp1d!@!c, 2, 3, 4) = 2 * 3 + 4
ASSUME I(55)!Op1(2)!(3)!2!1 = 2 + 4*3 + 6
ASSUME I(55)!Op1(2)!(3)!2!Op1a(4) = 16 + 6
ASSUME I(55)!Op3(Op1!@!2!Op1a, 2, 3, 4) = 22
ASSUME I(55)!COp(1, 2)!(3)!++(4, 5) = {2,1, 3, 4, 5}
ASSUME I(55)!COp(1, 2)!(3) = <<1, {99, 1, 2, 3} >>
ASSUME I(55)!COp(1, 2)!(3)!1 = <<1, {99, 1, 2, 3} >>
ASSUME I(55)!COp(1, 2)!(3)!1!>> = {99, 1, 2, 3}
ASSUME I(55)!OOp5(COp!@!++, 1, 2, 3, 4, 5) = {2,1, 3, 4, 5}
ASSUME I(55)!COp(1, 2)!lab(3)!:!++(4, 5) = {2,1, 3, 4, 5}
ASSUME I(55)!Inst!Foo(1, 2, 3, 4, 5) = {2,1, 3, 4, 5}
ASSUME I(55)!Inst!Bar(3)!>> = 3
ASSUME I(55)!Inst!Bar2(3)!>> = 3
ASSUME I(55)!Inst!Bar3!>> = 2
ASSUME I(55)!Inst!Bar4(1)!(2)!<< = 2
ASSUME I(55)!Inst!Bar4(1)!(2)!>> = 1
ASSUME I(55)!Inst!Bar4(1)!lab(2)!<< = 2
ASSUME I(55)!Inst!Bar4(1)!lab(2)!>> = 1
ASSUME I(55)!OOp2(Inst!Bar4!@!<<, 1, 2) = 2
ASSUME I(55)!OOp2(Inst!Bar4!@!>>, 1, 2) = 1
ASSUME I(55)!OOp2(Inst!Bar4!lab!<<, 1, 2) = 2
ASSUME I(55)!OOp2(Inst!Bar4!lab!>>, 1, 2) = 1
ASSUME I(55)!Inst!Bar5(1)!lab(2)!:!++(3, 4) = <<1, 3, 4, 2>>
ASSUME I(55)!Inst!Bar5(1)!(2)!++(3, 4) = <<1, 3, 4, 2>>
ASSUME I(55)!OOp4(Inst!Bar5!lab!:!++, 1, 2, 3, 4) = <<1, 3, 4, 2>>
ASSUME I(55)!Inst2(COp!@!++)!Foo(1, 2, 3, 4, 5) = {2,1, 3, 4, 5}
ASSUME I(55)!COp2(1,2)!lab(3)!:!++(9,10)!lab(11) = 30
ASSUME I(55)!COp2(1,2)!(3)!++(9,10)!lab(11) = 30
ASSUME I(55)!COp2(1,2)!lab(3)!:!++(9,10)!(11) = 30
ASSUME I(55)!OOp6(COp2!lab!:!++!lab, 1, 2, 3, 9, 10, 11) = 30
ASSUME I(55)!OOp6(COp2!@!++!lab, 1, 2, 3, 9, 10, 11) = 30
ASSUME I(55)!OOp6(COp2!lab!:!++!@, 1, 2, 3, 9, 10, 11) = 30
ASSUME I(55)!Def1!2 = 2
ASSUME I(55)!Def2!(14)!<< = 14
ASSUME I(55)!Def3!2!1 = 2
ASSUME I(55)!Def3!(1, 2)!<< = 1
ASSUME I(55)!Def4!<<!<<!2 = {2}
ASSUME I(55)!Def5!>> = 3
ASSUME I(55)!Def5!<<[4] = 5
ASSUME I(55)!Def5!<<!1!>> = 10
ASSUME I(55)!Def6!1[3] = 4
ASSUME I(55)!Def7!1 = 3
ASSUME I(55)!Def7!2 = "a"
ASSUME I(55)!Def8!2 = 2
ASSUME I(55)!Def9!2 = 2
ASSUME I(55)!Def10!2 = 2
ASSUME I(55)!Def11!3!1 = 3

ASSUME /\ Def12!1!<< = 2
       /\ Def12!2 = 2
       /\ Def12!3 = 3
ASSUME /\ Def13!(42)!1!<<!<< = 42
       /\ Def13!(42)!1!>> = 1
       /\ Def13!(42)!2!>> = 2
       /\ Def13!(42)!3!>> = 3

ASSUME /\ Def14!(2)!<< = 2
       /\ Def14!1!1 = 1

ASSUME /\ Def15!(2,3)!<<!<< = 2
       /\ Def15!(2,3)!>>!<< = 3
       /\ Def15!2!<< = 2

ASSUME /\ Def16!(2,3,4)!1!1 = 2
       /\ Def16!(2,3,4)!2!1 = 3
       /\ Def16!2!1!<< = 2

ASSUME /\ Def17!(2,3,4)!1!1 = 2
       /\ Def17!(2,3,4)!2!1 = 3

ASSUME Def18!(2)!<< = 2

ASSUME /\ Def19!(2)!<< = 2
       /\ Def19!1!1 = 42

ASSUME /\ Def20!1 = 12
       /\ Def20!>> = 23

ASSUME /\ Def21!1 = 12
       /\ Def21!>> = 23

ASSUME /\ Def22!1 = 12
       /\ Def22!>> = 23

ASSUME /\ Def23!(2,3,4)!1!1 = 2
       /\ Def23!(2,3,4)!2!1 = 3


=============================================================================

last modified on Thu  1 November 2012 at 10:11:43 PST by lamport
==============================================================================