------------------------------- MODULE test213 ------------------------------ 
\* Test that 
\* - A non-temporal theorem or proof step cannot have a
\*   temporal formula in its proof.
\* - A declared constant that appears in an ASSUME or an ASSUME/PROVE
\*   cannot be instantiated with a temporal formula 
\*
\* Parsing only; produces errors.

VARIABLE x

I1 == INSTANCE test213b WITH C <- x', D <- x' 
I2 == INSTANCE test213b WITH C <- [](x=0), D <- TRUE \* ERROR
I3 == INSTANCE test213b WITH C <- TRUE, D <- [](x=0) \* ERROR

THEOREM [](x=0)
<1>1. CASE FALSE
  <2>1. [](x=0)
  <2>2. QED
    <3>1. [](x # 0)
      BY [](x # 0)
    <3>2. QED
<1>2. x=0        \* ERROR
  <2>1. (x=0)   
  <2>2. QED
    <3>1. [](x=0)  
    <3>2. QED
<1>3. CASE TRUE
 <2>1. CASE x=0  \* ERROR
 <2>1a. CASE FALSE
 <2>2. HAVE x=0  \* ERROR
 <2>2a HAVE TRUE 
 <2>3. WITNESS 3 \in x \* ERROR
 <2>4. WITNESS 2 \in {}
 <2>5. QED
<1>4. QED
  <2>1. [](x=0)
  <2>2. QED
 


THEOREM x=0  \* ERROR
 <1>1. x'=0     \* ERROR
   BY [](x=0)   \* This BY causes an error, though it needn't 
 <1>2. [](x=0)  \* this causes error in THEOREM
 <1>3. QED
=============================================================================