-------------------------------- MODULE test64 --------------------------------
VARIABLE y   
 
I == INSTANCE test64a WITH x <- y  
  \* Changed from Test64a on 12 June 2014 because that's now illegal

Spec == I!Spec
=======================================================================
