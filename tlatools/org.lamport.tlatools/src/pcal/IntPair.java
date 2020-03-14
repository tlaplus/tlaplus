/***************************************************************************
* CLASS IntPair                                                            *
*                                                                          *
* Having a procedure return a tuple of values is an obvious thing to do.   *
* After 40 years of programming-language design, one might have expected   *
* that any language that pretends to be slightly higher-level than         *
* assembly language would provide a simple way to do that.  But no such    *
* luck.  The only way I can figure out to write a procedure in Java that   *
* returns a tuple of values is to define a separate class of objects for   *
* each type of tuple one wants.  So, here's a class whose objects are      *
* pairs of ints.  More precisely, IntPair(a, b) is the constructor of      *
* object obj such that obj.one = a and obj.two = b.  (It would             *
* be nicer to name the fields "1st" and "2nd", but apparently Java isn't   *
* sophisticated enough to allow such esoteric field names, and "first"     *
* and "second" are too long.  I'm surprised it lets me call them "one"     *
* and "two" instead of requiring them to be called "zero" and "one".)      *
***************************************************************************/
package pcal;

public class IntPair
  { public int one = 0 ;
    public int two = 0 ;
    public IntPair(int a, int b)
     { one = a ; 
       two = b ;
     }

    /***********************************************************************
    * For debugging.                                                       *
    ***********************************************************************/
    public String toString()
     { return "(" + one + ", " + two + ")" ;
     }    
  }
