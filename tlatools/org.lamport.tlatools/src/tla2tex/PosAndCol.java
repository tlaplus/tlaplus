// Copyright (c) 2003 Compaq Corporation.  All rights reserved.

/***************************************************************************
* CLASS PosAndCol                                                          *
*                                                                          *
* A PosAndCol object is a Position extended by a column field.  It has a   *
* the method:                                                              *
*                                                                          *
*   void sort(PosAndCol[] array)                                           *
*                                                                          *
*      Sorts the array first by column and, within column, by line.        *
***************************************************************************/
package tla2tex;
// import tlatex.Position;
//import java.util.Comparator;
public class PosAndCol extends Position
 { public int column ;

   public PosAndCol(int l, int i, int c)
    { item = i ;
      line = l ;
      column = c ;
    } ;
   
   /************************************************************************
   * The following heap-sorting method was obtained by trivially modifying *
   * a method found on the web with the following header:                  *
   *                                                                       *
   *    HeapSortAlgorithm.java 1.0 95/06/23 Jason Harrison                 *
   *    Copyright (c) 1995 University of British Columbia                  *
   *                                                                       *
   *    Permission to use, copy, modify, and distribute this software      *
   *    and its documentation for NON-COMMERCIAL purposes and without      *
   *    fee is hereby granted provided that this copyright notice          *
   *    appears in all copies.                                             *
   *                                                                       *
   *    UBC MAKES NO REPRESENTATIONS OR WARRANTIES ABOUT THE SUITABILITY   *
   *    OF THE SOFTWARE, EITHER EXPRESS OR IMPLIED, INCLUDING BUT NOT      *
   *    LIMITED TO THE IMPLIED WARRANTIES OF MERCHANTABILITY, FITNESS      *
   *    FOR A PARTICULAR PURPOSE, OR NON-INFRINGEMENT. UBC SHALL NOT BE    *
   *    LIABLE FOR ANY DAMAGES SUFFERED BY LICENSEE AS A RESULT OF         *
   *    USING, MODIFYING OR DISTRIBUTING THIS SOFTWARE OR ITS              *
   *    DERIVATIVES                                                        *
   ************************************************************************/
    public static void sort(PosAndCol a[]) 
      { int N = a.length; 
        for (int k = N/2; k > 0; k--) 
           { downHeap(a, k, N); 
           } 
        do { PosAndCol T = a[0]; 
             a[0] = a[N - 1]; 
             a[N - 1] = T;
             N = N - 1; 
             downHeap(a, 1, N); 
           } 
        while (N > 1); 
      }									
    private static void downHeap(PosAndCol a[], int k, int N) 
      { PosAndCol T = a[k - 1]; 
        while (k <= N/2) 
          { int j = k + k; 
            if ((j < N) && PosAndCol.lessThan(a[j - 1],a[j]))
              { j++; } 
            if ( ! PosAndCol.lessThan(T, a[j - 1]) )
              { break; } 
           else 
              { a[k - 1] = a[j - 1]; 
                k = j; 
              } 
          }
        a[k - 1] = T; 
      } 

   private static boolean lessThan(PosAndCol pc1, PosAndCol pc2)
    { if (pc1.column < pc2.column)
        { return true ;}
      else
        { if (pc1.column == pc2.column)
            { return (pc1.line < pc2.line) ;
            }
          else
            { return false ;
            }
        }
    }
 
   public String toString()
    { return   "[line |-> " + line + ", item |-> " + item 
             + ", col |-> " + column + "]";
    }
  }

/* Last modified on Tue 18 Sep 2007 at  6:51:12 PST0by lamport */
