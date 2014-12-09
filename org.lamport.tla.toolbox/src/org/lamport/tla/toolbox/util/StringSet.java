/**
 * 
 */
package org.lamport.tla.toolbox.util;

import java.util.HashSet;
import java.util.Iterator;
import java.util.Vector;

/**
 * A StringSet object represents a set of strings.  It provides the following
 * methods: 
 * 
 *   add(elt) : Adds the element elt to the set (no-op if elt is
 *              already in the set.
 *              
 *   addAll(sset) : Adds all the elements of the StringSet sset to the 
 *                 set represented by this object.
 *   
 *   contains(elt) : Returns true iff the element is in the set.
 *   
 *   isEmpty() : True iff the set is empty
 *   
 *   toCommaSeparatedString() : Returns the comma-separated list of all the
 *                              elements of the set.
 *                              
 *   CommaSeparatedListToStringSet(str) : 
 *      Assumes str is a comma-separated list of strings, each of which
 *      does not contain a comma or a space.  There may be arbitrary amounts
 *      of space (including none) anywhere in str.  It returns the corresponding
 *      StringSet.
 *   
* There is also a constructor that turns a HashSet<String> object
 * into a StringSet.
 * 
 * Because of the way Java implements strings, a HashSet provides these 
 * functions most of the time.  However, there are some ways of creating
 * strings that produces different String objects, and hence would put
 * two different copies of the same string into a HashSet--or might fail
 * to recognize that a string is in the HashSet.  So, this method is
 * used to be safe. 
 * 
 * This method is not implemented very efficiently, and should not be 
 * where space or execution time is an issue.  The implementation is based
 * on the algorithm in module BinarySort at the end of this file.
 *   
 * @author lamport
 *
 */
public class StringSet {

    
    private Vector<String> contents = new Vector<String>() ;

    
    public void add(String str) {
       int position = 0 ;
       if (contents.size() == 0) {
           contents.add(str) ;
           return ;
       }
       
       
       position = this.binarySearch(str) ;
       
       if ((position == -1)  || ! str.equals(contents.elementAt(position))) {
           contents.add(position+1, str) ;
       }
       return ;
    }

    public void addAll(StringSet ss) {
        for (int i=0; i < ss.contents.size(); i++) {
            this.add(ss.contents.elementAt(i)) ;
        }
    }
    public boolean contains(String str) {
        int position = binarySearch(str) ;
        if (position == -1) {
            return false;
        }
        return str.equals(contents.elementAt(binarySearch(str))) ;    
    }
    
    public boolean isEmpty() {
        return contents.size() == 0 ;
    }
    
    /**
     * Returns the following value, where << is lexicographical ordering
     * of strings:
     * 
     *   IF contents.size() = 0 \/ str << contents(0) 
     *     THEN -1
     *     ELSE the largest integer i in 0..(contents.size()-1) such that contents(i) =<< str
     *     
     * It uses the algorithm BinarySearch appended at the end of this file.
     * 
     * @param str
     * @return
     */
    private int binarySearch(String str) {
        if ( (contents.size() == 0) || (str.compareTo(contents.elementAt(0)) < 0) ) {
            return -1 ;
        }
        if (contents.elementAt(contents.size()-1).compareTo(str) <= 0) {
            return contents.size() - 1 ;
        }
        int bot = 0 ;
        int top = contents.size() - 1;
        while (bot+1 < top) {
          int mid = bot + ((top - bot) / 2) ;
          if (str.compareTo(contents.elementAt(mid)) < 0) {
              top = mid ;
          }
          else {
              bot = mid ;
          }
        }
        return bot ;
    }
    
    /*
     *  The Constructors
     */
    public StringSet() {
    }
    
    public StringSet(HashSet<String>hSet) {
        Iterator iter = hSet.iterator() ;
        while (iter.hasNext()) {
            contents.add((String) iter.next()) ;
        }
    }
    
    /**
     * Returns a shallow copy of the set, which for Strings is
     * equivalent to a deep copy.
     */
    public StringSet clone() {
        StringSet result = new StringSet() ;
        for (int i=0; i < contents.size(); i++) {
            result.add(contents.elementAt(i)) ;
        }
        return result;
    }
    
    /**
     * Returns the comma-separated list of all the elements of the list.
     * It returns "" if the set is empty.
     * @return
     */
    public String toCommaSeparatedString() {
        String result = "" ;
        for (int i=0 ; i < contents.size(); i++) {
            if (result.equals("")) {
                result = contents.elementAt(i) ;
            }
            else {
                result = result + ", " + contents.elementAt(i) ;
            }
        }
        return result ;
    }
    
    public static StringSet CommaSeparatedListToStringSet(String str) {
        StringSet result = new StringSet();
        String[] elements = str.split(",") ;
        for (int i=0; i < elements.length; i++) {
            result.add(elements[i].trim()) ;
        }
        return result;      
    }
    /**
     * For debugging.
     */
    public String toString() {
        return contents.toString() ;
    }
    
    /**
     * The following method tests all possible ways of constructing a StringSet by performing
     * five add() operations to add an element in {"1", ... , "max"} and checking that
     * it produces a StringSet such that content is lexicographically ordered without
     * duplicates and the value returned by contains(s) for any of those elements is the
     * same as for an identically constructed HashSet.  It also checks that the addAll
     * method and that the empty set contains no elements.
     * 
     * Note: The first version of this test was buggy and essentially tested
     * just five different sets.  The next version was slightly less buggy, but
     * was still checking many fewer sets than it should have.
     *   
     * ONE HAS TO TEST THAT A TEST IS TESTING WHAT YOU THINK IT'S TESTING.
     */
    public static void test() { 
       int max = 12 ;
       int[] elts = new int[5] ;
        for (int i=1 ; i < max; i++) {
          elts[0] = i;
           for (int j=1 ; j < max; j++) {
              elts[1] = j;              
              for (int k=1 ; k < max; k++) {
                  elts[2] = k ;
                  for (int m=1 ; m < max; m++) {
                      elts[3] = m ;
                      for (int n=1 ; n < max; n++) {
                          elts[4] = n ;
                          innerTest(elts, max) ;
                      }
                  }
              }
           }
        }
    }
    
    public static void innerTest(int[] elts, int max) {
        int n = elts.length;
        StringSet ss = new StringSet() ;
        HashSet<String> hs = new HashSet<String>();
        StringSet ss1 = new StringSet() ;
        StringSet ss2 = new StringSet() ;
        String str = "" ;
        for (int i=0; i < n; i++) {
           ss.add(""+elts[i]);
           hs.add(""+elts[i]);
           if (i>0) {
               str = str + " , " ;
           }
           str = str + elts[i] ;
           if (i < n/2) {
               ss1.add(""+elts[i]);
           } else {
               ss2.add(""+elts[i]);
           }  
        }
        
        // Check that contents is properly ordered
        for (int t=1; t < ss.contents.size()-1; t++) {
            if (! (ss.contents.elementAt(t).compareTo(ss.contents.elementAt(t+1)) < 0)) {
                System.out.println(t+", "+(t+1)+" malordered in: " + ss.toCommaSeparatedString());
            }
        }
        // Check that ss and hs have same elements
        for (int r=1; r < n; r++) {
            if (ss.contains(""+r) != hs.contains(""+r)) {
                System.out.println("ss and hs differ on " + r + " in: " + ss.toCommaSeparatedString()) ;
            }
        }
        // Check union of "two halves" 
        StringSet ss3 = ss1.clone(); ss3.addAll(ss2) ;
        for (int z=1; z < max; z++) {
            if (ss3.contains(""+z) != (ss1.contains(""+z) || ss2.contains(""+z))) {
                System.out.println(ss3.toCommaSeparatedString() + " != " +
                   ss1.toCommaSeparatedString() + " + " + ss2.toCommaSeparatedString());
            }
        }
        // Check CommaSeparatedListToStringSet
       
        StringSet csl = CommaSeparatedListToStringSet(str);
        if (!csl.toCommaSeparatedString().equals(ss.toCommaSeparatedString())) {
            System.out.println(csl.toCommaSeparatedString() + " != " + ss.toCommaSeparatedString()) ;
        }

        // Check handling of empty set.
        StringSet ss4 = new StringSet() ;
        if (ss4.contains("1")) {
            System.out.println("The empty set is not empty") ;
        }
    }
}

// The following module has been model-checked for N = 7.
//
//----------------------------- MODULE BinarySearch -----------------------------
//(***************************************************************************)
//(* This module describes algorithm an algorithm that does the following.   *)
//(* Given an increasing sequence <<e_1, ...  , e_n>> of distinct integers   *)
//(* and an integer e , it returns                                           *)
//(*                                                                         *)
//(*    IF n = 0 \/ e < e_1                                                  *)
//(*      THEN 0                                                             *)
//(*      ELSE the largest integer i in 1..n such that e_i =< e              *)
//(*                                                                         *)
//(* (The algorithm uses binary search.)                                     *)
//(*                                                                         *)
//(* This algorithm is used as the basis of code for implementing a class of *)
//(* object representing a set, with the the two operations of adding an     *)
//(* element to the set and determining if the set contains a given element. *)
//(*                                                                         *)
//(* Note: When implementing this method in Java, I made the following       *)
//(* error.  In translating from 1-based to 0-based indexing, I failed to    *)
//(* translate the value 0 returned by the first `if' test to -1.  This      *)
//(* caused a bug that was not found by the testing I did, which was         *)
//(* perfunctory because I was implementing a correct algorithm.  There are  *)
//(* two possible lessons to be drawn from this mistake:                     *)
//(*                                                                         *)
//(*  - Since my goal was to implement binary search on Java arrays, I       *)
//(*    should have written the algorithm to search a function with domain   *)
//(*    0..(N-1) rather than a sequence of length N.                         *)
//(*                                                                         *)
//(*  - I should have been more conscientious in testing my implementation,  *)
//(*    especially in checking boundary cases.                               *)
//(***************************************************************************)
//EXTENDS Integers, Sequences, TLC
//
//CONSTANT N  \* The maximum length of input sequence on which to test the 
//            \* algorithm.
//
//TestSequences == { seq \in UNION { [1..i -> -1 .. (N+1)] : i \in 0..N } :
//                     \A j \in 1..(Len(seq)-1) : \A k \in (j+1)..Len(seq) :
//                        seq[j] < seq[k] }
//
//Max(S) == CHOOSE x \in S : \A y \in S : x >= y
//
//CorrectValue(seq, i) == IF Len(seq) = 0 \/ i < seq[1]
//                          THEN 0
//                          ELSE Max ({j \in DOMAIN seq : seq[j] =< i})
//
//(***************************************************************************
//--fair algorithm BinarySearch {
//  variables seq \in TestSequences, elt \in (-1)..(N+1) ,
//            bot = 1 , top = Len(seq), result ;
//            
//  { if ( (Len(seq) = 0) \/ (elt < seq[1]) ) { result := 0 }
//    else if (seq[Len(seq)] =< elt) { result := Len(seq) }
//    else 
//       \* while loop maintains the invariant that :
//       \*  (bot < top) /\ (seq[bot] =< elt < seq[top]) /\ 
//     { while (bot+1 < top) 
//         { with (mid = bot + ((top - bot) \div 2)) 
//            { if (elt < seq[mid]) { top := mid }
//              else {bot := mid} 
//            } 
//         } ;
//       result := bot 
//     } ;
//    assert result = CorrectValue(seq, elt)
//  }
//}
// ***************************************************************************)
//\* BEGIN TRANSLATION
//CONSTANT defaultInitValue
//VARIABLES seq, elt, bot, top, result, pc
//
//vars == << seq, elt, bot, top, result, pc >>
//
//Init == (* Global variables *)
//        /\ seq \in TestSequences
//        /\ elt \in (-1)..(N+1)
//        /\ bot = 1
//        /\ top = Len(seq)
//        /\ result = defaultInitValue
//        /\ pc = "Lbl_1"
//
//Lbl_1 == /\ pc = "Lbl_1"
//         /\ IF (Len(seq) = 0) \/ (elt < seq[1])
//               THEN /\ result' = 0
//                    /\ pc' = "Lbl_3"
//               ELSE /\ IF seq[Len(seq)] =< elt
//                          THEN /\ result' = Len(seq)
//                               /\ pc' = "Lbl_3"
//                          ELSE /\ pc' = "Lbl_2"
//                               /\ UNCHANGED result
//         /\ UNCHANGED << seq, elt, bot, top >>
//
//Lbl_2 == /\ pc = "Lbl_2"
//         /\ IF bot+1 < top
//               THEN /\ LET mid == bot + ((top - bot) \div 2) IN
//                         IF elt < seq[mid]
//                            THEN /\ top' = mid
//                                 /\ bot' = bot
//                            ELSE /\ bot' = mid
//                                 /\ top' = top
//                    /\ pc' = "Lbl_2"
//                    /\ UNCHANGED result
//               ELSE /\ result' = bot
//                    /\ pc' = "Lbl_3"
//                    /\ UNCHANGED << bot, top >>
//         /\ UNCHANGED << seq, elt >>
//
//Lbl_3 == /\ pc = "Lbl_3"
//         /\ Assert(result = CorrectValue(seq, elt), 
//                   "Failure of assertion at line 48, column 5.")
//         /\ pc' = "Done"
//         /\ UNCHANGED << seq, elt, bot, top, result >>
//
//Next == Lbl_1 \/ Lbl_2 \/ Lbl_3
//           \/ (* Disjunct to prevent deadlock on termination *)
//              (pc = "Done" /\ UNCHANGED vars)
//
//Spec == /\ Init /\ [][Next]_vars
//        /\ WF_vars(Next)
//
//Termination == <>(pc = "Done")
//
//\* END TRANSLATION
//
//=============================================================================
//\* Modification History
//\* Last modified Wed Oct 08 10:56:42 PDT 2014 by lamport
//\* Created Wed Oct 08 09:44:00 PDT 2014 by lamport
