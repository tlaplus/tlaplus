/**
 * 
 */
package org.lamport.tla.toolbox.util;

import java.util.HashSet;
import java.util.Iterator;
import java.util.Vector;

/**
 * A StringSet object represents a set of strings.  It provides two
 * methods: 
 * 
 *   add(elt) : Adds the element elt to the set (no-op if elt is
 *              already in the set.
 *              
 *   contains(elt) : Returns true iff the element is in the set.
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
       
       if (! str.equals(contents.elementAt(position))) {
           contents.add(position+1, str) ;
       }
       return ;
    }
    
    public boolean contains(String str) {
        if (contents.size() == 0) {
            return false;
        }
        return str.equals(contents.elementAt(binarySearch(str))) ;    
    }
    
    /**
     * Returns the following value, where << is lexicographical ordering
     * of strings:
     * 
     *   IF contents.size() = 0 \/ str << contents(0) 
     *     THEN 0
     *     ELSE the largest integer i in 0..(contents.size()-1) such that contents(i) =<< str
     *     
     * It uses the algorithm BinarySearch appended at the end of this file.
     * 
     * @param str
     * @return
     */
    private int binarySearch(String str) {
        if ( (contents.size() == 0) || (str.compareTo(contents.elementAt(0)) < 0) ) {
            return 0 ;
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
     * For debugging.
     */
    public String toString() {
        return contents.toString() ;
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
//       \* while loop aintains the invariant that :
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
