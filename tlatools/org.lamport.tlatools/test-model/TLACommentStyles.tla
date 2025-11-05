------------------------- MODULE TLACommentStyles -------------------------

(*************************************************************************)
(* Calculate the sum of projections of the elements in a set.            *)
(*                                                                       *)
(* Example:                                                              *)
(*         MapThenSumSet(                                                *)
(*             LAMBDA e : e.n,                                           *)
(*             {[n |-> 0], [n |-> 1], [n |-> 2]}                         *)
(*         ) = 3                                                         *)
(*************************************************************************)
CommentStyle1 == TRUE

  (*************************************************************************)
  (* COMMENT STYLE 2: Indented Boxed Comment                              *)
  (* Used for nested or secondary explanations.                           *)
  (* Note the indentation at the start.                                   *)
  (*************************************************************************)
CommentStyle2 == TRUE

(* COMMENT STYLE 3: Simple Multi-line Comment Without Box
   This style doesn't use asterisks on every line.
   It's more free-form and less structured.
   Often used for algorithm descriptions or citations.
 *)
CommentStyle3 == TRUE

\* Declaring instances local causes definition overrides to be hidden. In the
\* case of Toolbox, this causes the definition override of `_TETrace` to be
\* invisible.  In turn, TLC will then try to evaluate the TLA+ definition of
\*
\* `_TETrace` as defined in Tooblox.tla:
\*   Attempted to enumerate S \ T when S:
\*   Nat
\*   is not enumerable.
\*
\* See: https://github.com/tlaplus/CommunityModules/issues/37
CommentStyle4 == TRUE

-----------------------------------------------------------------------------
(* Horizontal dividers (shown above and below) are used to separate       *)
(* major sections of the specification.                                   *)
-----------------------------------------------------------------------------

VARIABLE x,   \* COMMENT STYLE 5: Inline comment after code
         y    \* Explains individual variables or formula components

=============================================================================

