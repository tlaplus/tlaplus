--------------------- MODULE AllocatorRefinement ----------------------
(*********************************************************************)
(* The scheduling allocator is a refinement of the simple allocator. *)
(*********************************************************************)

EXTENDS SchedulingAllocator

Simple == INSTANCE SimpleAllocator
SimpleAllocator == Simple!SimpleAllocator

THEOREM
  Allocator => SimpleAllocator
=======================================================================