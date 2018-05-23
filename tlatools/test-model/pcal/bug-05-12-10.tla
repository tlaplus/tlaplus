CAUSES the translator to throw an exception

last modified on Sun 11 Dec 2005 at  0:30:16 UT by lamport

---------------------------- MODULE bug-05-12-10 ----------------------------
EXTENDS Naturals, Sequences, FiniteSets , TLC
(*
--algorithm Pcal
  procedure IsAlgorithm(alg)
    variable res = FALSE ; i = 0 ;
    begin IA1: assert \/ /\ alg.type = "uniprocess"
                         /\ DOMAIN alg = {"type", "name", "defs", 
                                           "decls", "prcds", "body"}
                      \/ /\ alg.type = "multiiprocess"
                         /\ DOMAIN alg = {"type", "name", "defs", 
                                            "decls", "prcds", "procs"};
               assert alg.name \in STRING ;
               assert IsExpr(alg.defs) ;
               assert IsSeq(alg.decls) ;
               i := Len(alg.decls) ;
          IA2: while i > 0 do call IsVarDecl(alg.decls[i]) end while ;
               i := Len(alg.prcds) ;
          IA3: while i > 0 do call IsProcedure(alg.prcds[i]) end while ;
               if alg.type = "uniprocess"
                 then assert IsNonemptySeq(alg.body) ;
                             i := Len(alg.body) ;
                 IA4: while i > 0 do call IsLabeledStmt(alg.prcds[i]) 
                      end while ;
                 else assert IsNonemptySeq(alg.procs) ;
                             i := Len(alg.procs) ;
                 IA5: while i > 0 do call IsLabeledStmt(alg.procs[i]) 
                      end while ;
               end if ;
          IA6: return ;
    end procedure
  begin PC1: call IsAlgorithm(alg) ;
        Pc2: print "IsAlgorithm(alg) = TRUE"
  end algorithm
*)

\* BEGIN TRANSLATION
\* END TRANSLATION
=============================================================================
