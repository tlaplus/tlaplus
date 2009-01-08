 last modified on Sun  5 Mar 2006 at  9:52:20 PST by lamport

Known problems with the translation:

- Does not permit the algorithm to contain an assignment to `stack'.

- Does not report an error when local variables are used outside their
  scope.  For example, it allows local process variables to appear in
  the body of a procedure.


(* 
--algorithm Pcal
  variables  
   i ; j ; \* Temporary index variables.
   gtemp1 ; gtemp2 ; gtemp3 ; gtemp4 ; \* temporary variable
   result = << >>; \* used to accumulate the translation
   rVal ; \* Used to return procedure values.
   pMap ; 
    (***********************************************************************)
    (* A record with a component for each procedure, where the pMap["P"]   *)
    (* for the procedure named "P" has fields:                             *)
    (*                                                                     *)
    (*    params: the sequence of the procedure's parameters               *)
    (*                                                                     *)
    (*    vars:    the sequence of the procedure's local variables         *)
    (*                                                                     *)
    (*    vals:    the sequence of the procedure's local variables initial *)
    (*             values.                                                 *)
    (*                                                                     *)
    (*    label:   the first label of the procedure's body                 *)
    (*                                                                     *)
    (*    tlavars: the set of all parameters and local variables of the    *)
    (*             procedure.                                              *)
    (***********************************************************************)

  prcdVars ;
    (***********************************************************************)
    (* Set to the set of all procedure variables (parameter and local      *)
    (* variables).                                                         *)
    (***********************************************************************)
    
  procSeq ;
    (***********************************************************************)
    (* A sequence with in which the i'th entry has the following           *)
    (* information for process i :                                         *)
    (*                                                                     *)
    (*    vars:    the sequence of the process's local variables           *)
    (*                                                                     *)
    (*    label:   the first label of the process's body                   *)
    (***********************************************************************)
    
  globalVars ;    \* Set equal to the set of variables in the global 
                  \* variable declaration.
  nonGlobalVars ; \* Set equal to the set of all TLA+ variables not in 
                  \* globalVars

  allVarSeq ;  \* Set to the sequence of all TLA+ variables of the algorithm.

   (************************************************************************)
   (* The following variable must be set to the appropriate value before   *)
   (* calling XlateLabStmtSeq.  I should probably rewrite the algorithm to *)
   (* pass it as a parameter, which requires adding it as a paramter to    *)
   (* XlateLabStmtSeq, XlateSStmtSeq, XlateSStmt, PrimeAndAddSub, and      *)
   (* ProcessVars.                                                         *)
   (************************************************************************)
   localVars ;  \* The set of variables to which localSub should be
                \* added as a subscript.
               
  define FinalStmtType(rec) == 
            rec.type \in {"if", "either", "with", "return", "callReturn", 
                          "call", "goto"}
  end define ;


\********************* BEGIN recursive definition of IsAlgorithm ***********
  (*************************************************************************)
  (* Algorithm = [type   : {"uniprocess"},                                 *)
  (*              name   : STRING,                                         *)
  (*              defs   : Expr,                                           *)
  (*              decls  : Seq(VarDecl),                                   *)
  (*              prcds  : Seq(Procedure),                                 *)
  (*              body   : NonemptySeq(LabeledStmt)]                       *)
  (*           \cup                                                        *)
  (*            [type   : {"multiprocess"},                                *)
  (*             name   : STRING,                                          *)
  (*             decls  : Seq(VarDecl),                                    *)
  (*             defs   : Expr,                                            *)
  (*             prcds  : Seq(Procedure),                                  *)
  (*             procs  : NonemptySeq(Process)]                            *)
  (*************************************************************************)
  procedure IsAlgorithm(A)
    variable res = FALSE ; ia = 0 ;
    begin IA1: assert \/ /\ A.type = "uniprocess"
                         /\ DOMAIN A = {"type", "name", "defs", 
                                           "decls", "prcds", "body"}
                      \/ /\ A.type = "multiprocess"
                         /\ DOMAIN A = {"type", "name", "defs", 
                                            "decls", "prcds", "procs"};
               assert A.name \in STRING ;
               call IsExpr(A.defs) ;
          IA2: assert IsSeq(A.decls) ;
               ia := Len(A.decls) ;
          IA3: while ia > 0 do call IsVarDecl(A.decls[ia]) ;
                        IA4: ia := ia-1 
               end while ;
               ia := Len(A.prcds) ;
          IA5: while ia > 0 do call IsProcedure(A.prcds[ia]) ;
                        IA6: ia := ia-1 
               end while ;
               if A.type = "uniprocess"
                 then assert Len(A.body) > 0 ;
                      call IsLabeledStmtSeq(A.body) ;
                 else assert IsNonemptySeq(A.procs) ;
                             ia := Len(A.procs) ;
                IA10: while ia > 0 do call IsProcess(A.procs[ia])  ;
                               IA11: ia := ia-1 
                      end while ;
               end if ;
         IA12: return ;
    end procedure

  (*************************************************************************)
  (* Procedure = [name   : STRING,                                         *)
  (*              params : Seq(PVarDecl),                                  *)
  (*              decls  : Seq(PVarDecl),                                  *)
  (*              body   : Seq(LabeledStmt)]                               *)
  (*************************************************************************)
  procedure IsProcedure(prcdr)
    variable ipr ;
    begin IPr1: assert DOMAIN prcdr = {"name", "params", "decls", "body"} ;
                assert IsSeq(prcdr.params) ;
                ipr := Len(prcdr.params) ;
          IPr2: while ipr > 0 do call IsPVarDecl(prcdr.params[ipr]) ;
                           IPr3: ipr := ipr-1 
                end while ;
                assert IsSeq(prcdr.decls) ;
                ipr := Len(prcdr.decls) ;
          IPr4: while ipr > 0 do call IsPVarDecl(prcdr.decls[ipr]) ;
                           IPr5: ipr := ipr-1 
                end while ;
                assert IsSeq(prcdr.decls) ;
                ipr := Len(prcdr.decls) ;
                assert Len(prcdr.body) > 0 ;
          IPr6: call IsLabeledStmtSeq(prcdr.body) ;
                return 
    end procedure

  (*************************************************************************)
  (* Process = [name   : STRING,                                           *)
  (*            eqOrIn : {"=", "\\in"},                                    *)
  (*            id     : Expr,                                             *)
  (*            decls  : Seq(VarDecl),                                     *)
  (*            body   : NonemptySeq(LabeledStmt)]                         *)
  (*************************************************************************)
  procedure IsProcess(proc)
    variable ip ;
    begin IP1: assert DOMAIN proc = 
                              {"name", "eqOrIn", "id", "decls", "body"} ;
               assert proc.name \in STRING ;
               assert proc.eqOrIn \in {"=", "\\in"} ;
               call IsExpr(proc.id) ;
          IP2: assert IsSeq(proc.decls) ;
               ip := Len(proc.decls) ;
          IP3: while ip > 0 do  call IsVarDecl(proc.decls[ip]) ;
                           IP4: ip := ip-1 
               end while ;
               call IsLabeledStmtSeq(proc.body) ;  
               return ;
    end procedure

  (*************************************************************************)
  (* LabeledStmtSeq = Seq(LabeledStmt)                                     *)
  (*************************************************************************)
  procedure IsLabeledStmtSeq(lsseq)  \* may be empty
    variable ilss ;
    begin ILSS1: assert IsSeq(lsseq) ;
                 ilss := Len(lsseq) ;
          ILSS2:  while ilss > 0 do  
                     call IsLabeledStmt(lsseq[ilss])  ;
              ILSS3: ilss := ilss-1 
                end while ;
                return 
    end procedure

  (*************************************************************************)
  (* LabeledStmt = [label : STRING,                                        *)
  (*                stmts : LabelSeq                                       *)
  (*                          \cup                                         *)
  (*                        {<<w>>> \o s : w \in While, s \in LabelSeq}    *)
  (*************************************************************************)
  procedure IsLabeledStmt(lstmt) \* may be empty
    begin IL1: assert DOMAIN lstmt = {"label", "stmts"} ;
               assert lstmt.label \in STRING ;
               if lstmt.stmts[1].type = "while"
                  then call IsWhile(lstmt.stmts[1]) ;
                  IL2: call IsLabelSeq(Tail(lstmt.stmts))
                  else call IsLabelSeq(lstmt.stmts) ;
               end if;
          IL3: return 
    end procedure

  (*************************************************************************)
  (* While = [type    : {"while"},                                         *)
  (*          test    : Expr,                                              *)
  (*          unlabDo : LabelSeq,                                          *)
  (*          labDo   : LabeledStmtSeq]                                    *)
  (*************************************************************************)
  procedure IsWhile(whl)
    begin IW1: assert DOMAIN whl = {"type", "test", "unlabDo", "labDo"};
               assert whl.type = "while" ;
               call IsExpr(whl.test) ;
          IW2: call IsLabelSeq(whl.unlabDo) ;
          IW3: if whl.labDo # << >> 
                 then call IsLabeledStmtSeq(whl.labDo) ;
               end if;
          IW4: return
    end procedure

  (*************************************************************************)
  (* LabelSeq = SimpleStmtSeq \cup                                         *)
  (*              {ss \o <<e>> : ss \in SimpleStmtSeq,                     *)
  (*                             e  \in LabelIf \cup                       *)
  (*                                     LabelEither \cup FinalStmt}       *)
  (*************************************************************************)
  procedure IsLabelSeq(ls)  \* may be empty
    variable ils ; ilLast ;
    begin ILS1: assert IsSeq(ls) ;
                ils := Len(ls) - 1 ;
          ILS2: while ils > 0 do
                  call IsSimpleStmt(ls[ils]) ;
            ILS3: ils := ils - 1 ;
                end while ;
          ILS4: if ls = << >> then return end if;
          ILS5: ilLast := ls[Len(ls)] ;
                if ilLast.type = "labelIf"
                  then call IsLabelIf(ilLast) ;
                  elsif ilLast.type = "labelEither"
                     then call IsLabelEither(ilLast) ;
                  elsif FinalStmtType(ilLast)
                     then call IsFinalStmt(ilLast)
                  else call IsSimpleStmt(ilLast) ;
                end if ;
          ILS6: return
    end procedure

  (*************************************************************************)
  (* LabelIf = [type      : {"labelIf"},                                   *)
  (*            test      : Expr,                                          *)
  (*            unlabThen : LabelSeq,                                      *)
  (*            labThen   : LabeledStmtSeq,                                *)
  (*            unlabElse : LabelSeq,                                      *)
  (*            labElse   : LabeledStmtSeq]                                *)
  (*************************************************************************)
  procedure IsLabelIf(ili)
    begin ILI1: assert DOMAIN ili = {"type", "test", "unlabThen", "labThen", 
                                     "unlabElse", "labElse"} ;
                call IsExpr(ili.test) ;
          ILI2: call IsLabelSeq(ili.unlabThen) ;
          ILI3: call IsLabeledStmtSeq(ili.labThen) ;
          ILI4: call IsLabelSeq(ili.unlabElse) ;
          ILI5: call IsLabeledStmtSeq(ili.labElse) ;
                return ;
  end procedure

  (*************************************************************************)
  (* LabelEither = [type    : {"labelEither"},                             *)
  (*                clauses : Seq([unlabOr : LabelSeq,                     *)
  (*                               labOr   : LabeledStmtSeq])]             *)
  (*************************************************************************)
  procedure IsLabelEither(le)
    variable ile ; 
    begin ILE1: assert DOMAIN le = {"type", "clauses"} ;
                assert IsSeq(le.clauses) ;
                ile := Len(le.clauses) ;
          ILE2: while ile > 0 do
                  assert DOMAIN le.clauses[ile] = {"unlabOr", "labOr"} ;
                  call IsLabelSeq(le.clauses[ile].unlabOr) ;
            ILE3: call IsLabeledStmtSeq(le.clauses[ile].labOr) ;
            ILE4: ile := ile - 1 ;
                end while ;
                return
  end procedure

  (*************************************************************************)
  (* FinalStmt = FinalIf \cup FinalEither \cup FinalWith \cup              *)
  (*               CallOrReturn \cup Goto                                  *)
  (*************************************************************************)
  procedure IsFinalStmt(fs)
    begin IFS1: if fs.type = "if"
                  then call IsFinalIf(fs)
                elsif fs.type = "either"
                  then call IsFinalEither(fs)
                elsif fs.type = "with"
                  then call IsFinalWith(fs)
                elsif fs.type \in {"return", "callReturn", "call"}
                  then call IsCallOrReturn(fs)
                elsif fs.type = "goto"
                  then call IsGoto(fs)
                else assert FALSE
                end if;
          IFS2: return
  end procedure

  (*************************************************************************)
  (* FinalIf = [type : {"if"},                                             *)
  (*            test : Expr,                                               *)
  (*            then : SimpleStmtSeq \cup                                  *)
  (*                     {ss \o <<fs>> : ss \in SimpleStmtSeq,             *)
  (*                                     fs \in FinalStmt},                *)
  (*            else : SimpleStmtSeq \cup                                  *)
  (*                     {ss \o <<fs>> : ss \in SimpleStmtSeq,             *)
  (*                                     fs \in FinalStmt}]                *)
  (*************************************************************************)
  procedure IsFinalIf(fi)
    variable ifi ; ifLast ;
    begin IFI1: assert DOMAIN fi = {"type", "test", "then", "else"} ;
                call IsExpr(fi.test) ;
          IFI2: assert IsSeq(fi.then) ;
                ifi := Len(fi.then) - 1 ;
          IFI3: while ifi > 0 do
                  call IsSimpleStmt(fi.then[ifi]) ;
            IFI4: ifi := ifi - 1 ;
                end while ;
                if fi.then = << >> then return end if;
          IFI5: ifLast := fi.then[Len(fi.then)] ;
                if FinalStmtType(ifLast)
                  then call IsFinalStmt(ifLast)
                else call IsSimpleStmt(ifLast) ;
                end if ;
          IFI6: assert IsSeq(fi.else) ;
                ifi := Len(fi.else) - 1 ;
          IFI7: while ifi > 0 do
                  call IsSimpleStmt(fi.else[ifi]) ;
            IFI8: ifi := ifi - 1 ;
                end while ;
                if fi.else = << >> then return end if;
          IFI9: ifLast := fi.else[Len(fi.else)] ;
                if FinalStmtType(ifLast)
                  then call IsFinalStmt(ifLast)
                else call IsSimpleStmt(ifLast) ;
                end if ;
         IFI10: return 
  end procedure

  (*************************************************************************)
  (* FinalEither = [type : {"either"},                                     *)
  (*                ors  : (SimpleStmtSeq \ {<< >>}) \cup                  *)
  (*                          {ss \o <<fs>> : ss \in SimpleStmtSeq,        *)
  (*                                          fs \in FinalStmt}]           *)
  (*************************************************************************)
  procedure IsFinalEither(fe)
    variable ife ; ife2 ; feSeq ; feSeqLast ;
    begin IFE1: assert DOMAIN fe = {"type", "ors"} ;
                 assert IsNonemptySeq(fe.ors) ;
                 ife := Len(fe.ors) ;
          IFE2: while ife > 0 do
                  feSeq := fe.ors[ife] ;
                  assert IsSeq(feSeq) ;
                  ife2 := Len(feSeq) - 1 ;
            IFE3: while ife2 > 0 do
                    call IsSimpleStmt(feSeq[ife2]) ;
              IFE4: ife2 := ife2 - 1 ;
                  end while ;
                  if Len(feSeq) > 0
                    then feSeqLast := feSeq[Len(feSeq)] ;
                         if FinalStmtType(feSeqLast)
                           then call IsFinalStmt(feSeqLast) 
                           else call IsSimpleStmt(feSeqLast) 
                         end if ;
                  end if ;
            IEF5: ife := ife - 1 ;
                end while ;
          IFE6: return ;
  end procedure

  (*************************************************************************)
  (* FinalWith = [type   : {"with"},                                       *)
  (*              var    : Variable,                                       *)
  (*              eqOrIn : {"=", "\\in"},                                  *)
  (*              exp    : Expr,                                           *)
  (*              do     : (SimpleStmtSeq \ {<< >>}) \cup                  *)
  (*                         {ss \o <<fs>> : ss \in SimpleStmtSeq,         *)
  (*                                         fs \in FinalStmt}]            *)
  (*************************************************************************)
  procedure IsFinalWith(fw)
    variables ifw ; fwLast ;
    begin IFW1: assert DOMAIN fw = {"type",  "var", "eqOrIn", "exp", "do"} ;
                assert fw.var \in STRING ;
                assert fw.eqOrIn \in {"=", "\\in"} ;
                call IsExpr(fw.exp) ;
          IFW2: assert IsSeq(fw.do) ;
                assert fw.do # << >> ;
                ifw := Len(fw.do) - 1 ;
          IFW3: while ifw > 0 do
                  call IsSimpleStmt(fw.do[ifw]) ;
            IFW4: ifw := ifw - 1 ;
                end while ;
                fwLast := fw.do[Len(fw.do)] ;
                if FinalStmtType(fwLast)
                  then call IsFinalStmt(fwLast)
                  else call IsSimpleStmt(fwLast)
                end if ;
          IFW5: return 
  end procedure

  (*************************************************************************)
  (* CallOrReturn = [type     : {"call"},                                  *)
  (*                 returnTo : STRING,                                    *)
  (*                 to       : STRING,                                    *)
  (*                 args     : Seq(Expr)]    \cup                         *)
  (*                [type : {"return"},  from : STRING]   \cup             *)
  (*                [type : {"callReturn"},                                *)
  (*                 from : STRING,                                        *)
  (*                 to   : STRING,                                        *)
  (*                 args : Seq(Expr)]                                     *)
  (*************************************************************************)
  procedure IsCallOrReturn(cr)
    variable icr ;
    begin ICR1: if cr.type = "call"
                  then assert DOMAIN cr = {"type", "returnTo", "to", "args"} ;
                       assert cr.returnTo \in STRING ;
                elsif cr.type = "return"
                  then assert DOMAIN cr = {"type", "from"}
                elsif cr.type = "callReturn"
                  then assert DOMAIN cr = {"type", "from", "to", "args"} ;
                else assert FALSE
                end if ;
                if cr.type # "return"
                  then assert cr.to \in STRING ;
                       assert IsSeq(cr.args) ;
                       icr := Len(cr.args) ;
                 ICR2: while icr > 0 do
                         call IsExpr(cr.args[icr]) ;
                   ICR3: icr := icr - 1 ;
                       end while      
                end if ;
          ICR4: if cr.type # "call"
                  then assert cr.from \in STRING
                end if ; 
                return 
  end procedure

  (*************************************************************************)
  (* Goto = [type : {"goto"},  to : STRING]                                *)
  (*************************************************************************)
  procedure IsGoto(gt)
    begin IGT1: assert DOMAIN gt = {"type", "to"} ;
                assert gt.to \in STRING ;
                return 
  end procedure

  (*************************************************************************)
  (* SimpleStmtSeq == Seq(SimpleStmt)                                      *)
  (*************************************************************************)
  procedure IsSimpleStmtSeq(sss)
    variable isss ;
    begin ISSS1: assert IsSeq(sss) ;
                 isss := Len(sss) ;
          ISSS2: while isss > 0 do
                   call IsSimpleStmt(sss[isss]) ;
            ISSS3: isss := isss - 1 
                 end while ;
          ISSS4: return
  end procedure 

  (*************************************************************************)
  (* SimpleStmt = Assign \cup If \cup Either \cup With \cup                *)
  (*                 [type : {"when"},   exp : Expr]   \cup                *)
  (*                 [type : {"print"},  exp : Expr]  \cup                 *)
  (*                 [type : {"assert"}, exp : Expr]  \cup                 *)
  (*                 [type : {"skip"}]                                     *)
  (*************************************************************************)
  procedure IsSimpleStmt(ss) 
    begin ISS1: if ss.type = "assignment"
                  then call IsAssign(ss)
                elsif ss.type = "if"
                  then call IsIf(ss)
                elsif ss.type = "either"
                  then call IsEither(ss)
                elsif ss.type = "with"
                  then call IsWith(ss)
                elsif ss.type \in {"when", "assert", "print"}
                  then call IsExpr(ss.exp)
                elsif ss.type = "skip"
                  then skip
                else assert FALSE 
                end if;
          ISS2: return
  end procedure

  (*************************************************************************)
  (* Assign = [type : {"assignment"},                                      *)
  (*           ass  : NonemptySeq([lhs: [var : STRING,  sub : Expr],       *)
  (*                               rhs : Expr]) ]                          *)
  (*************************************************************************)
  procedure IsAssign(asg)
    variable ias ;
    begin IAS1: assert DOMAIN asg = {"type", "ass"} ;
                assert IsNonemptySeq(asg.ass) ;
                ias := Len(asg.ass) ;
          IAS2: while ias > 0 do
                  assert DOMAIN asg.ass[ias] = {"lhs", "rhs"} ;
                  call IsExpr(asg.ass[ias].rhs) ;
            IAS3: assert DOMAIN asg.ass[ias].lhs = {"var", "sub"} ;
                  assert asg.ass[ias].lhs.var \in STRING ;
                  call IsExpr(asg.ass[ias].lhs.sub) ;
            IAS4: ias := ias - 1
                end while ;
          IAS5: return
  end procedure

  (*************************************************************************)
  (* If = [type : {"if"},                                                  *)
  (*       test : Expr,                                                    *)
  (*       then : SimpleStmtSeq                                            *)
  (*       else : SimpleStmtSeq]                                           *)
  (*************************************************************************)
  procedure IsIf(ifst)
    begin IIF1: assert DOMAIN ifst = {"type", "test", "then", "else"} ;
                call IsExpr(ifst.test) ;
          IIF2: call IsSimpleStmtSeq(ifst.then) ;
          IIF3: call IsSimpleStmtSeq(ifst.else) ;
                return
  end procedure

  (*************************************************************************)
  (* Either = [type : {"either"}, ors  : Seq(SimpleStmtSeq)]               *)
  (*************************************************************************)
  procedure IsEither(estmt)
    variable iee ;
    begin ISE1: assert DOMAIN estmt = {"type", "ors"} ;
                assert IsNonemptySeq(estmt.ors) ;
                iee := Len(estmt.ors) ;                          
          ISE2: while iee > 0 do
                  call IsSimpleStmtSeq(estmt.ors[iee]) ;           ISE3:
                  iee := iee - 1 ;
                end while ;
                return
  end procedure

  (*************************************************************************)
  (* With = [type   : {"with"},                                            *)
  (*         var    : STRING,                                              *)
  (*         eqOrIn : {"=", "\\in"},                                       *)
  (*         exp    : Expr,                                                *)
  (*         do     : NonemptySeq(SimpleStmt)]                             *)
  (*************************************************************************)
  procedure IsWith(wi)
    variable iw ;
    begin IWI1: assert DOMAIN wi = {"type", "var", "eqOrIn", "exp", "do"} ;
                assert wi.var \in STRING ;
                assert wi.eqOrIn \in {"=", "\\in"} ;
                call IsExpr(wi.exp) ;
          IWI2: assert IsNonemptySeq(wi.do) ;
                call IsSimpleStmtSeq(wi.do) ;                
                return
  end procedure


  (*************************************************************************)
  (* VarDecl = [var : STRING,  eqOrIn : {"=", "\\in"},  val : Expr]        *)
  (*************************************************************************)
  procedure IsVarDecl(vdcl)
    begin IV1 : assert DOMAIN vdcl = {"var", "eqOrIn", "val"} ;
                assert vdcl.var \in STRING ;
                assert vdcl.eqOrIn \in {"=", "\\in"} ;
                call IsExpr(vdcl.val) ;
                return ;
    end procedure

  (*************************************************************************)
  (* PVarDecl = [var : Variable,  eqOrIn : {"="}, val : Expr]              *)
  (*************************************************************************)
  procedure IsPVarDecl(pvdcl)
    begin IPV1: assert DOMAIN pvdcl = {"var", "eqOrIn", "val"} ;
                assert pvdcl.var \in STRING ;
                assert pvdcl.eqOrIn = "=" ;
                call IsExpr(pvdcl.val) ;
                return ;
    end procedure

  (*************************************************************************)
  (* Expr = Seq(STRING)                                                    *)
  (*************************************************************************)
  procedure IsExpr(exp)
    variable ie ;
    begin IE1 : assert IsSeq(exp) ;
               ie := Len(exp) ;
          IE2: while ie > 0 do assert exp[ie] \in STRING  ;
                            ie := ie-1 
               end while ;
               return               
    end procedure

\********************* BEGIN recursive definition of ExpandSeq ***********
  procedure ExpandSeq(elseq, nxt)
    (***********************************************************************)
    (* lseq is a sequence of LabeledStmts, and nxt is the label to which   *)
    (* control should go upon completion of the execution of that          *)
    (* sequence.  This sets rVal to the result of turning lseq into a      *)
    (* sequence of Labeled Simple Statements, meaning that all LabelIf,    *)
    (* LabelEither, and FinalStmt's have been replaced by their            *)
    (* expansions.  Moreover, the sequence of simple statements contains   *)
    (* explicit assignments to pc to indicate the flow of control.         *)
    (***********************************************************************)
    variables ixs ;  res = << >>;
    begin EX1: ixs := 1 ;
          EX2: while ixs \leq Len(elseq) do
                 if ixs < Len(elseq) 
                   then call ExpandLStmt(elseq[ixs], elseq[ixs+1].label)
                   else call ExpandLStmt(elseq[ixs], nxt)
                 end if ;
            EX3: res := res \o rVal ;
                 ixs := ixs + 1 ;
               end while ;
               rVal := res ;
               return ;
    end procedure

  procedure ExpandLStmt(lst, nxt)
    (***********************************************************************)
    (* Expands the single LabeledStmt ls into a sequence of labeled simple *)
    (* statements, where nxt is the label to which control should go upon  *)
    (* completing execution of the statement.                              *)
    (***********************************************************************)
    variable temp ; 
    begin ELS1: if Len(lst.stmts) = 0
                  then call Error("1: LabeledStmt with no statements.") ;
                end if;
          ELS2: if lst.stmts[1].type = "while"
                  then if lst.stmts[1].labDo = << >>
                         then call ExpandLSeq(lst.stmts[1].unlabDo, lst.label)
                         else call ExpandLSeq(lst.stmts[1].unlabDo, 
                                              lst.stmts[1].labDo[1].label)
                       end if ;
                 ELS3: temp := rVal ;
                       call ExpandSeq(lst.stmts[1].labDo, lst.label) ;
                 ELS4: temp.rst := temp.rst \o rVal ;
                       call ExpandLSeq(Tail(lst.stmts), nxt) ;
                 ELS5: rVal := << [label |-> lst.label,
                                   stmts |-> 
                                   << [then |-> temp.ss,
                                       type |-> "if",
                                       test |-> lst.stmts[1].test,
                                       else |-> rVal.ss] >>] >> \o
                                temp.rst \o rVal.rst

                  else call ExpandLSeq(lst.stmts, nxt) ;
                 ELS6: rVal := <<[label |-> lst.label,
                                  stmts |-> rVal.ss] >> \o rVal.rst
                end if;
          ELS7: return ;
    end procedure

  procedure IsFinalSeq(flseq)
    (***********************************************************************)
    (* When flseq is a LabelSeq not containing a label, it sets rVal to    *)
    (* TRUE or FALSE depending on whether or not flseq is nonempty and its *)
    (* last element is a call, return, or goto or has one in it.           *)
    (***********************************************************************)
    variable temp ; ifsqi ;
    begin  IFS1: if flseq = << >>
                   then rVal := FALSE
                 elsif FinalStmtType(Last(flseq))
                   then rVal := TRUE
                 elsif Last(flseq).type = "if"
                   then call IsFinalSeq(Last(flseq).then) ;
                  IFS2: if ~ rVal
                           then call IsFinalSeq(Last(flseq).else) 
                        end if
                 elsif Last(flseq).type = "with"
                   then call IsFinalSeq(Last(flseq).do) ;
                 elsif Last(flseq).type = "either"
                   then temp := FALSE ;
                        ifsqi := Len(Last(flseq).ors) ;
                  IFS3: while (~temp) /\ (ifsqi > 0) do
                          call IsFinalSeq(Last(flseq).ors[ifsqi]) ;
                    IFS4: temp := temp \/ rVal ;
                          ifsqi := ifsqi - 1
                        end while ;
                        rVal := temp
                 else rVal := FALSE
                 end if;
           IFS9: return 
    end procedure    

  procedure ExpandLSeq(lseq, nxt)
    (***********************************************************************)
    (* If lseq is a LabelSeq, then sets rVal to the record                 *)
    (*                                                                     *)
    (*    [ss  |-> a sequence of SimpleStmts,                              *)
    (*     rst |-> a sequence of LabeledStmts]                             *)
    (*                                                                     *)
    (* where executing lseq executes the simple statements, which set pc   *)
    (* appropriately to transfer control, and rst is the sequence of       *)
    (* labeled statements (if any) obtained from the final statement of    *)
    (* lseq, if that statement is a LabelIf or LabelEither.  As usual, nxt *)
    (* is the label after the sequence lseq.                               *)
    (***********************************************************************)
    variable xxtemp1 ; temp2 ; temp3; temp4; exlsq ; 

    begin ELSq1: 
      if /\ lseq # << >> 
         /\ Last(lseq).type \in {"labelIf", "labelEither"}
        then rVal := TRUE
        else call IsFinalSeq(lseq)
      end if ;                                                ELSq2:  
      if ~ rVal
        (*******************************************************************)
        (* CASE: Last statement not a final statement, LabelIf or          *)
        (* LabelEither.                                                    *)
        (*******************************************************************)
        then rVal := [ss  |-> lseq \o <<PCAssign(nxt)>>, 
                      rst |-> << >>]
      elsif Last(lseq).type = "labelIf"
        (*******************************************************************)
        (* CASE: Last statement a LabelIf.                                 *)
        (*******************************************************************)
        then (**************************************************************)
             (* Set xxtemp1 to the ExpandLSeq expansion of unlabThen.        *)
             (**************************************************************)
             if Last(lseq).labThen = << >>
               then call ExpandLSeq(Last(lseq).unlabThen, nxt)
               else call ExpandLSeq(Last(lseq).unlabThen, 
                                    Last(lseq).labThen[1].label)
             end if ;                                                 ELSq31:
             xxtemp1 := rVal ;                                          ELSq32:

             (**************************************************************)
             (* Set temp2 to the ExpandLSeq expansion of unlabElse.        *)
             (**************************************************************)
             if Last(lseq).labElse = << >>
               then call ExpandLSeq(Last(lseq).unlabElse, nxt)
               else call ExpandLSeq(Last(lseq).unlabElse, 
                                    Last(lseq).labElse[1].label)
             end if ;                                                 ELSq33:
             temp2 := rVal ; 

             (**************************************************************)
             (* Set temp3 to the expansion of labThen \o expansion of      *)
             (* labElse                                                    *)
             (**************************************************************)
             call ExpandSeq(Last(lseq).labThen, nxt) ;                ELSq34:
             temp3 := rVal ;
             call ExpandSeq(Last(lseq).labElse, nxt) ;                ELSq35:
             temp3 := temp3 \o rVal ; 

             rVal := [ss  |-> Front(lseq) \o
                                << [type |-> "if",
                                    test |-> Last(lseq).test,
                                    then |-> xxtemp1.ss ,
                                    else |-> temp2.ss] >> ,
                      rst |-> xxtemp1.rst \o temp2.rst \o temp3 ]

      elsif Last(lseq).type = "labelEither"
        then if Last(lseq).clauses = << >> 
               then call Error("2: labelEither with no clauses")
               end if ;                                               ELSq71:

             (**************************************************************)
             (* Set xxtemp1 to the sequence of ss fields in the ExpandLSeq   *)
             (* expansion of all the unlabOrs, and temp2 to the            *)
             (* concatenation of all their rst fields.                     *)
             (**************************************************************)
             xxtemp1 := << >> ;
             temp2 := << >> ;
             exlsq := Len(Last(lseq).clauses) ;                       ELSq72:
             while exlsq > 0 do
               if Last(lseq).clauses[exlsq].labOr = << >>
                 then call ExpandLSeq(Last(lseq).clauses[exlsq].unlabOr, nxt)
                 else call ExpandLSeq(Last(lseq).clauses[exlsq].unlabOr, 
                                      Last(lseq).clauses[exlsq].labOr[1].label)
               end if ;                                               ELSq73:
               xxtemp1 := <<rVal.ss>> \o xxtemp1 ;
               temp2 := rVal.rst \o temp2 ;
               exlsq := exlsq - 1
             end while ;

             (**************************************************************)
             (* Set temp3 to the concatenation of the ExpandSeq expansions *)
             (* of all the labOr clauses.                                  *)
             (**************************************************************)
             temp3 := << >> ;
             exlsq := Len(Last(lseq).clauses) ;                       ELSq74:
             while exlsq > 0 do
               call ExpandSeq(Last(lseq).clauses[exlsq].labOr, nxt); ELSq75:
               temp3 := rVal \o temp3 ;
               exlsq := exlsq - 1
             end while ;

             rVal := [ss  |-> Front(lseq) \o << [type    |-> "either",
                                                 clauses |-> xxtemp1] >>,
                      rst |-> temp2 \o temp3 ]

      elsif Last(lseq).type = "if"
        (*******************************************************)
        (* CASE: Last statement a final If.                    *)
        (*******************************************************)
        then call ExpandLSeq(Last(lseq).then, nxt) ;      ELSq11: 
             if rVal.rst # << >>
               then call Error("3: Label in `then' cls of `if'");
             end if;                                      ELSq12: 
             xxtemp1 := rVal ;                              ELSq13: 
             call ExpandLSeq(Last(lseq).else, nxt);       ELSq14: 
             if rVal.rst # << >>
               then call Error("4: Label in `else' cls of `if'");
             end if;                                      ELSq15: 
             temp2 := rVal ;
             rVal := [ss |-> Front(lseq) \o << [type |-> "if",
                                                test |-> Last(lseq).test,
                                                then |-> xxtemp1.ss, 
                                                else |-> temp2.ss] >>,
                      rst |-> << >>] 
       elsif Last(lseq).type = "with"
         (*******************************************************)
         (* CASE: Last statement a final With.                  *)
         (*******************************************************)
         then call ExpandLSeq(Last(lseq).do, nxt) ;        ELSq41: 
              if rVal.rst # << >>
                then call Error("5: Label in `with'") ;
              end if ;                                     ELSq42: 
              rVal := [ss  |-> Front(lseq) \o
                                    << [type   |-> "with",
                                        var    |-> Last(lseq).var ,
                                        eqOrIn |-> Last(lseq).eqOrIn ,
                                        exp    |-> Last(lseq).exp ,
                                        do     |-> rVal.ss] >> ,
                       rst |-> << >>]

       elsif Last(lseq).type = "either"
         (*******************************************************)
         (* CASE: Last statement a final Either.                *)
         (*******************************************************)
         then exlsq := Len(Last(lseq).ors);
              temp2 := << >> ;                                   ELSq51:
              while exlsq > 0 do
                call ExpandLSeq(Last(lseq).ors[exlsq], nxt) ;    ELSq52:
                if rVal.rst # << >> then call Error("6: Label in `either'")
                end if ;                                         ELSq53:
                temp2 := <<rVal.ss>> \o temp2 ;
                exlsq := exlsq - 1
              end while ;
              rVal :=  [ss  |-> Front(lseq) \o
                                    << [type |-> "either",
                                        ors  |-> temp2] >> ,
                       rst |-> << >>]

       elsif Last(lseq).type = "call"
         then \* xxtemp1 := name of procedure being called
              xxtemp1 := Last(lseq).to ;
              if xxtemp1 \notin DOMAIN pMap
                then   call Error("14: Call of nonexistent procedure " 
                                  \o xxtemp1) ;
              end if;                                                ELSq60:

              (*************************************************************)
              (* Set temp2 to the element to be put at the head of the     *)
              (* stack.                                                    *)
              (*************************************************************)
              temp2 := <<"[", "procedure", "|->">> \o Quote(Last(lseq).to)                                \o  << ",", "@pc@", "|->" >> 
                          \o  Quote(nxt)  ;
              exlsq := 1 ;                                            ELSq61:
              while exlsq \leq Len(pMap[xxtemp1].params) do
                temp2 := temp2 \o 
                          <<",", pMap[xxtemp1].params[exlsq], "|->",
                             pMap[xxtemp1].params[exlsq]>> ;
                exlsq := exlsq + 1;
              end while ;

              exlsq := 1 ;                                            ELSq62:
              while exlsq \leq Len(pMap[xxtemp1].vars) do
                temp2 := temp2 \o 
                          <<",", pMap[xxtemp1].vars[exlsq], "|->",
                             pMap[xxtemp1].vars[exlsq]>> ;
                exlsq := exlsq + 1;
              end while ;                                             ELSq63:
              temp2 := temp2 \o <<"]">> ;

              \* Set temp3 to the statements to initialize the procedures'
              \* variables
              call SetPrcdVarsOnCall(Last(lseq), xxtemp1) ;             ELSq64:
              temp3 := rVal ;
              rVal := [ss |-> 
                        Front(lseq) \o 
                          <<PCAssign(pMap[xxtemp1].label),
                            [type |-> "assignment",
                             ass  |-> 
                               << [lhs |-> [var |-> "@stack@", sub |-> << >>],
                                   rhs |-> <<"<<" >> \o temp2 \o
                                            << ">>", "\\o", "@stack@">>]
                               >> ] >> \o
                        temp3,
                       rst |-> << >>] ;

       elsif Last(lseq).type = "return"
         then call RestorePrcdVarsFrom(Last(lseq).from);              ELSq65:
              rVal := [ss |-> 
                        Front(lseq) \o 
                          << [type |-> "assignment",
                              ass  |-> << [lhs |-> [var |-> "@pc@", 
                                                    sub |-> << >>],
                                           rhs |-> <<"Head", "(", "@stack@", 
                                                        ")", ".", "@pc@">> ]
                                         >>] >> \o
                          rVal \o 
                           << [type |-> "assignment",
                               ass  |-> << [lhs |-> [var |-> "@stack@", 
                                                     sub |-> << >>],
                                             rhs |-> <<"Tail", "(", 
                                                        "@stack@", ")">>
                                           ] >>] >> ,
                       rst |-> << >>] ;

       elsif Last(lseq).type = "callReturn"
         then  \* Set temp4 to a sequence containing the assignment to pc.
               temp4 := << [type |-> "assignment",
                            ass  |-> << [lhs |-> [var |-> "@pc@", 
                                                  sub |-> << >>],
                                         rhs  |-> 
                                           Quote(pMap[Last(lseq).to].label) 
                                        ] >>] >>  ;
                if Last(lseq).to = Last(lseq).from
                then \* call and return to/from same procedure.
                     call SetPrcdVarsOnCall(Last(lseq),
                                                      Last(lseq).to); ELSq8:
                     rVal := [ss  |-> Front(lseq) \o temp4 \o rVal,
                              rst |-> << >>] 
                else \* call and return to/from different procedures.
                     \* Set temp2 to the new head of the stack, 
                     temp2 := <<"[", "procedure", "|->">>
                                 \o Quote(Last(lseq).to) \o 
                                << ",", "@pc@", "|->", "Head", "(", 
                                  "@stack@", ")", ".", "@pc@" >> ;
                     xxtemp1 := Last(lseq).to ;
                    if xxtemp1 \notin DOMAIN pMap
                      then   call Error("16: Call of nonexistent procedure " 
                                  \o xxtemp1) ;
                     end if;                                         ELSq80:
                     exlsq := 1 ;                                    ELSq81:
                     while exlsq \leq Len(pMap[xxtemp1].params) do
                       temp2 := temp2 \o 
                                 <<",", pMap[xxtemp1].params[exlsq], "|->",
                                    pMap[xxtemp1].params[exlsq]>> ;
                       exlsq := exlsq + 1 ;
                     end while ;                   
                     exlsq := 1 ;                                    ELSq82:
                     while exlsq \leq Len(pMap[xxtemp1].vars) do
                       temp2 := temp2 \o 
                                 <<",", pMap[xxtemp1].vars[exlsq], "|->",
                                    pMap[xxtemp1].vars[exlsq]>> ;
                       exlsq := exlsq + 1 ;
                     end while ;                                     ELSq83:
                     temp2 := temp2 \o <<"]">> ;
                     call SetPrcdVarsOnCall(Last(lseq), 
                                            Last(lseq).to) ;         ELSq84:
                     temp3 := rVal ;
                     call RestorePrcdVarsFrom(Last(lseq).from) ;     ELSq85:
                     temp3 := temp3 \o rVal;

                     rVal := [ss  |-> Front(lseq) \o temp4 \o
                               <<AssSeqToMultiAss(
                                  <<[type |-> "assignment",
                                     ass  |-> << [lhs |-> 
                                                   [var |-> "@stack@", 
                                                    sub |-> <<"[", "1", "]">>],
                                                  rhs |-> temp2] 
                                               >>]>> 
                                   \o temp3 ) >>, 
                              rst |-> << >>] ;
              end if ;

       elsif Last(lseq).type = "goto"
         (*******************************************************)
         (* CASE: Last statement a Goto.                        *)
         (*******************************************************)
         then rVal := [ss  |-> Front(lseq) \o <<PCAssign(Last(lseq).to)>>, 
                       rst |-> << >>]

      else call Error("7: Unknown statement type.") 
      end if ;                                                     ELSq3: 
      return;
    end procedure

  procedure SetPrcdVarsOnCall(callStmt, prcd)
  (*************************************************************************)
  (* Sets rVal equal to a sequence of 0-2 multiple assignment statements   *)
  (* to set the TLA+ variables of procedure prcd when called by a Call or  *)
  (* callReturn `callStmt'.                                                *)
  (*************************************************************************)
  variables svoci ; \* index
            temp ;
            res = << >>;
  begin SPV1:
    (***********************************************************************)
    (* Set temp to the sequence of assignments                             *)
    (* prcd.params[i] := callStmt.args[i].                                 *)
    (***********************************************************************)
    svoci := 1 ;  
    temp := << >> ;
    if Len(pMap[prcd].params) # Len(callStmt.args)
      then call Error("15: Procedure " \o <<prcd>> \o 
              "called with wrong number of variables") 
    end if ;                                                           SVP2:
    while svoci \leq Len(pMap[prcd].params) do 
      temp := temp \o 
               << [lhs |-> [var |-> pMap[prcd].params[svoci], sub |-> << >>],
                   rhs |-> callStmt.args[svoci] ] >> ;
      svoci := svoci + 1
    end while ;
    if temp # << >>
      then res := res \o <<[type |-> "assignment",
                            ass  |-> temp] >>
    end if;

    (***********************************************************************)
    (* Set temp to the sequence of assignments                             *)
    (* prcd.decls[i].var := prcd.decls[i].val                              *)
    (***********************************************************************)
    svoci := 1 ;  
    temp := << >> ;                                                     SVP3:
    while svoci \leq Len(pMap[prcd].vars) do 
      temp := temp \o 
               << [lhs |-> [var |-> pMap[prcd].vars[svoci], sub |-> << >>],
                   rhs |-> pMap[prcd].vals[svoci] ] >> ;
      svoci := svoci + 1
    end while ;
    if temp # << >>
      then res := res \o <<[type |-> "assignment",
                            ass  |-> temp] >>
    end if;
    rVal := res ;                                                      SVP4:
    return
  end procedure 

  procedure RestorePrcdVarsFrom(rprcd) 
   (************************************************************************)
   (* Sets rVal to a sequence of 0-2 multi-assignment statements to        *)
   (* restore the variables of procedure prcd when returning from the      *)
   (* procedure.  The saved values are obtained from Head(stack).          *)
   (************************************************************************)
   variables rpvi ; rpctemp ; res = << >>;
   begin                                                              RPV1:
     \* Set rpctemp to a sequence of single assignments to restore
     \* the parameters.
     rpctemp := << >> ;
     rpvi := 1 ;                                                      RPV2:
     while rpvi \leq Len(pMap[rprcd].params) do
       rpctemp := rpctemp \o 
               << [lhs |-> [var |-> pMap[rprcd].params[rpvi], sub |-> << >>],
                   rhs |-> <<"Head", "(", "@stack@", ")", ".", 
                             pMap[rprcd].params[rpvi] >>] >> ;
       rpvi := rpvi + 1 
     end while ;

     if rpctemp # << >> 
        then res := <<[type |-> "assignment", ass  |-> rpctemp]>> ;
     end if ;

     \* Set rpctemp to a sequence of single assignments to restore
     \* the local variables. 
     rpctemp := << >> ;
     rpvi := 1 ;                                                      RPV3:
     while rpvi \leq Len(pMap[rprcd].vars) do
       rpctemp := rpctemp \o 
               << [lhs |-> [var |-> pMap[rprcd].vars[rpvi], sub |-> << >>],
                   rhs |-> <<"Head", "(", "@stack@", ")", ".", 
                             pMap[rprcd].vars[rpvi] >>] >> ;
       rpvi := rpvi + 1 
     end while ;
     if rpctemp # << >> 
        then res := res \o <<[type |-> "assignment", ass  |-> rpctemp]>> ;
     end if ;

     rVal := res ;                                                      RPV4:
     return
   end procedure
   
(**************  thesed will go somewhere else
  call Error("15: Procedure " \o <<prcd>> \o 
              called with wrong number of variables") ;
***********)
	
\***************************** END definition of ExpandSeq ************
  procedure ProcessVars(vrs, addExpr, pvexpr)
    (***********************************************************************)
    (* Sets rVal to the expression obtained from the expression pvexpr by  *)
    (* inserting the sequence addExpr of strings after every occurrence of *)
    (* a variable in the set vrs of variables.  The procedure is used to   *)
    (* insert subscripts and prime variables in expressions.               *)
    (***********************************************************************)
    variables pvi = 1 ; \* the next token in pvexpr to be checked
              stk = << >> ;
                (***********************************************************)
                (* A sequence of Booleans whose length is the number of    *)
                (* unmatched "["s at the current point in pvexpr, and an   *)
                (* element of this sequence equals TRUE iff the            *)
                (* corresponding unmatched "[" began an expression of the  *)
                (* form [v : S, ...  ] or [v |-> S, ...  ]                 *)
                (***********************************************************)
             test = TRUE ;                
  begin PV1:        
    rVal := << >> ;                                                     PV2:
    while pvi \leq Len(pvexpr) do
      if pvexpr[pvi] = "["
        then if pvi + 2 > Len(pvexpr)
               then call Error("8: premature end of expression") 
               elsif pvexpr[pvi+2] \in {":", "|->"}
                 then stk  := <<TRUE>> \o stk ;
                      rVal := rVal \o <<pvexpr[pvi], pvexpr[pvi+1]>> ;
                      pvi  := pvi+2 
               else stk := stk \o <<FALSE>>
             end if 
      elsif pvexpr[pvi] = "]"
        then if Len(stk) = 0
               then call Error("9: unmatched `]' in expression")
               else stk := Tail(stk)
             end if ;
      elsif pvexpr[pvi] = "."
        then rVal := rVal \o <<pvexpr[pvi]>> ;
             pvi := pvi + 1 ;
             test := FALSE
      elsif /\ pvexpr[pvi] = ","
            /\ (Len(stk) > 0) /\ Head(stk)
            /\ pvi + 2 \leq Len(pvexpr)
            /\ pvexpr[pvi+2] \in {":", "|->"}
        then rVal := rVal \o <<pvexpr[pvi], pvexpr[pvi+1]>> ;
             pvi  := pvi+2 
      elsif pvexpr[pvi] = "\""
        then if \/ pvi + 2 > Len(pvexpr)
                \/ pvexpr[pvi+2] # "\""
               then call Error("10: unmatched quote in expression")
               else rVal := rVal \o <<pvexpr[pvi], pvexpr[pvi+1]>> ;
                    pvi  := pvi+2 
             end if
      end if ;                                                         PV8:
      if test /\ (pvi \leq Len(pvexpr)) \* test needed for bad expression.
              /\ pvexpr[pvi] \in vrs
        then rVal := rVal \o <<pvexpr[pvi]>> \o addExpr ;
        else rVal := rVal \o <<pvexpr[pvi]>> ;
      end if;
      pvi := pvi + 1;
      test := TRUE
    end while ;                                                        PV9:
    return
  end procedure


(****************** It appears that this procedure is not used
  procedure AddSubscript(vrs, sub, asstmts)
    (***********************************************************************)
    (* Sets rVal to the the sequence of simple statements obtained from    *)
    (* the sequence of simple statements asstmts by putting the expression *)
    (* sub after after each instance of v, for each v in the set vrs of    *)
    (* variables.                                                          *)
    (***********************************************************************)
    variables assi = 1 ; assi2 ; res = << >> ; temp1 ; temp2 ; newstmt ;
    begin                                                              ASS1:
      while assi \leq Len(asstmts) do
        if asstmts[assi].type = "assignment"
          then temp1 := << >> ;
               assi2 := 1 ;                                            ASS2:
               while assi2 \leq Len(asstmts[assi].ass) do
                 temp2 := asstmts[assi].ass[assi2] ;                   ASS3:
                 call ProcessVars(vrs, sub, temp2.lhs.sub) ;           ASS4:
                 temp2.lhs.sub := rVal ;                               
                 if temp2.lhs.var \in vrs then                         ASS5: 
                   temp2.lhs.sub := sub \o temp2.lhs.sub 
                 end if ;                                              ASS6:
                 call ProcessVars(vrs, sub, temp2.rhs) ;               ASS7:
                 temp2.rhs := rVal ;
                 temp1 := temp1 \o <<temp2>> ;
                 assi2 := assi2 + 1
               end while ;
               newstmt := [type |-> "assignment", ass |-> temp1] 

        elsif asstmts[assi].type = "if"
          then call ProcessVars(vrs, sub, asstmts[assi].test) ;        ASS71:
               newstmt := [type |-> "if", 
                           test |-> rVal, 
                           then |-> << >>,
                           else |-> << >>] ;                           ASS72:
               call AddSubscript(vrs, sub, asstmts[assi].then);        ASS73:
               newstmt.then := rVal ;                                  ASS74:
               call AddSubscript(vrs, sub, asstmts[assi].else);        ASS75:
               newstmt.else := rVal ;                                  

        elsif asstmts[assi].type = "either"
          then temp1 := << >> ;
               assi2 := 1 ;                                            ASS8:
               while assi2 \leq Len(asstmts[assi].ors) do
                 call AddSubscript(vrs, sub, asstmts[assi].ors[assi2]); ASS9:
                 temp1 := temp1 \o <<rVal>> ;
                 assi2 := assi2 + 1
               end while ;
               newstmt := [type |-> "either", ors |-> temp1] 

        elsif asstmts[assi].type = "with"
          then call ProcessVars(vrs, sub, asstmts[assi].exp) ;        ASS10:
               temp1 := rVal ;                                        ASS11:
               call AddSubscript(vrs, sub, asstmts[assi].do) ;        ASS12:
               newstmt := [asstmts[assi] EXCEPT !.exp = temp1,
                                                !.do  = rVal] 

        elsif asstmts[assi].type \in {"when", "print", "assert"}
          then call ProcessVars(vrs, sub, asstmts[assi].exp) ;        ASS13:
               newstmt := [type |-> asstmts[assi].type, exp |-> rVal]

        elsif asstmts[assi].type = "skip"
          then newstmt := asstmts[assi]

        else call Error("11: Unknown simple statement type " 
                           \o asstmts[assi].type )
        end if;                                                       ASS14:
        res := res \o <<newstmt>> ;
        assi := assi + 1 ;
      end while ;
      rVal := res ;
      return ;
    end procedure 
***************** end of unused procedure ********)

\**** RECURSIVE DEFINITIONS OF XlateSStmtSeq, XlateSStmt

  procedure PrimeAndAddSub(primeVars, sub, expr)
    (***********************************************************************)
    (* Returns the expression obtained from expr by adding the subscript   *)
    (* "[ sub ]" after every variable in localVars and priming all the     *)
    (* variables in primeVars.                                             *)
    (***********************************************************************)
    begin PAAS1: call ProcessVars(localVars, sub, expr) ;
          PAAS2: call ProcessVars(primeVars, <<"'">>, rVal) ;
          PAAS3: return
    end procedure

  procedure XlateSStmt(sst, primedVars, localSub)
    (***********************************************************************)
    (* Translate a single simple statement into an action.  The            *)
    (* arguments are                                                       *)
    (*                                                                     *)
    (*   sst        : The simple statement                                 *)
    (*   primedVars : The subset of SeqToSet(allVars) of variables         *)
    (*                that should be primed.                               *)
    (*   localSub   : The expression to be added as a subscript to local   *)
    (*                variables.                                           *)
    (*                                                                     *)
    (* It sets rVal to a record with fields:                               *)
    (*                                                                     *)
    (*    action: the action, represented as a sequence of expressions     *)
    (*            whose conjunction represents the action,                 *)
    (*    pVars: the union of primedVars and all the variables that        *)
    (*           are assigned a value by the action.                       *)
    (***********************************************************************)
    variables xlssi ; xltemp1 ; \* must be unique ident because of bug
                                \* in translator
              temp1; temp2 ; temp3 ;
              res = [action |-> << >>,
                     pVars  |-> primedVars ] ;
    begin XSt1: 
      res := [action |-> << >>,        \* needed because of bug in Pcal makes
              pVars  |-> primedVars] ; \* initialization not work right
      if sst.type = "assignment"
        then (**************************************************************)
             (* Set xltemp1 to a sequence of elements of the form          *)
             (*                                                            *)
             (*   [var    |-> variable name,                               *)
             (*    assign |-> NonEmptySeq([sub |->  expr, rhs |-> expr]) ] *)
             (*                                                            *)
             (* obtained by combining the individual assignments to the    *)
             (* same variable in sst.ass and performing the appropriate    *)
             (* priming and adding of local subscripts to the subscripts   *)
             (* and right-hand sides.                                      *)
             (**************************************************************)
             xltemp1 := << >> ;
             xlssi := 1 ;                                               XSt11:
             while xlssi \leq Len(sst.ass) do
                call PrimeAndAddSub(primedVars, localSub, 
                                    sst.ass[xlssi].lhs.sub);            XSt12:
                     temp2 := rVal ;
                call PrimeAndAddSub(primedVars, localSub, 
                                    sst.ass[xlssi].rhs);                XSt13:
                with newElt = << [sub |-> temp2, rhs |-> rVal] >> do  
                  if \E x \in 1..Len(xltemp1) : 
                         xltemp1[x].var = sst.ass[xlssi].lhs.var
                      then with y = CHOOSE x \in 1..Len(xltemp1) : 
                                      xltemp1[x].var = sst.ass[xlssi].lhs.var
                             do xltemp1[y].assign := 
                                  xltemp1[y].assign \o newElt
                           end with                             
                      else xltemp1 := 
                            xltemp1 \o <<[var    |-> sst.ass[xlssi].lhs.var,
                                          assign |-> newElt] >>
                  end if
                end with ;
                xlssi := xlssi + 1 
             end while ;
             xlssi := 1 ;                                               XSt14:
             while xlssi \leq Len(xltemp1) do
               if \/ xltemp1[xlssi].var \in primedVars 
                  \/ /\ Len(xltemp1[xlssi].assign) > 1
                     /\ \E x \in 1..Len(xltemp1[xlssi].assign) :
                            xltemp1[xlssi].assign[x].sub = << >>
                 then call Error("12: Multiple assignment to  " \o 
                                   xltemp1[xlssi].var) ;
               end if ;                                                XSt15:

              (*************************************************************)
              (* Set temp3 to the rhs of the action var' = rhs.            *)
              (*************************************************************)
               temp2 := IF xltemp1[xlssi].var \in localVars
                        THEN localSub 
                        ELSE << >> ;
               if temp2 \o xltemp1[xlssi].assign[1].sub = << >>
                 then temp3 := xltemp1[xlssi].assign[1].rhs
                 else temp3 := 
                        <<"[", xltemp1[xlssi].var, "EXCEPT">>
                          \o
                        SeqConcat([x \in 1..Len(xltemp1[xlssi].assign) |->
                                    << "!" >> \o temp2 \o
                                     xltemp1[xlssi].assign[x].sub \o
                                    <<"=">> \o xltemp1[xlssi].assign[x].rhs
                                    \o IF x = Len(xltemp1[xlssi].assign)
                                         THEN << >>
                                         ELSE << "," >>])
                            \o <<"]">>
               end if ; 

               res := [action |-> res.action \** extra << >> ?
                                   \o << <<  xltemp1[xlssi].var, "'", "=">>
                                   \o temp3 >>
,
                       pVars  |-> res.pVars \cup {xltemp1[xlssi].var}] ;

               xlssi := xlssi + 1 
             end while ;

      elsif sst.type = "if"
        then call XlateSStmtSeq(sst.then, primedVars, localSub) ;  XSt21:
             temp1 := rVal ;
             call XlateSStmtSeq(sst.else, primedVars, localSub) ;  XSt22:
             temp2 := rVal ;
             call PrimeAndAddSub(primedVars, localSub, sst.test) ;  XSt23:
             temp3 := rVal ;
             temp1.action := temp1.action \o 
                              MakeUnchanged(
                                   CompSetToSubseq(
                                      temp1.pVars,
                                      SetToSubseq(temp1.pVars \cup temp2.pVars,
                                               allVarSeq)))  ;
             temp2.action := temp2.action \o 
                               MakeUnchanged(
                                   CompSetToSubseq(
                                      temp2.pVars,
                                      SetToSubseq(temp1.pVars \cup temp2.pVars,
                                               allVarSeq))) ;
             res.action :=
               << << "(", "IF">> \o temp3 \o <<"THEN">> \o 
                            MakeConj(temp1.action)
                   \o <<"ELSE">> \o MakeConj(temp2.action) \o <<")">> >> ||
             res.pVars := temp1.pVars \cup temp2.pVars 
             
      elsif sst.type = "either"
        then (**************************************************************)
             (* Set xltemp1 to the sequence of results from calling        *)
             (* XlateSStmtSeq on the elements of sst.ors, and set temp2 to *)
             (* the union all the pVars values returned.                   *)
             (**************************************************************)
             xltemp1 := << >> ;                                       XSt31:
             temp2 := {} ;
             xlssi := 1 ;                                             XSt32:
             while xlssi \leq Len(sst.ors) do                         XSt33:
               call XlateSStmtSeq(sst.ors[xlssi], primedVars, localSub); XSt34:
               xltemp1 := xltemp1 \o <<rVal>> ;
               temp2 := temp2 \cup rVal.pVars ;
               xlssi := xlssi + 1
             end while ;                                              

             (**************************************************************)
             (* Set temp3 to the sequence of all `ors' actions.            *)
             (**************************************************************)
             temp3 := [x \in 1..Len(xltemp1) |->
                        xltemp1[x].action \o 
                            MakeUnchanged(
                                   CompSetToSubseq(
                                      xltemp1[x].pVars,
                                      SetToSubseq(temp2 ,
                                                  allVarSeq))) ] ;
             res := [action |-> MakeDisj([x \in 1..Len(temp3) |->
                                            <<"(">> \o MakeConj(temp3[x])
                                               \o <<")">>]),
                     pVars  |-> temp2]
             
      elsif sst.type = "with"
        then call PrimeAndAddSub(primedVars, localSub, sst.exp) ;     XSt41:
             temp1 := rVal ;
             call XlateSStmtSeq(sst.do, primedVars, localSub) ;       XSt42:
             temp2 := MakeConj(rVal.action) ;
             res.pVars := rVal.pVars ;                                XSt43:
             if sst.eqOrIn = "="
               then res.action := 
                      << <<"LET", sst.var, "==">> \o temp1 \o <<"IN">> \o
                           temp2 >>
               else res.action := 
                      << <<"\\E", sst.var, "\\in">> \o temp1 \o <<":">> \o
                           temp2 >>
             end if;
      elsif sst.type = "when"
        then call PrimeAndAddSub(primedVars, localSub, sst.exp) ;     XSt6:
             res.action := res.action \o  << rVal >>  \** << >> added 18 Dec 05
                        
      elsif sst.type = "print"
        then call PrimeAndAddSub(primedVars, localSub, sst.exp) ;     XSt7:
             res.action := res.action \o 
                            << <<"PrintT", "(">> \o rVal \o <<")">> >>

      elsif sst.type = "assert"
        then call PrimeAndAddSub(primedVars, localSub, sst.exp) ;     XSt8:
             res.action := res.action \o 
                            << <<"Assert", "(">> \o rVal \o 
                                  <<",">> \o Quote("Failed assert") \o 
                                << ")">> >>

      elsif sst.type = "skip"
        then skip

      else call Error("13: Unknown simple statement type " \o sst.type )
      end if ;                                                        XSt99:
      rVal := res ;
      return
    end procedure


  procedure XlateSStmtSeq(sstsq, xprimedVars, localSub)
    (***********************************************************************)
    (* Calls XlateSStmt iteratively to translate the sequence sstsq of     *)
    (* simple statements to a single action.  It sets rVal to a record     *)
    (* with fields:                                                        *)
    (*                                                                     *)
    (*    action: the action, represented as a sequence of expressions     *)
    (*            whose conjunction represents the action,                 *)
    (*    pVars: the union of primedVars and all the variables that        *)
    (*           are assigned a value by the action.                       *)
    (***********************************************************************)
    variables res ; xlsssqi = 1;
    begin XStSq1: 
      res := [action |-> << >>, pVars  |-> xprimedVars] ;            XStSq2:
      while xlsssqi \leq Len(sstsq) do
        call XlateSStmt(sstsq[xlsssqi], res.pVars, localSub) ;       XStSq3:
        res.action := res.action \o rVal.action ||
        res.pVars  := rVal.pVars ;
        xlsssqi := xlsssqi + 1 
      end while ;
      rVal := res ;
     return
    end procedure

\*****************************************************************

  procedure XlateLabStmtSeq(lsstsq, localSub, defSub, nxt)
    (***********************************************************************)
    (* Uses XlateSStmtSeq to translate a sequence of labeled statements,   *)
    (* where                                                               *)
    (*                                                                     *)
    (*  lsstsq   : The sequence of labeled statements.                     *)
    (*  localSub : The expression to be added as a subscript to local      *)
    (*             variables.                                              *)
    (*  defSub   : Either << >> or << "(", self, ")" >>.  Each definition  *)
    (*             produced by the translation has the form                *)
    (*                  label defsub == action                             *)
    (*  nxt      : The label at the end of the sequence.                   *)
    (*                                                                     *)
    (* It sets rVal to a record with fields                                *)
    (*                                                                     *)
    (*    defs : An expression that is a sequence of definitions of the    *)
    (*           actions produced by the statement, each definition of the *)
    (*           form label defsub == action, where defSub is going        *)
    (*           to be either << >> or <<"(", self, ")">>                  *)
    (*                                                                     *)
    (*    disj : An expression that is the disjunction of all the defined  *)
    (*           actions.                                                  *)
    (*                                                                     *)
    (* NOTE: We use the strings "@pc@" and "@stack@" instead of "pc" and   *)
    (* "stack" for the variables that we introduce.  As the final step of  *)
    (* the translation, we replace them with "pc" and "stack".  This means *)
    (* that any "pc" and "stack" in user expressions are not subscripted.  *)
    (* This makes the translation handle user-introduced instances of      *)
    (* these variables almost correctly.                                   *)
    (*                                                                     *)
    (* This introduces the bug that any strings "@pc@" and "@stack@" in    *)
    (* expressions will be translated to "pc" and "stack", but we're not   *)
    (* going to worry about that.                                          *)
    (***********************************************************************)
    variables lsstqi = 1 ; lsstemp ; disjs = << >> ; defs = << >> ;
    begin                                                              XLS1:
      call ExpandSeq(lsstsq, nxt) ;                                    XLS2:
      lsstemp := rVal ;                                                XLS3:
      while lsstqi \leq Len(lsstemp) do
        call XlateSStmtSeq(lsstemp[lsstqi].stmts, {}, localSub) ;      XLS4:
        defs := defs \o 
                        << lsstemp[lsstqi].label >> 
                           \o defSub \o <<"==">> 
                           \o MakeConj( << <<"@pc@">> \o localSub \o <<"=">> 
                                             \o Quote(lsstemp[lsstqi].label)
                                         >> \o rVal.action \o
                                         MakeUnchanged(
                                          CompSetToSubseq(rVal.pVars, 
                                                          allVarSeq))) ;
        disjs := Append(disjs, << lsstemp[lsstqi].label >> \o defSub) ;
        lsstqi := lsstqi + 1 
      end while ;
      rVal := [defs |-> defs, disj |-> MakeDisj(disjs)] ;
      return; 
    end procedure


\****************************  


\******************** UTILITY Procedures
       
  procedure Error(str) 
    (***********************************************************************)
    (* Reports an error and halts.                                         *)
    (***********************************************************************)
    begin Error1: print "<<@Error@" \o str \o "@EndError@";
                  goto Done ;
          Error2: return ;   \* Needed because translator requires a return.
    end procedure 
\********************* main body of algorithm *************************
  begin PC1: 
    call IsAlgorithm(ast) ;                                              PC2: 
    print ast.name \o " is a legal Algorithm" ;

    (**************************************************************)
    (* Set pMap and prcdVars.                                     *)
    (**************************************************************)
    pMap := << >>  ; \* The empty record
    i := 1 ;                                                            PC3: 
    while i \leq Len(ast.prcds) do
      pMap := pMap @@ 
                (ast.prcds[i].name :> 
                  [params  |-> [x \in 1..Len(ast.prcds[i].params) |-> 
                                          ast.prcds[i].params[x].var],
                   vars    |-> [x \in 1..Len(ast.prcds[i].decls) |-> 
                                          ast.prcds[i].decls[x].var],
                   vals    |-> [x \in 1..Len(ast.prcds[i].decls) |-> 
                                          ast.prcds[i].decls[x].val],
                   label   |-> ast.prcds[i].body[1].label,
                   tlavars |-> {ast.prcds[i].params[y].var :
                                   y \in 1..Len(ast.prcds[i].params)}
                                 \cup
                               {ast.prcds[i].decls[y].var :
                                   y \in 1..Len(ast.prcds[i].decls)}] ) ;
      i := i+1 ;
      end while ;
      prcdVars := UNION {SeqToSet(pMap[x].params) \cup
                          SeqToSet(pMap[x].vars) : x \in DOMAIN pMap} ;
      (**************************************************************)
      (* Set procSeq.                                               *)
      (**************************************************************)
      if ast.type = "multiprocess"  
        then procSeq := [y \in 1.. Len(ast.procs) |-> 
                           [vars  |-> [x \in 1..Len(ast.procs[y].decls) 
                                          |-> ast.procs[y].decls[x].var],
                            label |-> ast.procs[y].body[1].label] ] ;
        else procSeq := << >>  ; 
      end if ;

      (**************************************************************)
      (* Compute globalVars, nonGlobalVars, and allVarSeq           *)
      (**************************************************************)
      allVarSeq  := [x \in 1..Len(ast.decls) |-> ast.decls[x].var] 
                      \o <<"@pc@">>
;
      globalVars := SeqToSet(allVarSeq) ;                              PC4:
      if ast.prcds # << >>
        then allVarSeq := allVarSeq \o <<"@stack@">> \o
                          \* sequence of all procedure vars and params.
                          SeqConcat( 
                            [x \in 1..Len(ast.prcds) |->
                              [y \in 1..Len(ast.prcds[x].decls) |-> 
                                 ast.prcds[x].decls[y].var]
                              \o
                              [y \in 1..Len(ast.prcds[x].params) |->
                                 ast.prcds[x].params[y].var] ]) ;       
             globalVars := globalVars \cup {"@stack@"}
      end if ;                                                          PC5:
      if ast.type = "multiprocess"
        then allVarSeq := allVarSeq \o
                             SeqConcat(
                                 [x \in 1..Len(ast.procs) |->
                                   [y \in 1..Len(ast.procs[x].decls) |->
                                      ast.procs[x].decls[y].var]]) 
      end if ;
      nonGlobalVars := SeqToSet(allVarSeq) \ globalVars ;


      
      (*********************************************************************)
      (* Produce variable declarations and output of `definition'          *)
      (* statement.                                                        *)
      (*********************************************************************)
      if (ast.defs = << >>) \/ (globalVars = {})
        then result := ast.defs \o <<"VARIABLES">> \o CommaSeq(allVarSeq)
        else result := <<"VARIABLES">> \o 
                          CommaSeq(SetToSubseq(globalVars, allVarSeq)) \o
                       ast.defs \o <<"VARIABLES">> \o 
                          CommaSeq(SetToSubseq(nonGlobalVars, allVarSeq)) 
      end if ;                                                           PC6:

      (*********************************************************************)
      (* Output definition of `vars'.                                      *)
      (*********************************************************************)
      result := result \o <<"vars", "==", "<<">> \o CommaSeq(allVarSeq)
                 \o <<">>">> ;                                           PC7:

      (*********************************************************************)
      (* Output definition of ProcSet for a multiprocess algorithm.        *)
      (*********************************************************************)
      if ast.type = "multiprocess"
        then result := result \o <<"ProcSet", "==">> \o
                        MakeUnion(SeqConcat([x \in 1..Len(ast.procs) |->
                                   IF ast.procs[x].eqOrIn = "\\in"
                                     THEN <<ast.procs[x].id>>
                                     ELSE << <<"{">> \o  ast.procs[x].id
                                               \o << "}">>
                                          >> ] ) )
      end if ;                                                           PC8:

      (*********************************************************************)
      (* Output Init, setting gtemp1 to the sequence of its conjuncts.     *)
      (*                                                                   *)
      (* First set it to the the initialization of the globally declared   *)
      (* variables.                                                        *)
      (*********************************************************************)
      gtemp1 := << >> ;
      i := 1 ;                                                           PC9:
      while i \leq Len(ast.decls) do 
        gtemp1 := gtemp1 \o << <<ast.decls[i].var, ast.decls[i].eqOrIn>> 
                   \o ast.decls[i].val >> ;
        i := i + 1;
      end while ;

      (*********************************************************************)
      (* Append the initializations of procedure parameters and procedure  *)
      (* declarations.                                                     *)
      (*********************************************************************)
      i := 1 ;                                                          PC10:
      while i \leq Len(ast.prcds) do 
        j := 1 ;                                                        PC11:
        while j \leq Len(ast.prcds[i].params) do 
          if ast.type = "uniprocess"
            then gtemp1 := gtemp1 \o << <<ast.prcds[i].params[j].var, "=">>
                             \o ast.prcds[i].params[j].val >>
            else gtemp1 := gtemp1 \o 
                             << <<ast.prcds[i].params[j].var, "=", "[", 
                                "self", "\\in", "ProcSet", "|->">>
                             \o ast.prcds[i].params[j].val \o <<"]">> >>
          end if ;
          j := j + 1;
        end while ;
        j := 1 ;                                                        PC12:
        while j \leq Len(ast.prcds[i].decls) do 
          if ast.type = "uniprocess"
            then gtemp1 := gtemp1 \o << <<ast.prcds[i].decls[j].var, "=">>
                             \o ast.prcds[i].decls[j].val >>
            else gtemp1 := gtemp1 \o 
                             << <<ast.prcds[i].decls[j].var, "=", "[", 
                                "self", "\\in", "ProcSet", "|->">>
                             \o ast.prcds[i].decls[j].val \o <<"]">> >>
          end if ;
          j := j + 1;
        end while ;
        i := i + 1;
      end while ;

      (*********************************************************************)
      (* Append initializations of process variables.                      *)
      (*********************************************************************)
      if ast.type = "multiprocess" then 
        i := 1 ;                                                       PC13:
        while i \leq Len(ast.procs) do
          j := 1 ;                                                     PC14:
          while j \leq Len(ast.procs[i].decls) do
            if ast.procs[i].eqOrIn = "="
              then \* single process
                   gtemp1 := gtemp1 \o << <<ast.procs[i].decls[j].var, 
                                            ast.procs[i].decls[j].eqOrIn>> 
                                          \o ast.procs[i].decls[j].val >>
              else \* process set
                   if ast.procs[i].decls[j].eqOrIn = "="
                     then \* var = ...
                          gtemp1 := gtemp1 \o 
                                     << <<ast.procs[i].decls[j].var, "=",
                                          "[", "self", "\\in">> \o
                                          ast.procs[i].id \o <<"|->" >>
                                          \o ast.procs[i].decls[j].val 
                                          \o <<"]">> >>
                     else \* var \in ...
                          gtemp1 := gtemp1 \o 
                                     << <<ast.procs[i].decls[j].var, "\\in",
                                          "[">> \o ast.procs[i].id \o <<"->">>
                                          \o ast.procs[i].decls[j].val 
                                          \o <<"]">> >>
                   end if ;
            end if ;
            j := j + 1 ;
          end while ; 
          i := i + 1 ;
        end while ;
      end if ;                                                        PC15:

      (*********************************************************************)
      (* Append initialization of `stack'.                                 *)
      (*********************************************************************)
      if ast.prcds # << >> then
        if ast.type = "uniprocess"
          then gtemp1 := gtemp1 \o << <<"@stack@", "=", "<<", ">>" >> >>
          else gtemp1 := gtemp1 \o << <<"@stack@", "=", "[", "self", "\\in",
                                        "ProcSet", "|->", "<<", ">>", "]" >> >>
        end if ;
      end if ;                                                          PC16:
      
      (*********************************************************************)
      (* Append initialization of pc.                                      *)
      (*********************************************************************)
      if ast.type = "uniprocess"
          then gtemp1 := gtemp1 \o << <<"@pc@", "=">> \o 
                                  Quote(ast.body[1].label) >>
          else gtemp2 := <<"@pc@", "=", "[", "self", "\\in", "ProcSet",
                                "|->", "CASE">> ;
               i := 1 ;                                                PC17:
               while i \leq Len(ast.procs) do
                 if i > 1 then gtemp2 := gtemp2 \o <<"[]">> end if;    PC18:
                 gtemp2 := gtemp2 \o
                            <<"self", ast.procs[i].eqOrIn>> \o
                               ast.procs[i].id \o <<"->">> \o
                              Quote(ast.procs[i].body[1].label) ;             
                 i := i + 1 ;
               end while ;
               gtemp1 := gtemp1 \o <<gtemp2 \o <<"]">>>> 
      end if;                                                          PC19:
      result := result \o <<"Init", "==">> \o MakeConj(gtemp1) ;

      (*********************************************************************)
      (* Append procedures' definitions.                                   *)
      (*********************************************************************)
      if ast.prcds # << >> then
        i := 1 ;                                                       PC20:
        while i \leq Len(ast.prcds) do
          if ast.type = "uniprocess"
            then localVars := {} ;
                 call XlateLabStmtSeq(ast.prcds[i].body, 
                                         << >>, << >>, "Error")
            else localVars := prcdVars \cup {"@pc@", "@stack@"} ;
                 call XlateLabStmtSeq(ast.prcds[i].body, 
                                      <<"[", "self", "]">>, 
                                      <<"(", "self", ")">>, "Error")
          end if ;                                                    PC21:
          result := result \o rVal.defs
                     \o <<ast.prcds[i].name>>
                     \o (IF ast.type = "uniprocess" 
                           THEN << "==" >>
                           ELSE <<"(", "self", ")", "==">>)
                     \o rVal.disj ;
          i := i + 1 
        end while ;
      end if;                                                          PC29:

      (*********************************************************************)
      (* For a multiprocess algorithm, append processes' definitions and   *)
      (* append definition of Next.                                        *)
      (*********************************************************************)
      if ast.type = "multiprocess" then 
        i := 1 ;                                                       PC30:
        while i \leq Len(ast.procs) do
          if ast.procs[i].eqOrIn = "=" 
            then localVars := {"@pc@", "@stack@"} \cup prcdVars ;
                 call XlateLabStmtSeq(ast.procs[i].body, 
                                      <<"[">> \o ast.procs[i].id \o <<"]">>,
                                      << >>, "Done")
            else localVars := SeqToSet(procSeq[i].vars) \cup prcdVars \cup 
                                         {"@pc@", "@stack@"} ;
                 call XlateLabStmtSeq(ast.procs[i].body, 
                                      <<"[", "self", "]">>,
                                      <<"(", "self", ")">>, "Done")
          end if ;                                                    PC31:
          result := result \o rVal.defs ;                             

          \* set gtemp1 to the lhs of the process's next-state definition
          if ast.procs[i].eqOrIn = "="
            then gtemp1 := <<ast.procs[i].name>>
            else gtemp1 := <<ast.procs[i].name, "(", "self", ")">>
          end if;                                                     PC32:
          result := result \o gtemp1 \o <<"==">> \o rVal.disj ;
          i := i + 1;
        end while ;                                                   PC33:
        result := result \o <<"Next", "==">> \o
                   MakeDisj([x \in 1..Len(ast.procs) |->
                               IF ast.procs[x].eqOrIn = "="
                                   THEN << ast.procs[x].name >>
                                   ELSE <<"(", "\\E", "self" , "\\in">> \o
                                          ast.procs[x].id \o 
                                        <<":", ast.procs[x].name, "(",
                                          "self", ")", ")">>
                              ]) ;                                 PC34:
        if ast.prcds # << >> then    
          result := result \o <<"\\/", "(", "\\E", "self", "\\in",
                                "ProcSet", ":">> \o 
                      MakeDisj([x \in 1..Len(ast.prcds) |->
                                  << ast.prcds[x].name, "(", "self", ")">>
                                 ]) \o <<")">> 
        end if ;                                                     PC35:
        result := result \o 
                    <<"\\/", "(", "(", "\\A", "self", "\\in", "ProcSet", ":", 
                       "@pc@", "[", "self", "]", "=">> \o Quote("Done") \o
                    <<")", "/\\" , "(", "UNCHANGED", "vars", ")", ")" >> ;
        
      end if ;                                                       PC36:


      (*********************************************************************)
      (* Define Next for a uniprocess algorithm.                           *)
      (*********************************************************************)
      if ast.type = "uniprocess" then 
        localVars := {};
        call XlateLabStmtSeq(ast.body, << >>, << >>, "Done") ;       PC41:
        result := result \o rVal.defs \o <<"Next", "==" >> \o rVal.disj \o
                  (IF ast.prcds # << >> 
                     THEN <<"\\/">> \o 
                          MakeDisj([x \in 1..Len(ast.prcds) |->
                                  << ast.prcds[x].name>> ])
                     ELSE << >>) \o
                    <<"\\/", "(", "(", "@pc@", "=">> \o Quote("Done") \o
                    << ")", "/\\", "UNCHANGED", "vars", ")" >> 
      end if;                                                        PC49:

      (*********************************************************************)
      (* Set gtemp1 to the fairness conjunct.                              *)
      (*********************************************************************)
      if fairness = ""
        then gtemp1 := << >>
        else gtemp1 := << "/\\" >> ;                                   PC50:
             if (fairness \in {"wf", "sf"}) /\ (ast.type = "multiprocess")
               then i := 1 ;
                    gtemp2 := << (IF fairness = "wf" 
                                  THEN "WF_" ELSE "SF_") \o "vars", "(">> ;
                    \* set gtemp3 to the sequence of WF/SF conjuncts
                    gtemp3 := << >> ;                                  PC51:

                    \* fairness of next-state actions for processes
                    while i \leq Len(ast.procs) do 
                      if ast.procs[i].eqOrIn = "="
                        then gtemp3 := gtemp3 \o
                                        << gtemp2 \o 
                                              <<ast.procs[i].name, ")">> >>
                        else gtemp3 := 
                               gtemp3 \o
                               <<  << "\\A", "self", "\\in">> \o
                                  ast.procs[i].id \o << ":" >> \o gtemp2 \o
                               <<ast.procs[i].name, "(", "self", ")", ")">> >>
                      end if ;
                      i := i + 1 ;
                    end while ;

                    \* fairness of next-state actions for procedures.
                    gtemp4 := << >> ;
                    i := 1 ;                                            PC59:
                    while i \leq Len(ast.prcds) do 
                      gtemp4 := gtemp4 \o 
                                 << gtemp2 \o
                                     <<ast.prcds[i].name, "(", "self", 
                                         ")", ")">> >> ;
                      i := i + 1 ;
                    end while ;
                    gtemp3 := gtemp3 \o
                               <<  << "\\A", "self", "\\in", "ProcSet", 
                                      ":" >> \o
                                     MakeConj(gtemp4) >> ;

                    gtemp1 := gtemp1 \o MakeConj(gtemp3) ;
               else gtemp1 := gtemp1 \o <<"WF_", "vars", "(", "Next", ")">>
             end if;
      end if ;                                                         PC52:

      result := result \o 
                 <<"Spec", "==", "Init", "/\\", "[]", "[", "Next", "]_",
                   "vars">> \o gtemp1 ;                                PC53:
     
     (**********************************************************************)
     (* Add definition of Termination.                                     *)
     (**********************************************************************)
     if ast.type = "uniprocess"
       then result := result \o <<"Termination", "==", "<>", "(", "@pc@", "=">>
                        \o Quote("Done") \o <<")">>
       else result := result \o 
                        <<"Termination", "==", "<>", "(", "\\A", "self", 
                           "\\in", "ProcSet", ":", "@pc@", "[", "self", "]",  
                          "=">>
                        \o Quote("Done") \o <<")">>
     end if ;

 PC999: print FixPCandStack(result)
 
  end algorithm

*) 

------------------------------- MODULE Pcal ------------------------------
(***************************************************************************)
(* INTRODUCTION                                                            *)
(*                                                                         *)
(* This module specifies the translation from the abstract syntax tree of  *)
(* a (global-naming) +CAL algorithm to its TLA+ description.  The          *)
(* specification consists of two parts:                                    *)
(*                                                                         *)
(*   1. A specification of the grammar of an algorithm's abstract          *)
(*      syntax tree.                                                       *)
(*                                                                         *)
(*   2. The specification of an operator Translation such that             *)
(*      Translation(alg, fairnessOption) is a TLA+ specification of        *)
(*      the +CAL algorithm with abstract syntax tree alg, where            *)
(*      fairnessOption is one of:                                          *)
(*                                                                         *)
(*         ""       - No fainess condition.                                *)
(*         "wf"     - Weak fairness of all process actions.                *)
(*         "wfNext" - Weak fairness of entire next-state action.           *)
(*         "sf"     - Strong fairness of all process actions.              *)
(*                                                                         *)
(* For a uniprocess algorithm, "wf", "wfNext" and "sf", are all            *)
(* equivalent (strong and weak fairness are equivalent for a uniprocess    *)
(* algorithm).                                                             *)
(*                                                                         *)
(* The purpose of the specification is to serve as a partial spec of a     *)
(* algorithm to translate +CAL algorithms into TLA+.  It is not a complete *)
(* specification because:                                                  *)
(*                                                                         *)
(*  - It assumes that macro expansion has been performed.                  *)
(*                                                                         *)
(*  - It assume that all labels and variable names are distinct.  (The     *)
(*    translation program should rename labels and variables where         *)
(*    necessary to eliminate name collisions.)                             *)
(*                                                                         *)
(*  - It does not describe the formatting of the output.  Formulas that    *)
(*    the translation program should write for readability as              *)
(*                                                                         *)
(*       /\ A                                                              *)
(*       /\ ...                                                            *)
(*       /\ Z                                                              *)
(*                                                                         *)
(*    are instead written (A) /\ ...  /\ (Z).  Also, the formatting of     *)
(*    formulas that result from expressions in the algorithm is not        *)
(*    specified.  The translation program must preserve indentation in     *)
(*    such expressions both for readability and to maintain the meaning    *)
(*    of expressions that use TLA+'s conjunction/disjunction lists.        *)
(*                                                                         *)
(*  - It describes only the translation of algorithms that should be       *)
(*    successfully translated.  It does not specify when and how the       *)
(*    translation program should report errors.                            *)
(*                                                                         *)
(*  - It does not properly handle instances of `pc' and `stack' in         *)
(*    the a multiprocess algorithm.  (Instances occurring                  *)
(*    in the user algorithm have `self' subscripts added, when they        *)
(*    should not.                                                          *)
(*                                                                         *)
(* This specification should be modified as necessary to keep up with any  *)
(* changes to the +CAL language or how it should be translated.            *)
(*                                                                         *)
(* We assume that the reader is familiar with the text document describing *)
(* the +CAL language and the translation, titled "+CAL: A Programming      *)
(* Language for TLA+", herein referred to as the +CAL document.            *)
(*                                                                         *)
(* OUTPUT FORMATING                                                        *)
(*                                                                         *)
(* In the abstract syntax tree of a +CAL algorithm, a TLA+ expression is   *)
(* described as a sequence of lexemes, where a lexeme is a string.  The    *)
(* algorithm's TLA+ description is similarly described as a sequence of    *)
(* lexemes.  Missing from such a description is the two-dimensional        *)
(* aspect of TLA+.  In particular, a TLA+ expression such as               *)
(*                                                                         *)
(*     /\ C \/ D                                                           *)
(*     /\ E                                                                *)
(*                                                                         *)
(* is not described by the sequence `/\ C \/ D /\ E' of lexemes.  For      *)
(* Translation(alg, ...)  to produce a correct TLA+ specification, this    *)
(* TLA+ expression must be written as (C \/ D) /\ E.                       *)
(*                                                                         *)
(* This specification therefore omits an important part of the             *)
(* specification of an actual program to translate +CAL algorithms to its  *)
(* TLA+ version--namely, the precise formatting of the TLA+ version.       *)
(* Even if TLA+ expressions were not two-dimensional, the formatting of    *)
(* the output would be important because the user should be able to read   *)
(* and understand the output.  Formatting of the translation is discussed  *)
(* in the +CAL document.                                                   *)
(*                                                                         *)
(*                                                                         *)
(* ERRORS                                                                  *)
(*                                                                         *)
(* The definition of Translation is not a complete specification of        *)
(* an actual translation program because it does not adequately describe   *)
(* error detection and reporting.  Any +CAL algorithm text that satisfies  *)
(* the BNF grammar yields an abstract syntax tree.  However, the algorithm *)
(* and its syntax tree may have "semantic" errors such as declaring the    *)
(* same variable twice in the same context.  There are five ways errors in *)
(* a syntax tree `alg' could manifest itself in the definition of          *)
(* Translation(alg, ...).                                                  *)
(*                                                                         *)
(*   1. Translation(alg, ...) may contain a sequence of strings that       *)
(*      represents an error message rather than TLA+ -- for example:       *)
(*                                                                         *)
(*          Error : multiple assignemnt to variable var                    *)
(*                                                                         *)
(*   2. Translation(alg, ...) is undefined--more precisely, it equals      *)
(*      a "silly expression" (see Section 6.2, page 67 of the TLA+         *)
(*      book).  This means that TLC would report an error if it            *)
(*      tried to compute Translation(alg, ...).                            *)
(*                                                                         *)
(*   3. Translation(alg, ... ) is syntactically incorrect TLA+, so SANY    *)
(*      will complain when run on the output.                              *)
(*                                                                         *)
(*   4. Translation(alg, ...) will be syntactically correct TLA+ but will  *)
(*      produce an error when run by TLC.                                  *)
(*                                                                         *)
(*   5. Translation(alg, ...) will be syntactically correct TLA+ and will  *)
(*      be run without error by TLC, but will produce strange behavior.    *)
(*                                                                         *)
(* Errors of the first type are benign, since it is obvious from this      *)
(* specification how they can be detected and reported by a translation    *)
(* program.                                                                *)
(*                                                                         *)
(* All known errors of type 2 are clearly indicated in the specification   *)
(* and are similarly benign.  (They could be turned into type 1 errors,    *)
(* but this would complicate the specification.)  Other errors of type 2   *)
(* might exist; they could result in unexpected exceptions in a            *)
(* translation program.                                                    *)
(*                                                                         *)
(* Known errors of types 3-5 should be detected by a translation program   *)
(* Some of these errors can't be detected because they depend on other     *)
(* parts of the module containing the algorithm.  For example, the         *)
(* algorithm might declare a variable x when x is declared or defined      *)
(* elsewhere in the module.                                                *)
(*                                                                         *)
(* I know of the following type 3 errors:                                  *)
(*                                                                         *)
(*  - Most illegal multiple uses of the same identifier--for example,      *)
(*    two identical labels in the same procedure.                          *)
(*                                                                         *)
(* I know of the following errors that might produce type 4 or type 5      *)
(* errors.                                                                 *)
(*                                                                         *)
(*  - An algorithm or process variable initialized with non-constant       *)
(*    expressions.                                                         *)
(*                                                                         *)
(*  - A process or procedure using a variable that is local to             *)
(*    another process or procedure.                                        *)
(*                                                                         *)
(* There's a fuzzy line between type 5 errors and features that allow the  *)
(* user to take advantage of the translation to do things that could not   *)
(* be done with an ordinary programming language.  We'll probably have to  *)
(* decide on a case-by-case basis what should be considered an error       *)
(* rather than a feature.                                                  *)
(*                                                                         *)
(*                                                                         *)
(* EXECUTING THE SPECIFICATION WITH TLC                                    *)
(*                                                                         *)
(* The definitions were written so that they could be executed by TLC. In  *)
(* particular, TLC can, in principle, compute Translation(alg, ...  ) for  *)
(* any abstract syntax tree alg of a correct algorithm.  In practice, it   *)
(* probably can't do this for very complicated algorithms, where           *)
(* complexity is measured by how deeply nested the algorithm statements    *)
(* are.  Making the specification executable required doing some things in *)
(* a somewhat complicated way.  One such complication involves the         *)
(* representation of strings in TLA+ expressions.  Because TLC does not    *)
(* implement the TLA+ definition of a string as a sequence of characters,  *)
(* strings in a TLA+ expressions are represented in the following somewhat *)
(* strange way.  Recall that a TLA+ expression is represented in the       *)
(* abstract syntax tree and in the output as a sequence of strings, so     *)
(* `x+y' is represented as <<"x", "+", "y">>.  Recall also that special    *)
(* characters such as double-quote are preceded by a backslash when they   *)
(* appear in a string.  For example,                                       *)
(*                                                                         *)
(*    `. "\"x\\" .'                                                        *)
(* `~ Note: if you're reading this in the ASCII file rather than the       *)
(* output produced by TLATeX, ignore the strings `.  and .' , which are    *)
(* TLATeX formatting commands.  ~'                                         *)
(*                                                                         *)
(* is the string consisting of the three characters double-quote, x, and   *)
(* backslash.  In this specification, a string "foo" that appears in a     *)
(* TLA+ expression is represented by the sequence of three strings         *)
(*                                                                         *)
(*   `. "\""   "foo"   "\""  .'                                            *)
(*                                                                         *)
(* For example, the TLA+ expression `a["foo"]' is represented as           *)
(*                                                                         *)
(*   `. <<"a", "[", "\"", "foo", "\"", "]">> .'                            *)
(*                                                                         *)
(* CAVEAT                                                                  *)
(*                                                                         *)
(* This specification has not been carefully read or extensively tested.   *)
(* While it has been tested with a number of algorithms, that testing was  *)
(* not extensive enough to catch errors in corner cases.  Such errors      *)
(* undoubtedly exist.                                                      *)
(***************************************************************************)
EXTENDS AST, Naturals, Sequences, FiniteSets , TLC

Last(seq)  == seq[Len(seq)]
Front(seq) == [i \in 1..(Len(seq)-1) |-> seq[i]]

Quote(id) == <<"\"", id, "\"" >>
  (*************************************************************************)
  (* If id is an identifier such as a `Label', then this is the Expr that  *)
  (* represents "id" -- that is, id as a quoted string.  This              *)
  (* representation of strings in expressions is explained above.          *)
  (*************************************************************************)


PCAssign(label) == [type |-> "assignment",
                    ass  |-> << [lhs |-> [var |-> "@pc@", sub |-> << >>],
                                 rhs |-> Quote(label)] >> ]
FinalType == {"call", "return", "callReturn", "goto"}

SeqToSet(s) == {s[i] : i \in 1..Len(s)}
  (*************************************************************************)
  (* The set of elements in the sequence s                                 *)
  (*************************************************************************)

SetToSubseq(S, seq) ==
  (*************************************************************************)
  (* The subsequence of seq containing those elements in S.                *)
  (*************************************************************************)
  LET Test(e) == e \in S IN SelectSeq(seq, Test)

CompSetToSubseq(S, seq) ==
  (*************************************************************************)
  (* The subsequence of seq containing those elements not in S.            *)
  (*************************************************************************)
  LET Test(e) == e \notin S IN SelectSeq(seq, Test)

  
SeqConcat(s) ==
  (************************************************************************)
  (* If s is a sequence of sequences, then this is the concatenation of   *)
  (* those sequences.                                                     *)
  (************************************************************************)
  LET SC[i \in 0..Len(s)] ==
       (********************************************************************)
       (* The concatenation of the first i sequences of s.                 *)
       (********************************************************************)
       IF i = 0 THEN << >>
                ELSE SC[i-1] \o s[i]
  IN  SC[Len(s)]

MakeConj(eseq) ==
  (*************************************************************************)
  (* If eseq is a sequence of expressions, then this is their conjunction. *)
  (* Conjunctions are written with the usual binary operator /\ , with     *)
  (* each conjunct enclosed in parentheses.  A translation program would   *)
  (* translate the sequence of expressions into a /\-bulleted list of      *)
  (* conjuncts.                                                            *)
  (*                                                                       *)
  (* The conjunction of an empty sequence of expressions is defined to     *)
  (* equal TRUE. The only way I can think of an explicit formulat TRUE     *)
  (* being created by the translation is in a null ELSE clause, which can  *)
  (* arise in translating a statement like                                 *)
  (*  `.                                                                   *)
  (*    if x > 0 then when y = 0;                                     .'   *)
  (*                                                                       *)
  (*************************************************************************)
  CASE eseq = << >>  -> << "TRUE" >>
  []   Len(eseq) = 1 -> <<"(">> \o eseq[1] \o <<")">>
  []   OTHER -> 
         <<"(">> 
           \o SeqConcat([i \in 1..(2*Len(eseq)-1) |-> 
                         IF i % 2 = 0 THEN IF i > 1 THEN <<")", "/\\", "(">>
                                                    ELSE << >>
                                      ELSE eseq[(i + 1) \div 2]])
           \o <<")">>

MakeDisj(eseq) ==
  (*************************************************************************)
  (* If eseq is a sequence of expressions, then this is their disjunction. *)
  (* This is only used for making disjunctions of expressions each of      *)
  (* which consists of a single identifier (the name of an action).  It's  *)
  (* therefore not necessary to put parentheses around the disjuncts.  A   *)
  (* translation program would probably also just write the disjunction    *)
  (* using the binary \/ operator.  (However, it would have to use a bit   *)
  (* of cleverness in formatting a disjunction of a large number of        *)
  (* expressions.)                                                         *)
  (*************************************************************************)
  CASE eseq = << >>  -> << "FALSE" >>
  []   Len(eseq) = 1 -> eseq[1]
  []   OTHER -> 
        SeqConcat([i \in 1..(2*Len(eseq)-1) |-> 
                     IF i % 2 = 0 THEN <<"\\/">>
                                  ELSE eseq[(i + 1) \div 2]])
MakeUnion(eseq) ==
  (*************************************************************************)
  (* If eseq is a non-empty sequence of expressions, then this is their    *)
  (* union.                                                                *)
  (*************************************************************************)
  CASE Len(eseq) = 1 -> <<"(">> \o eseq[1] \o <<")">>
  []   Len(eseq) > 0 -> 
         <<"(">> \o 
         SeqConcat([i \in 1..(2*Len(eseq)-1) |-> 
                      IF i % 2 = 0 THEN IF i > 1 THEN <<")", "\\union", "(">>
                                                 ELSE << >>
                                   ELSE eseq[(i + 1) \div 2]])
          \o <<")">>

CommaSeq(s) ==
  (*************************************************************************)
  (* If s is a sequence of strings, then this equals the sequence obtained *)
  (* by inserting "," between each element of the sequence s.              *)
  (*************************************************************************)
   [i \in 1..(2*Len(s)-1) |-> IF i % 2 = 0 THEN "," 
                                           ELSE s[(i + 1) \div 2]]

MakeUnchanged(varSeq) == 
        (*******************************************************************)
        (* If varSeq is a sequence of variables, then this equals a        *)
        (* sequence that is empty if varSeq is empty or else contains a    *)
        (* single element: an Expr that is the UNCHANGED clause for these  *)
        (* variables.                                                      *)
        (*******************************************************************)
        IF varSeq = << >> 
          THEN << >>        
          ELSE << <<"UNCHANGED">> \o
                    (IF Len(varSeq) = 1
                       THEN <<varSeq[1]>>
                       ELSE << "<<" >> \o CommaSeq(varSeq) \o << ">>" >>)
               >>

AssSeqToMultiAss(aseq) ==
  (*************************************************************************)
  (* If aseq is the sequence <<A1, A2, ...  , An>> of assignment           *)
  (* statements, then this equals the single multi-assignment              *)
  (* A1 || A2 || ...  || An                                                *)
  (*************************************************************************)
  [type |-> "assignment",
   ass  |-> SeqConcat([i \in 1..Len(aseq) |-> aseq[i].ass]) ]

FixPCandStack(seq) ==
      [i \in 1..Len(seq) |-> IF seq[i] = "@pc@" 
                               THEN "pc"
                               ELSE IF seq[i] = "@stack@" 
                                      THEN "stack"
                                      ELSE seq[i] ]

-----------------------------------------------------------------------------

IsSeq(x)         == DOMAIN x = 1..Len(x)
IsNonemptySeq(x) == IsSeq(x) /\ (Len(x) > 0)


\* BEGIN TRANSLATION
\* Label IFS1 of procedure IsFinalStmt at line 290 col 17 changed to IFS1_
\* Label IFS2 of procedure IsFinalStmt at line 302 col 17 changed to IFS2_
\* Procedure variable res of procedure IsAlgorithm at line 93 col 14 changed to res_
\* Procedure variable res of procedure ExpandSeq at line 607 col 22 changed to res_E
\* Procedure variable temp of procedure ExpandLStmt at line 627 col 14 changed to temp_
\* Procedure variable temp of procedure IsFinalSeq at line 662 col 14 changed to temp_I
\* Procedure variable temp2 of procedure ExpandLSeq at line 701 col 24 changed to temp2_
\* Procedure variable temp3 of procedure ExpandLSeq at line 701 col 32 changed to temp3_
\* Procedure variable res of procedure SetPrcdVarsOnCall at line 993 col 13 changed to res_S
\* Procedure variable res of procedure RestorePrcdVarsFrom at line 1042 col 31 changed to res_R
\* Procedure variable res of procedure XlateSStmt at line 1257 col 15 changed to res_X
\* Parameter nxt of procedure ExpandSeq at line 597 col 30 changed to nxt_
\* Parameter nxt of procedure ExpandLStmt at line 621 col 30 changed to nxt_E
\* Parameter nxt of procedure ExpandLSeq at line 688 col 30 changed to nxt_Ex
\* Parameter localSub of procedure XlateSStmt at line 1236 col 41 changed to localSub_
\* Parameter localSub of procedure XlateSStmtSeq at line 1433 col 47 changed to localSub_X
VARIABLES i, j, gtemp1, gtemp2, gtemp3, gtemp4, result, rVal, pMap, prcdVars, 
          procSeq, globalVars, nonGlobalVars, allVarSeq, localVars, pc, stack

(* define statement *)
FinalStmtType(rec) ==
   rec.type \in {"if", "either", "with", "return", "callReturn",
                 "call", "goto"}

VARIABLES A, res_, ia, prcdr, ipr, proc, ip, lsseq, ilss, lstmt, whl, ls, ils, 
          ilLast, ili, le, ile, fs, fi, ifi, ifLast, fe, ife, ife2, feSeq, 
          feSeqLast, fw, ifw, fwLast, cr, icr, gt, sss, isss, ss, asg, ias, 
          ifst, estmt, iee, wi, iw, vdcl, pvdcl, exp, ie, elseq, nxt_, ixs, 
          res_E, lst, nxt_E, temp_, flseq, temp_I, ifsqi, lseq, nxt_Ex, 
          xxtemp1, temp2_, temp3_, temp4, exlsq, callStmt, prcd, svoci, temp, 
          res_S, rprcd, rpvi, rpctemp, res_R, vrs, addExpr, pvexpr, pvi, stk, 
          test, primeVars, sub, expr, sst, primedVars, localSub_, xlssi, 
          xltemp1, temp1, temp2, temp3, res_X, sstsq, xprimedVars, localSub_X, 
          res, xlsssqi, lsstsq, localSub, defSub, nxt, lsstqi, lsstemp, disjs, 
          defs, str

vars == << i, j, gtemp1, gtemp2, gtemp3, gtemp4, result, rVal, pMap, prcdVars, 
           procSeq, globalVars, nonGlobalVars, allVarSeq, localVars, pc, 
           stack, A, res_, ia, prcdr, ipr, proc, ip, lsseq, ilss, lstmt, whl, 
           ls, ils, ilLast, ili, le, ile, fs, fi, ifi, ifLast, fe, ife, ife2, 
           feSeq, feSeqLast, fw, ifw, fwLast, cr, icr, gt, sss, isss, ss, asg, 
           ias, ifst, estmt, iee, wi, iw, vdcl, pvdcl, exp, ie, elseq, nxt_, 
           ixs, res_E, lst, nxt_E, temp_, flseq, temp_I, ifsqi, lseq, nxt_Ex, 
           xxtemp1, temp2_, temp3_, temp4, exlsq, callStmt, prcd, svoci, temp, 
           res_S, rprcd, rpvi, rpctemp, res_R, vrs, addExpr, pvexpr, pvi, stk, 
           test, primeVars, sub, expr, sst, primedVars, localSub_, xlssi, 
           xltemp1, temp1, temp2, temp3, res_X, sstsq, xprimedVars, 
           localSub_X, res, xlsssqi, lsstsq, localSub, defSub, nxt, lsstqi, 
           lsstemp, disjs, defs, str >>

Init == (* Global variables *)
        /\ i = {}
        /\ j = {}
        /\ gtemp1 = {}
        /\ gtemp2 = {}
        /\ gtemp3 = {}
        /\ gtemp4 = {}
        /\ result = << >>
        /\ rVal = {}
        /\ pMap = {}
        /\ prcdVars = {}
        /\ procSeq = {}
        /\ globalVars = {}
        /\ nonGlobalVars = {}
        /\ allVarSeq = {}
        /\ localVars = {}
        (* Procedure IsAlgorithm *)
        /\ A = {}
        /\ res_ = FALSE
        /\ ia = 0
        (* Procedure IsProcedure *)
        /\ prcdr = {}
        /\ ipr = {}
        (* Procedure IsProcess *)
        /\ proc = {}
        /\ ip = {}
        (* Procedure IsLabeledStmtSeq *)
        /\ lsseq = {}
        /\ ilss = {}
        (* Procedure IsLabeledStmt *)
        /\ lstmt = {}
        (* Procedure IsWhile *)
        /\ whl = {}
        (* Procedure IsLabelSeq *)
        /\ ls = {}
        /\ ils = {}
        /\ ilLast = {}
        (* Procedure IsLabelIf *)
        /\ ili = {}
        (* Procedure IsLabelEither *)
        /\ le = {}
        /\ ile = {}
        (* Procedure IsFinalStmt *)
        /\ fs = {}
        (* Procedure IsFinalIf *)
        /\ fi = {}
        /\ ifi = {}
        /\ ifLast = {}
        (* Procedure IsFinalEither *)
        /\ fe = {}
        /\ ife = {}
        /\ ife2 = {}
        /\ feSeq = {}
        /\ feSeqLast = {}
        (* Procedure IsFinalWith *)
        /\ fw = {}
        /\ ifw = {}
        /\ fwLast = {}
        (* Procedure IsCallOrReturn *)
        /\ cr = {}
        /\ icr = {}
        (* Procedure IsGoto *)
        /\ gt = {}
        (* Procedure IsSimpleStmtSeq *)
        /\ sss = {}
        /\ isss = {}
        (* Procedure IsSimpleStmt *)
        /\ ss = {}
        (* Procedure IsAssign *)
        /\ asg = {}
        /\ ias = {}
        (* Procedure IsIf *)
        /\ ifst = {}
        (* Procedure IsEither *)
        /\ estmt = {}
        /\ iee = {}
        (* Procedure IsWith *)
        /\ wi = {}
        /\ iw = {}
        (* Procedure IsVarDecl *)
        /\ vdcl = {}
        (* Procedure IsPVarDecl *)
        /\ pvdcl = {}
        (* Procedure IsExpr *)
        /\ exp = {}
        /\ ie = {}
        (* Procedure ExpandSeq *)
        /\ elseq = {}
        /\ nxt_ = {}
        /\ ixs = {}
        /\ res_E = << >>
        (* Procedure ExpandLStmt *)
        /\ lst = {}
        /\ nxt_E = {}
        /\ temp_ = {}
        (* Procedure IsFinalSeq *)
        /\ flseq = {}
        /\ temp_I = {}
        /\ ifsqi = {}
        (* Procedure ExpandLSeq *)
        /\ lseq = {}
        /\ nxt_Ex = {}
        /\ xxtemp1 = {}
        /\ temp2_ = {}
        /\ temp3_ = {}
        /\ temp4 = {}
        /\ exlsq = {}
        (* Procedure SetPrcdVarsOnCall *)
        /\ callStmt = {}
        /\ prcd = {}
        /\ svoci = {}
        /\ temp = {}
        /\ res_S = << >>
        (* Procedure RestorePrcdVarsFrom *)
        /\ rprcd = {}
        /\ rpvi = {}
        /\ rpctemp = {}
        /\ res_R = << >>
        (* Procedure ProcessVars *)
        /\ vrs = {}
        /\ addExpr = {}
        /\ pvexpr = {}
        /\ pvi = 1
        /\ stk = << >>
        /\ test = TRUE
        (* Procedure PrimeAndAddSub *)
        /\ primeVars = {}
        /\ sub = {}
        /\ expr = {}
        (* Procedure XlateSStmt *)
        /\ sst = {}
        /\ primedVars = {}
        /\ localSub_ = {}
        /\ xlssi = {}
        /\ xltemp1 = {}
        /\ temp1 = {}
        /\ temp2 = {}
        /\ temp3 = {}
        /\ res_X = [action |-> << >>,
                    pVars  |-> primedVars ]
        (* Procedure XlateSStmtSeq *)
        /\ sstsq = {}
        /\ xprimedVars = {}
        /\ localSub_X = {}
        /\ res = {}
        /\ xlsssqi = 1
        (* Procedure XlateLabStmtSeq *)
        /\ lsstsq = {}
        /\ localSub = {}
        /\ defSub = {}
        /\ nxt = {}
        /\ lsstqi = 1
        /\ lsstemp = {}
        /\ disjs = << >>
        /\ defs = << >>
        (* Procedure Error *)
        /\ str = {}
        /\ stack = << >>
        /\ pc = "PC1"

IA1 == /\ pc = "IA1"
       /\ Assert(\/ /\ A.type = "uniprocess"
                    /\ DOMAIN A = {"type", "name", "defs",
                                      "decls", "prcds", "body"}
                 \/ /\ A.type = "multiprocess"
                    /\ DOMAIN A = {"type", "name", "defs",
                                       "decls", "prcds", "procs"}, 
                 "Failure of assertion at line 94, column 16.")
       /\ Assert(A.name \in STRING, 
                 "Failure of assertion at line 100, column 16.")
       /\ /\ exp' = A.defs
          /\ stack' = << [ procedure |->  "IsExpr",
                           pc        |->  "IA2",
                           ie        |->  ie,
                           exp       |->  exp ] >>
                       \o stack
       /\ ie' = {}
       /\ pc' = "IE1"
       /\ UNCHANGED << i, j, gtemp1, gtemp2, gtemp3, gtemp4, result, rVal, 
                       pMap, prcdVars, procSeq, globalVars, nonGlobalVars, 
                       allVarSeq, localVars, A, res_, ia, prcdr, ipr, proc, ip, 
                       lsseq, ilss, lstmt, whl, ls, ils, ilLast, ili, le, ile, 
                       fs, fi, ifi, ifLast, fe, ife, ife2, feSeq, feSeqLast, 
                       fw, ifw, fwLast, cr, icr, gt, sss, isss, ss, asg, ias, 
                       ifst, estmt, iee, wi, iw, vdcl, pvdcl, elseq, nxt_, ixs, 
                       res_E, lst, nxt_E, temp_, flseq, temp_I, ifsqi, lseq, 
                       nxt_Ex, xxtemp1, temp2_, temp3_, temp4, exlsq, callStmt, 
                       prcd, svoci, temp, res_S, rprcd, rpvi, rpctemp, res_R, 
                       vrs, addExpr, pvexpr, pvi, stk, test, primeVars, sub, 
                       expr, sst, primedVars, localSub_, xlssi, xltemp1, temp1, 
                       temp2, temp3, res_X, sstsq, xprimedVars, localSub_X, 
                       res, xlsssqi, lsstsq, localSub, defSub, nxt, lsstqi, 
                       lsstemp, disjs, defs, str >>

IA2 == /\ pc = "IA2"
       /\ Assert(IsSeq(A.decls), 
                 "Failure of assertion at line 102, column 16.")
       /\ ia' = Len(A.decls)
       /\ pc' = "IA3"
       /\ UNCHANGED << i, j, gtemp1, gtemp2, gtemp3, gtemp4, result, rVal, 
                       pMap, prcdVars, procSeq, globalVars, nonGlobalVars, 
                       allVarSeq, localVars, stack, A, res_, prcdr, ipr, proc, 
                       ip, lsseq, ilss, lstmt, whl, ls, ils, ilLast, ili, le, 
                       ile, fs, fi, ifi, ifLast, fe, ife, ife2, feSeq, 
                       feSeqLast, fw, ifw, fwLast, cr, icr, gt, sss, isss, ss, 
                       asg, ias, ifst, estmt, iee, wi, iw, vdcl, pvdcl, exp, 
                       ie, elseq, nxt_, ixs, res_E, lst, nxt_E, temp_, flseq, 
                       temp_I, ifsqi, lseq, nxt_Ex, xxtemp1, temp2_, temp3_, 
                       temp4, exlsq, callStmt, prcd, svoci, temp, res_S, rprcd, 
                       rpvi, rpctemp, res_R, vrs, addExpr, pvexpr, pvi, stk, 
                       test, primeVars, sub, expr, sst, primedVars, localSub_, 
                       xlssi, xltemp1, temp1, temp2, temp3, res_X, sstsq, 
                       xprimedVars, localSub_X, res, xlsssqi, lsstsq, localSub, 
                       defSub, nxt, lsstqi, lsstemp, disjs, defs, str >>

IA3 == /\ pc = "IA3"
       /\ IF ia > 0
             THEN /\ /\ stack' = << [ procedure |->  "IsVarDecl",
                                      pc        |->  "IA4",
                                      vdcl      |->  vdcl ] >>
                                  \o stack
                     /\ vdcl' = A.decls[ia]
                  /\ pc' = "IV1"
                  /\ UNCHANGED ia
             ELSE /\ ia' = Len(A.prcds)
                  /\ pc' = "IA5"
                  /\ UNCHANGED << stack, vdcl >>
       /\ UNCHANGED << i, j, gtemp1, gtemp2, gtemp3, gtemp4, result, rVal, 
                       pMap, prcdVars, procSeq, globalVars, nonGlobalVars, 
                       allVarSeq, localVars, A, res_, prcdr, ipr, proc, ip, 
                       lsseq, ilss, lstmt, whl, ls, ils, ilLast, ili, le, ile, 
                       fs, fi, ifi, ifLast, fe, ife, ife2, feSeq, feSeqLast, 
                       fw, ifw, fwLast, cr, icr, gt, sss, isss, ss, asg, ias, 
                       ifst, estmt, iee, wi, iw, pvdcl, exp, ie, elseq, nxt_, 
                       ixs, res_E, lst, nxt_E, temp_, flseq, temp_I, ifsqi, 
                       lseq, nxt_Ex, xxtemp1, temp2_, temp3_, temp4, exlsq, 
                       callStmt, prcd, svoci, temp, res_S, rprcd, rpvi, 
                       rpctemp, res_R, vrs, addExpr, pvexpr, pvi, stk, test, 
                       primeVars, sub, expr, sst, primedVars, localSub_, xlssi, 
                       xltemp1, temp1, temp2, temp3, res_X, sstsq, xprimedVars, 
                       localSub_X, res, xlsssqi, lsstsq, localSub, defSub, nxt, 
                       lsstqi, lsstemp, disjs, defs, str >>

IA4 == /\ pc = "IA4"
       /\ ia' = ia-1
       /\ pc' = "IA3"
       /\ UNCHANGED << i, j, gtemp1, gtemp2, gtemp3, gtemp4, result, rVal, 
                       pMap, prcdVars, procSeq, globalVars, nonGlobalVars, 
                       allVarSeq, localVars, stack, A, res_, prcdr, ipr, proc, 
                       ip, lsseq, ilss, lstmt, whl, ls, ils, ilLast, ili, le, 
                       ile, fs, fi, ifi, ifLast, fe, ife, ife2, feSeq, 
                       feSeqLast, fw, ifw, fwLast, cr, icr, gt, sss, isss, ss, 
                       asg, ias, ifst, estmt, iee, wi, iw, vdcl, pvdcl, exp, 
                       ie, elseq, nxt_, ixs, res_E, lst, nxt_E, temp_, flseq, 
                       temp_I, ifsqi, lseq, nxt_Ex, xxtemp1, temp2_, temp3_, 
                       temp4, exlsq, callStmt, prcd, svoci, temp, res_S, rprcd, 
                       rpvi, rpctemp, res_R, vrs, addExpr, pvexpr, pvi, stk, 
                       test, primeVars, sub, expr, sst, primedVars, localSub_, 
                       xlssi, xltemp1, temp1, temp2, temp3, res_X, sstsq, 
                       xprimedVars, localSub_X, res, xlsssqi, lsstsq, localSub, 
                       defSub, nxt, lsstqi, lsstemp, disjs, defs, str >>

IA5 == /\ pc = "IA5"
       /\ IF ia > 0
             THEN /\ /\ prcdr' = A.prcds[ia]
                     /\ stack' = << [ procedure |->  "IsProcedure",
                                      pc        |->  "IA6",
                                      ipr       |->  ipr,
                                      prcdr     |->  prcdr ] >>
                                  \o stack
                  /\ ipr' = {}
                  /\ pc' = "IPr1"
                  /\ UNCHANGED << ia, lsseq, ilss >>
             ELSE /\ IF A.type = "uniprocess"
                        THEN /\ Assert(Len(A.body) > 0, 
                                       "Failure of assertion at line 112, column 23.")
                             /\ /\ lsseq' = A.body
                                /\ stack' = << [ procedure |->  "IsLabeledStmtSeq",
                                                 pc        |->  "IA12",
                                                 ilss      |->  ilss,
                                                 lsseq     |->  lsseq ] >>
                                             \o stack
                             /\ ilss' = {}
                             /\ pc' = "ILSS1"
                             /\ UNCHANGED ia
                        ELSE /\ Assert(IsNonemptySeq(A.procs), 
                                       "Failure of assertion at line 114, column 23.")
                             /\ ia' = Len(A.procs)
                             /\ pc' = "IA10"
                             /\ UNCHANGED << stack, lsseq, ilss >>
                  /\ UNCHANGED << prcdr, ipr >>
       /\ UNCHANGED << i, j, gtemp1, gtemp2, gtemp3, gtemp4, result, rVal, 
                       pMap, prcdVars, procSeq, globalVars, nonGlobalVars, 
                       allVarSeq, localVars, A, res_, proc, ip, lstmt, whl, ls, 
                       ils, ilLast, ili, le, ile, fs, fi, ifi, ifLast, fe, ife, 
                       ife2, feSeq, feSeqLast, fw, ifw, fwLast, cr, icr, gt, 
                       sss, isss, ss, asg, ias, ifst, estmt, iee, wi, iw, vdcl, 
                       pvdcl, exp, ie, elseq, nxt_, ixs, res_E, lst, nxt_E, 
                       temp_, flseq, temp_I, ifsqi, lseq, nxt_Ex, xxtemp1, 
                       temp2_, temp3_, temp4, exlsq, callStmt, prcd, svoci, 
                       temp, res_S, rprcd, rpvi, rpctemp, res_R, vrs, addExpr, 
                       pvexpr, pvi, stk, test, primeVars, sub, expr, sst, 
                       primedVars, localSub_, xlssi, xltemp1, temp1, temp2, 
                       temp3, res_X, sstsq, xprimedVars, localSub_X, res, 
                       xlsssqi, lsstsq, localSub, defSub, nxt, lsstqi, lsstemp, 
                       disjs, defs, str >>

IA6 == /\ pc = "IA6"
       /\ ia' = ia-1
       /\ pc' = "IA5"
       /\ UNCHANGED << i, j, gtemp1, gtemp2, gtemp3, gtemp4, result, rVal, 
                       pMap, prcdVars, procSeq, globalVars, nonGlobalVars, 
                       allVarSeq, localVars, stack, A, res_, prcdr, ipr, proc, 
                       ip, lsseq, ilss, lstmt, whl, ls, ils, ilLast, ili, le, 
                       ile, fs, fi, ifi, ifLast, fe, ife, ife2, feSeq, 
                       feSeqLast, fw, ifw, fwLast, cr, icr, gt, sss, isss, ss, 
                       asg, ias, ifst, estmt, iee, wi, iw, vdcl, pvdcl, exp, 
                       ie, elseq, nxt_, ixs, res_E, lst, nxt_E, temp_, flseq, 
                       temp_I, ifsqi, lseq, nxt_Ex, xxtemp1, temp2_, temp3_, 
                       temp4, exlsq, callStmt, prcd, svoci, temp, res_S, rprcd, 
                       rpvi, rpctemp, res_R, vrs, addExpr, pvexpr, pvi, stk, 
                       test, primeVars, sub, expr, sst, primedVars, localSub_, 
                       xlssi, xltemp1, temp1, temp2, temp3, res_X, sstsq, 
                       xprimedVars, localSub_X, res, xlsssqi, lsstsq, localSub, 
                       defSub, nxt, lsstqi, lsstemp, disjs, defs, str >>

IA10 == /\ pc = "IA10"
        /\ IF ia > 0
              THEN /\ /\ proc' = A.procs[ia]
                      /\ stack' = << [ procedure |->  "IsProcess",
                                       pc        |->  "IA11",
                                       ip        |->  ip,
                                       proc      |->  proc ] >>
                                   \o stack
                   /\ ip' = {}
                   /\ pc' = "IP1"
              ELSE /\ pc' = "IA12"
                   /\ UNCHANGED << stack, proc, ip >>
        /\ UNCHANGED << i, j, gtemp1, gtemp2, gtemp3, gtemp4, result, rVal, 
                        pMap, prcdVars, procSeq, globalVars, nonGlobalVars, 
                        allVarSeq, localVars, A, res_, ia, prcdr, ipr, lsseq, 
                        ilss, lstmt, whl, ls, ils, ilLast, ili, le, ile, fs, 
                        fi, ifi, ifLast, fe, ife, ife2, feSeq, feSeqLast, fw, 
                        ifw, fwLast, cr, icr, gt, sss, isss, ss, asg, ias, 
                        ifst, estmt, iee, wi, iw, vdcl, pvdcl, exp, ie, elseq, 
                        nxt_, ixs, res_E, lst, nxt_E, temp_, flseq, temp_I, 
                        ifsqi, lseq, nxt_Ex, xxtemp1, temp2_, temp3_, temp4, 
                        exlsq, callStmt, prcd, svoci, temp, res_S, rprcd, rpvi, 
                        rpctemp, res_R, vrs, addExpr, pvexpr, pvi, stk, test, 
                        primeVars, sub, expr, sst, primedVars, localSub_, 
                        xlssi, xltemp1, temp1, temp2, temp3, res_X, sstsq, 
                        xprimedVars, localSub_X, res, xlsssqi, lsstsq, 
                        localSub, defSub, nxt, lsstqi, lsstemp, disjs, defs, 
                        str >>

IA11 == /\ pc = "IA11"
        /\ ia' = ia-1
        /\ pc' = "IA10"
        /\ UNCHANGED << i, j, gtemp1, gtemp2, gtemp3, gtemp4, result, rVal, 
                        pMap, prcdVars, procSeq, globalVars, nonGlobalVars, 
                        allVarSeq, localVars, stack, A, res_, prcdr, ipr, proc, 
                        ip, lsseq, ilss, lstmt, whl, ls, ils, ilLast, ili, le, 
                        ile, fs, fi, ifi, ifLast, fe, ife, ife2, feSeq, 
                        feSeqLast, fw, ifw, fwLast, cr, icr, gt, sss, isss, ss, 
                        asg, ias, ifst, estmt, iee, wi, iw, vdcl, pvdcl, exp, 
                        ie, elseq, nxt_, ixs, res_E, lst, nxt_E, temp_, flseq, 
                        temp_I, ifsqi, lseq, nxt_Ex, xxtemp1, temp2_, temp3_, 
                        temp4, exlsq, callStmt, prcd, svoci, temp, res_S, 
                        rprcd, rpvi, rpctemp, res_R, vrs, addExpr, pvexpr, pvi, 
                        stk, test, primeVars, sub, expr, sst, primedVars, 
                        localSub_, xlssi, xltemp1, temp1, temp2, temp3, res_X, 
                        sstsq, xprimedVars, localSub_X, res, xlsssqi, lsstsq, 
                        localSub, defSub, nxt, lsstqi, lsstemp, disjs, defs, 
                        str >>

IA12 == /\ pc = "IA12"
        /\ pc' = Head(stack).pc
        /\ res_' = Head(stack).res_
        /\ ia' = Head(stack).ia
        /\ A' = Head(stack).A
        /\ stack' = Tail(stack)
        /\ UNCHANGED << i, j, gtemp1, gtemp2, gtemp3, gtemp4, result, rVal, 
                        pMap, prcdVars, procSeq, globalVars, nonGlobalVars, 
                        allVarSeq, localVars, prcdr, ipr, proc, ip, lsseq, 
                        ilss, lstmt, whl, ls, ils, ilLast, ili, le, ile, fs, 
                        fi, ifi, ifLast, fe, ife, ife2, feSeq, feSeqLast, fw, 
                        ifw, fwLast, cr, icr, gt, sss, isss, ss, asg, ias, 
                        ifst, estmt, iee, wi, iw, vdcl, pvdcl, exp, ie, elseq, 
                        nxt_, ixs, res_E, lst, nxt_E, temp_, flseq, temp_I, 
                        ifsqi, lseq, nxt_Ex, xxtemp1, temp2_, temp3_, temp4, 
                        exlsq, callStmt, prcd, svoci, temp, res_S, rprcd, rpvi, 
                        rpctemp, res_R, vrs, addExpr, pvexpr, pvi, stk, test, 
                        primeVars, sub, expr, sst, primedVars, localSub_, 
                        xlssi, xltemp1, temp1, temp2, temp3, res_X, sstsq, 
                        xprimedVars, localSub_X, res, xlsssqi, lsstsq, 
                        localSub, defSub, nxt, lsstqi, lsstemp, disjs, defs, 
                        str >>

IsAlgorithm == IA1 \/ IA2 \/ IA3 \/ IA4 \/ IA5 \/ IA6 \/ IA10 \/ IA11
                  \/ IA12

IPr1 == /\ pc = "IPr1"
        /\ Assert(DOMAIN prcdr = {"name", "params", "decls", "body"}, 
                  "Failure of assertion at line 131, column 17.")
        /\ Assert(IsSeq(prcdr.params), 
                  "Failure of assertion at line 132, column 17.")
        /\ ipr' = Len(prcdr.params)
        /\ pc' = "IPr2"
        /\ UNCHANGED << i, j, gtemp1, gtemp2, gtemp3, gtemp4, result, rVal, 
                        pMap, prcdVars, procSeq, globalVars, nonGlobalVars, 
                        allVarSeq, localVars, stack, A, res_, ia, prcdr, proc, 
                        ip, lsseq, ilss, lstmt, whl, ls, ils, ilLast, ili, le, 
                        ile, fs, fi, ifi, ifLast, fe, ife, ife2, feSeq, 
                        feSeqLast, fw, ifw, fwLast, cr, icr, gt, sss, isss, ss, 
                        asg, ias, ifst, estmt, iee, wi, iw, vdcl, pvdcl, exp, 
                        ie, elseq, nxt_, ixs, res_E, lst, nxt_E, temp_, flseq, 
                        temp_I, ifsqi, lseq, nxt_Ex, xxtemp1, temp2_, temp3_, 
                        temp4, exlsq, callStmt, prcd, svoci, temp, res_S, 
                        rprcd, rpvi, rpctemp, res_R, vrs, addExpr, pvexpr, pvi, 
                        stk, test, primeVars, sub, expr, sst, primedVars, 
                        localSub_, xlssi, xltemp1, temp1, temp2, temp3, res_X, 
                        sstsq, xprimedVars, localSub_X, res, xlsssqi, lsstsq, 
                        localSub, defSub, nxt, lsstqi, lsstemp, disjs, defs, 
                        str >>

IPr2 == /\ pc = "IPr2"
        /\ IF ipr > 0
              THEN /\ /\ pvdcl' = prcdr.params[ipr]
                      /\ stack' = << [ procedure |->  "IsPVarDecl",
                                       pc        |->  "IPr3",
                                       pvdcl     |->  pvdcl ] >>
                                   \o stack
                   /\ pc' = "IPV1"
                   /\ UNCHANGED ipr
              ELSE /\ Assert(IsSeq(prcdr.decls), 
                             "Failure of assertion at line 137, column 17.")
                   /\ ipr' = Len(prcdr.decls)
                   /\ pc' = "IPr4"
                   /\ UNCHANGED << stack, pvdcl >>
        /\ UNCHANGED << i, j, gtemp1, gtemp2, gtemp3, gtemp4, result, rVal, 
                        pMap, prcdVars, procSeq, globalVars, nonGlobalVars, 
                        allVarSeq, localVars, A, res_, ia, prcdr, proc, ip, 
                        lsseq, ilss, lstmt, whl, ls, ils, ilLast, ili, le, ile, 
                        fs, fi, ifi, ifLast, fe, ife, ife2, feSeq, feSeqLast, 
                        fw, ifw, fwLast, cr, icr, gt, sss, isss, ss, asg, ias, 
                        ifst, estmt, iee, wi, iw, vdcl, exp, ie, elseq, nxt_, 
                        ixs, res_E, lst, nxt_E, temp_, flseq, temp_I, ifsqi, 
                        lseq, nxt_Ex, xxtemp1, temp2_, temp3_, temp4, exlsq, 
                        callStmt, prcd, svoci, temp, res_S, rprcd, rpvi, 
                        rpctemp, res_R, vrs, addExpr, pvexpr, pvi, stk, test, 
                        primeVars, sub, expr, sst, primedVars, localSub_, 
                        xlssi, xltemp1, temp1, temp2, temp3, res_X, sstsq, 
                        xprimedVars, localSub_X, res, xlsssqi, lsstsq, 
                        localSub, defSub, nxt, lsstqi, lsstemp, disjs, defs, 
                        str >>

IPr3 == /\ pc = "IPr3"
        /\ ipr' = ipr-1
        /\ pc' = "IPr2"
        /\ UNCHANGED << i, j, gtemp1, gtemp2, gtemp3, gtemp4, result, rVal, 
                        pMap, prcdVars, procSeq, globalVars, nonGlobalVars, 
                        allVarSeq, localVars, stack, A, res_, ia, prcdr, proc, 
                        ip, lsseq, ilss, lstmt, whl, ls, ils, ilLast, ili, le, 
                        ile, fs, fi, ifi, ifLast, fe, ife, ife2, feSeq, 
                        feSeqLast, fw, ifw, fwLast, cr, icr, gt, sss, isss, ss, 
                        asg, ias, ifst, estmt, iee, wi, iw, vdcl, pvdcl, exp, 
                        ie, elseq, nxt_, ixs, res_E, lst, nxt_E, temp_, flseq, 
                        temp_I, ifsqi, lseq, nxt_Ex, xxtemp1, temp2_, temp3_, 
                        temp4, exlsq, callStmt, prcd, svoci, temp, res_S, 
                        rprcd, rpvi, rpctemp, res_R, vrs, addExpr, pvexpr, pvi, 
                        stk, test, primeVars, sub, expr, sst, primedVars, 
                        localSub_, xlssi, xltemp1, temp1, temp2, temp3, res_X, 
                        sstsq, xprimedVars, localSub_X, res, xlsssqi, lsstsq, 
                        localSub, defSub, nxt, lsstqi, lsstemp, disjs, defs, 
                        str >>

IPr4 == /\ pc = "IPr4"
        /\ IF ipr > 0
              THEN /\ /\ pvdcl' = prcdr.decls[ipr]
                      /\ stack' = << [ procedure |->  "IsPVarDecl",
                                       pc        |->  "IPr5",
                                       pvdcl     |->  pvdcl ] >>
                                   \o stack
                   /\ pc' = "IPV1"
                   /\ UNCHANGED ipr
              ELSE /\ Assert(IsSeq(prcdr.decls), 
                             "Failure of assertion at line 142, column 17.")
                   /\ ipr' = Len(prcdr.decls)
                   /\ Assert(Len(prcdr.body) > 0, 
                             "Failure of assertion at line 144, column 17.")
                   /\ pc' = "IPr6"
                   /\ UNCHANGED << stack, pvdcl >>
        /\ UNCHANGED << i, j, gtemp1, gtemp2, gtemp3, gtemp4, result, rVal, 
                        pMap, prcdVars, procSeq, globalVars, nonGlobalVars, 
                        allVarSeq, localVars, A, res_, ia, prcdr, proc, ip, 
                        lsseq, ilss, lstmt, whl, ls, ils, ilLast, ili, le, ile, 
                        fs, fi, ifi, ifLast, fe, ife, ife2, feSeq, feSeqLast, 
                        fw, ifw, fwLast, cr, icr, gt, sss, isss, ss, asg, ias, 
                        ifst, estmt, iee, wi, iw, vdcl, exp, ie, elseq, nxt_, 
                        ixs, res_E, lst, nxt_E, temp_, flseq, temp_I, ifsqi, 
                        lseq, nxt_Ex, xxtemp1, temp2_, temp3_, temp4, exlsq, 
                        callStmt, prcd, svoci, temp, res_S, rprcd, rpvi, 
                        rpctemp, res_R, vrs, addExpr, pvexpr, pvi, stk, test, 
                        primeVars, sub, expr, sst, primedVars, localSub_, 
                        xlssi, xltemp1, temp1, temp2, temp3, res_X, sstsq, 
                        xprimedVars, localSub_X, res, xlsssqi, lsstsq, 
                        localSub, defSub, nxt, lsstqi, lsstemp, disjs, defs, 
                        str >>

IPr5 == /\ pc = "IPr5"
        /\ ipr' = ipr-1
        /\ pc' = "IPr4"
        /\ UNCHANGED << i, j, gtemp1, gtemp2, gtemp3, gtemp4, result, rVal, 
                        pMap, prcdVars, procSeq, globalVars, nonGlobalVars, 
                        allVarSeq, localVars, stack, A, res_, ia, prcdr, proc, 
                        ip, lsseq, ilss, lstmt, whl, ls, ils, ilLast, ili, le, 
                        ile, fs, fi, ifi, ifLast, fe, ife, ife2, feSeq, 
                        feSeqLast, fw, ifw, fwLast, cr, icr, gt, sss, isss, ss, 
                        asg, ias, ifst, estmt, iee, wi, iw, vdcl, pvdcl, exp, 
                        ie, elseq, nxt_, ixs, res_E, lst, nxt_E, temp_, flseq, 
                        temp_I, ifsqi, lseq, nxt_Ex, xxtemp1, temp2_, temp3_, 
                        temp4, exlsq, callStmt, prcd, svoci, temp, res_S, 
                        rprcd, rpvi, rpctemp, res_R, vrs, addExpr, pvexpr, pvi, 
                        stk, test, primeVars, sub, expr, sst, primedVars, 
                        localSub_, xlssi, xltemp1, temp1, temp2, temp3, res_X, 
                        sstsq, xprimedVars, localSub_X, res, xlsssqi, lsstsq, 
                        localSub, defSub, nxt, lsstqi, lsstemp, disjs, defs, 
                        str >>

IPr6 == /\ pc = "IPr6"
        /\ /\ ipr' = Head(stack).ipr
           /\ lsseq' = prcdr.body
           /\ stack' = << [ procedure |->  "IsLabeledStmtSeq",
                            pc        |->  Head(stack).pc,
                            ilss      |->  ilss,
                            lsseq     |->  lsseq ] >>
                        \o Tail(stack)
        /\ ilss' = {}
        /\ pc' = "ILSS1"
        /\ UNCHANGED << i, j, gtemp1, gtemp2, gtemp3, gtemp4, result, rVal, 
                        pMap, prcdVars, procSeq, globalVars, nonGlobalVars, 
                        allVarSeq, localVars, A, res_, ia, prcdr, proc, ip, 
                        lstmt, whl, ls, ils, ilLast, ili, le, ile, fs, fi, ifi, 
                        ifLast, fe, ife, ife2, feSeq, feSeqLast, fw, ifw, 
                        fwLast, cr, icr, gt, sss, isss, ss, asg, ias, ifst, 
                        estmt, iee, wi, iw, vdcl, pvdcl, exp, ie, elseq, nxt_, 
                        ixs, res_E, lst, nxt_E, temp_, flseq, temp_I, ifsqi, 
                        lseq, nxt_Ex, xxtemp1, temp2_, temp3_, temp4, exlsq, 
                        callStmt, prcd, svoci, temp, res_S, rprcd, rpvi, 
                        rpctemp, res_R, vrs, addExpr, pvexpr, pvi, stk, test, 
                        primeVars, sub, expr, sst, primedVars, localSub_, 
                        xlssi, xltemp1, temp1, temp2, temp3, res_X, sstsq, 
                        xprimedVars, localSub_X, res, xlsssqi, lsstsq, 
                        localSub, defSub, nxt, lsstqi, lsstemp, disjs, defs, 
                        str >>

IsProcedure == IPr1 \/ IPr2 \/ IPr3 \/ IPr4 \/ IPr5 \/ IPr6

IP1 == /\ pc = "IP1"
       /\ Assert(DOMAIN proc =
                         {"name", "eqOrIn", "id", "decls", "body"}, 
                 "Failure of assertion at line 158, column 16.")
       /\ Assert(proc.name \in STRING, 
                 "Failure of assertion at line 160, column 16.")
       /\ Assert(proc.eqOrIn \in {"=", "\\in"}, 
                 "Failure of assertion at line 161, column 16.")
       /\ /\ exp' = proc.id
          /\ stack' = << [ procedure |->  "IsExpr",
                           pc        |->  "IP2",
                           ie        |->  ie,
                           exp       |->  exp ] >>
                       \o stack
       /\ ie' = {}
       /\ pc' = "IE1"
       /\ UNCHANGED << i, j, gtemp1, gtemp2, gtemp3, gtemp4, result, rVal, 
                       pMap, prcdVars, procSeq, globalVars, nonGlobalVars, 
                       allVarSeq, localVars, A, res_, ia, prcdr, ipr, proc, ip, 
                       lsseq, ilss, lstmt, whl, ls, ils, ilLast, ili, le, ile, 
                       fs, fi, ifi, ifLast, fe, ife, ife2, feSeq, feSeqLast, 
                       fw, ifw, fwLast, cr, icr, gt, sss, isss, ss, asg, ias, 
                       ifst, estmt, iee, wi, iw, vdcl, pvdcl, elseq, nxt_, ixs, 
                       res_E, lst, nxt_E, temp_, flseq, temp_I, ifsqi, lseq, 
                       nxt_Ex, xxtemp1, temp2_, temp3_, temp4, exlsq, callStmt, 
                       prcd, svoci, temp, res_S, rprcd, rpvi, rpctemp, res_R, 
                       vrs, addExpr, pvexpr, pvi, stk, test, primeVars, sub, 
                       expr, sst, primedVars, localSub_, xlssi, xltemp1, temp1, 
                       temp2, temp3, res_X, sstsq, xprimedVars, localSub_X, 
                       res, xlsssqi, lsstsq, localSub, defSub, nxt, lsstqi, 
                       lsstemp, disjs, defs, str >>

IP2 == /\ pc = "IP2"
       /\ Assert(IsSeq(proc.decls), 
                 "Failure of assertion at line 163, column 16.")
       /\ ip' = Len(proc.decls)
       /\ pc' = "IP3"
       /\ UNCHANGED << i, j, gtemp1, gtemp2, gtemp3, gtemp4, result, rVal, 
                       pMap, prcdVars, procSeq, globalVars, nonGlobalVars, 
                       allVarSeq, localVars, stack, A, res_, ia, prcdr, ipr, 
                       proc, lsseq, ilss, lstmt, whl, ls, ils, ilLast, ili, le, 
                       ile, fs, fi, ifi, ifLast, fe, ife, ife2, feSeq, 
                       feSeqLast, fw, ifw, fwLast, cr, icr, gt, sss, isss, ss, 
                       asg, ias, ifst, estmt, iee, wi, iw, vdcl, pvdcl, exp, 
                       ie, elseq, nxt_, ixs, res_E, lst, nxt_E, temp_, flseq, 
                       temp_I, ifsqi, lseq, nxt_Ex, xxtemp1, temp2_, temp3_, 
                       temp4, exlsq, callStmt, prcd, svoci, temp, res_S, rprcd, 
                       rpvi, rpctemp, res_R, vrs, addExpr, pvexpr, pvi, stk, 
                       test, primeVars, sub, expr, sst, primedVars, localSub_, 
                       xlssi, xltemp1, temp1, temp2, temp3, res_X, sstsq, 
                       xprimedVars, localSub_X, res, xlsssqi, lsstsq, localSub, 
                       defSub, nxt, lsstqi, lsstemp, disjs, defs, str >>

IP3 == /\ pc = "IP3"
       /\ IF ip > 0
             THEN /\ /\ stack' = << [ procedure |->  "IsVarDecl",
                                      pc        |->  "IP4",
                                      vdcl      |->  vdcl ] >>
                                  \o stack
                     /\ vdcl' = proc.decls[ip]
                  /\ pc' = "IV1"
                  /\ UNCHANGED << ip, lsseq, ilss >>
             ELSE /\ /\ ip' = Head(stack).ip
                     /\ lsseq' = proc.body
                     /\ stack' = << [ procedure |->  "IsLabeledStmtSeq",
                                      pc        |->  Head(stack).pc,
                                      ilss      |->  ilss,
                                      lsseq     |->  lsseq ] >>
                                  \o Tail(stack)
                  /\ ilss' = {}
                  /\ pc' = "ILSS1"
                  /\ UNCHANGED vdcl
       /\ UNCHANGED << i, j, gtemp1, gtemp2, gtemp3, gtemp4, result, rVal, 
                       pMap, prcdVars, procSeq, globalVars, nonGlobalVars, 
                       allVarSeq, localVars, A, res_, ia, prcdr, ipr, proc, 
                       lstmt, whl, ls, ils, ilLast, ili, le, ile, fs, fi, ifi, 
                       ifLast, fe, ife, ife2, feSeq, feSeqLast, fw, ifw, 
                       fwLast, cr, icr, gt, sss, isss, ss, asg, ias, ifst, 
                       estmt, iee, wi, iw, pvdcl, exp, ie, elseq, nxt_, ixs, 
                       res_E, lst, nxt_E, temp_, flseq, temp_I, ifsqi, lseq, 
                       nxt_Ex, xxtemp1, temp2_, temp3_, temp4, exlsq, callStmt, 
                       prcd, svoci, temp, res_S, rprcd, rpvi, rpctemp, res_R, 
                       vrs, addExpr, pvexpr, pvi, stk, test, primeVars, sub, 
                       expr, sst, primedVars, localSub_, xlssi, xltemp1, temp1, 
                       temp2, temp3, res_X, sstsq, xprimedVars, localSub_X, 
                       res, xlsssqi, lsstsq, localSub, defSub, nxt, lsstqi, 
                       lsstemp, disjs, defs, str >>

IP4 == /\ pc = "IP4"
       /\ ip' = ip-1
       /\ pc' = "IP3"
       /\ UNCHANGED << i, j, gtemp1, gtemp2, gtemp3, gtemp4, result, rVal, 
                       pMap, prcdVars, procSeq, globalVars, nonGlobalVars, 
                       allVarSeq, localVars, stack, A, res_, ia, prcdr, ipr, 
                       proc, lsseq, ilss, lstmt, whl, ls, ils, ilLast, ili, le, 
                       ile, fs, fi, ifi, ifLast, fe, ife, ife2, feSeq, 
                       feSeqLast, fw, ifw, fwLast, cr, icr, gt, sss, isss, ss, 
                       asg, ias, ifst, estmt, iee, wi, iw, vdcl, pvdcl, exp, 
                       ie, elseq, nxt_, ixs, res_E, lst, nxt_E, temp_, flseq, 
                       temp_I, ifsqi, lseq, nxt_Ex, xxtemp1, temp2_, temp3_, 
                       temp4, exlsq, callStmt, prcd, svoci, temp, res_S, rprcd, 
                       rpvi, rpctemp, res_R, vrs, addExpr, pvexpr, pvi, stk, 
                       test, primeVars, sub, expr, sst, primedVars, localSub_, 
                       xlssi, xltemp1, temp1, temp2, temp3, res_X, sstsq, 
                       xprimedVars, localSub_X, res, xlsssqi, lsstsq, localSub, 
                       defSub, nxt, lsstqi, lsstemp, disjs, defs, str >>

IsProcess == IP1 \/ IP2 \/ IP3 \/ IP4

ILSS1 == /\ pc = "ILSS1"
         /\ Assert(IsSeq(lsseq), 
                   "Failure of assertion at line 177, column 18.")
         /\ ilss' = Len(lsseq)
         /\ pc' = "ILSS2"
         /\ UNCHANGED << i, j, gtemp1, gtemp2, gtemp3, gtemp4, result, rVal, 
                         pMap, prcdVars, procSeq, globalVars, nonGlobalVars, 
                         allVarSeq, localVars, stack, A, res_, ia, prcdr, ipr, 
                         proc, ip, lsseq, lstmt, whl, ls, ils, ilLast, ili, le, 
                         ile, fs, fi, ifi, ifLast, fe, ife, ife2, feSeq, 
                         feSeqLast, fw, ifw, fwLast, cr, icr, gt, sss, isss, 
                         ss, asg, ias, ifst, estmt, iee, wi, iw, vdcl, pvdcl, 
                         exp, ie, elseq, nxt_, ixs, res_E, lst, nxt_E, temp_, 
                         flseq, temp_I, ifsqi, lseq, nxt_Ex, xxtemp1, temp2_, 
                         temp3_, temp4, exlsq, callStmt, prcd, svoci, temp, 
                         res_S, rprcd, rpvi, rpctemp, res_R, vrs, addExpr, 
                         pvexpr, pvi, stk, test, primeVars, sub, expr, sst, 
                         primedVars, localSub_, xlssi, xltemp1, temp1, temp2, 
                         temp3, res_X, sstsq, xprimedVars, localSub_X, res, 
                         xlsssqi, lsstsq, localSub, defSub, nxt, lsstqi, 
                         lsstemp, disjs, defs, str >>

ILSS2 == /\ pc = "ILSS2"
         /\ IF ilss > 0
               THEN /\ /\ lstmt' = lsseq[ilss]
                       /\ stack' = << [ procedure |->  "IsLabeledStmt",
                                        pc        |->  "ILSS3",
                                        lstmt     |->  lstmt ] >>
                                    \o stack
                    /\ pc' = "IL1"
                    /\ UNCHANGED << lsseq, ilss >>
               ELSE /\ pc' = Head(stack).pc
                    /\ ilss' = Head(stack).ilss
                    /\ lsseq' = Head(stack).lsseq
                    /\ stack' = Tail(stack)
                    /\ UNCHANGED lstmt
         /\ UNCHANGED << i, j, gtemp1, gtemp2, gtemp3, gtemp4, result, rVal, 
                         pMap, prcdVars, procSeq, globalVars, nonGlobalVars, 
                         allVarSeq, localVars, A, res_, ia, prcdr, ipr, proc, 
                         ip, whl, ls, ils, ilLast, ili, le, ile, fs, fi, ifi, 
                         ifLast, fe, ife, ife2, feSeq, feSeqLast, fw, ifw, 
                         fwLast, cr, icr, gt, sss, isss, ss, asg, ias, ifst, 
                         estmt, iee, wi, iw, vdcl, pvdcl, exp, ie, elseq, nxt_, 
                         ixs, res_E, lst, nxt_E, temp_, flseq, temp_I, ifsqi, 
                         lseq, nxt_Ex, xxtemp1, temp2_, temp3_, temp4, exlsq, 
                         callStmt, prcd, svoci, temp, res_S, rprcd, rpvi, 
                         rpctemp, res_R, vrs, addExpr, pvexpr, pvi, stk, test, 
                         primeVars, sub, expr, sst, primedVars, localSub_, 
                         xlssi, xltemp1, temp1, temp2, temp3, res_X, sstsq, 
                         xprimedVars, localSub_X, res, xlsssqi, lsstsq, 
                         localSub, defSub, nxt, lsstqi, lsstemp, disjs, defs, 
                         str >>

ILSS3 == /\ pc = "ILSS3"
         /\ ilss' = ilss-1
         /\ pc' = "ILSS2"
         /\ UNCHANGED << i, j, gtemp1, gtemp2, gtemp3, gtemp4, result, rVal, 
                         pMap, prcdVars, procSeq, globalVars, nonGlobalVars, 
                         allVarSeq, localVars, stack, A, res_, ia, prcdr, ipr, 
                         proc, ip, lsseq, lstmt, whl, ls, ils, ilLast, ili, le, 
                         ile, fs, fi, ifi, ifLast, fe, ife, ife2, feSeq, 
                         feSeqLast, fw, ifw, fwLast, cr, icr, gt, sss, isss, 
                         ss, asg, ias, ifst, estmt, iee, wi, iw, vdcl, pvdcl, 
                         exp, ie, elseq, nxt_, ixs, res_E, lst, nxt_E, temp_, 
                         flseq, temp_I, ifsqi, lseq, nxt_Ex, xxtemp1, temp2_, 
                         temp3_, temp4, exlsq, callStmt, prcd, svoci, temp, 
                         res_S, rprcd, rpvi, rpctemp, res_R, vrs, addExpr, 
                         pvexpr, pvi, stk, test, primeVars, sub, expr, sst, 
                         primedVars, localSub_, xlssi, xltemp1, temp1, temp2, 
                         temp3, res_X, sstsq, xprimedVars, localSub_X, res, 
                         xlsssqi, lsstsq, localSub, defSub, nxt, lsstqi, 
                         lsstemp, disjs, defs, str >>

IsLabeledStmtSeq == ILSS1 \/ ILSS2 \/ ILSS3

IL1 == /\ pc = "IL1"
       /\ Assert(DOMAIN lstmt = {"label", "stmts"}, 
                 "Failure of assertion at line 193, column 16.")
       /\ Assert(lstmt.label \in STRING, 
                 "Failure of assertion at line 194, column 16.")
       /\ IF lstmt.stmts[1].type = "while"
             THEN /\ /\ stack' = << [ procedure |->  "IsWhile",
                                      pc        |->  "IL2",
                                      whl       |->  whl ] >>
                                  \o stack
                     /\ whl' = lstmt.stmts[1]
                  /\ pc' = "IW1"
                  /\ UNCHANGED << ls, ils, ilLast >>
             ELSE /\ /\ ls' = lstmt.stmts
                     /\ stack' = << [ procedure |->  "IsLabelSeq",
                                      pc        |->  "IL3",
                                      ils       |->  ils,
                                      ilLast    |->  ilLast,
                                      ls        |->  ls ] >>
                                  \o stack
                  /\ ils' = {}
                  /\ ilLast' = {}
                  /\ pc' = "ILS1"
                  /\ UNCHANGED whl
       /\ UNCHANGED << i, j, gtemp1, gtemp2, gtemp3, gtemp4, result, rVal, 
                       pMap, prcdVars, procSeq, globalVars, nonGlobalVars, 
                       allVarSeq, localVars, A, res_, ia, prcdr, ipr, proc, ip, 
                       lsseq, ilss, lstmt, ili, le, ile, fs, fi, ifi, ifLast, 
                       fe, ife, ife2, feSeq, feSeqLast, fw, ifw, fwLast, cr, 
                       icr, gt, sss, isss, ss, asg, ias, ifst, estmt, iee, wi, 
                       iw, vdcl, pvdcl, exp, ie, elseq, nxt_, ixs, res_E, lst, 
                       nxt_E, temp_, flseq, temp_I, ifsqi, lseq, nxt_Ex, 
                       xxtemp1, temp2_, temp3_, temp4, exlsq, callStmt, prcd, 
                       svoci, temp, res_S, rprcd, rpvi, rpctemp, res_R, vrs, 
                       addExpr, pvexpr, pvi, stk, test, primeVars, sub, expr, 
                       sst, primedVars, localSub_, xlssi, xltemp1, temp1, 
                       temp2, temp3, res_X, sstsq, xprimedVars, localSub_X, 
                       res, xlsssqi, lsstsq, localSub, defSub, nxt, lsstqi, 
                       lsstemp, disjs, defs, str >>

IL2 == /\ pc = "IL2"
       /\ /\ ls' = Tail(lstmt.stmts)
          /\ stack' = << [ procedure |->  "IsLabelSeq",
                           pc        |->  "IL3",
                           ils       |->  ils,
                           ilLast    |->  ilLast,
                           ls        |->  ls ] >>
                       \o stack
       /\ ils' = {}
       /\ ilLast' = {}
       /\ pc' = "ILS1"
       /\ UNCHANGED << i, j, gtemp1, gtemp2, gtemp3, gtemp4, result, rVal, 
                       pMap, prcdVars, procSeq, globalVars, nonGlobalVars, 
                       allVarSeq, localVars, A, res_, ia, prcdr, ipr, proc, ip, 
                       lsseq, ilss, lstmt, whl, ili, le, ile, fs, fi, ifi, 
                       ifLast, fe, ife, ife2, feSeq, feSeqLast, fw, ifw, 
                       fwLast, cr, icr, gt, sss, isss, ss, asg, ias, ifst, 
                       estmt, iee, wi, iw, vdcl, pvdcl, exp, ie, elseq, nxt_, 
                       ixs, res_E, lst, nxt_E, temp_, flseq, temp_I, ifsqi, 
                       lseq, nxt_Ex, xxtemp1, temp2_, temp3_, temp4, exlsq, 
                       callStmt, prcd, svoci, temp, res_S, rprcd, rpvi, 
                       rpctemp, res_R, vrs, addExpr, pvexpr, pvi, stk, test, 
                       primeVars, sub, expr, sst, primedVars, localSub_, xlssi, 
                       xltemp1, temp1, temp2, temp3, res_X, sstsq, xprimedVars, 
                       localSub_X, res, xlsssqi, lsstsq, localSub, defSub, nxt, 
                       lsstqi, lsstemp, disjs, defs, str >>

IL3 == /\ pc = "IL3"
       /\ pc' = Head(stack).pc
       /\ lstmt' = Head(stack).lstmt
       /\ stack' = Tail(stack)
       /\ UNCHANGED << i, j, gtemp1, gtemp2, gtemp3, gtemp4, result, rVal, 
                       pMap, prcdVars, procSeq, globalVars, nonGlobalVars, 
                       allVarSeq, localVars, A, res_, ia, prcdr, ipr, proc, ip, 
                       lsseq, ilss, whl, ls, ils, ilLast, ili, le, ile, fs, fi, 
                       ifi, ifLast, fe, ife, ife2, feSeq, feSeqLast, fw, ifw, 
                       fwLast, cr, icr, gt, sss, isss, ss, asg, ias, ifst, 
                       estmt, iee, wi, iw, vdcl, pvdcl, exp, ie, elseq, nxt_, 
                       ixs, res_E, lst, nxt_E, temp_, flseq, temp_I, ifsqi, 
                       lseq, nxt_Ex, xxtemp1, temp2_, temp3_, temp4, exlsq, 
                       callStmt, prcd, svoci, temp, res_S, rprcd, rpvi, 
                       rpctemp, res_R, vrs, addExpr, pvexpr, pvi, stk, test, 
                       primeVars, sub, expr, sst, primedVars, localSub_, xlssi, 
                       xltemp1, temp1, temp2, temp3, res_X, sstsq, xprimedVars, 
                       localSub_X, res, xlsssqi, lsstsq, localSub, defSub, nxt, 
                       lsstqi, lsstemp, disjs, defs, str >>

IsLabeledStmt == IL1 \/ IL2 \/ IL3

IW1 == /\ pc = "IW1"
       /\ Assert(DOMAIN whl = {"type", "test", "unlabDo", "labDo"}, 
                 "Failure of assertion at line 210, column 16.")
       /\ Assert(whl.type = "while", 
                 "Failure of assertion at line 211, column 16.")
       /\ /\ exp' = whl.test
          /\ stack' = << [ procedure |->  "IsExpr",
                           pc        |->  "IW2",
                           ie        |->  ie,
                           exp       |->  exp ] >>
                       \o stack
       /\ ie' = {}
       /\ pc' = "IE1"
       /\ UNCHANGED << i, j, gtemp1, gtemp2, gtemp3, gtemp4, result, rVal, 
                       pMap, prcdVars, procSeq, globalVars, nonGlobalVars, 
                       allVarSeq, localVars, A, res_, ia, prcdr, ipr, proc, ip, 
                       lsseq, ilss, lstmt, whl, ls, ils, ilLast, ili, le, ile, 
                       fs, fi, ifi, ifLast, fe, ife, ife2, feSeq, feSeqLast, 
                       fw, ifw, fwLast, cr, icr, gt, sss, isss, ss, asg, ias, 
                       ifst, estmt, iee, wi, iw, vdcl, pvdcl, elseq, nxt_, ixs, 
                       res_E, lst, nxt_E, temp_, flseq, temp_I, ifsqi, lseq, 
                       nxt_Ex, xxtemp1, temp2_, temp3_, temp4, exlsq, callStmt, 
                       prcd, svoci, temp, res_S, rprcd, rpvi, rpctemp, res_R, 
                       vrs, addExpr, pvexpr, pvi, stk, test, primeVars, sub, 
                       expr, sst, primedVars, localSub_, xlssi, xltemp1, temp1, 
                       temp2, temp3, res_X, sstsq, xprimedVars, localSub_X, 
                       res, xlsssqi, lsstsq, localSub, defSub, nxt, lsstqi, 
                       lsstemp, disjs, defs, str >>

IW2 == /\ pc = "IW2"
       /\ /\ ls' = whl.unlabDo
          /\ stack' = << [ procedure |->  "IsLabelSeq",
                           pc        |->  "IW3",
                           ils       |->  ils,
                           ilLast    |->  ilLast,
                           ls        |->  ls ] >>
                       \o stack
       /\ ils' = {}
       /\ ilLast' = {}
       /\ pc' = "ILS1"
       /\ UNCHANGED << i, j, gtemp1, gtemp2, gtemp3, gtemp4, result, rVal, 
                       pMap, prcdVars, procSeq, globalVars, nonGlobalVars, 
                       allVarSeq, localVars, A, res_, ia, prcdr, ipr, proc, ip, 
                       lsseq, ilss, lstmt, whl, ili, le, ile, fs, fi, ifi, 
                       ifLast, fe, ife, ife2, feSeq, feSeqLast, fw, ifw, 
                       fwLast, cr, icr, gt, sss, isss, ss, asg, ias, ifst, 
                       estmt, iee, wi, iw, vdcl, pvdcl, exp, ie, elseq, nxt_, 
                       ixs, res_E, lst, nxt_E, temp_, flseq, temp_I, ifsqi, 
                       lseq, nxt_Ex, xxtemp1, temp2_, temp3_, temp4, exlsq, 
                       callStmt, prcd, svoci, temp, res_S, rprcd, rpvi, 
                       rpctemp, res_R, vrs, addExpr, pvexpr, pvi, stk, test, 
                       primeVars, sub, expr, sst, primedVars, localSub_, xlssi, 
                       xltemp1, temp1, temp2, temp3, res_X, sstsq, xprimedVars, 
                       localSub_X, res, xlsssqi, lsstsq, localSub, defSub, nxt, 
                       lsstqi, lsstemp, disjs, defs, str >>

IW3 == /\ pc = "IW3"
       /\ IF whl.labDo # << >>
             THEN /\ /\ lsseq' = whl.labDo
                     /\ stack' = << [ procedure |->  "IsLabeledStmtSeq",
                                      pc        |->  "IW4",
                                      ilss      |->  ilss,
                                      lsseq     |->  lsseq ] >>
                                  \o stack
                  /\ ilss' = {}
                  /\ pc' = "ILSS1"
             ELSE /\ pc' = "IW4"
                  /\ UNCHANGED << stack, lsseq, ilss >>
       /\ UNCHANGED << i, j, gtemp1, gtemp2, gtemp3, gtemp4, result, rVal, 
                       pMap, prcdVars, procSeq, globalVars, nonGlobalVars, 
                       allVarSeq, localVars, A, res_, ia, prcdr, ipr, proc, ip, 
                       lstmt, whl, ls, ils, ilLast, ili, le, ile, fs, fi, ifi, 
                       ifLast, fe, ife, ife2, feSeq, feSeqLast, fw, ifw, 
                       fwLast, cr, icr, gt, sss, isss, ss, asg, ias, ifst, 
                       estmt, iee, wi, iw, vdcl, pvdcl, exp, ie, elseq, nxt_, 
                       ixs, res_E, lst, nxt_E, temp_, flseq, temp_I, ifsqi, 
                       lseq, nxt_Ex, xxtemp1, temp2_, temp3_, temp4, exlsq, 
                       callStmt, prcd, svoci, temp, res_S, rprcd, rpvi, 
                       rpctemp, res_R, vrs, addExpr, pvexpr, pvi, stk, test, 
                       primeVars, sub, expr, sst, primedVars, localSub_, xlssi, 
                       xltemp1, temp1, temp2, temp3, res_X, sstsq, xprimedVars, 
                       localSub_X, res, xlsssqi, lsstsq, localSub, defSub, nxt, 
                       lsstqi, lsstemp, disjs, defs, str >>

IW4 == /\ pc = "IW4"
       /\ pc' = Head(stack).pc
       /\ whl' = Head(stack).whl
       /\ stack' = Tail(stack)
       /\ UNCHANGED << i, j, gtemp1, gtemp2, gtemp3, gtemp4, result, rVal, 
                       pMap, prcdVars, procSeq, globalVars, nonGlobalVars, 
                       allVarSeq, localVars, A, res_, ia, prcdr, ipr, proc, ip, 
                       lsseq, ilss, lstmt, ls, ils, ilLast, ili, le, ile, fs, 
                       fi, ifi, ifLast, fe, ife, ife2, feSeq, feSeqLast, fw, 
                       ifw, fwLast, cr, icr, gt, sss, isss, ss, asg, ias, ifst, 
                       estmt, iee, wi, iw, vdcl, pvdcl, exp, ie, elseq, nxt_, 
                       ixs, res_E, lst, nxt_E, temp_, flseq, temp_I, ifsqi, 
                       lseq, nxt_Ex, xxtemp1, temp2_, temp3_, temp4, exlsq, 
                       callStmt, prcd, svoci, temp, res_S, rprcd, rpvi, 
                       rpctemp, res_R, vrs, addExpr, pvexpr, pvi, stk, test, 
                       primeVars, sub, expr, sst, primedVars, localSub_, xlssi, 
                       xltemp1, temp1, temp2, temp3, res_X, sstsq, xprimedVars, 
                       localSub_X, res, xlsssqi, lsstsq, localSub, defSub, nxt, 
                       lsstqi, lsstemp, disjs, defs, str >>

IsWhile == IW1 \/ IW2 \/ IW3 \/ IW4

ILS1 == /\ pc = "ILS1"
        /\ Assert(IsSeq(ls), "Failure of assertion at line 228, column 17.")
        /\ ils' = Len(ls) - 1
        /\ pc' = "ILS2"
        /\ UNCHANGED << i, j, gtemp1, gtemp2, gtemp3, gtemp4, result, rVal, 
                        pMap, prcdVars, procSeq, globalVars, nonGlobalVars, 
                        allVarSeq, localVars, stack, A, res_, ia, prcdr, ipr, 
                        proc, ip, lsseq, ilss, lstmt, whl, ls, ilLast, ili, le, 
                        ile, fs, fi, ifi, ifLast, fe, ife, ife2, feSeq, 
                        feSeqLast, fw, ifw, fwLast, cr, icr, gt, sss, isss, ss, 
                        asg, ias, ifst, estmt, iee, wi, iw, vdcl, pvdcl, exp, 
                        ie, elseq, nxt_, ixs, res_E, lst, nxt_E, temp_, flseq, 
                        temp_I, ifsqi, lseq, nxt_Ex, xxtemp1, temp2_, temp3_, 
                        temp4, exlsq, callStmt, prcd, svoci, temp, res_S, 
                        rprcd, rpvi, rpctemp, res_R, vrs, addExpr, pvexpr, pvi, 
                        stk, test, primeVars, sub, expr, sst, primedVars, 
                        localSub_, xlssi, xltemp1, temp1, temp2, temp3, res_X, 
                        sstsq, xprimedVars, localSub_X, res, xlsssqi, lsstsq, 
                        localSub, defSub, nxt, lsstqi, lsstemp, disjs, defs, 
                        str >>

ILS2 == /\ pc = "ILS2"
        /\ IF ils > 0
              THEN /\ /\ ss' = ls[ils]
                      /\ stack' = << [ procedure |->  "IsSimpleStmt",
                                       pc        |->  "ILS3",
                                       ss        |->  ss ] >>
                                   \o stack
                   /\ pc' = "ISS1"
              ELSE /\ pc' = "ILS4"
                   /\ UNCHANGED << stack, ss >>
        /\ UNCHANGED << i, j, gtemp1, gtemp2, gtemp3, gtemp4, result, rVal, 
                        pMap, prcdVars, procSeq, globalVars, nonGlobalVars, 
                        allVarSeq, localVars, A, res_, ia, prcdr, ipr, proc, 
                        ip, lsseq, ilss, lstmt, whl, ls, ils, ilLast, ili, le, 
                        ile, fs, fi, ifi, ifLast, fe, ife, ife2, feSeq, 
                        feSeqLast, fw, ifw, fwLast, cr, icr, gt, sss, isss, 
                        asg, ias, ifst, estmt, iee, wi, iw, vdcl, pvdcl, exp, 
                        ie, elseq, nxt_, ixs, res_E, lst, nxt_E, temp_, flseq, 
                        temp_I, ifsqi, lseq, nxt_Ex, xxtemp1, temp2_, temp3_, 
                        temp4, exlsq, callStmt, prcd, svoci, temp, res_S, 
                        rprcd, rpvi, rpctemp, res_R, vrs, addExpr, pvexpr, pvi, 
                        stk, test, primeVars, sub, expr, sst, primedVars, 
                        localSub_, xlssi, xltemp1, temp1, temp2, temp3, res_X, 
                        sstsq, xprimedVars, localSub_X, res, xlsssqi, lsstsq, 
                        localSub, defSub, nxt, lsstqi, lsstemp, disjs, defs, 
                        str >>

ILS3 == /\ pc = "ILS3"
        /\ ils' = ils - 1
        /\ pc' = "ILS2"
        /\ UNCHANGED << i, j, gtemp1, gtemp2, gtemp3, gtemp4, result, rVal, 
                        pMap, prcdVars, procSeq, globalVars, nonGlobalVars, 
                        allVarSeq, localVars, stack, A, res_, ia, prcdr, ipr, 
                        proc, ip, lsseq, ilss, lstmt, whl, ls, ilLast, ili, le, 
                        ile, fs, fi, ifi, ifLast, fe, ife, ife2, feSeq, 
                        feSeqLast, fw, ifw, fwLast, cr, icr, gt, sss, isss, ss, 
                        asg, ias, ifst, estmt, iee, wi, iw, vdcl, pvdcl, exp, 
                        ie, elseq, nxt_, ixs, res_E, lst, nxt_E, temp_, flseq, 
                        temp_I, ifsqi, lseq, nxt_Ex, xxtemp1, temp2_, temp3_, 
                        temp4, exlsq, callStmt, prcd, svoci, temp, res_S, 
                        rprcd, rpvi, rpctemp, res_R, vrs, addExpr, pvexpr, pvi, 
                        stk, test, primeVars, sub, expr, sst, primedVars, 
                        localSub_, xlssi, xltemp1, temp1, temp2, temp3, res_X, 
                        sstsq, xprimedVars, localSub_X, res, xlsssqi, lsstsq, 
                        localSub, defSub, nxt, lsstqi, lsstemp, disjs, defs, 
                        str >>

ILS4 == /\ pc = "ILS4"
        /\ IF ls = << >>
              THEN /\ pc' = Head(stack).pc
                   /\ ils' = Head(stack).ils
                   /\ ilLast' = Head(stack).ilLast
                   /\ ls' = Head(stack).ls
                   /\ stack' = Tail(stack)
              ELSE /\ pc' = "ILS5"
                   /\ UNCHANGED << stack, ls, ils, ilLast >>
        /\ UNCHANGED << i, j, gtemp1, gtemp2, gtemp3, gtemp4, result, rVal, 
                        pMap, prcdVars, procSeq, globalVars, nonGlobalVars, 
                        allVarSeq, localVars, A, res_, ia, prcdr, ipr, proc, 
                        ip, lsseq, ilss, lstmt, whl, ili, le, ile, fs, fi, ifi, 
                        ifLast, fe, ife, ife2, feSeq, feSeqLast, fw, ifw, 
                        fwLast, cr, icr, gt, sss, isss, ss, asg, ias, ifst, 
                        estmt, iee, wi, iw, vdcl, pvdcl, exp, ie, elseq, nxt_, 
                        ixs, res_E, lst, nxt_E, temp_, flseq, temp_I, ifsqi, 
                        lseq, nxt_Ex, xxtemp1, temp2_, temp3_, temp4, exlsq, 
                        callStmt, prcd, svoci, temp, res_S, rprcd, rpvi, 
                        rpctemp, res_R, vrs, addExpr, pvexpr, pvi, stk, test, 
                        primeVars, sub, expr, sst, primedVars, localSub_, 
                        xlssi, xltemp1, temp1, temp2, temp3, res_X, sstsq, 
                        xprimedVars, localSub_X, res, xlsssqi, lsstsq, 
                        localSub, defSub, nxt, lsstqi, lsstemp, disjs, defs, 
                        str >>

ILS5 == /\ pc = "ILS5"
        /\ ilLast' = ls[Len(ls)]
        /\ IF ilLast'.type = "labelIf"
              THEN /\ /\ ili' = ilLast'
                      /\ stack' = << [ procedure |->  "IsLabelIf",
                                       pc        |->  "ILS6",
                                       ili       |->  ili ] >>
                                   \o stack
                   /\ pc' = "ILI1"
                   /\ UNCHANGED << le, ile, fs, ss >>
              ELSE /\ IF ilLast'.type = "labelEither"
                         THEN /\ /\ le' = ilLast'
                                 /\ stack' = << [ procedure |->  "IsLabelEither",
                                                  pc        |->  "ILS6",
                                                  ile       |->  ile,
                                                  le        |->  le ] >>
                                              \o stack
                              /\ ile' = {}
                              /\ pc' = "ILE1"
                              /\ UNCHANGED << fs, ss >>
                         ELSE /\ IF FinalStmtType(ilLast')
                                    THEN /\ /\ fs' = ilLast'
                                            /\ stack' = << [ procedure |->  "IsFinalStmt",
                                                             pc        |->  "ILS6",
                                                             fs        |->  fs ] >>
                                                         \o stack
                                         /\ pc' = "IFS1_"
                                         /\ UNCHANGED ss
                                    ELSE /\ /\ ss' = ilLast'
                                            /\ stack' = << [ procedure |->  "IsSimpleStmt",
                                                             pc        |->  "ILS6",
                                                             ss        |->  ss ] >>
                                                         \o stack
                                         /\ pc' = "ISS1"
                                         /\ UNCHANGED fs
                              /\ UNCHANGED << le, ile >>
                   /\ UNCHANGED ili
        /\ UNCHANGED << i, j, gtemp1, gtemp2, gtemp3, gtemp4, result, rVal, 
                        pMap, prcdVars, procSeq, globalVars, nonGlobalVars, 
                        allVarSeq, localVars, A, res_, ia, prcdr, ipr, proc, 
                        ip, lsseq, ilss, lstmt, whl, ls, ils, fi, ifi, ifLast, 
                        fe, ife, ife2, feSeq, feSeqLast, fw, ifw, fwLast, cr, 
                        icr, gt, sss, isss, asg, ias, ifst, estmt, iee, wi, iw, 
                        vdcl, pvdcl, exp, ie, elseq, nxt_, ixs, res_E, lst, 
                        nxt_E, temp_, flseq, temp_I, ifsqi, lseq, nxt_Ex, 
                        xxtemp1, temp2_, temp3_, temp4, exlsq, callStmt, prcd, 
                        svoci, temp, res_S, rprcd, rpvi, rpctemp, res_R, vrs, 
                        addExpr, pvexpr, pvi, stk, test, primeVars, sub, expr, 
                        sst, primedVars, localSub_, xlssi, xltemp1, temp1, 
                        temp2, temp3, res_X, sstsq, xprimedVars, localSub_X, 
                        res, xlsssqi, lsstsq, localSub, defSub, nxt, lsstqi, 
                        lsstemp, disjs, defs, str >>

ILS6 == /\ pc = "ILS6"
        /\ pc' = Head(stack).pc
        /\ ils' = Head(stack).ils
        /\ ilLast' = Head(stack).ilLast
        /\ ls' = Head(stack).ls
        /\ stack' = Tail(stack)
        /\ UNCHANGED << i, j, gtemp1, gtemp2, gtemp3, gtemp4, result, rVal, 
                        pMap, prcdVars, procSeq, globalVars, nonGlobalVars, 
                        allVarSeq, localVars, A, res_, ia, prcdr, ipr, proc, 
                        ip, lsseq, ilss, lstmt, whl, ili, le, ile, fs, fi, ifi, 
                        ifLast, fe, ife, ife2, feSeq, feSeqLast, fw, ifw, 
                        fwLast, cr, icr, gt, sss, isss, ss, asg, ias, ifst, 
                        estmt, iee, wi, iw, vdcl, pvdcl, exp, ie, elseq, nxt_, 
                        ixs, res_E, lst, nxt_E, temp_, flseq, temp_I, ifsqi, 
                        lseq, nxt_Ex, xxtemp1, temp2_, temp3_, temp4, exlsq, 
                        callStmt, prcd, svoci, temp, res_S, rprcd, rpvi, 
                        rpctemp, res_R, vrs, addExpr, pvexpr, pvi, stk, test, 
                        primeVars, sub, expr, sst, primedVars, localSub_, 
                        xlssi, xltemp1, temp1, temp2, temp3, res_X, sstsq, 
                        xprimedVars, localSub_X, res, xlsssqi, lsstsq, 
                        localSub, defSub, nxt, lsstqi, lsstemp, disjs, defs, 
                        str >>

IsLabelSeq == ILS1 \/ ILS2 \/ ILS3 \/ ILS4 \/ ILS5 \/ ILS6

ILI1 == /\ pc = "ILI1"
        /\ Assert(DOMAIN ili = {"type", "test", "unlabThen", "labThen",
                                "unlabElse", "labElse"}, 
                  "Failure of assertion at line 256, column 17.")
        /\ /\ exp' = ili.test
           /\ stack' = << [ procedure |->  "IsExpr",
                            pc        |->  "ILI2",
                            ie        |->  ie,
                            exp       |->  exp ] >>
                        \o stack
        /\ ie' = {}
        /\ pc' = "IE1"
        /\ UNCHANGED << i, j, gtemp1, gtemp2, gtemp3, gtemp4, result, rVal, 
                        pMap, prcdVars, procSeq, globalVars, nonGlobalVars, 
                        allVarSeq, localVars, A, res_, ia, prcdr, ipr, proc, 
                        ip, lsseq, ilss, lstmt, whl, ls, ils, ilLast, ili, le, 
                        ile, fs, fi, ifi, ifLast, fe, ife, ife2, feSeq, 
                        feSeqLast, fw, ifw, fwLast, cr, icr, gt, sss, isss, ss, 
                        asg, ias, ifst, estmt, iee, wi, iw, vdcl, pvdcl, elseq, 
                        nxt_, ixs, res_E, lst, nxt_E, temp_, flseq, temp_I, 
                        ifsqi, lseq, nxt_Ex, xxtemp1, temp2_, temp3_, temp4, 
                        exlsq, callStmt, prcd, svoci, temp, res_S, rprcd, rpvi, 
                        rpctemp, res_R, vrs, addExpr, pvexpr, pvi, stk, test, 
                        primeVars, sub, expr, sst, primedVars, localSub_, 
                        xlssi, xltemp1, temp1, temp2, temp3, res_X, sstsq, 
                        xprimedVars, localSub_X, res, xlsssqi, lsstsq, 
                        localSub, defSub, nxt, lsstqi, lsstemp, disjs, defs, 
                        str >>

ILI2 == /\ pc = "ILI2"
        /\ /\ ls' = ili.unlabThen
           /\ stack' = << [ procedure |->  "IsLabelSeq",
                            pc        |->  "ILI3",
                            ils       |->  ils,
                            ilLast    |->  ilLast,
                            ls        |->  ls ] >>
                        \o stack
        /\ ils' = {}
        /\ ilLast' = {}
        /\ pc' = "ILS1"
        /\ UNCHANGED << i, j, gtemp1, gtemp2, gtemp3, gtemp4, result, rVal, 
                        pMap, prcdVars, procSeq, globalVars, nonGlobalVars, 
                        allVarSeq, localVars, A, res_, ia, prcdr, ipr, proc, 
                        ip, lsseq, ilss, lstmt, whl, ili, le, ile, fs, fi, ifi, 
                        ifLast, fe, ife, ife2, feSeq, feSeqLast, fw, ifw, 
                        fwLast, cr, icr, gt, sss, isss, ss, asg, ias, ifst, 
                        estmt, iee, wi, iw, vdcl, pvdcl, exp, ie, elseq, nxt_, 
                        ixs, res_E, lst, nxt_E, temp_, flseq, temp_I, ifsqi, 
                        lseq, nxt_Ex, xxtemp1, temp2_, temp3_, temp4, exlsq, 
                        callStmt, prcd, svoci, temp, res_S, rprcd, rpvi, 
                        rpctemp, res_R, vrs, addExpr, pvexpr, pvi, stk, test, 
                        primeVars, sub, expr, sst, primedVars, localSub_, 
                        xlssi, xltemp1, temp1, temp2, temp3, res_X, sstsq, 
                        xprimedVars, localSub_X, res, xlsssqi, lsstsq, 
                        localSub, defSub, nxt, lsstqi, lsstemp, disjs, defs, 
                        str >>

ILI3 == /\ pc = "ILI3"
        /\ /\ lsseq' = ili.labThen
           /\ stack' = << [ procedure |->  "IsLabeledStmtSeq",
                            pc        |->  "ILI4",
                            ilss      |->  ilss,
                            lsseq     |->  lsseq ] >>
                        \o stack
        /\ ilss' = {}
        /\ pc' = "ILSS1"
        /\ UNCHANGED << i, j, gtemp1, gtemp2, gtemp3, gtemp4, result, rVal, 
                        pMap, prcdVars, procSeq, globalVars, nonGlobalVars, 
                        allVarSeq, localVars, A, res_, ia, prcdr, ipr, proc, 
                        ip, lstmt, whl, ls, ils, ilLast, ili, le, ile, fs, fi, 
                        ifi, ifLast, fe, ife, ife2, feSeq, feSeqLast, fw, ifw, 
                        fwLast, cr, icr, gt, sss, isss, ss, asg, ias, ifst, 
                        estmt, iee, wi, iw, vdcl, pvdcl, exp, ie, elseq, nxt_, 
                        ixs, res_E, lst, nxt_E, temp_, flseq, temp_I, ifsqi, 
                        lseq, nxt_Ex, xxtemp1, temp2_, temp3_, temp4, exlsq, 
                        callStmt, prcd, svoci, temp, res_S, rprcd, rpvi, 
                        rpctemp, res_R, vrs, addExpr, pvexpr, pvi, stk, test, 
                        primeVars, sub, expr, sst, primedVars, localSub_, 
                        xlssi, xltemp1, temp1, temp2, temp3, res_X, sstsq, 
                        xprimedVars, localSub_X, res, xlsssqi, lsstsq, 
                        localSub, defSub, nxt, lsstqi, lsstemp, disjs, defs, 
                        str >>

ILI4 == /\ pc = "ILI4"
        /\ /\ ls' = ili.unlabElse
           /\ stack' = << [ procedure |->  "IsLabelSeq",
                            pc        |->  "ILI5",
                            ils       |->  ils,
                            ilLast    |->  ilLast,
                            ls        |->  ls ] >>
                        \o stack
        /\ ils' = {}
        /\ ilLast' = {}
        /\ pc' = "ILS1"
        /\ UNCHANGED << i, j, gtemp1, gtemp2, gtemp3, gtemp4, result, rVal, 
                        pMap, prcdVars, procSeq, globalVars, nonGlobalVars, 
                        allVarSeq, localVars, A, res_, ia, prcdr, ipr, proc, 
                        ip, lsseq, ilss, lstmt, whl, ili, le, ile, fs, fi, ifi, 
                        ifLast, fe, ife, ife2, feSeq, feSeqLast, fw, ifw, 
                        fwLast, cr, icr, gt, sss, isss, ss, asg, ias, ifst, 
                        estmt, iee, wi, iw, vdcl, pvdcl, exp, ie, elseq, nxt_, 
                        ixs, res_E, lst, nxt_E, temp_, flseq, temp_I, ifsqi, 
                        lseq, nxt_Ex, xxtemp1, temp2_, temp3_, temp4, exlsq, 
                        callStmt, prcd, svoci, temp, res_S, rprcd, rpvi, 
                        rpctemp, res_R, vrs, addExpr, pvexpr, pvi, stk, test, 
                        primeVars, sub, expr, sst, primedVars, localSub_, 
                        xlssi, xltemp1, temp1, temp2, temp3, res_X, sstsq, 
                        xprimedVars, localSub_X, res, xlsssqi, lsstsq, 
                        localSub, defSub, nxt, lsstqi, lsstemp, disjs, defs, 
                        str >>

ILI5 == /\ pc = "ILI5"
        /\ /\ lsseq' = ili.labElse
           /\ stack' = << [ procedure |->  "IsLabeledStmtSeq",
                            pc        |->  Head(stack).pc,
                            ilss      |->  ilss,
                            lsseq     |->  lsseq ] >>
                        \o Tail(stack)
        /\ ilss' = {}
        /\ pc' = "ILSS1"
        /\ UNCHANGED << i, j, gtemp1, gtemp2, gtemp3, gtemp4, result, rVal, 
                        pMap, prcdVars, procSeq, globalVars, nonGlobalVars, 
                        allVarSeq, localVars, A, res_, ia, prcdr, ipr, proc, 
                        ip, lstmt, whl, ls, ils, ilLast, ili, le, ile, fs, fi, 
                        ifi, ifLast, fe, ife, ife2, feSeq, feSeqLast, fw, ifw, 
                        fwLast, cr, icr, gt, sss, isss, ss, asg, ias, ifst, 
                        estmt, iee, wi, iw, vdcl, pvdcl, exp, ie, elseq, nxt_, 
                        ixs, res_E, lst, nxt_E, temp_, flseq, temp_I, ifsqi, 
                        lseq, nxt_Ex, xxtemp1, temp2_, temp3_, temp4, exlsq, 
                        callStmt, prcd, svoci, temp, res_S, rprcd, rpvi, 
                        rpctemp, res_R, vrs, addExpr, pvexpr, pvi, stk, test, 
                        primeVars, sub, expr, sst, primedVars, localSub_, 
                        xlssi, xltemp1, temp1, temp2, temp3, res_X, sstsq, 
                        xprimedVars, localSub_X, res, xlsssqi, lsstsq, 
                        localSub, defSub, nxt, lsstqi, lsstemp, disjs, defs, 
                        str >>

IsLabelIf == ILI1 \/ ILI2 \/ ILI3 \/ ILI4 \/ ILI5

ILE1 == /\ pc = "ILE1"
        /\ Assert(DOMAIN le = {"type", "clauses"}, 
                  "Failure of assertion at line 273, column 17.")
        /\ Assert(IsSeq(le.clauses), 
                  "Failure of assertion at line 274, column 17.")
        /\ ile' = Len(le.clauses)
        /\ pc' = "ILE2"
        /\ UNCHANGED << i, j, gtemp1, gtemp2, gtemp3, gtemp4, result, rVal, 
                        pMap, prcdVars, procSeq, globalVars, nonGlobalVars, 
                        allVarSeq, localVars, stack, A, res_, ia, prcdr, ipr, 
                        proc, ip, lsseq, ilss, lstmt, whl, ls, ils, ilLast, 
                        ili, le, fs, fi, ifi, ifLast, fe, ife, ife2, feSeq, 
                        feSeqLast, fw, ifw, fwLast, cr, icr, gt, sss, isss, ss, 
                        asg, ias, ifst, estmt, iee, wi, iw, vdcl, pvdcl, exp, 
                        ie, elseq, nxt_, ixs, res_E, lst, nxt_E, temp_, flseq, 
                        temp_I, ifsqi, lseq, nxt_Ex, xxtemp1, temp2_, temp3_, 
                        temp4, exlsq, callStmt, prcd, svoci, temp, res_S, 
                        rprcd, rpvi, rpctemp, res_R, vrs, addExpr, pvexpr, pvi, 
                        stk, test, primeVars, sub, expr, sst, primedVars, 
                        localSub_, xlssi, xltemp1, temp1, temp2, temp3, res_X, 
                        sstsq, xprimedVars, localSub_X, res, xlsssqi, lsstsq, 
                        localSub, defSub, nxt, lsstqi, lsstemp, disjs, defs, 
                        str >>

ILE2 == /\ pc = "ILE2"
        /\ IF ile > 0
              THEN /\ Assert(DOMAIN le.clauses[ile] = {"unlabOr", "labOr"}, 
                             "Failure of assertion at line 277, column 19.")
                   /\ /\ ls' = le.clauses[ile].unlabOr
                      /\ stack' = << [ procedure |->  "IsLabelSeq",
                                       pc        |->  "ILE3",
                                       ils       |->  ils,
                                       ilLast    |->  ilLast,
                                       ls        |->  ls ] >>
                                   \o stack
                   /\ ils' = {}
                   /\ ilLast' = {}
                   /\ pc' = "ILS1"
                   /\ UNCHANGED << le, ile >>
              ELSE /\ pc' = Head(stack).pc
                   /\ ile' = Head(stack).ile
                   /\ le' = Head(stack).le
                   /\ stack' = Tail(stack)
                   /\ UNCHANGED << ls, ils, ilLast >>
        /\ UNCHANGED << i, j, gtemp1, gtemp2, gtemp3, gtemp4, result, rVal, 
                        pMap, prcdVars, procSeq, globalVars, nonGlobalVars, 
                        allVarSeq, localVars, A, res_, ia, prcdr, ipr, proc, 
                        ip, lsseq, ilss, lstmt, whl, ili, fs, fi, ifi, ifLast, 
                        fe, ife, ife2, feSeq, feSeqLast, fw, ifw, fwLast, cr, 
                        icr, gt, sss, isss, ss, asg, ias, ifst, estmt, iee, wi, 
                        iw, vdcl, pvdcl, exp, ie, elseq, nxt_, ixs, res_E, lst, 
                        nxt_E, temp_, flseq, temp_I, ifsqi, lseq, nxt_Ex, 
                        xxtemp1, temp2_, temp3_, temp4, exlsq, callStmt, prcd, 
                        svoci, temp, res_S, rprcd, rpvi, rpctemp, res_R, vrs, 
                        addExpr, pvexpr, pvi, stk, test, primeVars, sub, expr, 
                        sst, primedVars, localSub_, xlssi, xltemp1, temp1, 
                        temp2, temp3, res_X, sstsq, xprimedVars, localSub_X, 
                        res, xlsssqi, lsstsq, localSub, defSub, nxt, lsstqi, 
                        lsstemp, disjs, defs, str >>

ILE3 == /\ pc = "ILE3"
        /\ /\ lsseq' = le.clauses[ile].labOr
           /\ stack' = << [ procedure |->  "IsLabeledStmtSeq",
                            pc        |->  "ILE4",
                            ilss      |->  ilss,
                            lsseq     |->  lsseq ] >>
                        \o stack
        /\ ilss' = {}
        /\ pc' = "ILSS1"
        /\ UNCHANGED << i, j, gtemp1, gtemp2, gtemp3, gtemp4, result, rVal, 
                        pMap, prcdVars, procSeq, globalVars, nonGlobalVars, 
                        allVarSeq, localVars, A, res_, ia, prcdr, ipr, proc, 
                        ip, lstmt, whl, ls, ils, ilLast, ili, le, ile, fs, fi, 
                        ifi, ifLast, fe, ife, ife2, feSeq, feSeqLast, fw, ifw, 
                        fwLast, cr, icr, gt, sss, isss, ss, asg, ias, ifst, 
                        estmt, iee, wi, iw, vdcl, pvdcl, exp, ie, elseq, nxt_, 
                        ixs, res_E, lst, nxt_E, temp_, flseq, temp_I, ifsqi, 
                        lseq, nxt_Ex, xxtemp1, temp2_, temp3_, temp4, exlsq, 
                        callStmt, prcd, svoci, temp, res_S, rprcd, rpvi, 
                        rpctemp, res_R, vrs, addExpr, pvexpr, pvi, stk, test, 
                        primeVars, sub, expr, sst, primedVars, localSub_, 
                        xlssi, xltemp1, temp1, temp2, temp3, res_X, sstsq, 
                        xprimedVars, localSub_X, res, xlsssqi, lsstsq, 
                        localSub, defSub, nxt, lsstqi, lsstemp, disjs, defs, 
                        str >>

ILE4 == /\ pc = "ILE4"
        /\ ile' = ile - 1
        /\ pc' = "ILE2"
        /\ UNCHANGED << i, j, gtemp1, gtemp2, gtemp3, gtemp4, result, rVal, 
                        pMap, prcdVars, procSeq, globalVars, nonGlobalVars, 
                        allVarSeq, localVars, stack, A, res_, ia, prcdr, ipr, 
                        proc, ip, lsseq, ilss, lstmt, whl, ls, ils, ilLast, 
                        ili, le, fs, fi, ifi, ifLast, fe, ife, ife2, feSeq, 
                        feSeqLast, fw, ifw, fwLast, cr, icr, gt, sss, isss, ss, 
                        asg, ias, ifst, estmt, iee, wi, iw, vdcl, pvdcl, exp, 
                        ie, elseq, nxt_, ixs, res_E, lst, nxt_E, temp_, flseq, 
                        temp_I, ifsqi, lseq, nxt_Ex, xxtemp1, temp2_, temp3_, 
                        temp4, exlsq, callStmt, prcd, svoci, temp, res_S, 
                        rprcd, rpvi, rpctemp, res_R, vrs, addExpr, pvexpr, pvi, 
                        stk, test, primeVars, sub, expr, sst, primedVars, 
                        localSub_, xlssi, xltemp1, temp1, temp2, temp3, res_X, 
                        sstsq, xprimedVars, localSub_X, res, xlsssqi, lsstsq, 
                        localSub, defSub, nxt, lsstqi, lsstemp, disjs, defs, 
                        str >>

IsLabelEither == ILE1 \/ ILE2 \/ ILE3 \/ ILE4

IFS1_ == /\ pc = "IFS1_"
         /\ IF fs.type = "if"
               THEN /\ /\ fi' = fs
                       /\ stack' = << [ procedure |->  "IsFinalIf",
                                        pc        |->  "IFS2_",
                                        ifi       |->  ifi,
                                        ifLast    |->  ifLast,
                                        fi        |->  fi ] >>
                                    \o stack
                    /\ ifi' = {}
                    /\ ifLast' = {}
                    /\ pc' = "IFI1"
                    /\ UNCHANGED << fe, ife, ife2, feSeq, feSeqLast, fw, ifw, 
                                    fwLast, cr, icr, gt >>
               ELSE /\ IF fs.type = "either"
                          THEN /\ /\ fe' = fs
                                  /\ stack' = << [ procedure |->  "IsFinalEither",
                                                   pc        |->  "IFS2_",
                                                   ife       |->  ife,
                                                   ife2      |->  ife2,
                                                   feSeq     |->  feSeq,
                                                   feSeqLast |->  feSeqLast,
                                                   fe        |->  fe ] >>
                                               \o stack
                               /\ ife' = {}
                               /\ ife2' = {}
                               /\ feSeq' = {}
                               /\ feSeqLast' = {}
                               /\ pc' = "IFE1"
                               /\ UNCHANGED << fw, ifw, fwLast, cr, icr, gt >>
                          ELSE /\ IF fs.type = "with"
                                     THEN /\ /\ fw' = fs
                                             /\ stack' = << [ procedure |->  "IsFinalWith",
                                                              pc        |->  "IFS2_",
                                                              ifw       |->  ifw,
                                                              fwLast    |->  fwLast,
                                                              fw        |->  fw ] >>
                                                          \o stack
                                          /\ ifw' = {}
                                          /\ fwLast' = {}
                                          /\ pc' = "IFW1"
                                          /\ UNCHANGED << cr, icr, gt >>
                                     ELSE /\ IF fs.type \in {"return", "callReturn", "call"}
                                                THEN /\ /\ cr' = fs
                                                        /\ stack' = << [ procedure |->  "IsCallOrReturn",
                                                                         pc        |->  "IFS2_",
                                                                         icr       |->  icr,
                                                                         cr        |->  cr ] >>
                                                                     \o stack
                                                     /\ icr' = {}
                                                     /\ pc' = "ICR1"
                                                     /\ UNCHANGED gt
                                                ELSE /\ IF fs.type = "goto"
                                                           THEN /\ /\ gt' = fs
                                                                   /\ stack' = << [ procedure |->  "IsGoto",
                                                                                    pc        |->  "IFS2_",
                                                                                    gt        |->  gt ] >>
                                                                                \o stack
                                                                /\ pc' = "IGT1"
                                                           ELSE /\ Assert(FALSE, 
                                                                          "Failure of assertion at line 300, column 22.")
                                                                /\ pc' = "IFS2_"
                                                                /\ UNCHANGED << stack, 
                                                                                gt >>
                                                     /\ UNCHANGED << cr, icr >>
                                          /\ UNCHANGED << fw, ifw, fwLast >>
                               /\ UNCHANGED << fe, ife, ife2, feSeq, feSeqLast >>
                    /\ UNCHANGED << fi, ifi, ifLast >>
         /\ UNCHANGED << i, j, gtemp1, gtemp2, gtemp3, gtemp4, result, rVal, 
                         pMap, prcdVars, procSeq, globalVars, nonGlobalVars, 
                         allVarSeq, localVars, A, res_, ia, prcdr, ipr, proc, 
                         ip, lsseq, ilss, lstmt, whl, ls, ils, ilLast, ili, le, 
                         ile, fs, sss, isss, ss, asg, ias, ifst, estmt, iee, 
                         wi, iw, vdcl, pvdcl, exp, ie, elseq, nxt_, ixs, res_E, 
                         lst, nxt_E, temp_, flseq, temp_I, ifsqi, lseq, nxt_Ex, 
                         xxtemp1, temp2_, temp3_, temp4, exlsq, callStmt, prcd, 
                         svoci, temp, res_S, rprcd, rpvi, rpctemp, res_R, vrs, 
                         addExpr, pvexpr, pvi, stk, test, primeVars, sub, expr, 
                         sst, primedVars, localSub_, xlssi, xltemp1, temp1, 
                         temp2, temp3, res_X, sstsq, xprimedVars, localSub_X, 
                         res, xlsssqi, lsstsq, localSub, defSub, nxt, lsstqi, 
                         lsstemp, disjs, defs, str >>

IFS2_ == /\ pc = "IFS2_"
         /\ pc' = Head(stack).pc
         /\ fs' = Head(stack).fs
         /\ stack' = Tail(stack)
         /\ UNCHANGED << i, j, gtemp1, gtemp2, gtemp3, gtemp4, result, rVal, 
                         pMap, prcdVars, procSeq, globalVars, nonGlobalVars, 
                         allVarSeq, localVars, A, res_, ia, prcdr, ipr, proc, 
                         ip, lsseq, ilss, lstmt, whl, ls, ils, ilLast, ili, le, 
                         ile, fi, ifi, ifLast, fe, ife, ife2, feSeq, feSeqLast, 
                         fw, ifw, fwLast, cr, icr, gt, sss, isss, ss, asg, ias, 
                         ifst, estmt, iee, wi, iw, vdcl, pvdcl, exp, ie, elseq, 
                         nxt_, ixs, res_E, lst, nxt_E, temp_, flseq, temp_I, 
                         ifsqi, lseq, nxt_Ex, xxtemp1, temp2_, temp3_, temp4, 
                         exlsq, callStmt, prcd, svoci, temp, res_S, rprcd, 
                         rpvi, rpctemp, res_R, vrs, addExpr, pvexpr, pvi, stk, 
                         test, primeVars, sub, expr, sst, primedVars, 
                         localSub_, xlssi, xltemp1, temp1, temp2, temp3, res_X, 
                         sstsq, xprimedVars, localSub_X, res, xlsssqi, lsstsq, 
                         localSub, defSub, nxt, lsstqi, lsstemp, disjs, defs, 
                         str >>

IsFinalStmt == IFS1_ \/ IFS2_

IFI1 == /\ pc = "IFI1"
        /\ Assert(DOMAIN fi = {"type", "test", "then", "else"}, 
                  "Failure of assertion at line 317, column 17.")
        /\ /\ exp' = fi.test
           /\ stack' = << [ procedure |->  "IsExpr",
                            pc        |->  "IFI2",
                            ie        |->  ie,
                            exp       |->  exp ] >>
                        \o stack
        /\ ie' = {}
        /\ pc' = "IE1"
        /\ UNCHANGED << i, j, gtemp1, gtemp2, gtemp3, gtemp4, result, rVal, 
                        pMap, prcdVars, procSeq, globalVars, nonGlobalVars, 
                        allVarSeq, localVars, A, res_, ia, prcdr, ipr, proc, 
                        ip, lsseq, ilss, lstmt, whl, ls, ils, ilLast, ili, le, 
                        ile, fs, fi, ifi, ifLast, fe, ife, ife2, feSeq, 
                        feSeqLast, fw, ifw, fwLast, cr, icr, gt, sss, isss, ss, 
                        asg, ias, ifst, estmt, iee, wi, iw, vdcl, pvdcl, elseq, 
                        nxt_, ixs, res_E, lst, nxt_E, temp_, flseq, temp_I, 
                        ifsqi, lseq, nxt_Ex, xxtemp1, temp2_, temp3_, temp4, 
                        exlsq, callStmt, prcd, svoci, temp, res_S, rprcd, rpvi, 
                        rpctemp, res_R, vrs, addExpr, pvexpr, pvi, stk, test, 
                        primeVars, sub, expr, sst, primedVars, localSub_, 
                        xlssi, xltemp1, temp1, temp2, temp3, res_X, sstsq, 
                        xprimedVars, localSub_X, res, xlsssqi, lsstsq, 
                        localSub, defSub, nxt, lsstqi, lsstemp, disjs, defs, 
                        str >>

IFI2 == /\ pc = "IFI2"
        /\ Assert(IsSeq(fi.then), 
                  "Failure of assertion at line 319, column 17.")
        /\ ifi' = Len(fi.then) - 1
        /\ pc' = "IFI3"
        /\ UNCHANGED << i, j, gtemp1, gtemp2, gtemp3, gtemp4, result, rVal, 
                        pMap, prcdVars, procSeq, globalVars, nonGlobalVars, 
                        allVarSeq, localVars, stack, A, res_, ia, prcdr, ipr, 
                        proc, ip, lsseq, ilss, lstmt, whl, ls, ils, ilLast, 
                        ili, le, ile, fs, fi, ifLast, fe, ife, ife2, feSeq, 
                        feSeqLast, fw, ifw, fwLast, cr, icr, gt, sss, isss, ss, 
                        asg, ias, ifst, estmt, iee, wi, iw, vdcl, pvdcl, exp, 
                        ie, elseq, nxt_, ixs, res_E, lst, nxt_E, temp_, flseq, 
                        temp_I, ifsqi, lseq, nxt_Ex, xxtemp1, temp2_, temp3_, 
                        temp4, exlsq, callStmt, prcd, svoci, temp, res_S, 
                        rprcd, rpvi, rpctemp, res_R, vrs, addExpr, pvexpr, pvi, 
                        stk, test, primeVars, sub, expr, sst, primedVars, 
                        localSub_, xlssi, xltemp1, temp1, temp2, temp3, res_X, 
                        sstsq, xprimedVars, localSub_X, res, xlsssqi, lsstsq, 
                        localSub, defSub, nxt, lsstqi, lsstemp, disjs, defs, 
                        str >>

IFI3 == /\ pc = "IFI3"
        /\ IF ifi > 0
              THEN /\ /\ ss' = fi.then[ifi]
                      /\ stack' = << [ procedure |->  "IsSimpleStmt",
                                       pc        |->  "IFI4",
                                       ss        |->  ss ] >>
                                   \o stack
                   /\ pc' = "ISS1"
                   /\ UNCHANGED << fi, ifi, ifLast >>
              ELSE /\ IF fi.then = << >>
                         THEN /\ pc' = Head(stack).pc
                              /\ ifi' = Head(stack).ifi
                              /\ ifLast' = Head(stack).ifLast
                              /\ fi' = Head(stack).fi
                              /\ stack' = Tail(stack)
                         ELSE /\ pc' = "IFI5"
                              /\ UNCHANGED << stack, fi, ifi, ifLast >>
                   /\ UNCHANGED ss
        /\ UNCHANGED << i, j, gtemp1, gtemp2, gtemp3, gtemp4, result, rVal, 
                        pMap, prcdVars, procSeq, globalVars, nonGlobalVars, 
                        allVarSeq, localVars, A, res_, ia, prcdr, ipr, proc, 
                        ip, lsseq, ilss, lstmt, whl, ls, ils, ilLast, ili, le, 
                        ile, fs, fe, ife, ife2, feSeq, feSeqLast, fw, ifw, 
                        fwLast, cr, icr, gt, sss, isss, asg, ias, ifst, estmt, 
                        iee, wi, iw, vdcl, pvdcl, exp, ie, elseq, nxt_, ixs, 
                        res_E, lst, nxt_E, temp_, flseq, temp_I, ifsqi, lseq, 
                        nxt_Ex, xxtemp1, temp2_, temp3_, temp4, exlsq, 
                        callStmt, prcd, svoci, temp, res_S, rprcd, rpvi, 
                        rpctemp, res_R, vrs, addExpr, pvexpr, pvi, stk, test, 
                        primeVars, sub, expr, sst, primedVars, localSub_, 
                        xlssi, xltemp1, temp1, temp2, temp3, res_X, sstsq, 
                        xprimedVars, localSub_X, res, xlsssqi, lsstsq, 
                        localSub, defSub, nxt, lsstqi, lsstemp, disjs, defs, 
                        str >>

IFI4 == /\ pc = "IFI4"
        /\ ifi' = ifi - 1
        /\ pc' = "IFI3"
        /\ UNCHANGED << i, j, gtemp1, gtemp2, gtemp3, gtemp4, result, rVal, 
                        pMap, prcdVars, procSeq, globalVars, nonGlobalVars, 
                        allVarSeq, localVars, stack, A, res_, ia, prcdr, ipr, 
                        proc, ip, lsseq, ilss, lstmt, whl, ls, ils, ilLast, 
                        ili, le, ile, fs, fi, ifLast, fe, ife, ife2, feSeq, 
                        feSeqLast, fw, ifw, fwLast, cr, icr, gt, sss, isss, ss, 
                        asg, ias, ifst, estmt, iee, wi, iw, vdcl, pvdcl, exp, 
                        ie, elseq, nxt_, ixs, res_E, lst, nxt_E, temp_, flseq, 
                        temp_I, ifsqi, lseq, nxt_Ex, xxtemp1, temp2_, temp3_, 
                        temp4, exlsq, callStmt, prcd, svoci, temp, res_S, 
                        rprcd, rpvi, rpctemp, res_R, vrs, addExpr, pvexpr, pvi, 
                        stk, test, primeVars, sub, expr, sst, primedVars, 
                        localSub_, xlssi, xltemp1, temp1, temp2, temp3, res_X, 
                        sstsq, xprimedVars, localSub_X, res, xlsssqi, lsstsq, 
                        localSub, defSub, nxt, lsstqi, lsstemp, disjs, defs, 
                        str >>

IFI5 == /\ pc = "IFI5"
        /\ ifLast' = fi.then[Len(fi.then)]
        /\ IF FinalStmtType(ifLast')
              THEN /\ /\ fs' = ifLast'
                      /\ stack' = << [ procedure |->  "IsFinalStmt",
                                       pc        |->  "IFI6",
                                       fs        |->  fs ] >>
                                   \o stack
                   /\ pc' = "IFS1_"
                   /\ UNCHANGED ss
              ELSE /\ /\ ss' = ifLast'
                      /\ stack' = << [ procedure |->  "IsSimpleStmt",
                                       pc        |->  "IFI6",
                                       ss        |->  ss ] >>
                                   \o stack
                   /\ pc' = "ISS1"
                   /\ UNCHANGED fs
        /\ UNCHANGED << i, j, gtemp1, gtemp2, gtemp3, gtemp4, result, rVal, 
                        pMap, prcdVars, procSeq, globalVars, nonGlobalVars, 
                        allVarSeq, localVars, A, res_, ia, prcdr, ipr, proc, 
                        ip, lsseq, ilss, lstmt, whl, ls, ils, ilLast, ili, le, 
                        ile, fi, ifi, fe, ife, ife2, feSeq, feSeqLast, fw, ifw, 
                        fwLast, cr, icr, gt, sss, isss, asg, ias, ifst, estmt, 
                        iee, wi, iw, vdcl, pvdcl, exp, ie, elseq, nxt_, ixs, 
                        res_E, lst, nxt_E, temp_, flseq, temp_I, ifsqi, lseq, 
                        nxt_Ex, xxtemp1, temp2_, temp3_, temp4, exlsq, 
                        callStmt, prcd, svoci, temp, res_S, rprcd, rpvi, 
                        rpctemp, res_R, vrs, addExpr, pvexpr, pvi, stk, test, 
                        primeVars, sub, expr, sst, primedVars, localSub_, 
                        xlssi, xltemp1, temp1, temp2, temp3, res_X, sstsq, 
                        xprimedVars, localSub_X, res, xlsssqi, lsstsq, 
                        localSub, defSub, nxt, lsstqi, lsstemp, disjs, defs, 
                        str >>

IFI6 == /\ pc = "IFI6"
        /\ Assert(IsSeq(fi.else), 
                  "Failure of assertion at line 331, column 17.")
        /\ ifi' = Len(fi.else) - 1
        /\ pc' = "IFI7"
        /\ UNCHANGED << i, j, gtemp1, gtemp2, gtemp3, gtemp4, result, rVal, 
                        pMap, prcdVars, procSeq, globalVars, nonGlobalVars, 
                        allVarSeq, localVars, stack, A, res_, ia, prcdr, ipr, 
                        proc, ip, lsseq, ilss, lstmt, whl, ls, ils, ilLast, 
                        ili, le, ile, fs, fi, ifLast, fe, ife, ife2, feSeq, 
                        feSeqLast, fw, ifw, fwLast, cr, icr, gt, sss, isss, ss, 
                        asg, ias, ifst, estmt, iee, wi, iw, vdcl, pvdcl, exp, 
                        ie, elseq, nxt_, ixs, res_E, lst, nxt_E, temp_, flseq, 
                        temp_I, ifsqi, lseq, nxt_Ex, xxtemp1, temp2_, temp3_, 
                        temp4, exlsq, callStmt, prcd, svoci, temp, res_S, 
                        rprcd, rpvi, rpctemp, res_R, vrs, addExpr, pvexpr, pvi, 
                        stk, test, primeVars, sub, expr, sst, primedVars, 
                        localSub_, xlssi, xltemp1, temp1, temp2, temp3, res_X, 
                        sstsq, xprimedVars, localSub_X, res, xlsssqi, lsstsq, 
                        localSub, defSub, nxt, lsstqi, lsstemp, disjs, defs, 
                        str >>

IFI7 == /\ pc = "IFI7"
        /\ IF ifi > 0
              THEN /\ /\ ss' = fi.else[ifi]
                      /\ stack' = << [ procedure |->  "IsSimpleStmt",
                                       pc        |->  "IFI8",
                                       ss        |->  ss ] >>
                                   \o stack
                   /\ pc' = "ISS1"
                   /\ UNCHANGED << fi, ifi, ifLast >>
              ELSE /\ IF fi.else = << >>
                         THEN /\ pc' = Head(stack).pc
                              /\ ifi' = Head(stack).ifi
                              /\ ifLast' = Head(stack).ifLast
                              /\ fi' = Head(stack).fi
                              /\ stack' = Tail(stack)
                         ELSE /\ pc' = "IFI9"
                              /\ UNCHANGED << stack, fi, ifi, ifLast >>
                   /\ UNCHANGED ss
        /\ UNCHANGED << i, j, gtemp1, gtemp2, gtemp3, gtemp4, result, rVal, 
                        pMap, prcdVars, procSeq, globalVars, nonGlobalVars, 
                        allVarSeq, localVars, A, res_, ia, prcdr, ipr, proc, 
                        ip, lsseq, ilss, lstmt, whl, ls, ils, ilLast, ili, le, 
                        ile, fs, fe, ife, ife2, feSeq, feSeqLast, fw, ifw, 
                        fwLast, cr, icr, gt, sss, isss, asg, ias, ifst, estmt, 
                        iee, wi, iw, vdcl, pvdcl, exp, ie, elseq, nxt_, ixs, 
                        res_E, lst, nxt_E, temp_, flseq, temp_I, ifsqi, lseq, 
                        nxt_Ex, xxtemp1, temp2_, temp3_, temp4, exlsq, 
                        callStmt, prcd, svoci, temp, res_S, rprcd, rpvi, 
                        rpctemp, res_R, vrs, addExpr, pvexpr, pvi, stk, test, 
                        primeVars, sub, expr, sst, primedVars, localSub_, 
                        xlssi, xltemp1, temp1, temp2, temp3, res_X, sstsq, 
                        xprimedVars, localSub_X, res, xlsssqi, lsstsq, 
                        localSub, defSub, nxt, lsstqi, lsstemp, disjs, defs, 
                        str >>

IFI8 == /\ pc = "IFI8"
        /\ ifi' = ifi - 1
        /\ pc' = "IFI7"
        /\ UNCHANGED << i, j, gtemp1, gtemp2, gtemp3, gtemp4, result, rVal, 
                        pMap, prcdVars, procSeq, globalVars, nonGlobalVars, 
                        allVarSeq, localVars, stack, A, res_, ia, prcdr, ipr, 
                        proc, ip, lsseq, ilss, lstmt, whl, ls, ils, ilLast, 
                        ili, le, ile, fs, fi, ifLast, fe, ife, ife2, feSeq, 
                        feSeqLast, fw, ifw, fwLast, cr, icr, gt, sss, isss, ss, 
                        asg, ias, ifst, estmt, iee, wi, iw, vdcl, pvdcl, exp, 
                        ie, elseq, nxt_, ixs, res_E, lst, nxt_E, temp_, flseq, 
                        temp_I, ifsqi, lseq, nxt_Ex, xxtemp1, temp2_, temp3_, 
                        temp4, exlsq, callStmt, prcd, svoci, temp, res_S, 
                        rprcd, rpvi, rpctemp, res_R, vrs, addExpr, pvexpr, pvi, 
                        stk, test, primeVars, sub, expr, sst, primedVars, 
                        localSub_, xlssi, xltemp1, temp1, temp2, temp3, res_X, 
                        sstsq, xprimedVars, localSub_X, res, xlsssqi, lsstsq, 
                        localSub, defSub, nxt, lsstqi, lsstemp, disjs, defs, 
                        str >>

IFI9 == /\ pc = "IFI9"
        /\ ifLast' = fi.else[Len(fi.else)]
        /\ IF FinalStmtType(ifLast')
              THEN /\ /\ fs' = ifLast'
                      /\ stack' = << [ procedure |->  "IsFinalStmt",
                                       pc        |->  "IFI10",
                                       fs        |->  fs ] >>
                                   \o stack
                   /\ pc' = "IFS1_"
                   /\ UNCHANGED ss
              ELSE /\ /\ ss' = ifLast'
                      /\ stack' = << [ procedure |->  "IsSimpleStmt",
                                       pc        |->  "IFI10",
                                       ss        |->  ss ] >>
                                   \o stack
                   /\ pc' = "ISS1"
                   /\ UNCHANGED fs
        /\ UNCHANGED << i, j, gtemp1, gtemp2, gtemp3, gtemp4, result, rVal, 
                        pMap, prcdVars, procSeq, globalVars, nonGlobalVars, 
                        allVarSeq, localVars, A, res_, ia, prcdr, ipr, proc, 
                        ip, lsseq, ilss, lstmt, whl, ls, ils, ilLast, ili, le, 
                        ile, fi, ifi, fe, ife, ife2, feSeq, feSeqLast, fw, ifw, 
                        fwLast, cr, icr, gt, sss, isss, asg, ias, ifst, estmt, 
                        iee, wi, iw, vdcl, pvdcl, exp, ie, elseq, nxt_, ixs, 
                        res_E, lst, nxt_E, temp_, flseq, temp_I, ifsqi, lseq, 
                        nxt_Ex, xxtemp1, temp2_, temp3_, temp4, exlsq, 
                        callStmt, prcd, svoci, temp, res_S, rprcd, rpvi, 
                        rpctemp, res_R, vrs, addExpr, pvexpr, pvi, stk, test, 
                        primeVars, sub, expr, sst, primedVars, localSub_, 
                        xlssi, xltemp1, temp1, temp2, temp3, res_X, sstsq, 
                        xprimedVars, localSub_X, res, xlsssqi, lsstsq, 
                        localSub, defSub, nxt, lsstqi, lsstemp, disjs, defs, 
                        str >>

IFI10 == /\ pc = "IFI10"
         /\ pc' = Head(stack).pc
         /\ ifi' = Head(stack).ifi
         /\ ifLast' = Head(stack).ifLast
         /\ fi' = Head(stack).fi
         /\ stack' = Tail(stack)
         /\ UNCHANGED << i, j, gtemp1, gtemp2, gtemp3, gtemp4, result, rVal, 
                         pMap, prcdVars, procSeq, globalVars, nonGlobalVars, 
                         allVarSeq, localVars, A, res_, ia, prcdr, ipr, proc, 
                         ip, lsseq, ilss, lstmt, whl, ls, ils, ilLast, ili, le, 
                         ile, fs, fe, ife, ife2, feSeq, feSeqLast, fw, ifw, 
                         fwLast, cr, icr, gt, sss, isss, ss, asg, ias, ifst, 
                         estmt, iee, wi, iw, vdcl, pvdcl, exp, ie, elseq, nxt_, 
                         ixs, res_E, lst, nxt_E, temp_, flseq, temp_I, ifsqi, 
                         lseq, nxt_Ex, xxtemp1, temp2_, temp3_, temp4, exlsq, 
                         callStmt, prcd, svoci, temp, res_S, rprcd, rpvi, 
                         rpctemp, res_R, vrs, addExpr, pvexpr, pvi, stk, test, 
                         primeVars, sub, expr, sst, primedVars, localSub_, 
                         xlssi, xltemp1, temp1, temp2, temp3, res_X, sstsq, 
                         xprimedVars, localSub_X, res, xlsssqi, lsstsq, 
                         localSub, defSub, nxt, lsstqi, lsstemp, disjs, defs, 
                         str >>

IsFinalIf == IFI1 \/ IFI2 \/ IFI3 \/ IFI4 \/ IFI5 \/ IFI6 \/ IFI7 \/ IFI8
                \/ IFI9 \/ IFI10

IFE1 == /\ pc = "IFE1"
        /\ Assert(DOMAIN fe = {"type", "ors"}, 
                  "Failure of assertion at line 354, column 17.")
        /\ Assert(IsNonemptySeq(fe.ors), 
                  "Failure of assertion at line 355, column 18.")
        /\ ife' = Len(fe.ors)
        /\ pc' = "IFE2"
        /\ UNCHANGED << i, j, gtemp1, gtemp2, gtemp3, gtemp4, result, rVal, 
                        pMap, prcdVars, procSeq, globalVars, nonGlobalVars, 
                        allVarSeq, localVars, stack, A, res_, ia, prcdr, ipr, 
                        proc, ip, lsseq, ilss, lstmt, whl, ls, ils, ilLast, 
                        ili, le, ile, fs, fi, ifi, ifLast, fe, ife2, feSeq, 
                        feSeqLast, fw, ifw, fwLast, cr, icr, gt, sss, isss, ss, 
                        asg, ias, ifst, estmt, iee, wi, iw, vdcl, pvdcl, exp, 
                        ie, elseq, nxt_, ixs, res_E, lst, nxt_E, temp_, flseq, 
                        temp_I, ifsqi, lseq, nxt_Ex, xxtemp1, temp2_, temp3_, 
                        temp4, exlsq, callStmt, prcd, svoci, temp, res_S, 
                        rprcd, rpvi, rpctemp, res_R, vrs, addExpr, pvexpr, pvi, 
                        stk, test, primeVars, sub, expr, sst, primedVars, 
                        localSub_, xlssi, xltemp1, temp1, temp2, temp3, res_X, 
                        sstsq, xprimedVars, localSub_X, res, xlsssqi, lsstsq, 
                        localSub, defSub, nxt, lsstqi, lsstemp, disjs, defs, 
                        str >>

IFE2 == /\ pc = "IFE2"
        /\ IF ife > 0
              THEN /\ feSeq' = fe.ors[ife]
                   /\ Assert(IsSeq(feSeq'), 
                             "Failure of assertion at line 359, column 19.")
                   /\ ife2' = Len(feSeq') - 1
                   /\ pc' = "IFE3"
              ELSE /\ pc' = "IFE6"
                   /\ UNCHANGED << ife2, feSeq >>
        /\ UNCHANGED << i, j, gtemp1, gtemp2, gtemp3, gtemp4, result, rVal, 
                        pMap, prcdVars, procSeq, globalVars, nonGlobalVars, 
                        allVarSeq, localVars, stack, A, res_, ia, prcdr, ipr, 
                        proc, ip, lsseq, ilss, lstmt, whl, ls, ils, ilLast, 
                        ili, le, ile, fs, fi, ifi, ifLast, fe, ife, feSeqLast, 
                        fw, ifw, fwLast, cr, icr, gt, sss, isss, ss, asg, ias, 
                        ifst, estmt, iee, wi, iw, vdcl, pvdcl, exp, ie, elseq, 
                        nxt_, ixs, res_E, lst, nxt_E, temp_, flseq, temp_I, 
                        ifsqi, lseq, nxt_Ex, xxtemp1, temp2_, temp3_, temp4, 
                        exlsq, callStmt, prcd, svoci, temp, res_S, rprcd, rpvi, 
                        rpctemp, res_R, vrs, addExpr, pvexpr, pvi, stk, test, 
                        primeVars, sub, expr, sst, primedVars, localSub_, 
                        xlssi, xltemp1, temp1, temp2, temp3, res_X, sstsq, 
                        xprimedVars, localSub_X, res, xlsssqi, lsstsq, 
                        localSub, defSub, nxt, lsstqi, lsstemp, disjs, defs, 
                        str >>

IFE3 == /\ pc = "IFE3"
        /\ IF ife2 > 0
              THEN /\ /\ ss' = feSeq[ife2]
                      /\ stack' = << [ procedure |->  "IsSimpleStmt",
                                       pc        |->  "IFE4",
                                       ss        |->  ss ] >>
                                   \o stack
                   /\ pc' = "ISS1"
                   /\ UNCHANGED << fs, feSeqLast >>
              ELSE /\ IF Len(feSeq) > 0
                         THEN /\ feSeqLast' = feSeq[Len(feSeq)]
                              /\ IF FinalStmtType(feSeqLast')
                                    THEN /\ /\ fs' = feSeqLast'
                                            /\ stack' = << [ procedure |->  "IsFinalStmt",
                                                             pc        |->  "IEF5",
                                                             fs        |->  fs ] >>
                                                         \o stack
                                         /\ pc' = "IFS1_"
                                         /\ UNCHANGED ss
                                    ELSE /\ /\ ss' = feSeqLast'
                                            /\ stack' = << [ procedure |->  "IsSimpleStmt",
                                                             pc        |->  "IEF5",
                                                             ss        |->  ss ] >>
                                                         \o stack
                                         /\ pc' = "ISS1"
                                         /\ UNCHANGED fs
                         ELSE /\ pc' = "IEF5"
                              /\ UNCHANGED << stack, fs, feSeqLast, ss >>
        /\ UNCHANGED << i, j, gtemp1, gtemp2, gtemp3, gtemp4, result, rVal, 
                        pMap, prcdVars, procSeq, globalVars, nonGlobalVars, 
                        allVarSeq, localVars, A, res_, ia, prcdr, ipr, proc, 
                        ip, lsseq, ilss, lstmt, whl, ls, ils, ilLast, ili, le, 
                        ile, fi, ifi, ifLast, fe, ife, ife2, feSeq, fw, ifw, 
                        fwLast, cr, icr, gt, sss, isss, asg, ias, ifst, estmt, 
                        iee, wi, iw, vdcl, pvdcl, exp, ie, elseq, nxt_, ixs, 
                        res_E, lst, nxt_E, temp_, flseq, temp_I, ifsqi, lseq, 
                        nxt_Ex, xxtemp1, temp2_, temp3_, temp4, exlsq, 
                        callStmt, prcd, svoci, temp, res_S, rprcd, rpvi, 
                        rpctemp, res_R, vrs, addExpr, pvexpr, pvi, stk, test, 
                        primeVars, sub, expr, sst, primedVars, localSub_, 
                        xlssi, xltemp1, temp1, temp2, temp3, res_X, sstsq, 
                        xprimedVars, localSub_X, res, xlsssqi, lsstsq, 
                        localSub, defSub, nxt, lsstqi, lsstemp, disjs, defs, 
                        str >>

IFE4 == /\ pc = "IFE4"
        /\ ife2' = ife2 - 1
        /\ pc' = "IFE3"
        /\ UNCHANGED << i, j, gtemp1, gtemp2, gtemp3, gtemp4, result, rVal, 
                        pMap, prcdVars, procSeq, globalVars, nonGlobalVars, 
                        allVarSeq, localVars, stack, A, res_, ia, prcdr, ipr, 
                        proc, ip, lsseq, ilss, lstmt, whl, ls, ils, ilLast, 
                        ili, le, ile, fs, fi, ifi, ifLast, fe, ife, feSeq, 
                        feSeqLast, fw, ifw, fwLast, cr, icr, gt, sss, isss, ss, 
                        asg, ias, ifst, estmt, iee, wi, iw, vdcl, pvdcl, exp, 
                        ie, elseq, nxt_, ixs, res_E, lst, nxt_E, temp_, flseq, 
                        temp_I, ifsqi, lseq, nxt_Ex, xxtemp1, temp2_, temp3_, 
                        temp4, exlsq, callStmt, prcd, svoci, temp, res_S, 
                        rprcd, rpvi, rpctemp, res_R, vrs, addExpr, pvexpr, pvi, 
                        stk, test, primeVars, sub, expr, sst, primedVars, 
                        localSub_, xlssi, xltemp1, temp1, temp2, temp3, res_X, 
                        sstsq, xprimedVars, localSub_X, res, xlsssqi, lsstsq, 
                        localSub, defSub, nxt, lsstqi, lsstemp, disjs, defs, 
                        str >>

IEF5 == /\ pc = "IEF5"
        /\ ife' = ife - 1
        /\ pc' = "IFE2"
        /\ UNCHANGED << i, j, gtemp1, gtemp2, gtemp3, gtemp4, result, rVal, 
                        pMap, prcdVars, procSeq, globalVars, nonGlobalVars, 
                        allVarSeq, localVars, stack, A, res_, ia, prcdr, ipr, 
                        proc, ip, lsseq, ilss, lstmt, whl, ls, ils, ilLast, 
                        ili, le, ile, fs, fi, ifi, ifLast, fe, ife2, feSeq, 
                        feSeqLast, fw, ifw, fwLast, cr, icr, gt, sss, isss, ss, 
                        asg, ias, ifst, estmt, iee, wi, iw, vdcl, pvdcl, exp, 
                        ie, elseq, nxt_, ixs, res_E, lst, nxt_E, temp_, flseq, 
                        temp_I, ifsqi, lseq, nxt_Ex, xxtemp1, temp2_, temp3_, 
                        temp4, exlsq, callStmt, prcd, svoci, temp, res_S, 
                        rprcd, rpvi, rpctemp, res_R, vrs, addExpr, pvexpr, pvi, 
                        stk, test, primeVars, sub, expr, sst, primedVars, 
                        localSub_, xlssi, xltemp1, temp1, temp2, temp3, res_X, 
                        sstsq, xprimedVars, localSub_X, res, xlsssqi, lsstsq, 
                        localSub, defSub, nxt, lsstqi, lsstemp, disjs, defs, 
                        str >>

IFE6 == /\ pc = "IFE6"
        /\ pc' = Head(stack).pc
        /\ ife' = Head(stack).ife
        /\ ife2' = Head(stack).ife2
        /\ feSeq' = Head(stack).feSeq
        /\ feSeqLast' = Head(stack).feSeqLast
        /\ fe' = Head(stack).fe
        /\ stack' = Tail(stack)
        /\ UNCHANGED << i, j, gtemp1, gtemp2, gtemp3, gtemp4, result, rVal, 
                        pMap, prcdVars, procSeq, globalVars, nonGlobalVars, 
                        allVarSeq, localVars, A, res_, ia, prcdr, ipr, proc, 
                        ip, lsseq, ilss, lstmt, whl, ls, ils, ilLast, ili, le, 
                        ile, fs, fi, ifi, ifLast, fw, ifw, fwLast, cr, icr, gt, 
                        sss, isss, ss, asg, ias, ifst, estmt, iee, wi, iw, 
                        vdcl, pvdcl, exp, ie, elseq, nxt_, ixs, res_E, lst, 
                        nxt_E, temp_, flseq, temp_I, ifsqi, lseq, nxt_Ex, 
                        xxtemp1, temp2_, temp3_, temp4, exlsq, callStmt, prcd, 
                        svoci, temp, res_S, rprcd, rpvi, rpctemp, res_R, vrs, 
                        addExpr, pvexpr, pvi, stk, test, primeVars, sub, expr, 
                        sst, primedVars, localSub_, xlssi, xltemp1, temp1, 
                        temp2, temp3, res_X, sstsq, xprimedVars, localSub_X, 
                        res, xlsssqi, lsstsq, localSub, defSub, nxt, lsstqi, 
                        lsstemp, disjs, defs, str >>

IsFinalEither == IFE1 \/ IFE2 \/ IFE3 \/ IFE4 \/ IEF5 \/ IFE6

IFW1 == /\ pc = "IFW1"
        /\ Assert(DOMAIN fw = {"type",  "var", "eqOrIn", "exp", "do"}, 
                  "Failure of assertion at line 388, column 17.")
        /\ Assert(fw.var \in STRING, 
                  "Failure of assertion at line 389, column 17.")
        /\ Assert(fw.eqOrIn \in {"=", "\\in"}, 
                  "Failure of assertion at line 390, column 17.")
        /\ /\ exp' = fw.exp
           /\ stack' = << [ procedure |->  "IsExpr",
                            pc        |->  "IFW2",
                            ie        |->  ie,
                            exp       |->  exp ] >>
                        \o stack
        /\ ie' = {}
        /\ pc' = "IE1"
        /\ UNCHANGED << i, j, gtemp1, gtemp2, gtemp3, gtemp4, result, rVal, 
                        pMap, prcdVars, procSeq, globalVars, nonGlobalVars, 
                        allVarSeq, localVars, A, res_, ia, prcdr, ipr, proc, 
                        ip, lsseq, ilss, lstmt, whl, ls, ils, ilLast, ili, le, 
                        ile, fs, fi, ifi, ifLast, fe, ife, ife2, feSeq, 
                        feSeqLast, fw, ifw, fwLast, cr, icr, gt, sss, isss, ss, 
                        asg, ias, ifst, estmt, iee, wi, iw, vdcl, pvdcl, elseq, 
                        nxt_, ixs, res_E, lst, nxt_E, temp_, flseq, temp_I, 
                        ifsqi, lseq, nxt_Ex, xxtemp1, temp2_, temp3_, temp4, 
                        exlsq, callStmt, prcd, svoci, temp, res_S, rprcd, rpvi, 
                        rpctemp, res_R, vrs, addExpr, pvexpr, pvi, stk, test, 
                        primeVars, sub, expr, sst, primedVars, localSub_, 
                        xlssi, xltemp1, temp1, temp2, temp3, res_X, sstsq, 
                        xprimedVars, localSub_X, res, xlsssqi, lsstsq, 
                        localSub, defSub, nxt, lsstqi, lsstemp, disjs, defs, 
                        str >>

IFW2 == /\ pc = "IFW2"
        /\ Assert(IsSeq(fw.do), 
                  "Failure of assertion at line 392, column 17.")
        /\ Assert(fw.do # << >>, 
                  "Failure of assertion at line 393, column 17.")
        /\ ifw' = Len(fw.do) - 1
        /\ pc' = "IFW3"
        /\ UNCHANGED << i, j, gtemp1, gtemp2, gtemp3, gtemp4, result, rVal, 
                        pMap, prcdVars, procSeq, globalVars, nonGlobalVars, 
                        allVarSeq, localVars, stack, A, res_, ia, prcdr, ipr, 
                        proc, ip, lsseq, ilss, lstmt, whl, ls, ils, ilLast, 
                        ili, le, ile, fs, fi, ifi, ifLast, fe, ife, ife2, 
                        feSeq, feSeqLast, fw, fwLast, cr, icr, gt, sss, isss, 
                        ss, asg, ias, ifst, estmt, iee, wi, iw, vdcl, pvdcl, 
                        exp, ie, elseq, nxt_, ixs, res_E, lst, nxt_E, temp_, 
                        flseq, temp_I, ifsqi, lseq, nxt_Ex, xxtemp1, temp2_, 
                        temp3_, temp4, exlsq, callStmt, prcd, svoci, temp, 
                        res_S, rprcd, rpvi, rpctemp, res_R, vrs, addExpr, 
                        pvexpr, pvi, stk, test, primeVars, sub, expr, sst, 
                        primedVars, localSub_, xlssi, xltemp1, temp1, temp2, 
                        temp3, res_X, sstsq, xprimedVars, localSub_X, res, 
                        xlsssqi, lsstsq, localSub, defSub, nxt, lsstqi, 
                        lsstemp, disjs, defs, str >>

IFW3 == /\ pc = "IFW3"
        /\ IF ifw > 0
              THEN /\ /\ ss' = fw.do[ifw]
                      /\ stack' = << [ procedure |->  "IsSimpleStmt",
                                       pc        |->  "IFW4",
                                       ss        |->  ss ] >>
                                   \o stack
                   /\ pc' = "ISS1"
                   /\ UNCHANGED << fs, fwLast >>
              ELSE /\ fwLast' = fw.do[Len(fw.do)]
                   /\ IF FinalStmtType(fwLast')
                         THEN /\ /\ fs' = fwLast'
                                 /\ stack' = << [ procedure |->  "IsFinalStmt",
                                                  pc        |->  "IFW5",
                                                  fs        |->  fs ] >>
                                              \o stack
                              /\ pc' = "IFS1_"
                              /\ UNCHANGED ss
                         ELSE /\ /\ ss' = fwLast'
                                 /\ stack' = << [ procedure |->  "IsSimpleStmt",
                                                  pc        |->  "IFW5",
                                                  ss        |->  ss ] >>
                                              \o stack
                              /\ pc' = "ISS1"
                              /\ UNCHANGED fs
        /\ UNCHANGED << i, j, gtemp1, gtemp2, gtemp3, gtemp4, result, rVal, 
                        pMap, prcdVars, procSeq, globalVars, nonGlobalVars, 
                        allVarSeq, localVars, A, res_, ia, prcdr, ipr, proc, 
                        ip, lsseq, ilss, lstmt, whl, ls, ils, ilLast, ili, le, 
                        ile, fi, ifi, ifLast, fe, ife, ife2, feSeq, feSeqLast, 
                        fw, ifw, cr, icr, gt, sss, isss, asg, ias, ifst, estmt, 
                        iee, wi, iw, vdcl, pvdcl, exp, ie, elseq, nxt_, ixs, 
                        res_E, lst, nxt_E, temp_, flseq, temp_I, ifsqi, lseq, 
                        nxt_Ex, xxtemp1, temp2_, temp3_, temp4, exlsq, 
                        callStmt, prcd, svoci, temp, res_S, rprcd, rpvi, 
                        rpctemp, res_R, vrs, addExpr, pvexpr, pvi, stk, test, 
                        primeVars, sub, expr, sst, primedVars, localSub_, 
                        xlssi, xltemp1, temp1, temp2, temp3, res_X, sstsq, 
                        xprimedVars, localSub_X, res, xlsssqi, lsstsq, 
                        localSub, defSub, nxt, lsstqi, lsstemp, disjs, defs, 
                        str >>

IFW4 == /\ pc = "IFW4"
        /\ ifw' = ifw - 1
        /\ pc' = "IFW3"
        /\ UNCHANGED << i, j, gtemp1, gtemp2, gtemp3, gtemp4, result, rVal, 
                        pMap, prcdVars, procSeq, globalVars, nonGlobalVars, 
                        allVarSeq, localVars, stack, A, res_, ia, prcdr, ipr, 
                        proc, ip, lsseq, ilss, lstmt, whl, ls, ils, ilLast, 
                        ili, le, ile, fs, fi, ifi, ifLast, fe, ife, ife2, 
                        feSeq, feSeqLast, fw, fwLast, cr, icr, gt, sss, isss, 
                        ss, asg, ias, ifst, estmt, iee, wi, iw, vdcl, pvdcl, 
                        exp, ie, elseq, nxt_, ixs, res_E, lst, nxt_E, temp_, 
                        flseq, temp_I, ifsqi, lseq, nxt_Ex, xxtemp1, temp2_, 
                        temp3_, temp4, exlsq, callStmt, prcd, svoci, temp, 
                        res_S, rprcd, rpvi, rpctemp, res_R, vrs, addExpr, 
                        pvexpr, pvi, stk, test, primeVars, sub, expr, sst, 
                        primedVars, localSub_, xlssi, xltemp1, temp1, temp2, 
                        temp3, res_X, sstsq, xprimedVars, localSub_X, res, 
                        xlsssqi, lsstsq, localSub, defSub, nxt, lsstqi, 
                        lsstemp, disjs, defs, str >>

IFW5 == /\ pc = "IFW5"
        /\ pc' = Head(stack).pc
        /\ ifw' = Head(stack).ifw
        /\ fwLast' = Head(stack).fwLast
        /\ fw' = Head(stack).fw
        /\ stack' = Tail(stack)
        /\ UNCHANGED << i, j, gtemp1, gtemp2, gtemp3, gtemp4, result, rVal, 
                        pMap, prcdVars, procSeq, globalVars, nonGlobalVars, 
                        allVarSeq, localVars, A, res_, ia, prcdr, ipr, proc, 
                        ip, lsseq, ilss, lstmt, whl, ls, ils, ilLast, ili, le, 
                        ile, fs, fi, ifi, ifLast, fe, ife, ife2, feSeq, 
                        feSeqLast, cr, icr, gt, sss, isss, ss, asg, ias, ifst, 
                        estmt, iee, wi, iw, vdcl, pvdcl, exp, ie, elseq, nxt_, 
                        ixs, res_E, lst, nxt_E, temp_, flseq, temp_I, ifsqi, 
                        lseq, nxt_Ex, xxtemp1, temp2_, temp3_, temp4, exlsq, 
                        callStmt, prcd, svoci, temp, res_S, rprcd, rpvi, 
                        rpctemp, res_R, vrs, addExpr, pvexpr, pvi, stk, test, 
                        primeVars, sub, expr, sst, primedVars, localSub_, 
                        xlssi, xltemp1, temp1, temp2, temp3, res_X, sstsq, 
                        xprimedVars, localSub_X, res, xlsssqi, lsstsq, 
                        localSub, defSub, nxt, lsstqi, lsstemp, disjs, defs, 
                        str >>

IsFinalWith == IFW1 \/ IFW2 \/ IFW3 \/ IFW4 \/ IFW5

ICR1 == /\ pc = "ICR1"
        /\ IF cr.type = "call"
              THEN /\ Assert(DOMAIN cr = {"type", "returnTo", "to", "args"}, 
                             "Failure of assertion at line 421, column 24.")
                   /\ Assert(cr.returnTo \in STRING, 
                             "Failure of assertion at line 422, column 24.")
              ELSE /\ IF cr.type = "return"
                         THEN /\ Assert(DOMAIN cr = {"type", "from"}, 
                                        "Failure of assertion at line 424, column 24.")
                         ELSE /\ IF cr.type = "callReturn"
                                    THEN /\ Assert(DOMAIN cr = {"type", "from", "to", "args"}, 
                                                   "Failure of assertion at line 426, column 24.")
                                    ELSE /\ Assert(FALSE, 
                                                   "Failure of assertion at line 427, column 22.")
        /\ IF cr.type # "return"
              THEN /\ Assert(cr.to \in STRING, 
                             "Failure of assertion at line 430, column 24.")
                   /\ Assert(IsSeq(cr.args), 
                             "Failure of assertion at line 431, column 24.")
                   /\ icr' = Len(cr.args)
                   /\ pc' = "ICR2"
              ELSE /\ pc' = "ICR4"
                   /\ UNCHANGED icr
        /\ UNCHANGED << i, j, gtemp1, gtemp2, gtemp3, gtemp4, result, rVal, 
                        pMap, prcdVars, procSeq, globalVars, nonGlobalVars, 
                        allVarSeq, localVars, stack, A, res_, ia, prcdr, ipr, 
                        proc, ip, lsseq, ilss, lstmt, whl, ls, ils, ilLast, 
                        ili, le, ile, fs, fi, ifi, ifLast, fe, ife, ife2, 
                        feSeq, feSeqLast, fw, ifw, fwLast, cr, gt, sss, isss, 
                        ss, asg, ias, ifst, estmt, iee, wi, iw, vdcl, pvdcl, 
                        exp, ie, elseq, nxt_, ixs, res_E, lst, nxt_E, temp_, 
                        flseq, temp_I, ifsqi, lseq, nxt_Ex, xxtemp1, temp2_, 
                        temp3_, temp4, exlsq, callStmt, prcd, svoci, temp, 
                        res_S, rprcd, rpvi, rpctemp, res_R, vrs, addExpr, 
                        pvexpr, pvi, stk, test, primeVars, sub, expr, sst, 
                        primedVars, localSub_, xlssi, xltemp1, temp1, temp2, 
                        temp3, res_X, sstsq, xprimedVars, localSub_X, res, 
                        xlsssqi, lsstsq, localSub, defSub, nxt, lsstqi, 
                        lsstemp, disjs, defs, str >>

ICR2 == /\ pc = "ICR2"
        /\ IF icr > 0
              THEN /\ /\ exp' = cr.args[icr]
                      /\ stack' = << [ procedure |->  "IsExpr",
                                       pc        |->  "ICR3",
                                       ie        |->  ie,
                                       exp       |->  exp ] >>
                                   \o stack
                   /\ ie' = {}
                   /\ pc' = "IE1"
              ELSE /\ pc' = "ICR4"
                   /\ UNCHANGED << stack, exp, ie >>
        /\ UNCHANGED << i, j, gtemp1, gtemp2, gtemp3, gtemp4, result, rVal, 
                        pMap, prcdVars, procSeq, globalVars, nonGlobalVars, 
                        allVarSeq, localVars, A, res_, ia, prcdr, ipr, proc, 
                        ip, lsseq, ilss, lstmt, whl, ls, ils, ilLast, ili, le, 
                        ile, fs, fi, ifi, ifLast, fe, ife, ife2, feSeq, 
                        feSeqLast, fw, ifw, fwLast, cr, icr, gt, sss, isss, ss, 
                        asg, ias, ifst, estmt, iee, wi, iw, vdcl, pvdcl, elseq, 
                        nxt_, ixs, res_E, lst, nxt_E, temp_, flseq, temp_I, 
                        ifsqi, lseq, nxt_Ex, xxtemp1, temp2_, temp3_, temp4, 
                        exlsq, callStmt, prcd, svoci, temp, res_S, rprcd, rpvi, 
                        rpctemp, res_R, vrs, addExpr, pvexpr, pvi, stk, test, 
                        primeVars, sub, expr, sst, primedVars, localSub_, 
                        xlssi, xltemp1, temp1, temp2, temp3, res_X, sstsq, 
                        xprimedVars, localSub_X, res, xlsssqi, lsstsq, 
                        localSub, defSub, nxt, lsstqi, lsstemp, disjs, defs, 
                        str >>

ICR3 == /\ pc = "ICR3"
        /\ icr' = icr - 1
        /\ pc' = "ICR2"
        /\ UNCHANGED << i, j, gtemp1, gtemp2, gtemp3, gtemp4, result, rVal, 
                        pMap, prcdVars, procSeq, globalVars, nonGlobalVars, 
                        allVarSeq, localVars, stack, A, res_, ia, prcdr, ipr, 
                        proc, ip, lsseq, ilss, lstmt, whl, ls, ils, ilLast, 
                        ili, le, ile, fs, fi, ifi, ifLast, fe, ife, ife2, 
                        feSeq, feSeqLast, fw, ifw, fwLast, cr, gt, sss, isss, 
                        ss, asg, ias, ifst, estmt, iee, wi, iw, vdcl, pvdcl, 
                        exp, ie, elseq, nxt_, ixs, res_E, lst, nxt_E, temp_, 
                        flseq, temp_I, ifsqi, lseq, nxt_Ex, xxtemp1, temp2_, 
                        temp3_, temp4, exlsq, callStmt, prcd, svoci, temp, 
                        res_S, rprcd, rpvi, rpctemp, res_R, vrs, addExpr, 
                        pvexpr, pvi, stk, test, primeVars, sub, expr, sst, 
                        primedVars, localSub_, xlssi, xltemp1, temp1, temp2, 
                        temp3, res_X, sstsq, xprimedVars, localSub_X, res, 
                        xlsssqi, lsstsq, localSub, defSub, nxt, lsstqi, 
                        lsstemp, disjs, defs, str >>

ICR4 == /\ pc = "ICR4"
        /\ IF cr.type # "call"
              THEN /\ Assert(cr.from \in STRING, 
                             "Failure of assertion at line 439, column 24.")
              ELSE /\ TRUE
        /\ pc' = Head(stack).pc
        /\ icr' = Head(stack).icr
        /\ cr' = Head(stack).cr
        /\ stack' = Tail(stack)
        /\ UNCHANGED << i, j, gtemp1, gtemp2, gtemp3, gtemp4, result, rVal, 
                        pMap, prcdVars, procSeq, globalVars, nonGlobalVars, 
                        allVarSeq, localVars, A, res_, ia, prcdr, ipr, proc, 
                        ip, lsseq, ilss, lstmt, whl, ls, ils, ilLast, ili, le, 
                        ile, fs, fi, ifi, ifLast, fe, ife, ife2, feSeq, 
                        feSeqLast, fw, ifw, fwLast, gt, sss, isss, ss, asg, 
                        ias, ifst, estmt, iee, wi, iw, vdcl, pvdcl, exp, ie, 
                        elseq, nxt_, ixs, res_E, lst, nxt_E, temp_, flseq, 
                        temp_I, ifsqi, lseq, nxt_Ex, xxtemp1, temp2_, temp3_, 
                        temp4, exlsq, callStmt, prcd, svoci, temp, res_S, 
                        rprcd, rpvi, rpctemp, res_R, vrs, addExpr, pvexpr, pvi, 
                        stk, test, primeVars, sub, expr, sst, primedVars, 
                        localSub_, xlssi, xltemp1, temp1, temp2, temp3, res_X, 
                        sstsq, xprimedVars, localSub_X, res, xlsssqi, lsstsq, 
                        localSub, defSub, nxt, lsstqi, lsstemp, disjs, defs, 
                        str >>

IsCallOrReturn == ICR1 \/ ICR2 \/ ICR3 \/ ICR4

IGT1 == /\ pc = "IGT1"
        /\ Assert(DOMAIN gt = {"type", "to"}, 
                  "Failure of assertion at line 448, column 17.")
        /\ Assert(gt.to \in STRING, 
                  "Failure of assertion at line 449, column 17.")
        /\ pc' = Head(stack).pc
        /\ gt' = Head(stack).gt
        /\ stack' = Tail(stack)
        /\ UNCHANGED << i, j, gtemp1, gtemp2, gtemp3, gtemp4, result, rVal, 
                        pMap, prcdVars, procSeq, globalVars, nonGlobalVars, 
                        allVarSeq, localVars, A, res_, ia, prcdr, ipr, proc, 
                        ip, lsseq, ilss, lstmt, whl, ls, ils, ilLast, ili, le, 
                        ile, fs, fi, ifi, ifLast, fe, ife, ife2, feSeq, 
                        feSeqLast, fw, ifw, fwLast, cr, icr, sss, isss, ss, 
                        asg, ias, ifst, estmt, iee, wi, iw, vdcl, pvdcl, exp, 
                        ie, elseq, nxt_, ixs, res_E, lst, nxt_E, temp_, flseq, 
                        temp_I, ifsqi, lseq, nxt_Ex, xxtemp1, temp2_, temp3_, 
                        temp4, exlsq, callStmt, prcd, svoci, temp, res_S, 
                        rprcd, rpvi, rpctemp, res_R, vrs, addExpr, pvexpr, pvi, 
                        stk, test, primeVars, sub, expr, sst, primedVars, 
                        localSub_, xlssi, xltemp1, temp1, temp2, temp3, res_X, 
                        sstsq, xprimedVars, localSub_X, res, xlsssqi, lsstsq, 
                        localSub, defSub, nxt, lsstqi, lsstemp, disjs, defs, 
                        str >>

IsGoto == IGT1

ISSS1 == /\ pc = "ISSS1"
         /\ Assert(IsSeq(sss), 
                   "Failure of assertion at line 458, column 18.")
         /\ isss' = Len(sss)
         /\ pc' = "ISSS2"
         /\ UNCHANGED << i, j, gtemp1, gtemp2, gtemp3, gtemp4, result, rVal, 
                         pMap, prcdVars, procSeq, globalVars, nonGlobalVars, 
                         allVarSeq, localVars, stack, A, res_, ia, prcdr, ipr, 
                         proc, ip, lsseq, ilss, lstmt, whl, ls, ils, ilLast, 
                         ili, le, ile, fs, fi, ifi, ifLast, fe, ife, ife2, 
                         feSeq, feSeqLast, fw, ifw, fwLast, cr, icr, gt, sss, 
                         ss, asg, ias, ifst, estmt, iee, wi, iw, vdcl, pvdcl, 
                         exp, ie, elseq, nxt_, ixs, res_E, lst, nxt_E, temp_, 
                         flseq, temp_I, ifsqi, lseq, nxt_Ex, xxtemp1, temp2_, 
                         temp3_, temp4, exlsq, callStmt, prcd, svoci, temp, 
                         res_S, rprcd, rpvi, rpctemp, res_R, vrs, addExpr, 
                         pvexpr, pvi, stk, test, primeVars, sub, expr, sst, 
                         primedVars, localSub_, xlssi, xltemp1, temp1, temp2, 
                         temp3, res_X, sstsq, xprimedVars, localSub_X, res, 
                         xlsssqi, lsstsq, localSub, defSub, nxt, lsstqi, 
                         lsstemp, disjs, defs, str >>

ISSS2 == /\ pc = "ISSS2"
         /\ IF isss > 0
               THEN /\ /\ ss' = sss[isss]
                       /\ stack' = << [ procedure |->  "IsSimpleStmt",
                                        pc        |->  "ISSS3",
                                        ss        |->  ss ] >>
                                    \o stack
                    /\ pc' = "ISS1"
               ELSE /\ pc' = "ISSS4"
                    /\ UNCHANGED << stack, ss >>
         /\ UNCHANGED << i, j, gtemp1, gtemp2, gtemp3, gtemp4, result, rVal, 
                         pMap, prcdVars, procSeq, globalVars, nonGlobalVars, 
                         allVarSeq, localVars, A, res_, ia, prcdr, ipr, proc, 
                         ip, lsseq, ilss, lstmt, whl, ls, ils, ilLast, ili, le, 
                         ile, fs, fi, ifi, ifLast, fe, ife, ife2, feSeq, 
                         feSeqLast, fw, ifw, fwLast, cr, icr, gt, sss, isss, 
                         asg, ias, ifst, estmt, iee, wi, iw, vdcl, pvdcl, exp, 
                         ie, elseq, nxt_, ixs, res_E, lst, nxt_E, temp_, flseq, 
                         temp_I, ifsqi, lseq, nxt_Ex, xxtemp1, temp2_, temp3_, 
                         temp4, exlsq, callStmt, prcd, svoci, temp, res_S, 
                         rprcd, rpvi, rpctemp, res_R, vrs, addExpr, pvexpr, 
                         pvi, stk, test, primeVars, sub, expr, sst, primedVars, 
                         localSub_, xlssi, xltemp1, temp1, temp2, temp3, res_X, 
                         sstsq, xprimedVars, localSub_X, res, xlsssqi, lsstsq, 
                         localSub, defSub, nxt, lsstqi, lsstemp, disjs, defs, 
                         str >>

ISSS3 == /\ pc = "ISSS3"
         /\ isss' = isss - 1
         /\ pc' = "ISSS2"
         /\ UNCHANGED << i, j, gtemp1, gtemp2, gtemp3, gtemp4, result, rVal, 
                         pMap, prcdVars, procSeq, globalVars, nonGlobalVars, 
                         allVarSeq, localVars, stack, A, res_, ia, prcdr, ipr, 
                         proc, ip, lsseq, ilss, lstmt, whl, ls, ils, ilLast, 
                         ili, le, ile, fs, fi, ifi, ifLast, fe, ife, ife2, 
                         feSeq, feSeqLast, fw, ifw, fwLast, cr, icr, gt, sss, 
                         ss, asg, ias, ifst, estmt, iee, wi, iw, vdcl, pvdcl, 
                         exp, ie, elseq, nxt_, ixs, res_E, lst, nxt_E, temp_, 
                         flseq, temp_I, ifsqi, lseq, nxt_Ex, xxtemp1, temp2_, 
                         temp3_, temp4, exlsq, callStmt, prcd, svoci, temp, 
                         res_S, rprcd, rpvi, rpctemp, res_R, vrs, addExpr, 
                         pvexpr, pvi, stk, test, primeVars, sub, expr, sst, 
                         primedVars, localSub_, xlssi, xltemp1, temp1, temp2, 
                         temp3, res_X, sstsq, xprimedVars, localSub_X, res, 
                         xlsssqi, lsstsq, localSub, defSub, nxt, lsstqi, 
                         lsstemp, disjs, defs, str >>

ISSS4 == /\ pc = "ISSS4"
         /\ pc' = Head(stack).pc
         /\ isss' = Head(stack).isss
         /\ sss' = Head(stack).sss
         /\ stack' = Tail(stack)
         /\ UNCHANGED << i, j, gtemp1, gtemp2, gtemp3, gtemp4, result, rVal, 
                         pMap, prcdVars, procSeq, globalVars, nonGlobalVars, 
                         allVarSeq, localVars, A, res_, ia, prcdr, ipr, proc, 
                         ip, lsseq, ilss, lstmt, whl, ls, ils, ilLast, ili, le, 
                         ile, fs, fi, ifi, ifLast, fe, ife, ife2, feSeq, 
                         feSeqLast, fw, ifw, fwLast, cr, icr, gt, ss, asg, ias, 
                         ifst, estmt, iee, wi, iw, vdcl, pvdcl, exp, ie, elseq, 
                         nxt_, ixs, res_E, lst, nxt_E, temp_, flseq, temp_I, 
                         ifsqi, lseq, nxt_Ex, xxtemp1, temp2_, temp3_, temp4, 
                         exlsq, callStmt, prcd, svoci, temp, res_S, rprcd, 
                         rpvi, rpctemp, res_R, vrs, addExpr, pvexpr, pvi, stk, 
                         test, primeVars, sub, expr, sst, primedVars, 
                         localSub_, xlssi, xltemp1, temp1, temp2, temp3, res_X, 
                         sstsq, xprimedVars, localSub_X, res, xlsssqi, lsstsq, 
                         localSub, defSub, nxt, lsstqi, lsstemp, disjs, defs, 
                         str >>

IsSimpleStmtSeq == ISSS1 \/ ISSS2 \/ ISSS3 \/ ISSS4

ISS1 == /\ pc = "ISS1"
        /\ IF ss.type = "assignment"
              THEN /\ /\ asg' = ss
                      /\ stack' = << [ procedure |->  "IsAssign",
                                       pc        |->  "ISS2",
                                       ias       |->  ias,
                                       asg       |->  asg ] >>
                                   \o stack
                   /\ ias' = {}
                   /\ pc' = "IAS1"
                   /\ UNCHANGED << ifst, estmt, iee, wi, iw, exp, ie >>
              ELSE /\ IF ss.type = "if"
                         THEN /\ /\ ifst' = ss
                                 /\ stack' = << [ procedure |->  "IsIf",
                                                  pc        |->  "ISS2",
                                                  ifst      |->  ifst ] >>
                                              \o stack
                              /\ pc' = "IIF1"
                              /\ UNCHANGED << estmt, iee, wi, iw, exp, ie >>
                         ELSE /\ IF ss.type = "either"
                                    THEN /\ /\ estmt' = ss
                                            /\ stack' = << [ procedure |->  "IsEither",
                                                             pc        |->  "ISS2",
                                                             iee       |->  iee,
                                                             estmt     |->  estmt ] >>
                                                         \o stack
                                         /\ iee' = {}
                                         /\ pc' = "ISE1"
                                         /\ UNCHANGED << wi, iw, exp, ie >>
                                    ELSE /\ IF ss.type = "with"
                                               THEN /\ /\ stack' = << [ procedure |->  "IsWith",
                                                                        pc        |->  "ISS2",
                                                                        iw        |->  iw,
                                                                        wi        |->  wi ] >>
                                                                    \o stack
                                                       /\ wi' = ss
                                                    /\ iw' = {}
                                                    /\ pc' = "IWI1"
                                                    /\ UNCHANGED << exp, ie >>
                                               ELSE /\ IF ss.type \in {"when", "assert", "print"}
                                                          THEN /\ /\ exp' = ss.exp
                                                                  /\ stack' = << [ procedure |->  "IsExpr",
                                                                                   pc        |->  "ISS2",
                                                                                   ie        |->  ie,
                                                                                   exp       |->  exp ] >>
                                                                               \o stack
                                                               /\ ie' = {}
                                                               /\ pc' = "IE1"
                                                          ELSE /\ IF ss.type = "skip"
                                                                     THEN /\ TRUE
                                                                     ELSE /\ Assert(FALSE, 
                                                                                    "Failure of assertion at line 487, column 22.")
                                                               /\ pc' = "ISS2"
                                                               /\ UNCHANGED << stack, 
                                                                               exp, 
                                                                               ie >>
                                                    /\ UNCHANGED << wi, iw >>
                                         /\ UNCHANGED << estmt, iee >>
                              /\ UNCHANGED ifst
                   /\ UNCHANGED << asg, ias >>
        /\ UNCHANGED << i, j, gtemp1, gtemp2, gtemp3, gtemp4, result, rVal, 
                        pMap, prcdVars, procSeq, globalVars, nonGlobalVars, 
                        allVarSeq, localVars, A, res_, ia, prcdr, ipr, proc, 
                        ip, lsseq, ilss, lstmt, whl, ls, ils, ilLast, ili, le, 
                        ile, fs, fi, ifi, ifLast, fe, ife, ife2, feSeq, 
                        feSeqLast, fw, ifw, fwLast, cr, icr, gt, sss, isss, ss, 
                        vdcl, pvdcl, elseq, nxt_, ixs, res_E, lst, nxt_E, 
                        temp_, flseq, temp_I, ifsqi, lseq, nxt_Ex, xxtemp1, 
                        temp2_, temp3_, temp4, exlsq, callStmt, prcd, svoci, 
                        temp, res_S, rprcd, rpvi, rpctemp, res_R, vrs, addExpr, 
                        pvexpr, pvi, stk, test, primeVars, sub, expr, sst, 
                        primedVars, localSub_, xlssi, xltemp1, temp1, temp2, 
                        temp3, res_X, sstsq, xprimedVars, localSub_X, res, 
                        xlsssqi, lsstsq, localSub, defSub, nxt, lsstqi, 
                        lsstemp, disjs, defs, str >>

ISS2 == /\ pc = "ISS2"
        /\ pc' = Head(stack).pc
        /\ ss' = Head(stack).ss
        /\ stack' = Tail(stack)
        /\ UNCHANGED << i, j, gtemp1, gtemp2, gtemp3, gtemp4, result, rVal, 
                        pMap, prcdVars, procSeq, globalVars, nonGlobalVars, 
                        allVarSeq, localVars, A, res_, ia, prcdr, ipr, proc, 
                        ip, lsseq, ilss, lstmt, whl, ls, ils, ilLast, ili, le, 
                        ile, fs, fi, ifi, ifLast, fe, ife, ife2, feSeq, 
                        feSeqLast, fw, ifw, fwLast, cr, icr, gt, sss, isss, 
                        asg, ias, ifst, estmt, iee, wi, iw, vdcl, pvdcl, exp, 
                        ie, elseq, nxt_, ixs, res_E, lst, nxt_E, temp_, flseq, 
                        temp_I, ifsqi, lseq, nxt_Ex, xxtemp1, temp2_, temp3_, 
                        temp4, exlsq, callStmt, prcd, svoci, temp, res_S, 
                        rprcd, rpvi, rpctemp, res_R, vrs, addExpr, pvexpr, pvi, 
                        stk, test, primeVars, sub, expr, sst, primedVars, 
                        localSub_, xlssi, xltemp1, temp1, temp2, temp3, res_X, 
                        sstsq, xprimedVars, localSub_X, res, xlsssqi, lsstsq, 
                        localSub, defSub, nxt, lsstqi, lsstemp, disjs, defs, 
                        str >>

IsSimpleStmt == ISS1 \/ ISS2

IAS1 == /\ pc = "IAS1"
        /\ Assert(DOMAIN asg = {"type", "ass"}, 
                  "Failure of assertion at line 499, column 17.")
        /\ Assert(IsNonemptySeq(asg.ass), 
                  "Failure of assertion at line 500, column 17.")
        /\ ias' = Len(asg.ass)
        /\ pc' = "IAS2"
        /\ UNCHANGED << i, j, gtemp1, gtemp2, gtemp3, gtemp4, result, rVal, 
                        pMap, prcdVars, procSeq, globalVars, nonGlobalVars, 
                        allVarSeq, localVars, stack, A, res_, ia, prcdr, ipr, 
                        proc, ip, lsseq, ilss, lstmt, whl, ls, ils, ilLast, 
                        ili, le, ile, fs, fi, ifi, ifLast, fe, ife, ife2, 
                        feSeq, feSeqLast, fw, ifw, fwLast, cr, icr, gt, sss, 
                        isss, ss, asg, ifst, estmt, iee, wi, iw, vdcl, pvdcl, 
                        exp, ie, elseq, nxt_, ixs, res_E, lst, nxt_E, temp_, 
                        flseq, temp_I, ifsqi, lseq, nxt_Ex, xxtemp1, temp2_, 
                        temp3_, temp4, exlsq, callStmt, prcd, svoci, temp, 
                        res_S, rprcd, rpvi, rpctemp, res_R, vrs, addExpr, 
                        pvexpr, pvi, stk, test, primeVars, sub, expr, sst, 
                        primedVars, localSub_, xlssi, xltemp1, temp1, temp2, 
                        temp3, res_X, sstsq, xprimedVars, localSub_X, res, 
                        xlsssqi, lsstsq, localSub, defSub, nxt, lsstqi, 
                        lsstemp, disjs, defs, str >>

IAS2 == /\ pc = "IAS2"
        /\ IF ias > 0
              THEN /\ Assert(DOMAIN asg.ass[ias] = {"lhs", "rhs"}, 
                             "Failure of assertion at line 503, column 19.")
                   /\ /\ exp' = asg.ass[ias].rhs
                      /\ stack' = << [ procedure |->  "IsExpr",
                                       pc        |->  "IAS3",
                                       ie        |->  ie,
                                       exp       |->  exp ] >>
                                   \o stack
                   /\ ie' = {}
                   /\ pc' = "IE1"
              ELSE /\ pc' = "IAS5"
                   /\ UNCHANGED << stack, exp, ie >>
        /\ UNCHANGED << i, j, gtemp1, gtemp2, gtemp3, gtemp4, result, rVal, 
                        pMap, prcdVars, procSeq, globalVars, nonGlobalVars, 
                        allVarSeq, localVars, A, res_, ia, prcdr, ipr, proc, 
                        ip, lsseq, ilss, lstmt, whl, ls, ils, ilLast, ili, le, 
                        ile, fs, fi, ifi, ifLast, fe, ife, ife2, feSeq, 
                        feSeqLast, fw, ifw, fwLast, cr, icr, gt, sss, isss, ss, 
                        asg, ias, ifst, estmt, iee, wi, iw, vdcl, pvdcl, elseq, 
                        nxt_, ixs, res_E, lst, nxt_E, temp_, flseq, temp_I, 
                        ifsqi, lseq, nxt_Ex, xxtemp1, temp2_, temp3_, temp4, 
                        exlsq, callStmt, prcd, svoci, temp, res_S, rprcd, rpvi, 
                        rpctemp, res_R, vrs, addExpr, pvexpr, pvi, stk, test, 
                        primeVars, sub, expr, sst, primedVars, localSub_, 
                        xlssi, xltemp1, temp1, temp2, temp3, res_X, sstsq, 
                        xprimedVars, localSub_X, res, xlsssqi, lsstsq, 
                        localSub, defSub, nxt, lsstqi, lsstemp, disjs, defs, 
                        str >>

IAS3 == /\ pc = "IAS3"
        /\ Assert(DOMAIN asg.ass[ias].lhs = {"var", "sub"}, 
                  "Failure of assertion at line 505, column 19.")
        /\ Assert(asg.ass[ias].lhs.var \in STRING, 
                  "Failure of assertion at line 506, column 19.")
        /\ /\ exp' = asg.ass[ias].lhs.sub
           /\ stack' = << [ procedure |->  "IsExpr",
                            pc        |->  "IAS4",
                            ie        |->  ie,
                            exp       |->  exp ] >>
                        \o stack
        /\ ie' = {}
        /\ pc' = "IE1"
        /\ UNCHANGED << i, j, gtemp1, gtemp2, gtemp3, gtemp4, result, rVal, 
                        pMap, prcdVars, procSeq, globalVars, nonGlobalVars, 
                        allVarSeq, localVars, A, res_, ia, prcdr, ipr, proc, 
                        ip, lsseq, ilss, lstmt, whl, ls, ils, ilLast, ili, le, 
                        ile, fs, fi, ifi, ifLast, fe, ife, ife2, feSeq, 
                        feSeqLast, fw, ifw, fwLast, cr, icr, gt, sss, isss, ss, 
                        asg, ias, ifst, estmt, iee, wi, iw, vdcl, pvdcl, elseq, 
                        nxt_, ixs, res_E, lst, nxt_E, temp_, flseq, temp_I, 
                        ifsqi, lseq, nxt_Ex, xxtemp1, temp2_, temp3_, temp4, 
                        exlsq, callStmt, prcd, svoci, temp, res_S, rprcd, rpvi, 
                        rpctemp, res_R, vrs, addExpr, pvexpr, pvi, stk, test, 
                        primeVars, sub, expr, sst, primedVars, localSub_, 
                        xlssi, xltemp1, temp1, temp2, temp3, res_X, sstsq, 
                        xprimedVars, localSub_X, res, xlsssqi, lsstsq, 
                        localSub, defSub, nxt, lsstqi, lsstemp, disjs, defs, 
                        str >>

IAS4 == /\ pc = "IAS4"
        /\ ias' = ias - 1
        /\ pc' = "IAS2"
        /\ UNCHANGED << i, j, gtemp1, gtemp2, gtemp3, gtemp4, result, rVal, 
                        pMap, prcdVars, procSeq, globalVars, nonGlobalVars, 
                        allVarSeq, localVars, stack, A, res_, ia, prcdr, ipr, 
                        proc, ip, lsseq, ilss, lstmt, whl, ls, ils, ilLast, 
                        ili, le, ile, fs, fi, ifi, ifLast, fe, ife, ife2, 
                        feSeq, feSeqLast, fw, ifw, fwLast, cr, icr, gt, sss, 
                        isss, ss, asg, ifst, estmt, iee, wi, iw, vdcl, pvdcl, 
                        exp, ie, elseq, nxt_, ixs, res_E, lst, nxt_E, temp_, 
                        flseq, temp_I, ifsqi, lseq, nxt_Ex, xxtemp1, temp2_, 
                        temp3_, temp4, exlsq, callStmt, prcd, svoci, temp, 
                        res_S, rprcd, rpvi, rpctemp, res_R, vrs, addExpr, 
                        pvexpr, pvi, stk, test, primeVars, sub, expr, sst, 
                        primedVars, localSub_, xlssi, xltemp1, temp1, temp2, 
                        temp3, res_X, sstsq, xprimedVars, localSub_X, res, 
                        xlsssqi, lsstsq, localSub, defSub, nxt, lsstqi, 
                        lsstemp, disjs, defs, str >>

IAS5 == /\ pc = "IAS5"
        /\ pc' = Head(stack).pc
        /\ ias' = Head(stack).ias
        /\ asg' = Head(stack).asg
        /\ stack' = Tail(stack)
        /\ UNCHANGED << i, j, gtemp1, gtemp2, gtemp3, gtemp4, result, rVal, 
                        pMap, prcdVars, procSeq, globalVars, nonGlobalVars, 
                        allVarSeq, localVars, A, res_, ia, prcdr, ipr, proc, 
                        ip, lsseq, ilss, lstmt, whl, ls, ils, ilLast, ili, le, 
                        ile, fs, fi, ifi, ifLast, fe, ife, ife2, feSeq, 
                        feSeqLast, fw, ifw, fwLast, cr, icr, gt, sss, isss, ss, 
                        ifst, estmt, iee, wi, iw, vdcl, pvdcl, exp, ie, elseq, 
                        nxt_, ixs, res_E, lst, nxt_E, temp_, flseq, temp_I, 
                        ifsqi, lseq, nxt_Ex, xxtemp1, temp2_, temp3_, temp4, 
                        exlsq, callStmt, prcd, svoci, temp, res_S, rprcd, rpvi, 
                        rpctemp, res_R, vrs, addExpr, pvexpr, pvi, stk, test, 
                        primeVars, sub, expr, sst, primedVars, localSub_, 
                        xlssi, xltemp1, temp1, temp2, temp3, res_X, sstsq, 
                        xprimedVars, localSub_X, res, xlsssqi, lsstsq, 
                        localSub, defSub, nxt, lsstqi, lsstemp, disjs, defs, 
                        str >>

IsAssign == IAS1 \/ IAS2 \/ IAS3 \/ IAS4 \/ IAS5

IIF1 == /\ pc = "IIF1"
        /\ Assert(DOMAIN ifst = {"type", "test", "then", "else"}, 
                  "Failure of assertion at line 520, column 17.")
        /\ /\ exp' = ifst.test
           /\ stack' = << [ procedure |->  "IsExpr",
                            pc        |->  "IIF2",
                            ie        |->  ie,
                            exp       |->  exp ] >>
                        \o stack
        /\ ie' = {}
        /\ pc' = "IE1"
        /\ UNCHANGED << i, j, gtemp1, gtemp2, gtemp3, gtemp4, result, rVal, 
                        pMap, prcdVars, procSeq, globalVars, nonGlobalVars, 
                        allVarSeq, localVars, A, res_, ia, prcdr, ipr, proc, 
                        ip, lsseq, ilss, lstmt, whl, ls, ils, ilLast, ili, le, 
                        ile, fs, fi, ifi, ifLast, fe, ife, ife2, feSeq, 
                        feSeqLast, fw, ifw, fwLast, cr, icr, gt, sss, isss, ss, 
                        asg, ias, ifst, estmt, iee, wi, iw, vdcl, pvdcl, elseq, 
                        nxt_, ixs, res_E, lst, nxt_E, temp_, flseq, temp_I, 
                        ifsqi, lseq, nxt_Ex, xxtemp1, temp2_, temp3_, temp4, 
                        exlsq, callStmt, prcd, svoci, temp, res_S, rprcd, rpvi, 
                        rpctemp, res_R, vrs, addExpr, pvexpr, pvi, stk, test, 
                        primeVars, sub, expr, sst, primedVars, localSub_, 
                        xlssi, xltemp1, temp1, temp2, temp3, res_X, sstsq, 
                        xprimedVars, localSub_X, res, xlsssqi, lsstsq, 
                        localSub, defSub, nxt, lsstqi, lsstemp, disjs, defs, 
                        str >>

IIF2 == /\ pc = "IIF2"
        /\ /\ sss' = ifst.then
           /\ stack' = << [ procedure |->  "IsSimpleStmtSeq",
                            pc        |->  "IIF3",
                            isss      |->  isss,
                            sss       |->  sss ] >>
                        \o stack
        /\ isss' = {}
        /\ pc' = "ISSS1"
        /\ UNCHANGED << i, j, gtemp1, gtemp2, gtemp3, gtemp4, result, rVal, 
                        pMap, prcdVars, procSeq, globalVars, nonGlobalVars, 
                        allVarSeq, localVars, A, res_, ia, prcdr, ipr, proc, 
                        ip, lsseq, ilss, lstmt, whl, ls, ils, ilLast, ili, le, 
                        ile, fs, fi, ifi, ifLast, fe, ife, ife2, feSeq, 
                        feSeqLast, fw, ifw, fwLast, cr, icr, gt, ss, asg, ias, 
                        ifst, estmt, iee, wi, iw, vdcl, pvdcl, exp, ie, elseq, 
                        nxt_, ixs, res_E, lst, nxt_E, temp_, flseq, temp_I, 
                        ifsqi, lseq, nxt_Ex, xxtemp1, temp2_, temp3_, temp4, 
                        exlsq, callStmt, prcd, svoci, temp, res_S, rprcd, rpvi, 
                        rpctemp, res_R, vrs, addExpr, pvexpr, pvi, stk, test, 
                        primeVars, sub, expr, sst, primedVars, localSub_, 
                        xlssi, xltemp1, temp1, temp2, temp3, res_X, sstsq, 
                        xprimedVars, localSub_X, res, xlsssqi, lsstsq, 
                        localSub, defSub, nxt, lsstqi, lsstemp, disjs, defs, 
                        str >>

IIF3 == /\ pc = "IIF3"
        /\ /\ sss' = ifst.else
           /\ stack' = << [ procedure |->  "IsSimpleStmtSeq",
                            pc        |->  Head(stack).pc,
                            isss      |->  isss,
                            sss       |->  sss ] >>
                        \o Tail(stack)
        /\ isss' = {}
        /\ pc' = "ISSS1"
        /\ UNCHANGED << i, j, gtemp1, gtemp2, gtemp3, gtemp4, result, rVal, 
                        pMap, prcdVars, procSeq, globalVars, nonGlobalVars, 
                        allVarSeq, localVars, A, res_, ia, prcdr, ipr, proc, 
                        ip, lsseq, ilss, lstmt, whl, ls, ils, ilLast, ili, le, 
                        ile, fs, fi, ifi, ifLast, fe, ife, ife2, feSeq, 
                        feSeqLast, fw, ifw, fwLast, cr, icr, gt, ss, asg, ias, 
                        ifst, estmt, iee, wi, iw, vdcl, pvdcl, exp, ie, elseq, 
                        nxt_, ixs, res_E, lst, nxt_E, temp_, flseq, temp_I, 
                        ifsqi, lseq, nxt_Ex, xxtemp1, temp2_, temp3_, temp4, 
                        exlsq, callStmt, prcd, svoci, temp, res_S, rprcd, rpvi, 
                        rpctemp, res_R, vrs, addExpr, pvexpr, pvi, stk, test, 
                        primeVars, sub, expr, sst, primedVars, localSub_, 
                        xlssi, xltemp1, temp1, temp2, temp3, res_X, sstsq, 
                        xprimedVars, localSub_X, res, xlsssqi, lsstsq, 
                        localSub, defSub, nxt, lsstqi, lsstemp, disjs, defs, 
                        str >>

IsIf == IIF1 \/ IIF2 \/ IIF3

ISE1 == /\ pc = "ISE1"
        /\ Assert(DOMAIN estmt = {"type", "ors"}, 
                  "Failure of assertion at line 532, column 17.")
        /\ Assert(IsNonemptySeq(estmt.ors), 
                  "Failure of assertion at line 533, column 17.")
        /\ iee' = Len(estmt.ors)
        /\ pc' = "ISE2"
        /\ UNCHANGED << i, j, gtemp1, gtemp2, gtemp3, gtemp4, result, rVal, 
                        pMap, prcdVars, procSeq, globalVars, nonGlobalVars, 
                        allVarSeq, localVars, stack, A, res_, ia, prcdr, ipr, 
                        proc, ip, lsseq, ilss, lstmt, whl, ls, ils, ilLast, 
                        ili, le, ile, fs, fi, ifi, ifLast, fe, ife, ife2, 
                        feSeq, feSeqLast, fw, ifw, fwLast, cr, icr, gt, sss, 
                        isss, ss, asg, ias, ifst, estmt, wi, iw, vdcl, pvdcl, 
                        exp, ie, elseq, nxt_, ixs, res_E, lst, nxt_E, temp_, 
                        flseq, temp_I, ifsqi, lseq, nxt_Ex, xxtemp1, temp2_, 
                        temp3_, temp4, exlsq, callStmt, prcd, svoci, temp, 
                        res_S, rprcd, rpvi, rpctemp, res_R, vrs, addExpr, 
                        pvexpr, pvi, stk, test, primeVars, sub, expr, sst, 
                        primedVars, localSub_, xlssi, xltemp1, temp1, temp2, 
                        temp3, res_X, sstsq, xprimedVars, localSub_X, res, 
                        xlsssqi, lsstsq, localSub, defSub, nxt, lsstqi, 
                        lsstemp, disjs, defs, str >>

ISE2 == /\ pc = "ISE2"
        /\ IF iee > 0
              THEN /\ /\ sss' = estmt.ors[iee]
                      /\ stack' = << [ procedure |->  "IsSimpleStmtSeq",
                                       pc        |->  "ISE3",
                                       isss      |->  isss,
                                       sss       |->  sss ] >>
                                   \o stack
                   /\ isss' = {}
                   /\ pc' = "ISSS1"
                   /\ UNCHANGED << estmt, iee >>
              ELSE /\ pc' = Head(stack).pc
                   /\ iee' = Head(stack).iee
                   /\ estmt' = Head(stack).estmt
                   /\ stack' = Tail(stack)
                   /\ UNCHANGED << sss, isss >>
        /\ UNCHANGED << i, j, gtemp1, gtemp2, gtemp3, gtemp4, result, rVal, 
                        pMap, prcdVars, procSeq, globalVars, nonGlobalVars, 
                        allVarSeq, localVars, A, res_, ia, prcdr, ipr, proc, 
                        ip, lsseq, ilss, lstmt, whl, ls, ils, ilLast, ili, le, 
                        ile, fs, fi, ifi, ifLast, fe, ife, ife2, feSeq, 
                        feSeqLast, fw, ifw, fwLast, cr, icr, gt, ss, asg, ias, 
                        ifst, wi, iw, vdcl, pvdcl, exp, ie, elseq, nxt_, ixs, 
                        res_E, lst, nxt_E, temp_, flseq, temp_I, ifsqi, lseq, 
                        nxt_Ex, xxtemp1, temp2_, temp3_, temp4, exlsq, 
                        callStmt, prcd, svoci, temp, res_S, rprcd, rpvi, 
                        rpctemp, res_R, vrs, addExpr, pvexpr, pvi, stk, test, 
                        primeVars, sub, expr, sst, primedVars, localSub_, 
                        xlssi, xltemp1, temp1, temp2, temp3, res_X, sstsq, 
                        xprimedVars, localSub_X, res, xlsssqi, lsstsq, 
                        localSub, defSub, nxt, lsstqi, lsstemp, disjs, defs, 
                        str >>

ISE3 == /\ pc = "ISE3"
        /\ iee' = iee - 1
        /\ pc' = "ISE2"
        /\ UNCHANGED << i, j, gtemp1, gtemp2, gtemp3, gtemp4, result, rVal, 
                        pMap, prcdVars, procSeq, globalVars, nonGlobalVars, 
                        allVarSeq, localVars, stack, A, res_, ia, prcdr, ipr, 
                        proc, ip, lsseq, ilss, lstmt, whl, ls, ils, ilLast, 
                        ili, le, ile, fs, fi, ifi, ifLast, fe, ife, ife2, 
                        feSeq, feSeqLast, fw, ifw, fwLast, cr, icr, gt, sss, 
                        isss, ss, asg, ias, ifst, estmt, wi, iw, vdcl, pvdcl, 
                        exp, ie, elseq, nxt_, ixs, res_E, lst, nxt_E, temp_, 
                        flseq, temp_I, ifsqi, lseq, nxt_Ex, xxtemp1, temp2_, 
                        temp3_, temp4, exlsq, callStmt, prcd, svoci, temp, 
                        res_S, rprcd, rpvi, rpctemp, res_R, vrs, addExpr, 
                        pvexpr, pvi, stk, test, primeVars, sub, expr, sst, 
                        primedVars, localSub_, xlssi, xltemp1, temp1, temp2, 
                        temp3, res_X, sstsq, xprimedVars, localSub_X, res, 
                        xlsssqi, lsstsq, localSub, defSub, nxt, lsstqi, 
                        lsstemp, disjs, defs, str >>

IsEither == ISE1 \/ ISE2 \/ ISE3

IWI1 == /\ pc = "IWI1"
        /\ Assert(DOMAIN wi = {"type", "var", "eqOrIn", "exp", "do"}, 
                  "Failure of assertion at line 551, column 17.")
        /\ Assert(wi.var \in STRING, 
                  "Failure of assertion at line 552, column 17.")
        /\ Assert(wi.eqOrIn \in {"=", "\\in"}, 
                  "Failure of assertion at line 553, column 17.")
        /\ /\ exp' = wi.exp
           /\ stack' = << [ procedure |->  "IsExpr",
                            pc        |->  "IWI2",
                            ie        |->  ie,
                            exp       |->  exp ] >>
                        \o stack
        /\ ie' = {}
        /\ pc' = "IE1"
        /\ UNCHANGED << i, j, gtemp1, gtemp2, gtemp3, gtemp4, result, rVal, 
                        pMap, prcdVars, procSeq, globalVars, nonGlobalVars, 
                        allVarSeq, localVars, A, res_, ia, prcdr, ipr, proc, 
                        ip, lsseq, ilss, lstmt, whl, ls, ils, ilLast, ili, le, 
                        ile, fs, fi, ifi, ifLast, fe, ife, ife2, feSeq, 
                        feSeqLast, fw, ifw, fwLast, cr, icr, gt, sss, isss, ss, 
                        asg, ias, ifst, estmt, iee, wi, iw, vdcl, pvdcl, elseq, 
                        nxt_, ixs, res_E, lst, nxt_E, temp_, flseq, temp_I, 
                        ifsqi, lseq, nxt_Ex, xxtemp1, temp2_, temp3_, temp4, 
                        exlsq, callStmt, prcd, svoci, temp, res_S, rprcd, rpvi, 
                        rpctemp, res_R, vrs, addExpr, pvexpr, pvi, stk, test, 
                        primeVars, sub, expr, sst, primedVars, localSub_, 
                        xlssi, xltemp1, temp1, temp2, temp3, res_X, sstsq, 
                        xprimedVars, localSub_X, res, xlsssqi, lsstsq, 
                        localSub, defSub, nxt, lsstqi, lsstemp, disjs, defs, 
                        str >>

IWI2 == /\ pc = "IWI2"
        /\ Assert(IsNonemptySeq(wi.do), 
                  "Failure of assertion at line 555, column 17.")
        /\ /\ iw' = Head(stack).iw
           /\ sss' = wi.do
           /\ stack' = << [ procedure |->  "IsSimpleStmtSeq",
                            pc        |->  Head(stack).pc,
                            isss      |->  isss,
                            sss       |->  sss ] >>
                        \o Tail(stack)
        /\ isss' = {}
        /\ pc' = "ISSS1"
        /\ UNCHANGED << i, j, gtemp1, gtemp2, gtemp3, gtemp4, result, rVal, 
                        pMap, prcdVars, procSeq, globalVars, nonGlobalVars, 
                        allVarSeq, localVars, A, res_, ia, prcdr, ipr, proc, 
                        ip, lsseq, ilss, lstmt, whl, ls, ils, ilLast, ili, le, 
                        ile, fs, fi, ifi, ifLast, fe, ife, ife2, feSeq, 
                        feSeqLast, fw, ifw, fwLast, cr, icr, gt, ss, asg, ias, 
                        ifst, estmt, iee, wi, vdcl, pvdcl, exp, ie, elseq, 
                        nxt_, ixs, res_E, lst, nxt_E, temp_, flseq, temp_I, 
                        ifsqi, lseq, nxt_Ex, xxtemp1, temp2_, temp3_, temp4, 
                        exlsq, callStmt, prcd, svoci, temp, res_S, rprcd, rpvi, 
                        rpctemp, res_R, vrs, addExpr, pvexpr, pvi, stk, test, 
                        primeVars, sub, expr, sst, primedVars, localSub_, 
                        xlssi, xltemp1, temp1, temp2, temp3, res_X, sstsq, 
                        xprimedVars, localSub_X, res, xlsssqi, lsstsq, 
                        localSub, defSub, nxt, lsstqi, lsstemp, disjs, defs, 
                        str >>

IsWith == IWI1 \/ IWI2

IV1 == /\ pc = "IV1"
       /\ Assert(DOMAIN vdcl = {"var", "eqOrIn", "val"}, 
                 "Failure of assertion at line 565, column 17.")
       /\ Assert(vdcl.var \in STRING, 
                 "Failure of assertion at line 566, column 17.")
       /\ Assert(vdcl.eqOrIn \in {"=", "\\in"}, 
                 "Failure of assertion at line 567, column 17.")
       /\ /\ exp' = vdcl.val
          /\ stack' = << [ procedure |->  "IsExpr",
                           pc        |->  Head(stack).pc,
                           ie        |->  ie,
                           exp       |->  exp ] >>
                       \o Tail(stack)
       /\ ie' = {}
       /\ pc' = "IE1"
       /\ UNCHANGED << i, j, gtemp1, gtemp2, gtemp3, gtemp4, result, rVal, 
                       pMap, prcdVars, procSeq, globalVars, nonGlobalVars, 
                       allVarSeq, localVars, A, res_, ia, prcdr, ipr, proc, ip, 
                       lsseq, ilss, lstmt, whl, ls, ils, ilLast, ili, le, ile, 
                       fs, fi, ifi, ifLast, fe, ife, ife2, feSeq, feSeqLast, 
                       fw, ifw, fwLast, cr, icr, gt, sss, isss, ss, asg, ias, 
                       ifst, estmt, iee, wi, iw, vdcl, pvdcl, elseq, nxt_, ixs, 
                       res_E, lst, nxt_E, temp_, flseq, temp_I, ifsqi, lseq, 
                       nxt_Ex, xxtemp1, temp2_, temp3_, temp4, exlsq, callStmt, 
                       prcd, svoci, temp, res_S, rprcd, rpvi, rpctemp, res_R, 
                       vrs, addExpr, pvexpr, pvi, stk, test, primeVars, sub, 
                       expr, sst, primedVars, localSub_, xlssi, xltemp1, temp1, 
                       temp2, temp3, res_X, sstsq, xprimedVars, localSub_X, 
                       res, xlsssqi, lsstsq, localSub, defSub, nxt, lsstqi, 
                       lsstemp, disjs, defs, str >>

IsVarDecl == IV1

IPV1 == /\ pc = "IPV1"
        /\ Assert(DOMAIN pvdcl = {"var", "eqOrIn", "val"}, 
                  "Failure of assertion at line 576, column 17.")
        /\ Assert(pvdcl.var \in STRING, 
                  "Failure of assertion at line 577, column 17.")
        /\ Assert(pvdcl.eqOrIn = "=", 
                  "Failure of assertion at line 578, column 17.")
        /\ /\ exp' = pvdcl.val
           /\ stack' = << [ procedure |->  "IsExpr",
                            pc        |->  Head(stack).pc,
                            ie        |->  ie,
                            exp       |->  exp ] >>
                        \o Tail(stack)
        /\ ie' = {}
        /\ pc' = "IE1"
        /\ UNCHANGED << i, j, gtemp1, gtemp2, gtemp3, gtemp4, result, rVal, 
                        pMap, prcdVars, procSeq, globalVars, nonGlobalVars, 
                        allVarSeq, localVars, A, res_, ia, prcdr, ipr, proc, 
                        ip, lsseq, ilss, lstmt, whl, ls, ils, ilLast, ili, le, 
                        ile, fs, fi, ifi, ifLast, fe, ife, ife2, feSeq, 
                        feSeqLast, fw, ifw, fwLast, cr, icr, gt, sss, isss, ss, 
                        asg, ias, ifst, estmt, iee, wi, iw, vdcl, pvdcl, elseq, 
                        nxt_, ixs, res_E, lst, nxt_E, temp_, flseq, temp_I, 
                        ifsqi, lseq, nxt_Ex, xxtemp1, temp2_, temp3_, temp4, 
                        exlsq, callStmt, prcd, svoci, temp, res_S, rprcd, rpvi, 
                        rpctemp, res_R, vrs, addExpr, pvexpr, pvi, stk, test, 
                        primeVars, sub, expr, sst, primedVars, localSub_, 
                        xlssi, xltemp1, temp1, temp2, temp3, res_X, sstsq, 
                        xprimedVars, localSub_X, res, xlsssqi, lsstsq, 
                        localSub, defSub, nxt, lsstqi, lsstemp, disjs, defs, 
                        str >>

IsPVarDecl == IPV1

IE1 == /\ pc = "IE1"
       /\ Assert(IsSeq(exp), "Failure of assertion at line 588, column 17.")
       /\ ie' = Len(exp)
       /\ pc' = "IE2"
       /\ UNCHANGED << i, j, gtemp1, gtemp2, gtemp3, gtemp4, result, rVal, 
                       pMap, prcdVars, procSeq, globalVars, nonGlobalVars, 
                       allVarSeq, localVars, stack, A, res_, ia, prcdr, ipr, 
                       proc, ip, lsseq, ilss, lstmt, whl, ls, ils, ilLast, ili, 
                       le, ile, fs, fi, ifi, ifLast, fe, ife, ife2, feSeq, 
                       feSeqLast, fw, ifw, fwLast, cr, icr, gt, sss, isss, ss, 
                       asg, ias, ifst, estmt, iee, wi, iw, vdcl, pvdcl, exp, 
                       elseq, nxt_, ixs, res_E, lst, nxt_E, temp_, flseq, 
                       temp_I, ifsqi, lseq, nxt_Ex, xxtemp1, temp2_, temp3_, 
                       temp4, exlsq, callStmt, prcd, svoci, temp, res_S, rprcd, 
                       rpvi, rpctemp, res_R, vrs, addExpr, pvexpr, pvi, stk, 
                       test, primeVars, sub, expr, sst, primedVars, localSub_, 
                       xlssi, xltemp1, temp1, temp2, temp3, res_X, sstsq, 
                       xprimedVars, localSub_X, res, xlsssqi, lsstsq, localSub, 
                       defSub, nxt, lsstqi, lsstemp, disjs, defs, str >>

IE2 == /\ pc = "IE2"
       /\ IF ie > 0
             THEN /\ Assert(exp[ie] \in STRING, 
                            "Failure of assertion at line 590, column 32.")
                  /\ ie' = ie-1
                  /\ pc' = "IE2"
                  /\ UNCHANGED << stack, exp >>
             ELSE /\ pc' = Head(stack).pc
                  /\ ie' = Head(stack).ie
                  /\ exp' = Head(stack).exp
                  /\ stack' = Tail(stack)
       /\ UNCHANGED << i, j, gtemp1, gtemp2, gtemp3, gtemp4, result, rVal, 
                       pMap, prcdVars, procSeq, globalVars, nonGlobalVars, 
                       allVarSeq, localVars, A, res_, ia, prcdr, ipr, proc, ip, 
                       lsseq, ilss, lstmt, whl, ls, ils, ilLast, ili, le, ile, 
                       fs, fi, ifi, ifLast, fe, ife, ife2, feSeq, feSeqLast, 
                       fw, ifw, fwLast, cr, icr, gt, sss, isss, ss, asg, ias, 
                       ifst, estmt, iee, wi, iw, vdcl, pvdcl, elseq, nxt_, ixs, 
                       res_E, lst, nxt_E, temp_, flseq, temp_I, ifsqi, lseq, 
                       nxt_Ex, xxtemp1, temp2_, temp3_, temp4, exlsq, callStmt, 
                       prcd, svoci, temp, res_S, rprcd, rpvi, rpctemp, res_R, 
                       vrs, addExpr, pvexpr, pvi, stk, test, primeVars, sub, 
                       expr, sst, primedVars, localSub_, xlssi, xltemp1, temp1, 
                       temp2, temp3, res_X, sstsq, xprimedVars, localSub_X, 
                       res, xlsssqi, lsstsq, localSub, defSub, nxt, lsstqi, 
                       lsstemp, disjs, defs, str >>

IsExpr == IE1 \/ IE2

EX1 == /\ pc = "EX1"
       /\ ixs' = 1
       /\ pc' = "EX2"
       /\ UNCHANGED << i, j, gtemp1, gtemp2, gtemp3, gtemp4, result, rVal, 
                       pMap, prcdVars, procSeq, globalVars, nonGlobalVars, 
                       allVarSeq, localVars, stack, A, res_, ia, prcdr, ipr, 
                       proc, ip, lsseq, ilss, lstmt, whl, ls, ils, ilLast, ili, 
                       le, ile, fs, fi, ifi, ifLast, fe, ife, ife2, feSeq, 
                       feSeqLast, fw, ifw, fwLast, cr, icr, gt, sss, isss, ss, 
                       asg, ias, ifst, estmt, iee, wi, iw, vdcl, pvdcl, exp, 
                       ie, elseq, nxt_, res_E, lst, nxt_E, temp_, flseq, 
                       temp_I, ifsqi, lseq, nxt_Ex, xxtemp1, temp2_, temp3_, 
                       temp4, exlsq, callStmt, prcd, svoci, temp, res_S, rprcd, 
                       rpvi, rpctemp, res_R, vrs, addExpr, pvexpr, pvi, stk, 
                       test, primeVars, sub, expr, sst, primedVars, localSub_, 
                       xlssi, xltemp1, temp1, temp2, temp3, res_X, sstsq, 
                       xprimedVars, localSub_X, res, xlsssqi, lsstsq, localSub, 
                       defSub, nxt, lsstqi, lsstemp, disjs, defs, str >>

EX2 == /\ pc = "EX2"
       /\ IF ixs \leq Len(elseq)
             THEN /\ IF ixs < Len(elseq)
                        THEN /\ /\ lst' = elseq[ixs]
                                /\ nxt_E' = elseq[ixs+1].label
                                /\ stack' = << [ procedure |->  "ExpandLStmt",
                                                 pc        |->  "EX3",
                                                 temp_     |->  temp_,
                                                 lst       |->  lst,
                                                 nxt_E     |->  nxt_E ] >>
                                             \o stack
                             /\ temp_' = {}
                             /\ pc' = "ELS1"
                        ELSE /\ /\ lst' = elseq[ixs]
                                /\ nxt_E' = nxt_
                                /\ stack' = << [ procedure |->  "ExpandLStmt",
                                                 pc        |->  "EX3",
                                                 temp_     |->  temp_,
                                                 lst       |->  lst,
                                                 nxt_E     |->  nxt_E ] >>
                                             \o stack
                             /\ temp_' = {}
                             /\ pc' = "ELS1"
                  /\ UNCHANGED << rVal, elseq, nxt_, ixs, res_E >>
             ELSE /\ rVal' = res_E
                  /\ pc' = Head(stack).pc
                  /\ ixs' = Head(stack).ixs
                  /\ res_E' = Head(stack).res_E
                  /\ elseq' = Head(stack).elseq
                  /\ nxt_' = Head(stack).nxt_
                  /\ stack' = Tail(stack)
                  /\ UNCHANGED << lst, nxt_E, temp_ >>
       /\ UNCHANGED << i, j, gtemp1, gtemp2, gtemp3, gtemp4, result, pMap, 
                       prcdVars, procSeq, globalVars, nonGlobalVars, allVarSeq, 
                       localVars, A, res_, ia, prcdr, ipr, proc, ip, lsseq, 
                       ilss, lstmt, whl, ls, ils, ilLast, ili, le, ile, fs, fi, 
                       ifi, ifLast, fe, ife, ife2, feSeq, feSeqLast, fw, ifw, 
                       fwLast, cr, icr, gt, sss, isss, ss, asg, ias, ifst, 
                       estmt, iee, wi, iw, vdcl, pvdcl, exp, ie, flseq, temp_I, 
                       ifsqi, lseq, nxt_Ex, xxtemp1, temp2_, temp3_, temp4, 
                       exlsq, callStmt, prcd, svoci, temp, res_S, rprcd, rpvi, 
                       rpctemp, res_R, vrs, addExpr, pvexpr, pvi, stk, test, 
                       primeVars, sub, expr, sst, primedVars, localSub_, xlssi, 
                       xltemp1, temp1, temp2, temp3, res_X, sstsq, xprimedVars, 
                       localSub_X, res, xlsssqi, lsstsq, localSub, defSub, nxt, 
                       lsstqi, lsstemp, disjs, defs, str >>

EX3 == /\ pc = "EX3"
       /\ res_E' = res_E \o rVal
       /\ ixs' = ixs + 1
       /\ pc' = "EX2"
       /\ UNCHANGED << i, j, gtemp1, gtemp2, gtemp3, gtemp4, result, rVal, 
                       pMap, prcdVars, procSeq, globalVars, nonGlobalVars, 
                       allVarSeq, localVars, stack, A, res_, ia, prcdr, ipr, 
                       proc, ip, lsseq, ilss, lstmt, whl, ls, ils, ilLast, ili, 
                       le, ile, fs, fi, ifi, ifLast, fe, ife, ife2, feSeq, 
                       feSeqLast, fw, ifw, fwLast, cr, icr, gt, sss, isss, ss, 
                       asg, ias, ifst, estmt, iee, wi, iw, vdcl, pvdcl, exp, 
                       ie, elseq, nxt_, lst, nxt_E, temp_, flseq, temp_I, 
                       ifsqi, lseq, nxt_Ex, xxtemp1, temp2_, temp3_, temp4, 
                       exlsq, callStmt, prcd, svoci, temp, res_S, rprcd, rpvi, 
                       rpctemp, res_R, vrs, addExpr, pvexpr, pvi, stk, test, 
                       primeVars, sub, expr, sst, primedVars, localSub_, xlssi, 
                       xltemp1, temp1, temp2, temp3, res_X, sstsq, xprimedVars, 
                       localSub_X, res, xlsssqi, lsstsq, localSub, defSub, nxt, 
                       lsstqi, lsstemp, disjs, defs, str >>

ExpandSeq == EX1 \/ EX2 \/ EX3

ELS1 == /\ pc = "ELS1"
        /\ IF Len(lst.stmts) = 0
              THEN /\ /\ stack' = << [ procedure |->  "Error",
                                       pc        |->  "ELS2",
                                       str       |->  str ] >>
                                   \o stack
                      /\ str' = "1: LabeledStmt with no statements."
                   /\ pc' = "Error1"
              ELSE /\ pc' = "ELS2"
                   /\ UNCHANGED << stack, str >>
        /\ UNCHANGED << i, j, gtemp1, gtemp2, gtemp3, gtemp4, result, rVal, 
                        pMap, prcdVars, procSeq, globalVars, nonGlobalVars, 
                        allVarSeq, localVars, A, res_, ia, prcdr, ipr, proc, 
                        ip, lsseq, ilss, lstmt, whl, ls, ils, ilLast, ili, le, 
                        ile, fs, fi, ifi, ifLast, fe, ife, ife2, feSeq, 
                        feSeqLast, fw, ifw, fwLast, cr, icr, gt, sss, isss, ss, 
                        asg, ias, ifst, estmt, iee, wi, iw, vdcl, pvdcl, exp, 
                        ie, elseq, nxt_, ixs, res_E, lst, nxt_E, temp_, flseq, 
                        temp_I, ifsqi, lseq, nxt_Ex, xxtemp1, temp2_, temp3_, 
                        temp4, exlsq, callStmt, prcd, svoci, temp, res_S, 
                        rprcd, rpvi, rpctemp, res_R, vrs, addExpr, pvexpr, pvi, 
                        stk, test, primeVars, sub, expr, sst, primedVars, 
                        localSub_, xlssi, xltemp1, temp1, temp2, temp3, res_X, 
                        sstsq, xprimedVars, localSub_X, res, xlsssqi, lsstsq, 
                        localSub, defSub, nxt, lsstqi, lsstemp, disjs, defs >>

ELS2 == /\ pc = "ELS2"
        /\ IF lst.stmts[1].type = "while"
              THEN /\ IF lst.stmts[1].labDo = << >>
                         THEN /\ /\ lseq' = lst.stmts[1].unlabDo
                                 /\ nxt_Ex' = lst.label
                                 /\ stack' = << [ procedure |->  "ExpandLSeq",
                                                  pc        |->  "ELS3",
                                                  xxtemp1   |->  xxtemp1,
                                                  temp2_    |->  temp2_,
                                                  temp3_    |->  temp3_,
                                                  temp4     |->  temp4,
                                                  exlsq     |->  exlsq,
                                                  lseq      |->  lseq,
                                                  nxt_Ex    |->  nxt_Ex ] >>
                                              \o stack
                              /\ xxtemp1' = {}
                              /\ temp2_' = {}
                              /\ temp3_' = {}
                              /\ temp4' = {}
                              /\ exlsq' = {}
                              /\ pc' = "ELSq1"
                         ELSE /\ /\ lseq' = lst.stmts[1].unlabDo
                                 /\ nxt_Ex' = lst.stmts[1].labDo[1].label
                                 /\ stack' = << [ procedure |->  "ExpandLSeq",
                                                  pc        |->  "ELS3",
                                                  xxtemp1   |->  xxtemp1,
                                                  temp2_    |->  temp2_,
                                                  temp3_    |->  temp3_,
                                                  temp4     |->  temp4,
                                                  exlsq     |->  exlsq,
                                                  lseq      |->  lseq,
                                                  nxt_Ex    |->  nxt_Ex ] >>
                                              \o stack
                              /\ xxtemp1' = {}
                              /\ temp2_' = {}
                              /\ temp3_' = {}
                              /\ temp4' = {}
                              /\ exlsq' = {}
                              /\ pc' = "ELSq1"
              ELSE /\ /\ lseq' = lst.stmts
                      /\ nxt_Ex' = nxt_E
                      /\ stack' = << [ procedure |->  "ExpandLSeq",
                                       pc        |->  "ELS6",
                                       xxtemp1   |->  xxtemp1,
                                       temp2_    |->  temp2_,
                                       temp3_    |->  temp3_,
                                       temp4     |->  temp4,
                                       exlsq     |->  exlsq,
                                       lseq      |->  lseq,
                                       nxt_Ex    |->  nxt_Ex ] >>
                                   \o stack
                   /\ xxtemp1' = {}
                   /\ temp2_' = {}
                   /\ temp3_' = {}
                   /\ temp4' = {}
                   /\ exlsq' = {}
                   /\ pc' = "ELSq1"
        /\ UNCHANGED << i, j, gtemp1, gtemp2, gtemp3, gtemp4, result, rVal, 
                        pMap, prcdVars, procSeq, globalVars, nonGlobalVars, 
                        allVarSeq, localVars, A, res_, ia, prcdr, ipr, proc, 
                        ip, lsseq, ilss, lstmt, whl, ls, ils, ilLast, ili, le, 
                        ile, fs, fi, ifi, ifLast, fe, ife, ife2, feSeq, 
                        feSeqLast, fw, ifw, fwLast, cr, icr, gt, sss, isss, ss, 
                        asg, ias, ifst, estmt, iee, wi, iw, vdcl, pvdcl, exp, 
                        ie, elseq, nxt_, ixs, res_E, lst, nxt_E, temp_, flseq, 
                        temp_I, ifsqi, callStmt, prcd, svoci, temp, res_S, 
                        rprcd, rpvi, rpctemp, res_R, vrs, addExpr, pvexpr, pvi, 
                        stk, test, primeVars, sub, expr, sst, primedVars, 
                        localSub_, xlssi, xltemp1, temp1, temp2, temp3, res_X, 
                        sstsq, xprimedVars, localSub_X, res, xlsssqi, lsstsq, 
                        localSub, defSub, nxt, lsstqi, lsstemp, disjs, defs, 
                        str >>

ELS3 == /\ pc = "ELS3"
        /\ temp_' = rVal
        /\ /\ elseq' = lst.stmts[1].labDo
           /\ nxt_' = lst.label
           /\ stack' = << [ procedure |->  "ExpandSeq",
                            pc        |->  "ELS4",
                            ixs       |->  ixs,
                            res_E     |->  res_E,
                            elseq     |->  elseq,
                            nxt_      |->  nxt_ ] >>
                        \o stack
        /\ ixs' = {}
        /\ res_E' = << >>
        /\ pc' = "EX1"
        /\ UNCHANGED << i, j, gtemp1, gtemp2, gtemp3, gtemp4, result, rVal, 
                        pMap, prcdVars, procSeq, globalVars, nonGlobalVars, 
                        allVarSeq, localVars, A, res_, ia, prcdr, ipr, proc, 
                        ip, lsseq, ilss, lstmt, whl, ls, ils, ilLast, ili, le, 
                        ile, fs, fi, ifi, ifLast, fe, ife, ife2, feSeq, 
                        feSeqLast, fw, ifw, fwLast, cr, icr, gt, sss, isss, ss, 
                        asg, ias, ifst, estmt, iee, wi, iw, vdcl, pvdcl, exp, 
                        ie, lst, nxt_E, flseq, temp_I, ifsqi, lseq, nxt_Ex, 
                        xxtemp1, temp2_, temp3_, temp4, exlsq, callStmt, prcd, 
                        svoci, temp, res_S, rprcd, rpvi, rpctemp, res_R, vrs, 
                        addExpr, pvexpr, pvi, stk, test, primeVars, sub, expr, 
                        sst, primedVars, localSub_, xlssi, xltemp1, temp1, 
                        temp2, temp3, res_X, sstsq, xprimedVars, localSub_X, 
                        res, xlsssqi, lsstsq, localSub, defSub, nxt, lsstqi, 
                        lsstemp, disjs, defs, str >>

ELS4 == /\ pc = "ELS4"
        /\ temp_' = [temp_ EXCEPT !.rst = temp_.rst \o rVal]
        /\ /\ lseq' = Tail(lst.stmts)
           /\ nxt_Ex' = nxt_E
           /\ stack' = << [ procedure |->  "ExpandLSeq",
                            pc        |->  "ELS5",
                            xxtemp1   |->  xxtemp1,
                            temp2_    |->  temp2_,
                            temp3_    |->  temp3_,
                            temp4     |->  temp4,
                            exlsq     |->  exlsq,
                            lseq      |->  lseq,
                            nxt_Ex    |->  nxt_Ex ] >>
                        \o stack
        /\ xxtemp1' = {}
        /\ temp2_' = {}
        /\ temp3_' = {}
        /\ temp4' = {}
        /\ exlsq' = {}
        /\ pc' = "ELSq1"
        /\ UNCHANGED << i, j, gtemp1, gtemp2, gtemp3, gtemp4, result, rVal, 
                        pMap, prcdVars, procSeq, globalVars, nonGlobalVars, 
                        allVarSeq, localVars, A, res_, ia, prcdr, ipr, proc, 
                        ip, lsseq, ilss, lstmt, whl, ls, ils, ilLast, ili, le, 
                        ile, fs, fi, ifi, ifLast, fe, ife, ife2, feSeq, 
                        feSeqLast, fw, ifw, fwLast, cr, icr, gt, sss, isss, ss, 
                        asg, ias, ifst, estmt, iee, wi, iw, vdcl, pvdcl, exp, 
                        ie, elseq, nxt_, ixs, res_E, lst, nxt_E, flseq, temp_I, 
                        ifsqi, callStmt, prcd, svoci, temp, res_S, rprcd, rpvi, 
                        rpctemp, res_R, vrs, addExpr, pvexpr, pvi, stk, test, 
                        primeVars, sub, expr, sst, primedVars, localSub_, 
                        xlssi, xltemp1, temp1, temp2, temp3, res_X, sstsq, 
                        xprimedVars, localSub_X, res, xlsssqi, lsstsq, 
                        localSub, defSub, nxt, lsstqi, lsstemp, disjs, defs, 
                        str >>

ELS5 == /\ pc = "ELS5"
        /\ rVal' = << [label |-> lst.label,
                       stmts |->
                       << [then |-> temp_.ss,
                           type |-> "if",
                           test |-> lst.stmts[1].test,
                           else |-> rVal.ss] >>] >> \o
                    temp_.rst \o rVal.rst
        /\ pc' = "ELS7"
        /\ UNCHANGED << i, j, gtemp1, gtemp2, gtemp3, gtemp4, result, pMap, 
                        prcdVars, procSeq, globalVars, nonGlobalVars, 
                        allVarSeq, localVars, stack, A, res_, ia, prcdr, ipr, 
                        proc, ip, lsseq, ilss, lstmt, whl, ls, ils, ilLast, 
                        ili, le, ile, fs, fi, ifi, ifLast, fe, ife, ife2, 
                        feSeq, feSeqLast, fw, ifw, fwLast, cr, icr, gt, sss, 
                        isss, ss, asg, ias, ifst, estmt, iee, wi, iw, vdcl, 
                        pvdcl, exp, ie, elseq, nxt_, ixs, res_E, lst, nxt_E, 
                        temp_, flseq, temp_I, ifsqi, lseq, nxt_Ex, xxtemp1, 
                        temp2_, temp3_, temp4, exlsq, callStmt, prcd, svoci, 
                        temp, res_S, rprcd, rpvi, rpctemp, res_R, vrs, addExpr, 
                        pvexpr, pvi, stk, test, primeVars, sub, expr, sst, 
                        primedVars, localSub_, xlssi, xltemp1, temp1, temp2, 
                        temp3, res_X, sstsq, xprimedVars, localSub_X, res, 
                        xlsssqi, lsstsq, localSub, defSub, nxt, lsstqi, 
                        lsstemp, disjs, defs, str >>

ELS6 == /\ pc = "ELS6"
        /\ rVal' = <<[label |-> lst.label,
                      stmts |-> rVal.ss] >> \o rVal.rst
        /\ pc' = "ELS7"
        /\ UNCHANGED << i, j, gtemp1, gtemp2, gtemp3, gtemp4, result, pMap, 
                        prcdVars, procSeq, globalVars, nonGlobalVars, 
                        allVarSeq, localVars, stack, A, res_, ia, prcdr, ipr, 
                        proc, ip, lsseq, ilss, lstmt, whl, ls, ils, ilLast, 
                        ili, le, ile, fs, fi, ifi, ifLast, fe, ife, ife2, 
                        feSeq, feSeqLast, fw, ifw, fwLast, cr, icr, gt, sss, 
                        isss, ss, asg, ias, ifst, estmt, iee, wi, iw, vdcl, 
                        pvdcl, exp, ie, elseq, nxt_, ixs, res_E, lst, nxt_E, 
                        temp_, flseq, temp_I, ifsqi, lseq, nxt_Ex, xxtemp1, 
                        temp2_, temp3_, temp4, exlsq, callStmt, prcd, svoci, 
                        temp, res_S, rprcd, rpvi, rpctemp, res_R, vrs, addExpr, 
                        pvexpr, pvi, stk, test, primeVars, sub, expr, sst, 
                        primedVars, localSub_, xlssi, xltemp1, temp1, temp2, 
                        temp3, res_X, sstsq, xprimedVars, localSub_X, res, 
                        xlsssqi, lsstsq, localSub, defSub, nxt, lsstqi, 
                        lsstemp, disjs, defs, str >>

ELS7 == /\ pc = "ELS7"
        /\ pc' = Head(stack).pc
        /\ temp_' = Head(stack).temp_
        /\ lst' = Head(stack).lst
        /\ nxt_E' = Head(stack).nxt_E
        /\ stack' = Tail(stack)
        /\ UNCHANGED << i, j, gtemp1, gtemp2, gtemp3, gtemp4, result, rVal, 
                        pMap, prcdVars, procSeq, globalVars, nonGlobalVars, 
                        allVarSeq, localVars, A, res_, ia, prcdr, ipr, proc, 
                        ip, lsseq, ilss, lstmt, whl, ls, ils, ilLast, ili, le, 
                        ile, fs, fi, ifi, ifLast, fe, ife, ife2, feSeq, 
                        feSeqLast, fw, ifw, fwLast, cr, icr, gt, sss, isss, ss, 
                        asg, ias, ifst, estmt, iee, wi, iw, vdcl, pvdcl, exp, 
                        ie, elseq, nxt_, ixs, res_E, flseq, temp_I, ifsqi, 
                        lseq, nxt_Ex, xxtemp1, temp2_, temp3_, temp4, exlsq, 
                        callStmt, prcd, svoci, temp, res_S, rprcd, rpvi, 
                        rpctemp, res_R, vrs, addExpr, pvexpr, pvi, stk, test, 
                        primeVars, sub, expr, sst, primedVars, localSub_, 
                        xlssi, xltemp1, temp1, temp2, temp3, res_X, sstsq, 
                        xprimedVars, localSub_X, res, xlsssqi, lsstsq, 
                        localSub, defSub, nxt, lsstqi, lsstemp, disjs, defs, 
                        str >>

ExpandLStmt == ELS1 \/ ELS2 \/ ELS3 \/ ELS4 \/ ELS5 \/ ELS6 \/ ELS7

IFS1 == /\ pc = "IFS1"
        /\ IF flseq = << >>
              THEN /\ rVal' = FALSE
                   /\ pc' = "IFS9"
                   /\ UNCHANGED << stack, flseq, temp_I, ifsqi >>
              ELSE /\ IF FinalStmtType(Last(flseq))
                         THEN /\ rVal' = TRUE
                              /\ pc' = "IFS9"
                              /\ UNCHANGED << stack, flseq, temp_I, ifsqi >>
                         ELSE /\ IF Last(flseq).type = "if"
                                    THEN /\ /\ flseq' = Last(flseq).then
                                            /\ stack' = << [ procedure |->  "IsFinalSeq",
                                                             pc        |->  "IFS2",
                                                             temp_I    |->  temp_I,
                                                             ifsqi     |->  ifsqi,
                                                             flseq     |->  flseq ] >>
                                                         \o stack
                                         /\ temp_I' = {}
                                         /\ ifsqi' = {}
                                         /\ pc' = "IFS1"
                                         /\ UNCHANGED rVal
                                    ELSE /\ IF Last(flseq).type = "with"
                                               THEN /\ /\ flseq' = Last(flseq).do
                                                       /\ stack' = << [ procedure |->  "IsFinalSeq",
                                                                        pc        |->  "IFS9",
                                                                        temp_I    |->  temp_I,
                                                                        ifsqi     |->  ifsqi,
                                                                        flseq     |->  flseq ] >>
                                                                    \o stack
                                                    /\ temp_I' = {}
                                                    /\ ifsqi' = {}
                                                    /\ pc' = "IFS1"
                                                    /\ UNCHANGED rVal
                                               ELSE /\ IF Last(flseq).type = "either"
                                                          THEN /\ temp_I' = FALSE
                                                               /\ ifsqi' = Len(Last(flseq).ors)
                                                               /\ pc' = "IFS3"
                                                               /\ UNCHANGED rVal
                                                          ELSE /\ rVal' = FALSE
                                                               /\ pc' = "IFS9"
                                                               /\ UNCHANGED << temp_I, 
                                                                               ifsqi >>
                                                    /\ UNCHANGED << stack, 
                                                                    flseq >>
        /\ UNCHANGED << i, j, gtemp1, gtemp2, gtemp3, gtemp4, result, pMap, 
                        prcdVars, procSeq, globalVars, nonGlobalVars, 
                        allVarSeq, localVars, A, res_, ia, prcdr, ipr, proc, 
                        ip, lsseq, ilss, lstmt, whl, ls, ils, ilLast, ili, le, 
                        ile, fs, fi, ifi, ifLast, fe, ife, ife2, feSeq, 
                        feSeqLast, fw, ifw, fwLast, cr, icr, gt, sss, isss, ss, 
                        asg, ias, ifst, estmt, iee, wi, iw, vdcl, pvdcl, exp, 
                        ie, elseq, nxt_, ixs, res_E, lst, nxt_E, temp_, lseq, 
                        nxt_Ex, xxtemp1, temp2_, temp3_, temp4, exlsq, 
                        callStmt, prcd, svoci, temp, res_S, rprcd, rpvi, 
                        rpctemp, res_R, vrs, addExpr, pvexpr, pvi, stk, test, 
                        primeVars, sub, expr, sst, primedVars, localSub_, 
                        xlssi, xltemp1, temp1, temp2, temp3, res_X, sstsq, 
                        xprimedVars, localSub_X, res, xlsssqi, lsstsq, 
                        localSub, defSub, nxt, lsstqi, lsstemp, disjs, defs, 
                        str >>

IFS2 == /\ pc = "IFS2"
        /\ IF ~ rVal
              THEN /\ /\ flseq' = Last(flseq).else
                      /\ stack' = << [ procedure |->  "IsFinalSeq",
                                       pc        |->  "IFS9",
                                       temp_I    |->  temp_I,
                                       ifsqi     |->  ifsqi,
                                       flseq     |->  flseq ] >>
                                   \o stack
                   /\ temp_I' = {}
                   /\ ifsqi' = {}
                   /\ pc' = "IFS1"
              ELSE /\ pc' = "IFS9"
                   /\ UNCHANGED << stack, flseq, temp_I, ifsqi >>
        /\ UNCHANGED << i, j, gtemp1, gtemp2, gtemp3, gtemp4, result, rVal, 
                        pMap, prcdVars, procSeq, globalVars, nonGlobalVars, 
                        allVarSeq, localVars, A, res_, ia, prcdr, ipr, proc, 
                        ip, lsseq, ilss, lstmt, whl, ls, ils, ilLast, ili, le, 
                        ile, fs, fi, ifi, ifLast, fe, ife, ife2, feSeq, 
                        feSeqLast, fw, ifw, fwLast, cr, icr, gt, sss, isss, ss, 
                        asg, ias, ifst, estmt, iee, wi, iw, vdcl, pvdcl, exp, 
                        ie, elseq, nxt_, ixs, res_E, lst, nxt_E, temp_, lseq, 
                        nxt_Ex, xxtemp1, temp2_, temp3_, temp4, exlsq, 
                        callStmt, prcd, svoci, temp, res_S, rprcd, rpvi, 
                        rpctemp, res_R, vrs, addExpr, pvexpr, pvi, stk, test, 
                        primeVars, sub, expr, sst, primedVars, localSub_, 
                        xlssi, xltemp1, temp1, temp2, temp3, res_X, sstsq, 
                        xprimedVars, localSub_X, res, xlsssqi, lsstsq, 
                        localSub, defSub, nxt, lsstqi, lsstemp, disjs, defs, 
                        str >>

IFS3 == /\ pc = "IFS3"
        /\ IF (~temp_I) /\ (ifsqi > 0)
              THEN /\ /\ flseq' = Last(flseq).ors[ifsqi]
                      /\ stack' = << [ procedure |->  "IsFinalSeq",
                                       pc        |->  "IFS4",
                                       temp_I    |->  temp_I,
                                       ifsqi     |->  ifsqi,
                                       flseq     |->  flseq ] >>
                                   \o stack
                   /\ temp_I' = {}
                   /\ ifsqi' = {}
                   /\ pc' = "IFS1"
                   /\ UNCHANGED rVal
              ELSE /\ rVal' = temp_I
                   /\ pc' = "IFS9"
                   /\ UNCHANGED << stack, flseq, temp_I, ifsqi >>
        /\ UNCHANGED << i, j, gtemp1, gtemp2, gtemp3, gtemp4, result, pMap, 
                        prcdVars, procSeq, globalVars, nonGlobalVars, 
                        allVarSeq, localVars, A, res_, ia, prcdr, ipr, proc, 
                        ip, lsseq, ilss, lstmt, whl, ls, ils, ilLast, ili, le, 
                        ile, fs, fi, ifi, ifLast, fe, ife, ife2, feSeq, 
                        feSeqLast, fw, ifw, fwLast, cr, icr, gt, sss, isss, ss, 
                        asg, ias, ifst, estmt, iee, wi, iw, vdcl, pvdcl, exp, 
                        ie, elseq, nxt_, ixs, res_E, lst, nxt_E, temp_, lseq, 
                        nxt_Ex, xxtemp1, temp2_, temp3_, temp4, exlsq, 
                        callStmt, prcd, svoci, temp, res_S, rprcd, rpvi, 
                        rpctemp, res_R, vrs, addExpr, pvexpr, pvi, stk, test, 
                        primeVars, sub, expr, sst, primedVars, localSub_, 
                        xlssi, xltemp1, temp1, temp2, temp3, res_X, sstsq, 
                        xprimedVars, localSub_X, res, xlsssqi, lsstsq, 
                        localSub, defSub, nxt, lsstqi, lsstemp, disjs, defs, 
                        str >>

IFS4 == /\ pc = "IFS4"
        /\ temp_I' = temp_I \/ rVal
        /\ ifsqi' = ifsqi - 1
        /\ pc' = "IFS3"
        /\ UNCHANGED << i, j, gtemp1, gtemp2, gtemp3, gtemp4, result, rVal, 
                        pMap, prcdVars, procSeq, globalVars, nonGlobalVars, 
                        allVarSeq, localVars, stack, A, res_, ia, prcdr, ipr, 
                        proc, ip, lsseq, ilss, lstmt, whl, ls, ils, ilLast, 
                        ili, le, ile, fs, fi, ifi, ifLast, fe, ife, ife2, 
                        feSeq, feSeqLast, fw, ifw, fwLast, cr, icr, gt, sss, 
                        isss, ss, asg, ias, ifst, estmt, iee, wi, iw, vdcl, 
                        pvdcl, exp, ie, elseq, nxt_, ixs, res_E, lst, nxt_E, 
                        temp_, flseq, lseq, nxt_Ex, xxtemp1, temp2_, temp3_, 
                        temp4, exlsq, callStmt, prcd, svoci, temp, res_S, 
                        rprcd, rpvi, rpctemp, res_R, vrs, addExpr, pvexpr, pvi, 
                        stk, test, primeVars, sub, expr, sst, primedVars, 
                        localSub_, xlssi, xltemp1, temp1, temp2, temp3, res_X, 
                        sstsq, xprimedVars, localSub_X, res, xlsssqi, lsstsq, 
                        localSub, defSub, nxt, lsstqi, lsstemp, disjs, defs, 
                        str >>

IFS9 == /\ pc = "IFS9"
        /\ pc' = Head(stack).pc
        /\ temp_I' = Head(stack).temp_I
        /\ ifsqi' = Head(stack).ifsqi
        /\ flseq' = Head(stack).flseq
        /\ stack' = Tail(stack)
        /\ UNCHANGED << i, j, gtemp1, gtemp2, gtemp3, gtemp4, result, rVal, 
                        pMap, prcdVars, procSeq, globalVars, nonGlobalVars, 
                        allVarSeq, localVars, A, res_, ia, prcdr, ipr, proc, 
                        ip, lsseq, ilss, lstmt, whl, ls, ils, ilLast, ili, le, 
                        ile, fs, fi, ifi, ifLast, fe, ife, ife2, feSeq, 
                        feSeqLast, fw, ifw, fwLast, cr, icr, gt, sss, isss, ss, 
                        asg, ias, ifst, estmt, iee, wi, iw, vdcl, pvdcl, exp, 
                        ie, elseq, nxt_, ixs, res_E, lst, nxt_E, temp_, lseq, 
                        nxt_Ex, xxtemp1, temp2_, temp3_, temp4, exlsq, 
                        callStmt, prcd, svoci, temp, res_S, rprcd, rpvi, 
                        rpctemp, res_R, vrs, addExpr, pvexpr, pvi, stk, test, 
                        primeVars, sub, expr, sst, primedVars, localSub_, 
                        xlssi, xltemp1, temp1, temp2, temp3, res_X, sstsq, 
                        xprimedVars, localSub_X, res, xlsssqi, lsstsq, 
                        localSub, defSub, nxt, lsstqi, lsstemp, disjs, defs, 
                        str >>

IsFinalSeq == IFS1 \/ IFS2 \/ IFS3 \/ IFS4 \/ IFS9

ELSq1 == /\ pc = "ELSq1"
         /\ IF /\ lseq # << >>
               /\ Last(lseq).type \in {"labelIf", "labelEither"}
               THEN /\ rVal' = TRUE
                    /\ pc' = "ELSq2"
                    /\ UNCHANGED << stack, flseq, temp_I, ifsqi >>
               ELSE /\ /\ flseq' = lseq
                       /\ stack' = << [ procedure |->  "IsFinalSeq",
                                        pc        |->  "ELSq2",
                                        temp_I    |->  temp_I,
                                        ifsqi     |->  ifsqi,
                                        flseq     |->  flseq ] >>
                                    \o stack
                    /\ temp_I' = {}
                    /\ ifsqi' = {}
                    /\ pc' = "IFS1"
                    /\ UNCHANGED rVal
         /\ UNCHANGED << i, j, gtemp1, gtemp2, gtemp3, gtemp4, result, pMap, 
                         prcdVars, procSeq, globalVars, nonGlobalVars, 
                         allVarSeq, localVars, A, res_, ia, prcdr, ipr, proc, 
                         ip, lsseq, ilss, lstmt, whl, ls, ils, ilLast, ili, le, 
                         ile, fs, fi, ifi, ifLast, fe, ife, ife2, feSeq, 
                         feSeqLast, fw, ifw, fwLast, cr, icr, gt, sss, isss, 
                         ss, asg, ias, ifst, estmt, iee, wi, iw, vdcl, pvdcl, 
                         exp, ie, elseq, nxt_, ixs, res_E, lst, nxt_E, temp_, 
                         lseq, nxt_Ex, xxtemp1, temp2_, temp3_, temp4, exlsq, 
                         callStmt, prcd, svoci, temp, res_S, rprcd, rpvi, 
                         rpctemp, res_R, vrs, addExpr, pvexpr, pvi, stk, test, 
                         primeVars, sub, expr, sst, primedVars, localSub_, 
                         xlssi, xltemp1, temp1, temp2, temp3, res_X, sstsq, 
                         xprimedVars, localSub_X, res, xlsssqi, lsstsq, 
                         localSub, defSub, nxt, lsstqi, lsstemp, disjs, defs, 
                         str >>

ELSq2 == /\ pc = "ELSq2"
         /\ IF ~ rVal
               THEN /\ rVal' = [ss  |-> lseq \o <<PCAssign(nxt_Ex)>>,
                                rst |-> << >>]
                    /\ pc' = "ELSq3"
                    /\ UNCHANGED << stack, lseq, nxt_Ex, xxtemp1, temp2_, 
                                    temp3_, temp4, exlsq, callStmt, prcd, 
                                    svoci, temp, res_S, rprcd, rpvi, rpctemp, 
                                    res_R, str >>
               ELSE /\ IF Last(lseq).type = "labelIf"
                          THEN /\ IF Last(lseq).labThen = << >>
                                     THEN /\ /\ lseq' = Last(lseq).unlabThen
                                             /\ nxt_Ex' = nxt_Ex
                                             /\ stack' = << [ procedure |->  "ExpandLSeq",
                                                              pc        |->  "ELSq31",
                                                              xxtemp1   |->  xxtemp1,
                                                              temp2_    |->  temp2_,
                                                              temp3_    |->  temp3_,
                                                              temp4     |->  temp4,
                                                              exlsq     |->  exlsq,
                                                              lseq      |->  lseq,
                                                              nxt_Ex    |->  nxt_Ex ] >>
                                                          \o stack
                                          /\ xxtemp1' = {}
                                          /\ temp2_' = {}
                                          /\ temp3_' = {}
                                          /\ temp4' = {}
                                          /\ exlsq' = {}
                                          /\ pc' = "ELSq1"
                                     ELSE /\ /\ lseq' = Last(lseq).unlabThen
                                             /\ nxt_Ex' = Last(lseq).labThen[1].label
                                             /\ stack' = << [ procedure |->  "ExpandLSeq",
                                                              pc        |->  "ELSq31",
                                                              xxtemp1   |->  xxtemp1,
                                                              temp2_    |->  temp2_,
                                                              temp3_    |->  temp3_,
                                                              temp4     |->  temp4,
                                                              exlsq     |->  exlsq,
                                                              lseq      |->  lseq,
                                                              nxt_Ex    |->  nxt_Ex ] >>
                                                          \o stack
                                          /\ xxtemp1' = {}
                                          /\ temp2_' = {}
                                          /\ temp3_' = {}
                                          /\ temp4' = {}
                                          /\ exlsq' = {}
                                          /\ pc' = "ELSq1"
                               /\ UNCHANGED << rVal, callStmt, prcd, svoci, 
                                               temp, res_S, rprcd, rpvi, 
                                               rpctemp, res_R, str >>
                          ELSE /\ IF Last(lseq).type = "labelEither"
                                     THEN /\ IF Last(lseq).clauses = << >>
                                                THEN /\ /\ stack' = << [ procedure |->  "Error",
                                                                         pc        |->  "ELSq71",
                                                                         str       |->  str ] >>
                                                                     \o stack
                                                        /\ str' = "2: labelEither with no clauses"
                                                     /\ pc' = "Error1"
                                                ELSE /\ pc' = "ELSq71"
                                                     /\ UNCHANGED << stack, 
                                                                     str >>
                                          /\ UNCHANGED << rVal, lseq, nxt_Ex, 
                                                          xxtemp1, temp2_, 
                                                          temp3_, temp4, exlsq, 
                                                          callStmt, prcd, 
                                                          svoci, temp, res_S, 
                                                          rprcd, rpvi, rpctemp, 
                                                          res_R >>
                                     ELSE /\ IF Last(lseq).type = "if"
                                                THEN /\ /\ lseq' = Last(lseq).then
                                                        /\ nxt_Ex' = nxt_Ex
                                                        /\ stack' = << [ procedure |->  "ExpandLSeq",
                                                                         pc        |->  "ELSq11",
                                                                         xxtemp1   |->  xxtemp1,
                                                                         temp2_    |->  temp2_,
                                                                         temp3_    |->  temp3_,
                                                                         temp4     |->  temp4,
                                                                         exlsq     |->  exlsq,
                                                                         lseq      |->  lseq,
                                                                         nxt_Ex    |->  nxt_Ex ] >>
                                                                     \o stack
                                                     /\ xxtemp1' = {}
                                                     /\ temp2_' = {}
                                                     /\ temp3_' = {}
                                                     /\ temp4' = {}
                                                     /\ exlsq' = {}
                                                     /\ pc' = "ELSq1"
                                                     /\ UNCHANGED << rVal, 
                                                                     callStmt, 
                                                                     prcd, 
                                                                     svoci, 
                                                                     temp, 
                                                                     res_S, 
                                                                     rprcd, 
                                                                     rpvi, 
                                                                     rpctemp, 
                                                                     res_R, 
                                                                     str >>
                                                ELSE /\ IF Last(lseq).type = "with"
                                                           THEN /\ /\ lseq' = Last(lseq).do
                                                                   /\ nxt_Ex' = nxt_Ex
                                                                   /\ stack' = << [ procedure |->  "ExpandLSeq",
                                                                                    pc        |->  "ELSq41",
                                                                                    xxtemp1   |->  xxtemp1,
                                                                                    temp2_    |->  temp2_,
                                                                                    temp3_    |->  temp3_,
                                                                                    temp4     |->  temp4,
                                                                                    exlsq     |->  exlsq,
                                                                                    lseq      |->  lseq,
                                                                                    nxt_Ex    |->  nxt_Ex ] >>
                                                                                \o stack
                                                                /\ xxtemp1' = {}
                                                                /\ temp2_' = {}
                                                                /\ temp3_' = {}
                                                                /\ temp4' = {}
                                                                /\ exlsq' = {}
                                                                /\ pc' = "ELSq1"
                                                                /\ UNCHANGED << rVal, 
                                                                                callStmt, 
                                                                                prcd, 
                                                                                svoci, 
                                                                                temp, 
                                                                                res_S, 
                                                                                rprcd, 
                                                                                rpvi, 
                                                                                rpctemp, 
                                                                                res_R, 
                                                                                str >>
                                                           ELSE /\ IF Last(lseq).type = "either"
                                                                      THEN /\ exlsq' = Len(Last(lseq).ors)
                                                                           /\ temp2_' = << >>
                                                                           /\ pc' = "ELSq51"
                                                                           /\ UNCHANGED << rVal, 
                                                                                           stack, 
                                                                                           xxtemp1, 
                                                                                           temp4, 
                                                                                           callStmt, 
                                                                                           prcd, 
                                                                                           svoci, 
                                                                                           temp, 
                                                                                           res_S, 
                                                                                           rprcd, 
                                                                                           rpvi, 
                                                                                           rpctemp, 
                                                                                           res_R, 
                                                                                           str >>
                                                                      ELSE /\ IF Last(lseq).type = "call"
                                                                                 THEN /\ xxtemp1' = Last(lseq).to
                                                                                      /\ IF xxtemp1' \notin DOMAIN pMap
                                                                                            THEN /\ /\ stack' = << [ procedure |->  "Error",
                                                                                                                     pc        |->  "ELSq60",
                                                                                                                     str       |->  str ] >>
                                                                                                                 \o stack
                                                                                                    /\ str' = "14: Call of nonexistent procedure "
                                                                                                              \o xxtemp1'
                                                                                                 /\ pc' = "Error1"
                                                                                            ELSE /\ pc' = "ELSq60"
                                                                                                 /\ UNCHANGED << stack, 
                                                                                                                 str >>
                                                                                      /\ UNCHANGED << rVal, 
                                                                                                      temp2_, 
                                                                                                      temp4, 
                                                                                                      callStmt, 
                                                                                                      prcd, 
                                                                                                      svoci, 
                                                                                                      temp, 
                                                                                                      res_S, 
                                                                                                      rprcd, 
                                                                                                      rpvi, 
                                                                                                      rpctemp, 
                                                                                                      res_R >>
                                                                                 ELSE /\ IF Last(lseq).type = "return"
                                                                                            THEN /\ /\ rprcd' = Last(lseq).from
                                                                                                    /\ stack' = << [ procedure |->  "RestorePrcdVarsFrom",
                                                                                                                     pc        |->  "ELSq65",
                                                                                                                     rpvi      |->  rpvi,
                                                                                                                     rpctemp   |->  rpctemp,
                                                                                                                     res_R     |->  res_R,
                                                                                                                     rprcd     |->  rprcd ] >>
                                                                                                                 \o stack
                                                                                                 /\ rpvi' = {}
                                                                                                 /\ rpctemp' = {}
                                                                                                 /\ res_R' = << >>
                                                                                                 /\ pc' = "RPV1"
                                                                                                 /\ UNCHANGED << rVal, 
                                                                                                                 xxtemp1, 
                                                                                                                 temp2_, 
                                                                                                                 temp4, 
                                                                                                                 callStmt, 
                                                                                                                 prcd, 
                                                                                                                 svoci, 
                                                                                                                 temp, 
                                                                                                                 res_S, 
                                                                                                                 str >>
                                                                                            ELSE /\ IF Last(lseq).type = "callReturn"
                                                                                                       THEN /\ temp4' = << [type |-> "assignment",
                                                                                                                            ass  |-> << [lhs |-> [var |-> "@pc@",
                                                                                                                                                  sub |-> << >>],
                                                                                                                                         rhs  |->
                                                                                                                                           Quote(pMap[Last(lseq).to].label)
                                                                                                                                        ] >>] >>
                                                                                                            /\ IF Last(lseq).to = Last(lseq).from
                                                                                                                  THEN /\ /\ callStmt' = Last(lseq)
                                                                                                                          /\ prcd' = Last(lseq).to
                                                                                                                          /\ stack' = << [ procedure |->  "SetPrcdVarsOnCall",
                                                                                                                                           pc        |->  "ELSq8",
                                                                                                                                           svoci     |->  svoci,
                                                                                                                                           temp      |->  temp,
                                                                                                                                           res_S     |->  res_S,
                                                                                                                                           callStmt  |->  callStmt,
                                                                                                                                           prcd      |->  prcd ] >>
                                                                                                                                       \o stack
                                                                                                                       /\ svoci' = {}
                                                                                                                       /\ temp' = {}
                                                                                                                       /\ res_S' = << >>
                                                                                                                       /\ pc' = "SPV1"
                                                                                                                       /\ UNCHANGED << xxtemp1, 
                                                                                                                                       temp2_, 
                                                                                                                                       str >>
                                                                                                                  ELSE /\ temp2_' = <<"[", "procedure", "|->">>
                                                                                                                                       \o Quote(Last(lseq).to) \o
                                                                                                                                      << ",", "@pc@", "|->", "Head", "(",
                                                                                                                                        "@stack@", ")", ".", "@pc@" >>
                                                                                                                       /\ xxtemp1' = Last(lseq).to
                                                                                                                       /\ IF xxtemp1' \notin DOMAIN pMap
                                                                                                                             THEN /\ /\ stack' = << [ procedure |->  "Error",
                                                                                                                                                      pc        |->  "ELSq80",
                                                                                                                                                      str       |->  str ] >>
                                                                                                                                                  \o stack
                                                                                                                                     /\ str' =       "16: Call of nonexistent procedure "
                                                                                                                                               \o xxtemp1'
                                                                                                                                  /\ pc' = "Error1"
                                                                                                                             ELSE /\ pc' = "ELSq80"
                                                                                                                                  /\ UNCHANGED << stack, 
                                                                                                                                                  str >>
                                                                                                                       /\ UNCHANGED << callStmt, 
                                                                                                                                       prcd, 
                                                                                                                                       svoci, 
                                                                                                                                       temp, 
                                                                                                                                       res_S >>
                                                                                                            /\ UNCHANGED rVal
                                                                                                       ELSE /\ IF Last(lseq).type = "goto"
                                                                                                                  THEN /\ rVal' = [ss  |-> Front(lseq) \o <<PCAssign(Last(lseq).to)>>,
                                                                                                                                   rst |-> << >>]
                                                                                                                       /\ pc' = "ELSq3"
                                                                                                                       /\ UNCHANGED << stack, 
                                                                                                                                       str >>
                                                                                                                  ELSE /\ /\ stack' = << [ procedure |->  "Error",
                                                                                                                                           pc        |->  "ELSq3",
                                                                                                                                           str       |->  str ] >>
                                                                                                                                       \o stack
                                                                                                                          /\ str' = "7: Unknown statement type."
                                                                                                                       /\ pc' = "Error1"
                                                                                                                       /\ UNCHANGED rVal
                                                                                                            /\ UNCHANGED << xxtemp1, 
                                                                                                                            temp2_, 
                                                                                                                            temp4, 
                                                                                                                            callStmt, 
                                                                                                                            prcd, 
                                                                                                                            svoci, 
                                                                                                                            temp, 
                                                                                                                            res_S >>
                                                                                                 /\ UNCHANGED << rprcd, 
                                                                                                                 rpvi, 
                                                                                                                 rpctemp, 
                                                                                                                 res_R >>
                                                                           /\ UNCHANGED exlsq
                                                                /\ UNCHANGED << lseq, 
                                                                                nxt_Ex, 
                                                                                temp3_ >>
         /\ UNCHANGED << i, j, gtemp1, gtemp2, gtemp3, gtemp4, result, pMap, 
                         prcdVars, procSeq, globalVars, nonGlobalVars, 
                         allVarSeq, localVars, A, res_, ia, prcdr, ipr, proc, 
                         ip, lsseq, ilss, lstmt, whl, ls, ils, ilLast, ili, le, 
                         ile, fs, fi, ifi, ifLast, fe, ife, ife2, feSeq, 
                         feSeqLast, fw, ifw, fwLast, cr, icr, gt, sss, isss, 
                         ss, asg, ias, ifst, estmt, iee, wi, iw, vdcl, pvdcl, 
                         exp, ie, elseq, nxt_, ixs, res_E, lst, nxt_E, temp_, 
                         flseq, temp_I, ifsqi, vrs, addExpr, pvexpr, pvi, stk, 
                         test, primeVars, sub, expr, sst, primedVars, 
                         localSub_, xlssi, xltemp1, temp1, temp2, temp3, res_X, 
                         sstsq, xprimedVars, localSub_X, res, xlsssqi, lsstsq, 
                         localSub, defSub, nxt, lsstqi, lsstemp, disjs, defs >>

ELSq31 == /\ pc = "ELSq31"
          /\ xxtemp1' = rVal
          /\ pc' = "ELSq32"
          /\ UNCHANGED << i, j, gtemp1, gtemp2, gtemp3, gtemp4, result, rVal, 
                          pMap, prcdVars, procSeq, globalVars, nonGlobalVars, 
                          allVarSeq, localVars, stack, A, res_, ia, prcdr, ipr, 
                          proc, ip, lsseq, ilss, lstmt, whl, ls, ils, ilLast, 
                          ili, le, ile, fs, fi, ifi, ifLast, fe, ife, ife2, 
                          feSeq, feSeqLast, fw, ifw, fwLast, cr, icr, gt, sss, 
                          isss, ss, asg, ias, ifst, estmt, iee, wi, iw, vdcl, 
                          pvdcl, exp, ie, elseq, nxt_, ixs, res_E, lst, nxt_E, 
                          temp_, flseq, temp_I, ifsqi, lseq, nxt_Ex, temp2_, 
                          temp3_, temp4, exlsq, callStmt, prcd, svoci, temp, 
                          res_S, rprcd, rpvi, rpctemp, res_R, vrs, addExpr, 
                          pvexpr, pvi, stk, test, primeVars, sub, expr, sst, 
                          primedVars, localSub_, xlssi, xltemp1, temp1, temp2, 
                          temp3, res_X, sstsq, xprimedVars, localSub_X, res, 
                          xlsssqi, lsstsq, localSub, defSub, nxt, lsstqi, 
                          lsstemp, disjs, defs, str >>

ELSq32 == /\ pc = "ELSq32"
          /\ IF Last(lseq).labElse = << >>
                THEN /\ /\ lseq' = Last(lseq).unlabElse
                        /\ nxt_Ex' = nxt_Ex
                        /\ stack' = << [ procedure |->  "ExpandLSeq",
                                         pc        |->  "ELSq33",
                                         xxtemp1   |->  xxtemp1,
                                         temp2_    |->  temp2_,
                                         temp3_    |->  temp3_,
                                         temp4     |->  temp4,
                                         exlsq     |->  exlsq,
                                         lseq      |->  lseq,
                                         nxt_Ex    |->  nxt_Ex ] >>
                                     \o stack
                     /\ xxtemp1' = {}
                     /\ temp2_' = {}
                     /\ temp3_' = {}
                     /\ temp4' = {}
                     /\ exlsq' = {}
                     /\ pc' = "ELSq1"
                ELSE /\ /\ lseq' = Last(lseq).unlabElse
                        /\ nxt_Ex' = Last(lseq).labElse[1].label
                        /\ stack' = << [ procedure |->  "ExpandLSeq",
                                         pc        |->  "ELSq33",
                                         xxtemp1   |->  xxtemp1,
                                         temp2_    |->  temp2_,
                                         temp3_    |->  temp3_,
                                         temp4     |->  temp4,
                                         exlsq     |->  exlsq,
                                         lseq      |->  lseq,
                                         nxt_Ex    |->  nxt_Ex ] >>
                                     \o stack
                     /\ xxtemp1' = {}
                     /\ temp2_' = {}
                     /\ temp3_' = {}
                     /\ temp4' = {}
                     /\ exlsq' = {}
                     /\ pc' = "ELSq1"
          /\ UNCHANGED << i, j, gtemp1, gtemp2, gtemp3, gtemp4, result, rVal, 
                          pMap, prcdVars, procSeq, globalVars, nonGlobalVars, 
                          allVarSeq, localVars, A, res_, ia, prcdr, ipr, proc, 
                          ip, lsseq, ilss, lstmt, whl, ls, ils, ilLast, ili, 
                          le, ile, fs, fi, ifi, ifLast, fe, ife, ife2, feSeq, 
                          feSeqLast, fw, ifw, fwLast, cr, icr, gt, sss, isss, 
                          ss, asg, ias, ifst, estmt, iee, wi, iw, vdcl, pvdcl, 
                          exp, ie, elseq, nxt_, ixs, res_E, lst, nxt_E, temp_, 
                          flseq, temp_I, ifsqi, callStmt, prcd, svoci, temp, 
                          res_S, rprcd, rpvi, rpctemp, res_R, vrs, addExpr, 
                          pvexpr, pvi, stk, test, primeVars, sub, expr, sst, 
                          primedVars, localSub_, xlssi, xltemp1, temp1, temp2, 
                          temp3, res_X, sstsq, xprimedVars, localSub_X, res, 
                          xlsssqi, lsstsq, localSub, defSub, nxt, lsstqi, 
                          lsstemp, disjs, defs, str >>

ELSq33 == /\ pc = "ELSq33"
          /\ temp2_' = rVal
          /\ /\ elseq' = Last(lseq).labThen
             /\ nxt_' = nxt_Ex
             /\ stack' = << [ procedure |->  "ExpandSeq",
                              pc        |->  "ELSq34",
                              ixs       |->  ixs,
                              res_E     |->  res_E,
                              elseq     |->  elseq,
                              nxt_      |->  nxt_ ] >>
                          \o stack
          /\ ixs' = {}
          /\ res_E' = << >>
          /\ pc' = "EX1"
          /\ UNCHANGED << i, j, gtemp1, gtemp2, gtemp3, gtemp4, result, rVal, 
                          pMap, prcdVars, procSeq, globalVars, nonGlobalVars, 
                          allVarSeq, localVars, A, res_, ia, prcdr, ipr, proc, 
                          ip, lsseq, ilss, lstmt, whl, ls, ils, ilLast, ili, 
                          le, ile, fs, fi, ifi, ifLast, fe, ife, ife2, feSeq, 
                          feSeqLast, fw, ifw, fwLast, cr, icr, gt, sss, isss, 
                          ss, asg, ias, ifst, estmt, iee, wi, iw, vdcl, pvdcl, 
                          exp, ie, lst, nxt_E, temp_, flseq, temp_I, ifsqi, 
                          lseq, nxt_Ex, xxtemp1, temp3_, temp4, exlsq, 
                          callStmt, prcd, svoci, temp, res_S, rprcd, rpvi, 
                          rpctemp, res_R, vrs, addExpr, pvexpr, pvi, stk, test, 
                          primeVars, sub, expr, sst, primedVars, localSub_, 
                          xlssi, xltemp1, temp1, temp2, temp3, res_X, sstsq, 
                          xprimedVars, localSub_X, res, xlsssqi, lsstsq, 
                          localSub, defSub, nxt, lsstqi, lsstemp, disjs, defs, 
                          str >>

ELSq34 == /\ pc = "ELSq34"
          /\ temp3_' = rVal
          /\ /\ elseq' = Last(lseq).labElse
             /\ nxt_' = nxt_Ex
             /\ stack' = << [ procedure |->  "ExpandSeq",
                              pc        |->  "ELSq35",
                              ixs       |->  ixs,
                              res_E     |->  res_E,
                              elseq     |->  elseq,
                              nxt_      |->  nxt_ ] >>
                          \o stack
          /\ ixs' = {}
          /\ res_E' = << >>
          /\ pc' = "EX1"
          /\ UNCHANGED << i, j, gtemp1, gtemp2, gtemp3, gtemp4, result, rVal, 
                          pMap, prcdVars, procSeq, globalVars, nonGlobalVars, 
                          allVarSeq, localVars, A, res_, ia, prcdr, ipr, proc, 
                          ip, lsseq, ilss, lstmt, whl, ls, ils, ilLast, ili, 
                          le, ile, fs, fi, ifi, ifLast, fe, ife, ife2, feSeq, 
                          feSeqLast, fw, ifw, fwLast, cr, icr, gt, sss, isss, 
                          ss, asg, ias, ifst, estmt, iee, wi, iw, vdcl, pvdcl, 
                          exp, ie, lst, nxt_E, temp_, flseq, temp_I, ifsqi, 
                          lseq, nxt_Ex, xxtemp1, temp2_, temp4, exlsq, 
                          callStmt, prcd, svoci, temp, res_S, rprcd, rpvi, 
                          rpctemp, res_R, vrs, addExpr, pvexpr, pvi, stk, test, 
                          primeVars, sub, expr, sst, primedVars, localSub_, 
                          xlssi, xltemp1, temp1, temp2, temp3, res_X, sstsq, 
                          xprimedVars, localSub_X, res, xlsssqi, lsstsq, 
                          localSub, defSub, nxt, lsstqi, lsstemp, disjs, defs, 
                          str >>

ELSq35 == /\ pc = "ELSq35"
          /\ temp3_' = temp3_ \o rVal
          /\ rVal' = [ss  |-> Front(lseq) \o
                                << [type |-> "if",
                                    test |-> Last(lseq).test,
                                    then |-> xxtemp1.ss ,
                                    else |-> temp2_.ss] >> ,
                      rst |-> xxtemp1.rst \o temp2_.rst \o temp3_' ]
          /\ pc' = "ELSq3"
          /\ UNCHANGED << i, j, gtemp1, gtemp2, gtemp3, gtemp4, result, pMap, 
                          prcdVars, procSeq, globalVars, nonGlobalVars, 
                          allVarSeq, localVars, stack, A, res_, ia, prcdr, ipr, 
                          proc, ip, lsseq, ilss, lstmt, whl, ls, ils, ilLast, 
                          ili, le, ile, fs, fi, ifi, ifLast, fe, ife, ife2, 
                          feSeq, feSeqLast, fw, ifw, fwLast, cr, icr, gt, sss, 
                          isss, ss, asg, ias, ifst, estmt, iee, wi, iw, vdcl, 
                          pvdcl, exp, ie, elseq, nxt_, ixs, res_E, lst, nxt_E, 
                          temp_, flseq, temp_I, ifsqi, lseq, nxt_Ex, xxtemp1, 
                          temp2_, temp4, exlsq, callStmt, prcd, svoci, temp, 
                          res_S, rprcd, rpvi, rpctemp, res_R, vrs, addExpr, 
                          pvexpr, pvi, stk, test, primeVars, sub, expr, sst, 
                          primedVars, localSub_, xlssi, xltemp1, temp1, temp2, 
                          temp3, res_X, sstsq, xprimedVars, localSub_X, res, 
                          xlsssqi, lsstsq, localSub, defSub, nxt, lsstqi, 
                          lsstemp, disjs, defs, str >>

ELSq71 == /\ pc = "ELSq71"
          /\ xxtemp1' = << >>
          /\ temp2_' = << >>
          /\ exlsq' = Len(Last(lseq).clauses)
          /\ pc' = "ELSq72"
          /\ UNCHANGED << i, j, gtemp1, gtemp2, gtemp3, gtemp4, result, rVal, 
                          pMap, prcdVars, procSeq, globalVars, nonGlobalVars, 
                          allVarSeq, localVars, stack, A, res_, ia, prcdr, ipr, 
                          proc, ip, lsseq, ilss, lstmt, whl, ls, ils, ilLast, 
                          ili, le, ile, fs, fi, ifi, ifLast, fe, ife, ife2, 
                          feSeq, feSeqLast, fw, ifw, fwLast, cr, icr, gt, sss, 
                          isss, ss, asg, ias, ifst, estmt, iee, wi, iw, vdcl, 
                          pvdcl, exp, ie, elseq, nxt_, ixs, res_E, lst, nxt_E, 
                          temp_, flseq, temp_I, ifsqi, lseq, nxt_Ex, temp3_, 
                          temp4, callStmt, prcd, svoci, temp, res_S, rprcd, 
                          rpvi, rpctemp, res_R, vrs, addExpr, pvexpr, pvi, stk, 
                          test, primeVars, sub, expr, sst, primedVars, 
                          localSub_, xlssi, xltemp1, temp1, temp2, temp3, 
                          res_X, sstsq, xprimedVars, localSub_X, res, xlsssqi, 
                          lsstsq, localSub, defSub, nxt, lsstqi, lsstemp, 
                          disjs, defs, str >>

ELSq72 == /\ pc = "ELSq72"
          /\ IF exlsq > 0
                THEN /\ IF Last(lseq).clauses[exlsq].labOr = << >>
                           THEN /\ /\ lseq' = Last(lseq).clauses[exlsq].unlabOr
                                   /\ nxt_Ex' = nxt_Ex
                                   /\ stack' = << [ procedure |->  "ExpandLSeq",
                                                    pc        |->  "ELSq73",
                                                    xxtemp1   |->  xxtemp1,
                                                    temp2_    |->  temp2_,
                                                    temp3_    |->  temp3_,
                                                    temp4     |->  temp4,
                                                    exlsq     |->  exlsq,
                                                    lseq      |->  lseq,
                                                    nxt_Ex    |->  nxt_Ex ] >>
                                                \o stack
                                /\ xxtemp1' = {}
                                /\ temp2_' = {}
                                /\ temp3_' = {}
                                /\ temp4' = {}
                                /\ exlsq' = {}
                                /\ pc' = "ELSq1"
                           ELSE /\ /\ lseq' = Last(lseq).clauses[exlsq].unlabOr
                                   /\ nxt_Ex' = Last(lseq).clauses[exlsq].labOr[1].label
                                   /\ stack' = << [ procedure |->  "ExpandLSeq",
                                                    pc        |->  "ELSq73",
                                                    xxtemp1   |->  xxtemp1,
                                                    temp2_    |->  temp2_,
                                                    temp3_    |->  temp3_,
                                                    temp4     |->  temp4,
                                                    exlsq     |->  exlsq,
                                                    lseq      |->  lseq,
                                                    nxt_Ex    |->  nxt_Ex ] >>
                                                \o stack
                                /\ xxtemp1' = {}
                                /\ temp2_' = {}
                                /\ temp3_' = {}
                                /\ temp4' = {}
                                /\ exlsq' = {}
                                /\ pc' = "ELSq1"
                ELSE /\ temp3_' = << >>
                     /\ exlsq' = Len(Last(lseq).clauses)
                     /\ pc' = "ELSq74"
                     /\ UNCHANGED << stack, lseq, nxt_Ex, xxtemp1, temp2_, 
                                     temp4 >>
          /\ UNCHANGED << i, j, gtemp1, gtemp2, gtemp3, gtemp4, result, rVal, 
                          pMap, prcdVars, procSeq, globalVars, nonGlobalVars, 
                          allVarSeq, localVars, A, res_, ia, prcdr, ipr, proc, 
                          ip, lsseq, ilss, lstmt, whl, ls, ils, ilLast, ili, 
                          le, ile, fs, fi, ifi, ifLast, fe, ife, ife2, feSeq, 
                          feSeqLast, fw, ifw, fwLast, cr, icr, gt, sss, isss, 
                          ss, asg, ias, ifst, estmt, iee, wi, iw, vdcl, pvdcl, 
                          exp, ie, elseq, nxt_, ixs, res_E, lst, nxt_E, temp_, 
                          flseq, temp_I, ifsqi, callStmt, prcd, svoci, temp, 
                          res_S, rprcd, rpvi, rpctemp, res_R, vrs, addExpr, 
                          pvexpr, pvi, stk, test, primeVars, sub, expr, sst, 
                          primedVars, localSub_, xlssi, xltemp1, temp1, temp2, 
                          temp3, res_X, sstsq, xprimedVars, localSub_X, res, 
                          xlsssqi, lsstsq, localSub, defSub, nxt, lsstqi, 
                          lsstemp, disjs, defs, str >>

ELSq73 == /\ pc = "ELSq73"
          /\ xxtemp1' = <<rVal.ss>> \o xxtemp1
          /\ temp2_' = rVal.rst \o temp2_
          /\ exlsq' = exlsq - 1
          /\ pc' = "ELSq72"
          /\ UNCHANGED << i, j, gtemp1, gtemp2, gtemp3, gtemp4, result, rVal, 
                          pMap, prcdVars, procSeq, globalVars, nonGlobalVars, 
                          allVarSeq, localVars, stack, A, res_, ia, prcdr, ipr, 
                          proc, ip, lsseq, ilss, lstmt, whl, ls, ils, ilLast, 
                          ili, le, ile, fs, fi, ifi, ifLast, fe, ife, ife2, 
                          feSeq, feSeqLast, fw, ifw, fwLast, cr, icr, gt, sss, 
                          isss, ss, asg, ias, ifst, estmt, iee, wi, iw, vdcl, 
                          pvdcl, exp, ie, elseq, nxt_, ixs, res_E, lst, nxt_E, 
                          temp_, flseq, temp_I, ifsqi, lseq, nxt_Ex, temp3_, 
                          temp4, callStmt, prcd, svoci, temp, res_S, rprcd, 
                          rpvi, rpctemp, res_R, vrs, addExpr, pvexpr, pvi, stk, 
                          test, primeVars, sub, expr, sst, primedVars, 
                          localSub_, xlssi, xltemp1, temp1, temp2, temp3, 
                          res_X, sstsq, xprimedVars, localSub_X, res, xlsssqi, 
                          lsstsq, localSub, defSub, nxt, lsstqi, lsstemp, 
                          disjs, defs, str >>

ELSq74 == /\ pc = "ELSq74"
          /\ IF exlsq > 0
                THEN /\ /\ elseq' = Last(lseq).clauses[exlsq].labOr
                        /\ nxt_' = nxt_Ex
                        /\ stack' = << [ procedure |->  "ExpandSeq",
                                         pc        |->  "ELSq75",
                                         ixs       |->  ixs,
                                         res_E     |->  res_E,
                                         elseq     |->  elseq,
                                         nxt_      |->  nxt_ ] >>
                                     \o stack
                     /\ ixs' = {}
                     /\ res_E' = << >>
                     /\ pc' = "EX1"
                     /\ UNCHANGED rVal
                ELSE /\ rVal' = [ss  |-> Front(lseq) \o << [type    |-> "either",
                                                            clauses |-> xxtemp1] >>,
                                 rst |-> temp2_ \o temp3_ ]
                     /\ pc' = "ELSq3"
                     /\ UNCHANGED << stack, elseq, nxt_, ixs, res_E >>
          /\ UNCHANGED << i, j, gtemp1, gtemp2, gtemp3, gtemp4, result, pMap, 
                          prcdVars, procSeq, globalVars, nonGlobalVars, 
                          allVarSeq, localVars, A, res_, ia, prcdr, ipr, proc, 
                          ip, lsseq, ilss, lstmt, whl, ls, ils, ilLast, ili, 
                          le, ile, fs, fi, ifi, ifLast, fe, ife, ife2, feSeq, 
                          feSeqLast, fw, ifw, fwLast, cr, icr, gt, sss, isss, 
                          ss, asg, ias, ifst, estmt, iee, wi, iw, vdcl, pvdcl, 
                          exp, ie, lst, nxt_E, temp_, flseq, temp_I, ifsqi, 
                          lseq, nxt_Ex, xxtemp1, temp2_, temp3_, temp4, exlsq, 
                          callStmt, prcd, svoci, temp, res_S, rprcd, rpvi, 
                          rpctemp, res_R, vrs, addExpr, pvexpr, pvi, stk, test, 
                          primeVars, sub, expr, sst, primedVars, localSub_, 
                          xlssi, xltemp1, temp1, temp2, temp3, res_X, sstsq, 
                          xprimedVars, localSub_X, res, xlsssqi, lsstsq, 
                          localSub, defSub, nxt, lsstqi, lsstemp, disjs, defs, 
                          str >>

ELSq75 == /\ pc = "ELSq75"
          /\ temp3_' = rVal \o temp3_
          /\ exlsq' = exlsq - 1
          /\ pc' = "ELSq74"
          /\ UNCHANGED << i, j, gtemp1, gtemp2, gtemp3, gtemp4, result, rVal, 
                          pMap, prcdVars, procSeq, globalVars, nonGlobalVars, 
                          allVarSeq, localVars, stack, A, res_, ia, prcdr, ipr, 
                          proc, ip, lsseq, ilss, lstmt, whl, ls, ils, ilLast, 
                          ili, le, ile, fs, fi, ifi, ifLast, fe, ife, ife2, 
                          feSeq, feSeqLast, fw, ifw, fwLast, cr, icr, gt, sss, 
                          isss, ss, asg, ias, ifst, estmt, iee, wi, iw, vdcl, 
                          pvdcl, exp, ie, elseq, nxt_, ixs, res_E, lst, nxt_E, 
                          temp_, flseq, temp_I, ifsqi, lseq, nxt_Ex, xxtemp1, 
                          temp2_, temp4, callStmt, prcd, svoci, temp, res_S, 
                          rprcd, rpvi, rpctemp, res_R, vrs, addExpr, pvexpr, 
                          pvi, stk, test, primeVars, sub, expr, sst, 
                          primedVars, localSub_, xlssi, xltemp1, temp1, temp2, 
                          temp3, res_X, sstsq, xprimedVars, localSub_X, res, 
                          xlsssqi, lsstsq, localSub, defSub, nxt, lsstqi, 
                          lsstemp, disjs, defs, str >>

ELSq11 == /\ pc = "ELSq11"
          /\ IF rVal.rst # << >>
                THEN /\ /\ stack' = << [ procedure |->  "Error",
                                         pc        |->  "ELSq12",
                                         str       |->  str ] >>
                                     \o stack
                        /\ str' = "3: Label in `then' cls of `if'"
                     /\ pc' = "Error1"
                ELSE /\ pc' = "ELSq12"
                     /\ UNCHANGED << stack, str >>
          /\ UNCHANGED << i, j, gtemp1, gtemp2, gtemp3, gtemp4, result, rVal, 
                          pMap, prcdVars, procSeq, globalVars, nonGlobalVars, 
                          allVarSeq, localVars, A, res_, ia, prcdr, ipr, proc, 
                          ip, lsseq, ilss, lstmt, whl, ls, ils, ilLast, ili, 
                          le, ile, fs, fi, ifi, ifLast, fe, ife, ife2, feSeq, 
                          feSeqLast, fw, ifw, fwLast, cr, icr, gt, sss, isss, 
                          ss, asg, ias, ifst, estmt, iee, wi, iw, vdcl, pvdcl, 
                          exp, ie, elseq, nxt_, ixs, res_E, lst, nxt_E, temp_, 
                          flseq, temp_I, ifsqi, lseq, nxt_Ex, xxtemp1, temp2_, 
                          temp3_, temp4, exlsq, callStmt, prcd, svoci, temp, 
                          res_S, rprcd, rpvi, rpctemp, res_R, vrs, addExpr, 
                          pvexpr, pvi, stk, test, primeVars, sub, expr, sst, 
                          primedVars, localSub_, xlssi, xltemp1, temp1, temp2, 
                          temp3, res_X, sstsq, xprimedVars, localSub_X, res, 
                          xlsssqi, lsstsq, localSub, defSub, nxt, lsstqi, 
                          lsstemp, disjs, defs >>

ELSq12 == /\ pc = "ELSq12"
          /\ xxtemp1' = rVal
          /\ pc' = "ELSq13"
          /\ UNCHANGED << i, j, gtemp1, gtemp2, gtemp3, gtemp4, result, rVal, 
                          pMap, prcdVars, procSeq, globalVars, nonGlobalVars, 
                          allVarSeq, localVars, stack, A, res_, ia, prcdr, ipr, 
                          proc, ip, lsseq, ilss, lstmt, whl, ls, ils, ilLast, 
                          ili, le, ile, fs, fi, ifi, ifLast, fe, ife, ife2, 
                          feSeq, feSeqLast, fw, ifw, fwLast, cr, icr, gt, sss, 
                          isss, ss, asg, ias, ifst, estmt, iee, wi, iw, vdcl, 
                          pvdcl, exp, ie, elseq, nxt_, ixs, res_E, lst, nxt_E, 
                          temp_, flseq, temp_I, ifsqi, lseq, nxt_Ex, temp2_, 
                          temp3_, temp4, exlsq, callStmt, prcd, svoci, temp, 
                          res_S, rprcd, rpvi, rpctemp, res_R, vrs, addExpr, 
                          pvexpr, pvi, stk, test, primeVars, sub, expr, sst, 
                          primedVars, localSub_, xlssi, xltemp1, temp1, temp2, 
                          temp3, res_X, sstsq, xprimedVars, localSub_X, res, 
                          xlsssqi, lsstsq, localSub, defSub, nxt, lsstqi, 
                          lsstemp, disjs, defs, str >>

ELSq13 == /\ pc = "ELSq13"
          /\ /\ lseq' = Last(lseq).else
             /\ nxt_Ex' = nxt_Ex
             /\ stack' = << [ procedure |->  "ExpandLSeq",
                              pc        |->  "ELSq14",
                              xxtemp1   |->  xxtemp1,
                              temp2_    |->  temp2_,
                              temp3_    |->  temp3_,
                              temp4     |->  temp4,
                              exlsq     |->  exlsq,
                              lseq      |->  lseq,
                              nxt_Ex    |->  nxt_Ex ] >>
                          \o stack
          /\ xxtemp1' = {}
          /\ temp2_' = {}
          /\ temp3_' = {}
          /\ temp4' = {}
          /\ exlsq' = {}
          /\ pc' = "ELSq1"
          /\ UNCHANGED << i, j, gtemp1, gtemp2, gtemp3, gtemp4, result, rVal, 
                          pMap, prcdVars, procSeq, globalVars, nonGlobalVars, 
                          allVarSeq, localVars, A, res_, ia, prcdr, ipr, proc, 
                          ip, lsseq, ilss, lstmt, whl, ls, ils, ilLast, ili, 
                          le, ile, fs, fi, ifi, ifLast, fe, ife, ife2, feSeq, 
                          feSeqLast, fw, ifw, fwLast, cr, icr, gt, sss, isss, 
                          ss, asg, ias, ifst, estmt, iee, wi, iw, vdcl, pvdcl, 
                          exp, ie, elseq, nxt_, ixs, res_E, lst, nxt_E, temp_, 
                          flseq, temp_I, ifsqi, callStmt, prcd, svoci, temp, 
                          res_S, rprcd, rpvi, rpctemp, res_R, vrs, addExpr, 
                          pvexpr, pvi, stk, test, primeVars, sub, expr, sst, 
                          primedVars, localSub_, xlssi, xltemp1, temp1, temp2, 
                          temp3, res_X, sstsq, xprimedVars, localSub_X, res, 
                          xlsssqi, lsstsq, localSub, defSub, nxt, lsstqi, 
                          lsstemp, disjs, defs, str >>

ELSq14 == /\ pc = "ELSq14"
          /\ IF rVal.rst # << >>
                THEN /\ /\ stack' = << [ procedure |->  "Error",
                                         pc        |->  "ELSq15",
                                         str       |->  str ] >>
                                     \o stack
                        /\ str' = "4: Label in `else' cls of `if'"
                     /\ pc' = "Error1"
                ELSE /\ pc' = "ELSq15"
                     /\ UNCHANGED << stack, str >>
          /\ UNCHANGED << i, j, gtemp1, gtemp2, gtemp3, gtemp4, result, rVal, 
                          pMap, prcdVars, procSeq, globalVars, nonGlobalVars, 
                          allVarSeq, localVars, A, res_, ia, prcdr, ipr, proc, 
                          ip, lsseq, ilss, lstmt, whl, ls, ils, ilLast, ili, 
                          le, ile, fs, fi, ifi, ifLast, fe, ife, ife2, feSeq, 
                          feSeqLast, fw, ifw, fwLast, cr, icr, gt, sss, isss, 
                          ss, asg, ias, ifst, estmt, iee, wi, iw, vdcl, pvdcl, 
                          exp, ie, elseq, nxt_, ixs, res_E, lst, nxt_E, temp_, 
                          flseq, temp_I, ifsqi, lseq, nxt_Ex, xxtemp1, temp2_, 
                          temp3_, temp4, exlsq, callStmt, prcd, svoci, temp, 
                          res_S, rprcd, rpvi, rpctemp, res_R, vrs, addExpr, 
                          pvexpr, pvi, stk, test, primeVars, sub, expr, sst, 
                          primedVars, localSub_, xlssi, xltemp1, temp1, temp2, 
                          temp3, res_X, sstsq, xprimedVars, localSub_X, res, 
                          xlsssqi, lsstsq, localSub, defSub, nxt, lsstqi, 
                          lsstemp, disjs, defs >>

ELSq15 == /\ pc = "ELSq15"
          /\ temp2_' = rVal
          /\ rVal' = [ss |-> Front(lseq) \o << [type |-> "if",
                                                test |-> Last(lseq).test,
                                                then |-> xxtemp1.ss,
                                                else |-> temp2_'.ss] >>,
                      rst |-> << >>]
          /\ pc' = "ELSq3"
          /\ UNCHANGED << i, j, gtemp1, gtemp2, gtemp3, gtemp4, result, pMap, 
                          prcdVars, procSeq, globalVars, nonGlobalVars, 
                          allVarSeq, localVars, stack, A, res_, ia, prcdr, ipr, 
                          proc, ip, lsseq, ilss, lstmt, whl, ls, ils, ilLast, 
                          ili, le, ile, fs, fi, ifi, ifLast, fe, ife, ife2, 
                          feSeq, feSeqLast, fw, ifw, fwLast, cr, icr, gt, sss, 
                          isss, ss, asg, ias, ifst, estmt, iee, wi, iw, vdcl, 
                          pvdcl, exp, ie, elseq, nxt_, ixs, res_E, lst, nxt_E, 
                          temp_, flseq, temp_I, ifsqi, lseq, nxt_Ex, xxtemp1, 
                          temp3_, temp4, exlsq, callStmt, prcd, svoci, temp, 
                          res_S, rprcd, rpvi, rpctemp, res_R, vrs, addExpr, 
                          pvexpr, pvi, stk, test, primeVars, sub, expr, sst, 
                          primedVars, localSub_, xlssi, xltemp1, temp1, temp2, 
                          temp3, res_X, sstsq, xprimedVars, localSub_X, res, 
                          xlsssqi, lsstsq, localSub, defSub, nxt, lsstqi, 
                          lsstemp, disjs, defs, str >>

ELSq41 == /\ pc = "ELSq41"
          /\ IF rVal.rst # << >>
                THEN /\ /\ stack' = << [ procedure |->  "Error",
                                         pc        |->  "ELSq42",
                                         str       |->  str ] >>
                                     \o stack
                        /\ str' = "5: Label in `with'"
                     /\ pc' = "Error1"
                ELSE /\ pc' = "ELSq42"
                     /\ UNCHANGED << stack, str >>
          /\ UNCHANGED << i, j, gtemp1, gtemp2, gtemp3, gtemp4, result, rVal, 
                          pMap, prcdVars, procSeq, globalVars, nonGlobalVars, 
                          allVarSeq, localVars, A, res_, ia, prcdr, ipr, proc, 
                          ip, lsseq, ilss, lstmt, whl, ls, ils, ilLast, ili, 
                          le, ile, fs, fi, ifi, ifLast, fe, ife, ife2, feSeq, 
                          feSeqLast, fw, ifw, fwLast, cr, icr, gt, sss, isss, 
                          ss, asg, ias, ifst, estmt, iee, wi, iw, vdcl, pvdcl, 
                          exp, ie, elseq, nxt_, ixs, res_E, lst, nxt_E, temp_, 
                          flseq, temp_I, ifsqi, lseq, nxt_Ex, xxtemp1, temp2_, 
                          temp3_, temp4, exlsq, callStmt, prcd, svoci, temp, 
                          res_S, rprcd, rpvi, rpctemp, res_R, vrs, addExpr, 
                          pvexpr, pvi, stk, test, primeVars, sub, expr, sst, 
                          primedVars, localSub_, xlssi, xltemp1, temp1, temp2, 
                          temp3, res_X, sstsq, xprimedVars, localSub_X, res, 
                          xlsssqi, lsstsq, localSub, defSub, nxt, lsstqi, 
                          lsstemp, disjs, defs >>

ELSq42 == /\ pc = "ELSq42"
          /\ rVal' = [ss  |-> Front(lseq) \o
                                   << [type   |-> "with",
                                       var    |-> Last(lseq).var ,
                                       eqOrIn |-> Last(lseq).eqOrIn ,
                                       exp    |-> Last(lseq).exp ,
                                       do     |-> rVal.ss] >> ,
                      rst |-> << >>]
          /\ pc' = "ELSq3"
          /\ UNCHANGED << i, j, gtemp1, gtemp2, gtemp3, gtemp4, result, pMap, 
                          prcdVars, procSeq, globalVars, nonGlobalVars, 
                          allVarSeq, localVars, stack, A, res_, ia, prcdr, ipr, 
                          proc, ip, lsseq, ilss, lstmt, whl, ls, ils, ilLast, 
                          ili, le, ile, fs, fi, ifi, ifLast, fe, ife, ife2, 
                          feSeq, feSeqLast, fw, ifw, fwLast, cr, icr, gt, sss, 
                          isss, ss, asg, ias, ifst, estmt, iee, wi, iw, vdcl, 
                          pvdcl, exp, ie, elseq, nxt_, ixs, res_E, lst, nxt_E, 
                          temp_, flseq, temp_I, ifsqi, lseq, nxt_Ex, xxtemp1, 
                          temp2_, temp3_, temp4, exlsq, callStmt, prcd, svoci, 
                          temp, res_S, rprcd, rpvi, rpctemp, res_R, vrs, 
                          addExpr, pvexpr, pvi, stk, test, primeVars, sub, 
                          expr, sst, primedVars, localSub_, xlssi, xltemp1, 
                          temp1, temp2, temp3, res_X, sstsq, xprimedVars, 
                          localSub_X, res, xlsssqi, lsstsq, localSub, defSub, 
                          nxt, lsstqi, lsstemp, disjs, defs, str >>

ELSq51 == /\ pc = "ELSq51"
          /\ IF exlsq > 0
                THEN /\ /\ lseq' = Last(lseq).ors[exlsq]
                        /\ nxt_Ex' = nxt_Ex
                        /\ stack' = << [ procedure |->  "ExpandLSeq",
                                         pc        |->  "ELSq52",
                                         xxtemp1   |->  xxtemp1,
                                         temp2_    |->  temp2_,
                                         temp3_    |->  temp3_,
                                         temp4     |->  temp4,
                                         exlsq     |->  exlsq,
                                         lseq      |->  lseq,
                                         nxt_Ex    |->  nxt_Ex ] >>
                                     \o stack
                     /\ xxtemp1' = {}
                     /\ temp2_' = {}
                     /\ temp3_' = {}
                     /\ temp4' = {}
                     /\ exlsq' = {}
                     /\ pc' = "ELSq1"
                     /\ UNCHANGED rVal
                ELSE /\ rVal' = [ss  |-> Front(lseq) \o
                                             << [type |-> "either",
                                                 ors  |-> temp2_] >> ,
                                rst |-> << >>]
                     /\ pc' = "ELSq3"
                     /\ UNCHANGED << stack, lseq, nxt_Ex, xxtemp1, temp2_, 
                                     temp3_, temp4, exlsq >>
          /\ UNCHANGED << i, j, gtemp1, gtemp2, gtemp3, gtemp4, result, pMap, 
                          prcdVars, procSeq, globalVars, nonGlobalVars, 
                          allVarSeq, localVars, A, res_, ia, prcdr, ipr, proc, 
                          ip, lsseq, ilss, lstmt, whl, ls, ils, ilLast, ili, 
                          le, ile, fs, fi, ifi, ifLast, fe, ife, ife2, feSeq, 
                          feSeqLast, fw, ifw, fwLast, cr, icr, gt, sss, isss, 
                          ss, asg, ias, ifst, estmt, iee, wi, iw, vdcl, pvdcl, 
                          exp, ie, elseq, nxt_, ixs, res_E, lst, nxt_E, temp_, 
                          flseq, temp_I, ifsqi, callStmt, prcd, svoci, temp, 
                          res_S, rprcd, rpvi, rpctemp, res_R, vrs, addExpr, 
                          pvexpr, pvi, stk, test, primeVars, sub, expr, sst, 
                          primedVars, localSub_, xlssi, xltemp1, temp1, temp2, 
                          temp3, res_X, sstsq, xprimedVars, localSub_X, res, 
                          xlsssqi, lsstsq, localSub, defSub, nxt, lsstqi, 
                          lsstemp, disjs, defs, str >>

ELSq52 == /\ pc = "ELSq52"
          /\ IF rVal.rst # << >>
                THEN /\ /\ stack' = << [ procedure |->  "Error",
                                         pc        |->  "ELSq53",
                                         str       |->  str ] >>
                                     \o stack
                        /\ str' = "6: Label in `either'"
                     /\ pc' = "Error1"
                ELSE /\ pc' = "ELSq53"
                     /\ UNCHANGED << stack, str >>
          /\ UNCHANGED << i, j, gtemp1, gtemp2, gtemp3, gtemp4, result, rVal, 
                          pMap, prcdVars, procSeq, globalVars, nonGlobalVars, 
                          allVarSeq, localVars, A, res_, ia, prcdr, ipr, proc, 
                          ip, lsseq, ilss, lstmt, whl, ls, ils, ilLast, ili, 
                          le, ile, fs, fi, ifi, ifLast, fe, ife, ife2, feSeq, 
                          feSeqLast, fw, ifw, fwLast, cr, icr, gt, sss, isss, 
                          ss, asg, ias, ifst, estmt, iee, wi, iw, vdcl, pvdcl, 
                          exp, ie, elseq, nxt_, ixs, res_E, lst, nxt_E, temp_, 
                          flseq, temp_I, ifsqi, lseq, nxt_Ex, xxtemp1, temp2_, 
                          temp3_, temp4, exlsq, callStmt, prcd, svoci, temp, 
                          res_S, rprcd, rpvi, rpctemp, res_R, vrs, addExpr, 
                          pvexpr, pvi, stk, test, primeVars, sub, expr, sst, 
                          primedVars, localSub_, xlssi, xltemp1, temp1, temp2, 
                          temp3, res_X, sstsq, xprimedVars, localSub_X, res, 
                          xlsssqi, lsstsq, localSub, defSub, nxt, lsstqi, 
                          lsstemp, disjs, defs >>

ELSq53 == /\ pc = "ELSq53"
          /\ temp2_' = <<rVal.ss>> \o temp2_
          /\ exlsq' = exlsq - 1
          /\ pc' = "ELSq51"
          /\ UNCHANGED << i, j, gtemp1, gtemp2, gtemp3, gtemp4, result, rVal, 
                          pMap, prcdVars, procSeq, globalVars, nonGlobalVars, 
                          allVarSeq, localVars, stack, A, res_, ia, prcdr, ipr, 
                          proc, ip, lsseq, ilss, lstmt, whl, ls, ils, ilLast, 
                          ili, le, ile, fs, fi, ifi, ifLast, fe, ife, ife2, 
                          feSeq, feSeqLast, fw, ifw, fwLast, cr, icr, gt, sss, 
                          isss, ss, asg, ias, ifst, estmt, iee, wi, iw, vdcl, 
                          pvdcl, exp, ie, elseq, nxt_, ixs, res_E, lst, nxt_E, 
                          temp_, flseq, temp_I, ifsqi, lseq, nxt_Ex, xxtemp1, 
                          temp3_, temp4, callStmt, prcd, svoci, temp, res_S, 
                          rprcd, rpvi, rpctemp, res_R, vrs, addExpr, pvexpr, 
                          pvi, stk, test, primeVars, sub, expr, sst, 
                          primedVars, localSub_, xlssi, xltemp1, temp1, temp2, 
                          temp3, res_X, sstsq, xprimedVars, localSub_X, res, 
                          xlsssqi, lsstsq, localSub, defSub, nxt, lsstqi, 
                          lsstemp, disjs, defs, str >>

ELSq60 == /\ pc = "ELSq60"
          /\ temp2_' = <<"[", "procedure", "|->">> \o Quote(Last(lseq).to)                                \o  << ",", "@pc@", "|->" >>
                          \o  Quote(nxt_Ex)
          /\ exlsq' = 1
          /\ pc' = "ELSq61"
          /\ UNCHANGED << i, j, gtemp1, gtemp2, gtemp3, gtemp4, result, rVal, 
                          pMap, prcdVars, procSeq, globalVars, nonGlobalVars, 
                          allVarSeq, localVars, stack, A, res_, ia, prcdr, ipr, 
                          proc, ip, lsseq, ilss, lstmt, whl, ls, ils, ilLast, 
                          ili, le, ile, fs, fi, ifi, ifLast, fe, ife, ife2, 
                          feSeq, feSeqLast, fw, ifw, fwLast, cr, icr, gt, sss, 
                          isss, ss, asg, ias, ifst, estmt, iee, wi, iw, vdcl, 
                          pvdcl, exp, ie, elseq, nxt_, ixs, res_E, lst, nxt_E, 
                          temp_, flseq, temp_I, ifsqi, lseq, nxt_Ex, xxtemp1, 
                          temp3_, temp4, callStmt, prcd, svoci, temp, res_S, 
                          rprcd, rpvi, rpctemp, res_R, vrs, addExpr, pvexpr, 
                          pvi, stk, test, primeVars, sub, expr, sst, 
                          primedVars, localSub_, xlssi, xltemp1, temp1, temp2, 
                          temp3, res_X, sstsq, xprimedVars, localSub_X, res, 
                          xlsssqi, lsstsq, localSub, defSub, nxt, lsstqi, 
                          lsstemp, disjs, defs, str >>

ELSq61 == /\ pc = "ELSq61"
          /\ IF exlsq \leq Len(pMap[xxtemp1].params)
                THEN /\ temp2_' = temp2_ \o
                                   <<",", pMap[xxtemp1].params[exlsq], "|->",
                                      pMap[xxtemp1].params[exlsq]>>
                     /\ exlsq' = exlsq + 1
                     /\ pc' = "ELSq61"
                ELSE /\ exlsq' = 1
                     /\ pc' = "ELSq62"
                     /\ UNCHANGED temp2_
          /\ UNCHANGED << i, j, gtemp1, gtemp2, gtemp3, gtemp4, result, rVal, 
                          pMap, prcdVars, procSeq, globalVars, nonGlobalVars, 
                          allVarSeq, localVars, stack, A, res_, ia, prcdr, ipr, 
                          proc, ip, lsseq, ilss, lstmt, whl, ls, ils, ilLast, 
                          ili, le, ile, fs, fi, ifi, ifLast, fe, ife, ife2, 
                          feSeq, feSeqLast, fw, ifw, fwLast, cr, icr, gt, sss, 
                          isss, ss, asg, ias, ifst, estmt, iee, wi, iw, vdcl, 
                          pvdcl, exp, ie, elseq, nxt_, ixs, res_E, lst, nxt_E, 
                          temp_, flseq, temp_I, ifsqi, lseq, nxt_Ex, xxtemp1, 
                          temp3_, temp4, callStmt, prcd, svoci, temp, res_S, 
                          rprcd, rpvi, rpctemp, res_R, vrs, addExpr, pvexpr, 
                          pvi, stk, test, primeVars, sub, expr, sst, 
                          primedVars, localSub_, xlssi, xltemp1, temp1, temp2, 
                          temp3, res_X, sstsq, xprimedVars, localSub_X, res, 
                          xlsssqi, lsstsq, localSub, defSub, nxt, lsstqi, 
                          lsstemp, disjs, defs, str >>

ELSq62 == /\ pc = "ELSq62"
          /\ IF exlsq \leq Len(pMap[xxtemp1].vars)
                THEN /\ temp2_' = temp2_ \o
                                   <<",", pMap[xxtemp1].vars[exlsq], "|->",
                                      pMap[xxtemp1].vars[exlsq]>>
                     /\ exlsq' = exlsq + 1
                     /\ pc' = "ELSq62"
                ELSE /\ pc' = "ELSq63"
                     /\ UNCHANGED << temp2_, exlsq >>
          /\ UNCHANGED << i, j, gtemp1, gtemp2, gtemp3, gtemp4, result, rVal, 
                          pMap, prcdVars, procSeq, globalVars, nonGlobalVars, 
                          allVarSeq, localVars, stack, A, res_, ia, prcdr, ipr, 
                          proc, ip, lsseq, ilss, lstmt, whl, ls, ils, ilLast, 
                          ili, le, ile, fs, fi, ifi, ifLast, fe, ife, ife2, 
                          feSeq, feSeqLast, fw, ifw, fwLast, cr, icr, gt, sss, 
                          isss, ss, asg, ias, ifst, estmt, iee, wi, iw, vdcl, 
                          pvdcl, exp, ie, elseq, nxt_, ixs, res_E, lst, nxt_E, 
                          temp_, flseq, temp_I, ifsqi, lseq, nxt_Ex, xxtemp1, 
                          temp3_, temp4, callStmt, prcd, svoci, temp, res_S, 
                          rprcd, rpvi, rpctemp, res_R, vrs, addExpr, pvexpr, 
                          pvi, stk, test, primeVars, sub, expr, sst, 
                          primedVars, localSub_, xlssi, xltemp1, temp1, temp2, 
                          temp3, res_X, sstsq, xprimedVars, localSub_X, res, 
                          xlsssqi, lsstsq, localSub, defSub, nxt, lsstqi, 
                          lsstemp, disjs, defs, str >>

ELSq63 == /\ pc = "ELSq63"
          /\ temp2_' = temp2_ \o <<"]">>
          /\ /\ callStmt' = Last(lseq)
             /\ prcd' = xxtemp1
             /\ stack' = << [ procedure |->  "SetPrcdVarsOnCall",
                              pc        |->  "ELSq64",
                              svoci     |->  svoci,
                              temp      |->  temp,
                              res_S     |->  res_S,
                              callStmt  |->  callStmt,
                              prcd      |->  prcd ] >>
                          \o stack
          /\ svoci' = {}
          /\ temp' = {}
          /\ res_S' = << >>
          /\ pc' = "SPV1"
          /\ UNCHANGED << i, j, gtemp1, gtemp2, gtemp3, gtemp4, result, rVal, 
                          pMap, prcdVars, procSeq, globalVars, nonGlobalVars, 
                          allVarSeq, localVars, A, res_, ia, prcdr, ipr, proc, 
                          ip, lsseq, ilss, lstmt, whl, ls, ils, ilLast, ili, 
                          le, ile, fs, fi, ifi, ifLast, fe, ife, ife2, feSeq, 
                          feSeqLast, fw, ifw, fwLast, cr, icr, gt, sss, isss, 
                          ss, asg, ias, ifst, estmt, iee, wi, iw, vdcl, pvdcl, 
                          exp, ie, elseq, nxt_, ixs, res_E, lst, nxt_E, temp_, 
                          flseq, temp_I, ifsqi, lseq, nxt_Ex, xxtemp1, temp3_, 
                          temp4, exlsq, rprcd, rpvi, rpctemp, res_R, vrs, 
                          addExpr, pvexpr, pvi, stk, test, primeVars, sub, 
                          expr, sst, primedVars, localSub_, xlssi, xltemp1, 
                          temp1, temp2, temp3, res_X, sstsq, xprimedVars, 
                          localSub_X, res, xlsssqi, lsstsq, localSub, defSub, 
                          nxt, lsstqi, lsstemp, disjs, defs, str >>

ELSq64 == /\ pc = "ELSq64"
          /\ temp3_' = rVal
          /\ rVal' = [ss |->
                       Front(lseq) \o
                         <<PCAssign(pMap[xxtemp1].label),
                           [type |-> "assignment",
                            ass  |->
                              << [lhs |-> [var |-> "@stack@", sub |-> << >>],
                                  rhs |-> <<"<<" >> \o temp2_ \o
                                           << ">>", "\\o", "@stack@">>]
                              >> ] >> \o
                       temp3_',
                      rst |-> << >>]
          /\ pc' = "ELSq3"
          /\ UNCHANGED << i, j, gtemp1, gtemp2, gtemp3, gtemp4, result, pMap, 
                          prcdVars, procSeq, globalVars, nonGlobalVars, 
                          allVarSeq, localVars, stack, A, res_, ia, prcdr, ipr, 
                          proc, ip, lsseq, ilss, lstmt, whl, ls, ils, ilLast, 
                          ili, le, ile, fs, fi, ifi, ifLast, fe, ife, ife2, 
                          feSeq, feSeqLast, fw, ifw, fwLast, cr, icr, gt, sss, 
                          isss, ss, asg, ias, ifst, estmt, iee, wi, iw, vdcl, 
                          pvdcl, exp, ie, elseq, nxt_, ixs, res_E, lst, nxt_E, 
                          temp_, flseq, temp_I, ifsqi, lseq, nxt_Ex, xxtemp1, 
                          temp2_, temp4, exlsq, callStmt, prcd, svoci, temp, 
                          res_S, rprcd, rpvi, rpctemp, res_R, vrs, addExpr, 
                          pvexpr, pvi, stk, test, primeVars, sub, expr, sst, 
                          primedVars, localSub_, xlssi, xltemp1, temp1, temp2, 
                          temp3, res_X, sstsq, xprimedVars, localSub_X, res, 
                          xlsssqi, lsstsq, localSub, defSub, nxt, lsstqi, 
                          lsstemp, disjs, defs, str >>

ELSq65 == /\ pc = "ELSq65"
          /\ rVal' = [ss |->
                       Front(lseq) \o
                         << [type |-> "assignment",
                             ass  |-> << [lhs |-> [var |-> "@pc@",
                                                   sub |-> << >>],
                                          rhs |-> <<"Head", "(", "@stack@",
                                                       ")", ".", "@pc@">> ]
                                        >>] >> \o
                         rVal \o
                          << [type |-> "assignment",
                              ass  |-> << [lhs |-> [var |-> "@stack@",
                                                    sub |-> << >>],
                                            rhs |-> <<"Tail", "(",
                                                       "@stack@", ")">>
                                          ] >>] >> ,
                      rst |-> << >>]
          /\ pc' = "ELSq3"
          /\ UNCHANGED << i, j, gtemp1, gtemp2, gtemp3, gtemp4, result, pMap, 
                          prcdVars, procSeq, globalVars, nonGlobalVars, 
                          allVarSeq, localVars, stack, A, res_, ia, prcdr, ipr, 
                          proc, ip, lsseq, ilss, lstmt, whl, ls, ils, ilLast, 
                          ili, le, ile, fs, fi, ifi, ifLast, fe, ife, ife2, 
                          feSeq, feSeqLast, fw, ifw, fwLast, cr, icr, gt, sss, 
                          isss, ss, asg, ias, ifst, estmt, iee, wi, iw, vdcl, 
                          pvdcl, exp, ie, elseq, nxt_, ixs, res_E, lst, nxt_E, 
                          temp_, flseq, temp_I, ifsqi, lseq, nxt_Ex, xxtemp1, 
                          temp2_, temp3_, temp4, exlsq, callStmt, prcd, svoci, 
                          temp, res_S, rprcd, rpvi, rpctemp, res_R, vrs, 
                          addExpr, pvexpr, pvi, stk, test, primeVars, sub, 
                          expr, sst, primedVars, localSub_, xlssi, xltemp1, 
                          temp1, temp2, temp3, res_X, sstsq, xprimedVars, 
                          localSub_X, res, xlsssqi, lsstsq, localSub, defSub, 
                          nxt, lsstqi, lsstemp, disjs, defs, str >>

ELSq8 == /\ pc = "ELSq8"
         /\ rVal' = [ss  |-> Front(lseq) \o temp4 \o rVal,
                     rst |-> << >>]
         /\ pc' = "ELSq3"
         /\ UNCHANGED << i, j, gtemp1, gtemp2, gtemp3, gtemp4, result, pMap, 
                         prcdVars, procSeq, globalVars, nonGlobalVars, 
                         allVarSeq, localVars, stack, A, res_, ia, prcdr, ipr, 
                         proc, ip, lsseq, ilss, lstmt, whl, ls, ils, ilLast, 
                         ili, le, ile, fs, fi, ifi, ifLast, fe, ife, ife2, 
                         feSeq, feSeqLast, fw, ifw, fwLast, cr, icr, gt, sss, 
                         isss, ss, asg, ias, ifst, estmt, iee, wi, iw, vdcl, 
                         pvdcl, exp, ie, elseq, nxt_, ixs, res_E, lst, nxt_E, 
                         temp_, flseq, temp_I, ifsqi, lseq, nxt_Ex, xxtemp1, 
                         temp2_, temp3_, temp4, exlsq, callStmt, prcd, svoci, 
                         temp, res_S, rprcd, rpvi, rpctemp, res_R, vrs, 
                         addExpr, pvexpr, pvi, stk, test, primeVars, sub, expr, 
                         sst, primedVars, localSub_, xlssi, xltemp1, temp1, 
                         temp2, temp3, res_X, sstsq, xprimedVars, localSub_X, 
                         res, xlsssqi, lsstsq, localSub, defSub, nxt, lsstqi, 
                         lsstemp, disjs, defs, str >>

ELSq80 == /\ pc = "ELSq80"
          /\ exlsq' = 1
          /\ pc' = "ELSq81"
          /\ UNCHANGED << i, j, gtemp1, gtemp2, gtemp3, gtemp4, result, rVal, 
                          pMap, prcdVars, procSeq, globalVars, nonGlobalVars, 
                          allVarSeq, localVars, stack, A, res_, ia, prcdr, ipr, 
                          proc, ip, lsseq, ilss, lstmt, whl, ls, ils, ilLast, 
                          ili, le, ile, fs, fi, ifi, ifLast, fe, ife, ife2, 
                          feSeq, feSeqLast, fw, ifw, fwLast, cr, icr, gt, sss, 
                          isss, ss, asg, ias, ifst, estmt, iee, wi, iw, vdcl, 
                          pvdcl, exp, ie, elseq, nxt_, ixs, res_E, lst, nxt_E, 
                          temp_, flseq, temp_I, ifsqi, lseq, nxt_Ex, xxtemp1, 
                          temp2_, temp3_, temp4, callStmt, prcd, svoci, temp, 
                          res_S, rprcd, rpvi, rpctemp, res_R, vrs, addExpr, 
                          pvexpr, pvi, stk, test, primeVars, sub, expr, sst, 
                          primedVars, localSub_, xlssi, xltemp1, temp1, temp2, 
                          temp3, res_X, sstsq, xprimedVars, localSub_X, res, 
                          xlsssqi, lsstsq, localSub, defSub, nxt, lsstqi, 
                          lsstemp, disjs, defs, str >>

ELSq81 == /\ pc = "ELSq81"
          /\ IF exlsq \leq Len(pMap[xxtemp1].params)
                THEN /\ temp2_' = temp2_ \o
                                   <<",", pMap[xxtemp1].params[exlsq], "|->",
                                      pMap[xxtemp1].params[exlsq]>>
                     /\ exlsq' = exlsq + 1
                     /\ pc' = "ELSq81"
                ELSE /\ exlsq' = 1
                     /\ pc' = "ELSq82"
                     /\ UNCHANGED temp2_
          /\ UNCHANGED << i, j, gtemp1, gtemp2, gtemp3, gtemp4, result, rVal, 
                          pMap, prcdVars, procSeq, globalVars, nonGlobalVars, 
                          allVarSeq, localVars, stack, A, res_, ia, prcdr, ipr, 
                          proc, ip, lsseq, ilss, lstmt, whl, ls, ils, ilLast, 
                          ili, le, ile, fs, fi, ifi, ifLast, fe, ife, ife2, 
                          feSeq, feSeqLast, fw, ifw, fwLast, cr, icr, gt, sss, 
                          isss, ss, asg, ias, ifst, estmt, iee, wi, iw, vdcl, 
                          pvdcl, exp, ie, elseq, nxt_, ixs, res_E, lst, nxt_E, 
                          temp_, flseq, temp_I, ifsqi, lseq, nxt_Ex, xxtemp1, 
                          temp3_, temp4, callStmt, prcd, svoci, temp, res_S, 
                          rprcd, rpvi, rpctemp, res_R, vrs, addExpr, pvexpr, 
                          pvi, stk, test, primeVars, sub, expr, sst, 
                          primedVars, localSub_, xlssi, xltemp1, temp1, temp2, 
                          temp3, res_X, sstsq, xprimedVars, localSub_X, res, 
                          xlsssqi, lsstsq, localSub, defSub, nxt, lsstqi, 
                          lsstemp, disjs, defs, str >>

ELSq82 == /\ pc = "ELSq82"
          /\ IF exlsq \leq Len(pMap[xxtemp1].vars)
                THEN /\ temp2_' = temp2_ \o
                                   <<",", pMap[xxtemp1].vars[exlsq], "|->",
                                      pMap[xxtemp1].vars[exlsq]>>
                     /\ exlsq' = exlsq + 1
                     /\ pc' = "ELSq82"
                ELSE /\ pc' = "ELSq83"
                     /\ UNCHANGED << temp2_, exlsq >>
          /\ UNCHANGED << i, j, gtemp1, gtemp2, gtemp3, gtemp4, result, rVal, 
                          pMap, prcdVars, procSeq, globalVars, nonGlobalVars, 
                          allVarSeq, localVars, stack, A, res_, ia, prcdr, ipr, 
                          proc, ip, lsseq, ilss, lstmt, whl, ls, ils, ilLast, 
                          ili, le, ile, fs, fi, ifi, ifLast, fe, ife, ife2, 
                          feSeq, feSeqLast, fw, ifw, fwLast, cr, icr, gt, sss, 
                          isss, ss, asg, ias, ifst, estmt, iee, wi, iw, vdcl, 
                          pvdcl, exp, ie, elseq, nxt_, ixs, res_E, lst, nxt_E, 
                          temp_, flseq, temp_I, ifsqi, lseq, nxt_Ex, xxtemp1, 
                          temp3_, temp4, callStmt, prcd, svoci, temp, res_S, 
                          rprcd, rpvi, rpctemp, res_R, vrs, addExpr, pvexpr, 
                          pvi, stk, test, primeVars, sub, expr, sst, 
                          primedVars, localSub_, xlssi, xltemp1, temp1, temp2, 
                          temp3, res_X, sstsq, xprimedVars, localSub_X, res, 
                          xlsssqi, lsstsq, localSub, defSub, nxt, lsstqi, 
                          lsstemp, disjs, defs, str >>

ELSq83 == /\ pc = "ELSq83"
          /\ temp2_' = temp2_ \o <<"]">>
          /\ /\ callStmt' = Last(lseq)
             /\ prcd' = Last(lseq).to
             /\ stack' = << [ procedure |->  "SetPrcdVarsOnCall",
                              pc        |->  "ELSq84",
                              svoci     |->  svoci,
                              temp      |->  temp,
                              res_S     |->  res_S,
                              callStmt  |->  callStmt,
                              prcd      |->  prcd ] >>
                          \o stack
          /\ svoci' = {}
          /\ temp' = {}
          /\ res_S' = << >>
          /\ pc' = "SPV1"
          /\ UNCHANGED << i, j, gtemp1, gtemp2, gtemp3, gtemp4, result, rVal, 
                          pMap, prcdVars, procSeq, globalVars, nonGlobalVars, 
                          allVarSeq, localVars, A, res_, ia, prcdr, ipr, proc, 
                          ip, lsseq, ilss, lstmt, whl, ls, ils, ilLast, ili, 
                          le, ile, fs, fi, ifi, ifLast, fe, ife, ife2, feSeq, 
                          feSeqLast, fw, ifw, fwLast, cr, icr, gt, sss, isss, 
                          ss, asg, ias, ifst, estmt, iee, wi, iw, vdcl, pvdcl, 
                          exp, ie, elseq, nxt_, ixs, res_E, lst, nxt_E, temp_, 
                          flseq, temp_I, ifsqi, lseq, nxt_Ex, xxtemp1, temp3_, 
                          temp4, exlsq, rprcd, rpvi, rpctemp, res_R, vrs, 
                          addExpr, pvexpr, pvi, stk, test, primeVars, sub, 
                          expr, sst, primedVars, localSub_, xlssi, xltemp1, 
                          temp1, temp2, temp3, res_X, sstsq, xprimedVars, 
                          localSub_X, res, xlsssqi, lsstsq, localSub, defSub, 
                          nxt, lsstqi, lsstemp, disjs, defs, str >>

ELSq84 == /\ pc = "ELSq84"
          /\ temp3_' = rVal
          /\ /\ rprcd' = Last(lseq).from
             /\ stack' = << [ procedure |->  "RestorePrcdVarsFrom",
                              pc        |->  "ELSq85",
                              rpvi      |->  rpvi,
                              rpctemp   |->  rpctemp,
                              res_R     |->  res_R,
                              rprcd     |->  rprcd ] >>
                          \o stack
          /\ rpvi' = {}
          /\ rpctemp' = {}
          /\ res_R' = << >>
          /\ pc' = "RPV1"
          /\ UNCHANGED << i, j, gtemp1, gtemp2, gtemp3, gtemp4, result, rVal, 
                          pMap, prcdVars, procSeq, globalVars, nonGlobalVars, 
                          allVarSeq, localVars, A, res_, ia, prcdr, ipr, proc, 
                          ip, lsseq, ilss, lstmt, whl, ls, ils, ilLast, ili, 
                          le, ile, fs, fi, ifi, ifLast, fe, ife, ife2, feSeq, 
                          feSeqLast, fw, ifw, fwLast, cr, icr, gt, sss, isss, 
                          ss, asg, ias, ifst, estmt, iee, wi, iw, vdcl, pvdcl, 
                          exp, ie, elseq, nxt_, ixs, res_E, lst, nxt_E, temp_, 
                          flseq, temp_I, ifsqi, lseq, nxt_Ex, xxtemp1, temp2_, 
                          temp4, exlsq, callStmt, prcd, svoci, temp, res_S, 
                          vrs, addExpr, pvexpr, pvi, stk, test, primeVars, sub, 
                          expr, sst, primedVars, localSub_, xlssi, xltemp1, 
                          temp1, temp2, temp3, res_X, sstsq, xprimedVars, 
                          localSub_X, res, xlsssqi, lsstsq, localSub, defSub, 
                          nxt, lsstqi, lsstemp, disjs, defs, str >>

ELSq85 == /\ pc = "ELSq85"
          /\ temp3_' = temp3_ \o rVal
          /\ rVal' = [ss  |-> Front(lseq) \o temp4 \o
                       <<AssSeqToMultiAss(
                          <<[type |-> "assignment",
                             ass  |-> << [lhs |->
                                           [var |-> "@stack@",
                                            sub |-> <<"[", "1", "]">>],
                                          rhs |-> temp2_]
                                       >>]>>
                           \o temp3_' ) >>,
                      rst |-> << >>]
          /\ pc' = "ELSq3"
          /\ UNCHANGED << i, j, gtemp1, gtemp2, gtemp3, gtemp4, result, pMap, 
                          prcdVars, procSeq, globalVars, nonGlobalVars, 
                          allVarSeq, localVars, stack, A, res_, ia, prcdr, ipr, 
                          proc, ip, lsseq, ilss, lstmt, whl, ls, ils, ilLast, 
                          ili, le, ile, fs, fi, ifi, ifLast, fe, ife, ife2, 
                          feSeq, feSeqLast, fw, ifw, fwLast, cr, icr, gt, sss, 
                          isss, ss, asg, ias, ifst, estmt, iee, wi, iw, vdcl, 
                          pvdcl, exp, ie, elseq, nxt_, ixs, res_E, lst, nxt_E, 
                          temp_, flseq, temp_I, ifsqi, lseq, nxt_Ex, xxtemp1, 
                          temp2_, temp4, exlsq, callStmt, prcd, svoci, temp, 
                          res_S, rprcd, rpvi, rpctemp, res_R, vrs, addExpr, 
                          pvexpr, pvi, stk, test, primeVars, sub, expr, sst, 
                          primedVars, localSub_, xlssi, xltemp1, temp1, temp2, 
                          temp3, res_X, sstsq, xprimedVars, localSub_X, res, 
                          xlsssqi, lsstsq, localSub, defSub, nxt, lsstqi, 
                          lsstemp, disjs, defs, str >>

ELSq3 == /\ pc = "ELSq3"
         /\ pc' = Head(stack).pc
         /\ xxtemp1' = Head(stack).xxtemp1
         /\ temp2_' = Head(stack).temp2_
         /\ temp3_' = Head(stack).temp3_
         /\ temp4' = Head(stack).temp4
         /\ exlsq' = Head(stack).exlsq
         /\ lseq' = Head(stack).lseq
         /\ nxt_Ex' = Head(stack).nxt_Ex
         /\ stack' = Tail(stack)
         /\ UNCHANGED << i, j, gtemp1, gtemp2, gtemp3, gtemp4, result, rVal, 
                         pMap, prcdVars, procSeq, globalVars, nonGlobalVars, 
                         allVarSeq, localVars, A, res_, ia, prcdr, ipr, proc, 
                         ip, lsseq, ilss, lstmt, whl, ls, ils, ilLast, ili, le, 
                         ile, fs, fi, ifi, ifLast, fe, ife, ife2, feSeq, 
                         feSeqLast, fw, ifw, fwLast, cr, icr, gt, sss, isss, 
                         ss, asg, ias, ifst, estmt, iee, wi, iw, vdcl, pvdcl, 
                         exp, ie, elseq, nxt_, ixs, res_E, lst, nxt_E, temp_, 
                         flseq, temp_I, ifsqi, callStmt, prcd, svoci, temp, 
                         res_S, rprcd, rpvi, rpctemp, res_R, vrs, addExpr, 
                         pvexpr, pvi, stk, test, primeVars, sub, expr, sst, 
                         primedVars, localSub_, xlssi, xltemp1, temp1, temp2, 
                         temp3, res_X, sstsq, xprimedVars, localSub_X, res, 
                         xlsssqi, lsstsq, localSub, defSub, nxt, lsstqi, 
                         lsstemp, disjs, defs, str >>

ExpandLSeq == ELSq1 \/ ELSq2 \/ ELSq31 \/ ELSq32 \/ ELSq33 \/ ELSq34
                 \/ ELSq35 \/ ELSq71 \/ ELSq72 \/ ELSq73 \/ ELSq74 \/ ELSq75
                 \/ ELSq11 \/ ELSq12 \/ ELSq13 \/ ELSq14 \/ ELSq15 \/ ELSq41
                 \/ ELSq42 \/ ELSq51 \/ ELSq52 \/ ELSq53 \/ ELSq60 \/ ELSq61
                 \/ ELSq62 \/ ELSq63 \/ ELSq64 \/ ELSq65 \/ ELSq8 \/ ELSq80
                 \/ ELSq81 \/ ELSq82 \/ ELSq83 \/ ELSq84 \/ ELSq85 \/ ELSq3

SPV1 == /\ pc = "SPV1"
        /\ svoci' = 1
        /\ temp' = << >>
        /\ IF Len(pMap[prcd].params) # Len(callStmt.args)
              THEN /\ /\ stack' = << [ procedure |->  "Error",
                                       pc        |->  "SVP2",
                                       str       |->  str ] >>
                                   \o stack
                      /\ str' =         "15: Procedure " \o <<prcd>> \o
                                "called with wrong number of variables"
                   /\ pc' = "Error1"
              ELSE /\ pc' = "SVP2"
                   /\ UNCHANGED << stack, str >>
        /\ UNCHANGED << i, j, gtemp1, gtemp2, gtemp3, gtemp4, result, rVal, 
                        pMap, prcdVars, procSeq, globalVars, nonGlobalVars, 
                        allVarSeq, localVars, A, res_, ia, prcdr, ipr, proc, 
                        ip, lsseq, ilss, lstmt, whl, ls, ils, ilLast, ili, le, 
                        ile, fs, fi, ifi, ifLast, fe, ife, ife2, feSeq, 
                        feSeqLast, fw, ifw, fwLast, cr, icr, gt, sss, isss, ss, 
                        asg, ias, ifst, estmt, iee, wi, iw, vdcl, pvdcl, exp, 
                        ie, elseq, nxt_, ixs, res_E, lst, nxt_E, temp_, flseq, 
                        temp_I, ifsqi, lseq, nxt_Ex, xxtemp1, temp2_, temp3_, 
                        temp4, exlsq, callStmt, prcd, res_S, rprcd, rpvi, 
                        rpctemp, res_R, vrs, addExpr, pvexpr, pvi, stk, test, 
                        primeVars, sub, expr, sst, primedVars, localSub_, 
                        xlssi, xltemp1, temp1, temp2, temp3, res_X, sstsq, 
                        xprimedVars, localSub_X, res, xlsssqi, lsstsq, 
                        localSub, defSub, nxt, lsstqi, lsstemp, disjs, defs >>

SVP2 == /\ pc = "SVP2"
        /\ IF svoci \leq Len(pMap[prcd].params)
              THEN /\ temp' = temp \o
                               << [lhs |-> [var |-> pMap[prcd].params[svoci], sub |-> << >>],
                                   rhs |-> callStmt.args[svoci] ] >>
                   /\ svoci' = svoci + 1
                   /\ pc' = "SVP2"
                   /\ UNCHANGED res_S
              ELSE /\ IF temp # << >>
                         THEN /\ res_S' = res_S \o <<[type |-> "assignment",
                                                      ass  |-> temp] >>
                         ELSE /\ TRUE
                              /\ UNCHANGED res_S
                   /\ svoci' = 1
                   /\ temp' = << >>
                   /\ pc' = "SVP3"
        /\ UNCHANGED << i, j, gtemp1, gtemp2, gtemp3, gtemp4, result, rVal, 
                        pMap, prcdVars, procSeq, globalVars, nonGlobalVars, 
                        allVarSeq, localVars, stack, A, res_, ia, prcdr, ipr, 
                        proc, ip, lsseq, ilss, lstmt, whl, ls, ils, ilLast, 
                        ili, le, ile, fs, fi, ifi, ifLast, fe, ife, ife2, 
                        feSeq, feSeqLast, fw, ifw, fwLast, cr, icr, gt, sss, 
                        isss, ss, asg, ias, ifst, estmt, iee, wi, iw, vdcl, 
                        pvdcl, exp, ie, elseq, nxt_, ixs, res_E, lst, nxt_E, 
                        temp_, flseq, temp_I, ifsqi, lseq, nxt_Ex, xxtemp1, 
                        temp2_, temp3_, temp4, exlsq, callStmt, prcd, rprcd, 
                        rpvi, rpctemp, res_R, vrs, addExpr, pvexpr, pvi, stk, 
                        test, primeVars, sub, expr, sst, primedVars, localSub_, 
                        xlssi, xltemp1, temp1, temp2, temp3, res_X, sstsq, 
                        xprimedVars, localSub_X, res, xlsssqi, lsstsq, 
                        localSub, defSub, nxt, lsstqi, lsstemp, disjs, defs, 
                        str >>

SVP3 == /\ pc = "SVP3"
        /\ IF svoci \leq Len(pMap[prcd].vars)
              THEN /\ temp' = temp \o
                               << [lhs |-> [var |-> pMap[prcd].vars[svoci], sub |-> << >>],
                                   rhs |-> pMap[prcd].vals[svoci] ] >>
                   /\ svoci' = svoci + 1
                   /\ pc' = "SVP3"
                   /\ UNCHANGED << rVal, res_S >>
              ELSE /\ IF temp # << >>
                         THEN /\ res_S' = res_S \o <<[type |-> "assignment",
                                                      ass  |-> temp] >>
                         ELSE /\ TRUE
                              /\ UNCHANGED res_S
                   /\ rVal' = res_S'
                   /\ pc' = "SVP4"
                   /\ UNCHANGED << svoci, temp >>
        /\ UNCHANGED << i, j, gtemp1, gtemp2, gtemp3, gtemp4, result, pMap, 
                        prcdVars, procSeq, globalVars, nonGlobalVars, 
                        allVarSeq, localVars, stack, A, res_, ia, prcdr, ipr, 
                        proc, ip, lsseq, ilss, lstmt, whl, ls, ils, ilLast, 
                        ili, le, ile, fs, fi, ifi, ifLast, fe, ife, ife2, 
                        feSeq, feSeqLast, fw, ifw, fwLast, cr, icr, gt, sss, 
                        isss, ss, asg, ias, ifst, estmt, iee, wi, iw, vdcl, 
                        pvdcl, exp, ie, elseq, nxt_, ixs, res_E, lst, nxt_E, 
                        temp_, flseq, temp_I, ifsqi, lseq, nxt_Ex, xxtemp1, 
                        temp2_, temp3_, temp4, exlsq, callStmt, prcd, rprcd, 
                        rpvi, rpctemp, res_R, vrs, addExpr, pvexpr, pvi, stk, 
                        test, primeVars, sub, expr, sst, primedVars, localSub_, 
                        xlssi, xltemp1, temp1, temp2, temp3, res_X, sstsq, 
                        xprimedVars, localSub_X, res, xlsssqi, lsstsq, 
                        localSub, defSub, nxt, lsstqi, lsstemp, disjs, defs, 
                        str >>

SVP4 == /\ pc = "SVP4"
        /\ pc' = Head(stack).pc
        /\ svoci' = Head(stack).svoci
        /\ temp' = Head(stack).temp
        /\ res_S' = Head(stack).res_S
        /\ callStmt' = Head(stack).callStmt
        /\ prcd' = Head(stack).prcd
        /\ stack' = Tail(stack)
        /\ UNCHANGED << i, j, gtemp1, gtemp2, gtemp3, gtemp4, result, rVal, 
                        pMap, prcdVars, procSeq, globalVars, nonGlobalVars, 
                        allVarSeq, localVars, A, res_, ia, prcdr, ipr, proc, 
                        ip, lsseq, ilss, lstmt, whl, ls, ils, ilLast, ili, le, 
                        ile, fs, fi, ifi, ifLast, fe, ife, ife2, feSeq, 
                        feSeqLast, fw, ifw, fwLast, cr, icr, gt, sss, isss, ss, 
                        asg, ias, ifst, estmt, iee, wi, iw, vdcl, pvdcl, exp, 
                        ie, elseq, nxt_, ixs, res_E, lst, nxt_E, temp_, flseq, 
                        temp_I, ifsqi, lseq, nxt_Ex, xxtemp1, temp2_, temp3_, 
                        temp4, exlsq, rprcd, rpvi, rpctemp, res_R, vrs, 
                        addExpr, pvexpr, pvi, stk, test, primeVars, sub, expr, 
                        sst, primedVars, localSub_, xlssi, xltemp1, temp1, 
                        temp2, temp3, res_X, sstsq, xprimedVars, localSub_X, 
                        res, xlsssqi, lsstsq, localSub, defSub, nxt, lsstqi, 
                        lsstemp, disjs, defs, str >>

SetPrcdVarsOnCall == SPV1 \/ SVP2 \/ SVP3 \/ SVP4

RPV1 == /\ pc = "RPV1"
        /\ rpctemp' = << >>
        /\ rpvi' = 1
        /\ pc' = "RPV2"
        /\ UNCHANGED << i, j, gtemp1, gtemp2, gtemp3, gtemp4, result, rVal, 
                        pMap, prcdVars, procSeq, globalVars, nonGlobalVars, 
                        allVarSeq, localVars, stack, A, res_, ia, prcdr, ipr, 
                        proc, ip, lsseq, ilss, lstmt, whl, ls, ils, ilLast, 
                        ili, le, ile, fs, fi, ifi, ifLast, fe, ife, ife2, 
                        feSeq, feSeqLast, fw, ifw, fwLast, cr, icr, gt, sss, 
                        isss, ss, asg, ias, ifst, estmt, iee, wi, iw, vdcl, 
                        pvdcl, exp, ie, elseq, nxt_, ixs, res_E, lst, nxt_E, 
                        temp_, flseq, temp_I, ifsqi, lseq, nxt_Ex, xxtemp1, 
                        temp2_, temp3_, temp4, exlsq, callStmt, prcd, svoci, 
                        temp, res_S, rprcd, res_R, vrs, addExpr, pvexpr, pvi, 
                        stk, test, primeVars, sub, expr, sst, primedVars, 
                        localSub_, xlssi, xltemp1, temp1, temp2, temp3, res_X, 
                        sstsq, xprimedVars, localSub_X, res, xlsssqi, lsstsq, 
                        localSub, defSub, nxt, lsstqi, lsstemp, disjs, defs, 
                        str >>

RPV2 == /\ pc = "RPV2"
        /\ IF rpvi \leq Len(pMap[rprcd].params)
              THEN /\ rpctemp' =    rpctemp \o
                                 << [lhs |-> [var |-> pMap[rprcd].params[rpvi], sub |-> << >>],
                                     rhs |-> <<"Head", "(", "@stack@", ")", ".",
                                               pMap[rprcd].params[rpvi] >>] >>
                   /\ rpvi' = rpvi + 1
                   /\ pc' = "RPV2"
                   /\ UNCHANGED res_R
              ELSE /\ IF rpctemp # << >>
                         THEN /\ res_R' = <<[type |-> "assignment", ass  |-> rpctemp]>>
                         ELSE /\ TRUE
                              /\ UNCHANGED res_R
                   /\ rpctemp' = << >>
                   /\ rpvi' = 1
                   /\ pc' = "RPV3"
        /\ UNCHANGED << i, j, gtemp1, gtemp2, gtemp3, gtemp4, result, rVal, 
                        pMap, prcdVars, procSeq, globalVars, nonGlobalVars, 
                        allVarSeq, localVars, stack, A, res_, ia, prcdr, ipr, 
                        proc, ip, lsseq, ilss, lstmt, whl, ls, ils, ilLast, 
                        ili, le, ile, fs, fi, ifi, ifLast, fe, ife, ife2, 
                        feSeq, feSeqLast, fw, ifw, fwLast, cr, icr, gt, sss, 
                        isss, ss, asg, ias, ifst, estmt, iee, wi, iw, vdcl, 
                        pvdcl, exp, ie, elseq, nxt_, ixs, res_E, lst, nxt_E, 
                        temp_, flseq, temp_I, ifsqi, lseq, nxt_Ex, xxtemp1, 
                        temp2_, temp3_, temp4, exlsq, callStmt, prcd, svoci, 
                        temp, res_S, rprcd, vrs, addExpr, pvexpr, pvi, stk, 
                        test, primeVars, sub, expr, sst, primedVars, localSub_, 
                        xlssi, xltemp1, temp1, temp2, temp3, res_X, sstsq, 
                        xprimedVars, localSub_X, res, xlsssqi, lsstsq, 
                        localSub, defSub, nxt, lsstqi, lsstemp, disjs, defs, 
                        str >>

RPV3 == /\ pc = "RPV3"
        /\ IF rpvi \leq Len(pMap[rprcd].vars)
              THEN /\ rpctemp' =    rpctemp \o
                                 << [lhs |-> [var |-> pMap[rprcd].vars[rpvi], sub |-> << >>],
                                     rhs |-> <<"Head", "(", "@stack@", ")", ".",
                                               pMap[rprcd].vars[rpvi] >>] >>
                   /\ rpvi' = rpvi + 1
                   /\ pc' = "RPV3"
                   /\ UNCHANGED << rVal, res_R >>
              ELSE /\ IF rpctemp # << >>
                         THEN /\ res_R' = res_R \o <<[type |-> "assignment", ass  |-> rpctemp]>>
                         ELSE /\ TRUE
                              /\ UNCHANGED res_R
                   /\ rVal' = res_R'
                   /\ pc' = "RPV4"
                   /\ UNCHANGED << rpvi, rpctemp >>
        /\ UNCHANGED << i, j, gtemp1, gtemp2, gtemp3, gtemp4, result, pMap, 
                        prcdVars, procSeq, globalVars, nonGlobalVars, 
                        allVarSeq, localVars, stack, A, res_, ia, prcdr, ipr, 
                        proc, ip, lsseq, ilss, lstmt, whl, ls, ils, ilLast, 
                        ili, le, ile, fs, fi, ifi, ifLast, fe, ife, ife2, 
                        feSeq, feSeqLast, fw, ifw, fwLast, cr, icr, gt, sss, 
                        isss, ss, asg, ias, ifst, estmt, iee, wi, iw, vdcl, 
                        pvdcl, exp, ie, elseq, nxt_, ixs, res_E, lst, nxt_E, 
                        temp_, flseq, temp_I, ifsqi, lseq, nxt_Ex, xxtemp1, 
                        temp2_, temp3_, temp4, exlsq, callStmt, prcd, svoci, 
                        temp, res_S, rprcd, vrs, addExpr, pvexpr, pvi, stk, 
                        test, primeVars, sub, expr, sst, primedVars, localSub_, 
                        xlssi, xltemp1, temp1, temp2, temp3, res_X, sstsq, 
                        xprimedVars, localSub_X, res, xlsssqi, lsstsq, 
                        localSub, defSub, nxt, lsstqi, lsstemp, disjs, defs, 
                        str >>

RPV4 == /\ pc = "RPV4"
        /\ pc' = Head(stack).pc
        /\ rpvi' = Head(stack).rpvi
        /\ rpctemp' = Head(stack).rpctemp
        /\ res_R' = Head(stack).res_R
        /\ rprcd' = Head(stack).rprcd
        /\ stack' = Tail(stack)
        /\ UNCHANGED << i, j, gtemp1, gtemp2, gtemp3, gtemp4, result, rVal, 
                        pMap, prcdVars, procSeq, globalVars, nonGlobalVars, 
                        allVarSeq, localVars, A, res_, ia, prcdr, ipr, proc, 
                        ip, lsseq, ilss, lstmt, whl, ls, ils, ilLast, ili, le, 
                        ile, fs, fi, ifi, ifLast, fe, ife, ife2, feSeq, 
                        feSeqLast, fw, ifw, fwLast, cr, icr, gt, sss, isss, ss, 
                        asg, ias, ifst, estmt, iee, wi, iw, vdcl, pvdcl, exp, 
                        ie, elseq, nxt_, ixs, res_E, lst, nxt_E, temp_, flseq, 
                        temp_I, ifsqi, lseq, nxt_Ex, xxtemp1, temp2_, temp3_, 
                        temp4, exlsq, callStmt, prcd, svoci, temp, res_S, vrs, 
                        addExpr, pvexpr, pvi, stk, test, primeVars, sub, expr, 
                        sst, primedVars, localSub_, xlssi, xltemp1, temp1, 
                        temp2, temp3, res_X, sstsq, xprimedVars, localSub_X, 
                        res, xlsssqi, lsstsq, localSub, defSub, nxt, lsstqi, 
                        lsstemp, disjs, defs, str >>

RestorePrcdVarsFrom == RPV1 \/ RPV2 \/ RPV3 \/ RPV4

PV1 == /\ pc = "PV1"
       /\ rVal' = << >>
       /\ pc' = "PV2"
       /\ UNCHANGED << i, j, gtemp1, gtemp2, gtemp3, gtemp4, result, pMap, 
                       prcdVars, procSeq, globalVars, nonGlobalVars, allVarSeq, 
                       localVars, stack, A, res_, ia, prcdr, ipr, proc, ip, 
                       lsseq, ilss, lstmt, whl, ls, ils, ilLast, ili, le, ile, 
                       fs, fi, ifi, ifLast, fe, ife, ife2, feSeq, feSeqLast, 
                       fw, ifw, fwLast, cr, icr, gt, sss, isss, ss, asg, ias, 
                       ifst, estmt, iee, wi, iw, vdcl, pvdcl, exp, ie, elseq, 
                       nxt_, ixs, res_E, lst, nxt_E, temp_, flseq, temp_I, 
                       ifsqi, lseq, nxt_Ex, xxtemp1, temp2_, temp3_, temp4, 
                       exlsq, callStmt, prcd, svoci, temp, res_S, rprcd, rpvi, 
                       rpctemp, res_R, vrs, addExpr, pvexpr, pvi, stk, test, 
                       primeVars, sub, expr, sst, primedVars, localSub_, xlssi, 
                       xltemp1, temp1, temp2, temp3, res_X, sstsq, xprimedVars, 
                       localSub_X, res, xlsssqi, lsstsq, localSub, defSub, nxt, 
                       lsstqi, lsstemp, disjs, defs, str >>

PV2 == /\ pc = "PV2"
       /\ IF pvi \leq Len(pvexpr)
             THEN /\ IF pvexpr[pvi] = "["
                        THEN /\ IF pvi + 2 > Len(pvexpr)
                                   THEN /\ /\ stack' = << [ procedure |->  "Error",
                                                            pc        |->  "PV8",
                                                            str       |->  str ] >>
                                                        \o stack
                                           /\ str' = "8: premature end of expression"
                                        /\ pc' = "Error1"
                                        /\ UNCHANGED << rVal, pvi, stk >>
                                   ELSE /\ IF pvexpr[pvi+2] \in {":", "|->"}
                                              THEN /\ stk' = <<TRUE>> \o stk
                                                   /\ rVal' = rVal \o <<pvexpr[pvi], pvexpr[pvi+1]>>
                                                   /\ pvi' = pvi+2
                                              ELSE /\ stk' = stk \o <<FALSE>>
                                                   /\ UNCHANGED << rVal, pvi >>
                                        /\ pc' = "PV8"
                                        /\ UNCHANGED << stack, str >>
                             /\ UNCHANGED test
                        ELSE /\ IF pvexpr[pvi] = "]"
                                   THEN /\ IF Len(stk) = 0
                                              THEN /\ /\ stack' = << [ procedure |->  "Error",
                                                                       pc        |->  "PV8",
                                                                       str       |->  str ] >>
                                                                   \o stack
                                                      /\ str' = "9: unmatched `]' in expression"
                                                   /\ pc' = "Error1"
                                                   /\ UNCHANGED stk
                                              ELSE /\ stk' = Tail(stk)
                                                   /\ pc' = "PV8"
                                                   /\ UNCHANGED << stack, str >>
                                        /\ UNCHANGED << rVal, pvi, test >>
                                   ELSE /\ IF pvexpr[pvi] = "."
                                              THEN /\ rVal' = rVal \o <<pvexpr[pvi]>>
                                                   /\ pvi' = pvi + 1
                                                   /\ test' = FALSE
                                                   /\ pc' = "PV8"
                                                   /\ UNCHANGED << stack, str >>
                                              ELSE /\ IF /\ pvexpr[pvi] = ","
                                                         /\ (Len(stk) > 0) /\ Head(stk)
                                                         /\ pvi + 2 \leq Len(pvexpr)
                                                         /\ pvexpr[pvi+2] \in {":", "|->"}
                                                         THEN /\ rVal' = rVal \o <<pvexpr[pvi], pvexpr[pvi+1]>>
                                                              /\ pvi' = pvi+2
                                                              /\ pc' = "PV8"
                                                              /\ UNCHANGED << stack, 
                                                                              str >>
                                                         ELSE /\ IF pvexpr[pvi] = "\""
                                                                    THEN /\ IF \/ pvi + 2 > Len(pvexpr)
                                                                               \/ pvexpr[pvi+2] # "\""
                                                                               THEN /\ /\ stack' = << [ procedure |->  "Error",
                                                                                                        pc        |->  "PV8",
                                                                                                        str       |->  str ] >>
                                                                                                    \o stack
                                                                                       /\ str' = "10: unmatched quote in expression"
                                                                                    /\ pc' = "Error1"
                                                                                    /\ UNCHANGED << rVal, 
                                                                                                    pvi >>
                                                                               ELSE /\ rVal' = rVal \o <<pvexpr[pvi], pvexpr[pvi+1]>>
                                                                                    /\ pvi' = pvi+2
                                                                                    /\ pc' = "PV8"
                                                                                    /\ UNCHANGED << stack, 
                                                                                                    str >>
                                                                    ELSE /\ pc' = "PV8"
                                                                         /\ UNCHANGED << rVal, 
                                                                                         stack, 
                                                                                         pvi, 
                                                                                         str >>
                                                   /\ UNCHANGED test
                                        /\ UNCHANGED stk
             ELSE /\ pc' = "PV9"
                  /\ UNCHANGED << rVal, stack, pvi, stk, test, str >>
       /\ UNCHANGED << i, j, gtemp1, gtemp2, gtemp3, gtemp4, result, pMap, 
                       prcdVars, procSeq, globalVars, nonGlobalVars, allVarSeq, 
                       localVars, A, res_, ia, prcdr, ipr, proc, ip, lsseq, 
                       ilss, lstmt, whl, ls, ils, ilLast, ili, le, ile, fs, fi, 
                       ifi, ifLast, fe, ife, ife2, feSeq, feSeqLast, fw, ifw, 
                       fwLast, cr, icr, gt, sss, isss, ss, asg, ias, ifst, 
                       estmt, iee, wi, iw, vdcl, pvdcl, exp, ie, elseq, nxt_, 
                       ixs, res_E, lst, nxt_E, temp_, flseq, temp_I, ifsqi, 
                       lseq, nxt_Ex, xxtemp1, temp2_, temp3_, temp4, exlsq, 
                       callStmt, prcd, svoci, temp, res_S, rprcd, rpvi, 
                       rpctemp, res_R, vrs, addExpr, pvexpr, primeVars, sub, 
                       expr, sst, primedVars, localSub_, xlssi, xltemp1, temp1, 
                       temp2, temp3, res_X, sstsq, xprimedVars, localSub_X, 
                       res, xlsssqi, lsstsq, localSub, defSub, nxt, lsstqi, 
                       lsstemp, disjs, defs >>

PV8 == /\ pc = "PV8"
       /\ IF test /\ (pvi \leq Len(pvexpr))
                  /\ pvexpr[pvi] \in vrs
             THEN /\ rVal' = rVal \o <<pvexpr[pvi]>> \o addExpr
             ELSE /\ rVal' = rVal \o <<pvexpr[pvi]>>
       /\ pvi' = pvi + 1
       /\ test' = TRUE
       /\ pc' = "PV2"
       /\ UNCHANGED << i, j, gtemp1, gtemp2, gtemp3, gtemp4, result, pMap, 
                       prcdVars, procSeq, globalVars, nonGlobalVars, allVarSeq, 
                       localVars, stack, A, res_, ia, prcdr, ipr, proc, ip, 
                       lsseq, ilss, lstmt, whl, ls, ils, ilLast, ili, le, ile, 
                       fs, fi, ifi, ifLast, fe, ife, ife2, feSeq, feSeqLast, 
                       fw, ifw, fwLast, cr, icr, gt, sss, isss, ss, asg, ias, 
                       ifst, estmt, iee, wi, iw, vdcl, pvdcl, exp, ie, elseq, 
                       nxt_, ixs, res_E, lst, nxt_E, temp_, flseq, temp_I, 
                       ifsqi, lseq, nxt_Ex, xxtemp1, temp2_, temp3_, temp4, 
                       exlsq, callStmt, prcd, svoci, temp, res_S, rprcd, rpvi, 
                       rpctemp, res_R, vrs, addExpr, pvexpr, stk, primeVars, 
                       sub, expr, sst, primedVars, localSub_, xlssi, xltemp1, 
                       temp1, temp2, temp3, res_X, sstsq, xprimedVars, 
                       localSub_X, res, xlsssqi, lsstsq, localSub, defSub, nxt, 
                       lsstqi, lsstemp, disjs, defs, str >>

PV9 == /\ pc = "PV9"
       /\ pc' = Head(stack).pc
       /\ pvi' = Head(stack).pvi
       /\ stk' = Head(stack).stk
       /\ test' = Head(stack).test
       /\ vrs' = Head(stack).vrs
       /\ addExpr' = Head(stack).addExpr
       /\ pvexpr' = Head(stack).pvexpr
       /\ stack' = Tail(stack)
       /\ UNCHANGED << i, j, gtemp1, gtemp2, gtemp3, gtemp4, result, rVal, 
                       pMap, prcdVars, procSeq, globalVars, nonGlobalVars, 
                       allVarSeq, localVars, A, res_, ia, prcdr, ipr, proc, ip, 
                       lsseq, ilss, lstmt, whl, ls, ils, ilLast, ili, le, ile, 
                       fs, fi, ifi, ifLast, fe, ife, ife2, feSeq, feSeqLast, 
                       fw, ifw, fwLast, cr, icr, gt, sss, isss, ss, asg, ias, 
                       ifst, estmt, iee, wi, iw, vdcl, pvdcl, exp, ie, elseq, 
                       nxt_, ixs, res_E, lst, nxt_E, temp_, flseq, temp_I, 
                       ifsqi, lseq, nxt_Ex, xxtemp1, temp2_, temp3_, temp4, 
                       exlsq, callStmt, prcd, svoci, temp, res_S, rprcd, rpvi, 
                       rpctemp, res_R, primeVars, sub, expr, sst, primedVars, 
                       localSub_, xlssi, xltemp1, temp1, temp2, temp3, res_X, 
                       sstsq, xprimedVars, localSub_X, res, xlsssqi, lsstsq, 
                       localSub, defSub, nxt, lsstqi, lsstemp, disjs, defs, 
                       str >>

ProcessVars == PV1 \/ PV2 \/ PV8 \/ PV9

PAAS1 == /\ pc = "PAAS1"
         /\ /\ addExpr' = sub
            /\ pvexpr' = expr
            /\ stack' = << [ procedure |->  "ProcessVars",
                             pc        |->  "PAAS2",
                             pvi       |->  pvi,
                             stk       |->  stk,
                             test      |->  test,
                             vrs       |->  vrs,
                             addExpr   |->  addExpr,
                             pvexpr    |->  pvexpr ] >>
                         \o stack
            /\ vrs' = localVars
         /\ pvi' = 1
         /\ stk' = << >>
         /\ test' = TRUE
         /\ pc' = "PV1"
         /\ UNCHANGED << i, j, gtemp1, gtemp2, gtemp3, gtemp4, result, rVal, 
                         pMap, prcdVars, procSeq, globalVars, nonGlobalVars, 
                         allVarSeq, localVars, A, res_, ia, prcdr, ipr, proc, 
                         ip, lsseq, ilss, lstmt, whl, ls, ils, ilLast, ili, le, 
                         ile, fs, fi, ifi, ifLast, fe, ife, ife2, feSeq, 
                         feSeqLast, fw, ifw, fwLast, cr, icr, gt, sss, isss, 
                         ss, asg, ias, ifst, estmt, iee, wi, iw, vdcl, pvdcl, 
                         exp, ie, elseq, nxt_, ixs, res_E, lst, nxt_E, temp_, 
                         flseq, temp_I, ifsqi, lseq, nxt_Ex, xxtemp1, temp2_, 
                         temp3_, temp4, exlsq, callStmt, prcd, svoci, temp, 
                         res_S, rprcd, rpvi, rpctemp, res_R, primeVars, sub, 
                         expr, sst, primedVars, localSub_, xlssi, xltemp1, 
                         temp1, temp2, temp3, res_X, sstsq, xprimedVars, 
                         localSub_X, res, xlsssqi, lsstsq, localSub, defSub, 
                         nxt, lsstqi, lsstemp, disjs, defs, str >>

PAAS2 == /\ pc = "PAAS2"
         /\ /\ addExpr' = <<"'">>
            /\ pvexpr' = rVal
            /\ stack' = << [ procedure |->  "ProcessVars",
                             pc        |->  "PAAS3",
                             pvi       |->  pvi,
                             stk       |->  stk,
                             test      |->  test,
                             vrs       |->  vrs,
                             addExpr   |->  addExpr,
                             pvexpr    |->  pvexpr ] >>
                         \o stack
            /\ vrs' = primeVars
         /\ pvi' = 1
         /\ stk' = << >>
         /\ test' = TRUE
         /\ pc' = "PV1"
         /\ UNCHANGED << i, j, gtemp1, gtemp2, gtemp3, gtemp4, result, rVal, 
                         pMap, prcdVars, procSeq, globalVars, nonGlobalVars, 
                         allVarSeq, localVars, A, res_, ia, prcdr, ipr, proc, 
                         ip, lsseq, ilss, lstmt, whl, ls, ils, ilLast, ili, le, 
                         ile, fs, fi, ifi, ifLast, fe, ife, ife2, feSeq, 
                         feSeqLast, fw, ifw, fwLast, cr, icr, gt, sss, isss, 
                         ss, asg, ias, ifst, estmt, iee, wi, iw, vdcl, pvdcl, 
                         exp, ie, elseq, nxt_, ixs, res_E, lst, nxt_E, temp_, 
                         flseq, temp_I, ifsqi, lseq, nxt_Ex, xxtemp1, temp2_, 
                         temp3_, temp4, exlsq, callStmt, prcd, svoci, temp, 
                         res_S, rprcd, rpvi, rpctemp, res_R, primeVars, sub, 
                         expr, sst, primedVars, localSub_, xlssi, xltemp1, 
                         temp1, temp2, temp3, res_X, sstsq, xprimedVars, 
                         localSub_X, res, xlsssqi, lsstsq, localSub, defSub, 
                         nxt, lsstqi, lsstemp, disjs, defs, str >>

PAAS3 == /\ pc = "PAAS3"
         /\ pc' = Head(stack).pc
         /\ primeVars' = Head(stack).primeVars
         /\ sub' = Head(stack).sub
         /\ expr' = Head(stack).expr
         /\ stack' = Tail(stack)
         /\ UNCHANGED << i, j, gtemp1, gtemp2, gtemp3, gtemp4, result, rVal, 
                         pMap, prcdVars, procSeq, globalVars, nonGlobalVars, 
                         allVarSeq, localVars, A, res_, ia, prcdr, ipr, proc, 
                         ip, lsseq, ilss, lstmt, whl, ls, ils, ilLast, ili, le, 
                         ile, fs, fi, ifi, ifLast, fe, ife, ife2, feSeq, 
                         feSeqLast, fw, ifw, fwLast, cr, icr, gt, sss, isss, 
                         ss, asg, ias, ifst, estmt, iee, wi, iw, vdcl, pvdcl, 
                         exp, ie, elseq, nxt_, ixs, res_E, lst, nxt_E, temp_, 
                         flseq, temp_I, ifsqi, lseq, nxt_Ex, xxtemp1, temp2_, 
                         temp3_, temp4, exlsq, callStmt, prcd, svoci, temp, 
                         res_S, rprcd, rpvi, rpctemp, res_R, vrs, addExpr, 
                         pvexpr, pvi, stk, test, sst, primedVars, localSub_, 
                         xlssi, xltemp1, temp1, temp2, temp3, res_X, sstsq, 
                         xprimedVars, localSub_X, res, xlsssqi, lsstsq, 
                         localSub, defSub, nxt, lsstqi, lsstemp, disjs, defs, 
                         str >>

PrimeAndAddSub == PAAS1 \/ PAAS2 \/ PAAS3

XSt1 == /\ pc = "XSt1"
        /\ res_X' = [action |-> << >>,
                     pVars  |-> primedVars]
        /\ IF sst.type = "assignment"
              THEN /\ xltemp1' = << >>
                   /\ xlssi' = 1
                   /\ pc' = "XSt11"
                   /\ UNCHANGED << stack, primeVars, sub, expr, sstsq, 
                                   xprimedVars, localSub_X, res, xlsssqi, str >>
              ELSE /\ IF sst.type = "if"
                         THEN /\ /\ localSub_X' = localSub_
                                 /\ sstsq' = sst.then
                                 /\ stack' = << [ procedure |->  "XlateSStmtSeq",
                                                  pc        |->  "XSt21",
                                                  res       |->  res,
                                                  xlsssqi   |->  xlsssqi,
                                                  sstsq     |->  sstsq,
                                                  xprimedVars |->  xprimedVars,
                                                  localSub_X |->  localSub_X ] >>
                                              \o stack
                                 /\ xprimedVars' = primedVars
                              /\ res' = {}
                              /\ xlsssqi' = 1
                              /\ pc' = "XStSq1"
                              /\ UNCHANGED << primeVars, sub, expr, xltemp1, 
                                              str >>
                         ELSE /\ IF sst.type = "either"
                                    THEN /\ xltemp1' = << >>
                                         /\ pc' = "XSt31"
                                         /\ UNCHANGED << stack, primeVars, sub, 
                                                         expr, str >>
                                    ELSE /\ IF sst.type = "with"
                                               THEN /\ /\ expr' = sst.exp
                                                       /\ primeVars' = primedVars
                                                       /\ stack' = << [ procedure |->  "PrimeAndAddSub",
                                                                        pc        |->  "XSt41",
                                                                        primeVars |->  primeVars,
                                                                        sub       |->  sub,
                                                                        expr      |->  expr ] >>
                                                                    \o stack
                                                       /\ sub' = localSub_
                                                    /\ pc' = "PAAS1"
                                                    /\ UNCHANGED str
                                               ELSE /\ IF sst.type = "when"
                                                          THEN /\ /\ expr' = sst.exp
                                                                  /\ primeVars' = primedVars
                                                                  /\ stack' = << [ procedure |->  "PrimeAndAddSub",
                                                                                   pc        |->  "XSt6",
                                                                                   primeVars |->  primeVars,
                                                                                   sub       |->  sub,
                                                                                   expr      |->  expr ] >>
                                                                               \o stack
                                                                  /\ sub' = localSub_
                                                               /\ pc' = "PAAS1"
                                                               /\ UNCHANGED str
                                                          ELSE /\ IF sst.type = "print"
                                                                     THEN /\ /\ expr' = sst.exp
                                                                             /\ primeVars' = primedVars
                                                                             /\ stack' = << [ procedure |->  "PrimeAndAddSub",
                                                                                              pc        |->  "XSt7",
                                                                                              primeVars |->  primeVars,
                                                                                              sub       |->  sub,
                                                                                              expr      |->  expr ] >>
                                                                                          \o stack
                                                                             /\ sub' = localSub_
                                                                          /\ pc' = "PAAS1"
                                                                          /\ UNCHANGED str
                                                                     ELSE /\ IF sst.type = "assert"
                                                                                THEN /\ /\ expr' = sst.exp
                                                                                        /\ primeVars' = primedVars
                                                                                        /\ stack' = << [ procedure |->  "PrimeAndAddSub",
                                                                                                         pc        |->  "XSt8",
                                                                                                         primeVars |->  primeVars,
                                                                                                         sub       |->  sub,
                                                                                                         expr      |->  expr ] >>
                                                                                                     \o stack
                                                                                        /\ sub' = localSub_
                                                                                     /\ pc' = "PAAS1"
                                                                                     /\ UNCHANGED str
                                                                                ELSE /\ IF sst.type = "skip"
                                                                                           THEN /\ TRUE
                                                                                                /\ pc' = "XSt99"
                                                                                                /\ UNCHANGED << stack, 
                                                                                                                str >>
                                                                                           ELSE /\ /\ stack' = << [ procedure |->  "Error",
                                                                                                                    pc        |->  "XSt99",
                                                                                                                    str       |->  str ] >>
                                                                                                                \o stack
                                                                                                   /\ str' = "13: Unknown simple statement type " \o sst.type
                                                                                                /\ pc' = "Error1"
                                                                                     /\ UNCHANGED << primeVars, 
                                                                                                     sub, 
                                                                                                     expr >>
                                         /\ UNCHANGED xltemp1
                              /\ UNCHANGED << sstsq, xprimedVars, localSub_X, 
                                              res, xlsssqi >>
                   /\ UNCHANGED xlssi
        /\ UNCHANGED << i, j, gtemp1, gtemp2, gtemp3, gtemp4, result, rVal, 
                        pMap, prcdVars, procSeq, globalVars, nonGlobalVars, 
                        allVarSeq, localVars, A, res_, ia, prcdr, ipr, proc, 
                        ip, lsseq, ilss, lstmt, whl, ls, ils, ilLast, ili, le, 
                        ile, fs, fi, ifi, ifLast, fe, ife, ife2, feSeq, 
                        feSeqLast, fw, ifw, fwLast, cr, icr, gt, sss, isss, ss, 
                        asg, ias, ifst, estmt, iee, wi, iw, vdcl, pvdcl, exp, 
                        ie, elseq, nxt_, ixs, res_E, lst, nxt_E, temp_, flseq, 
                        temp_I, ifsqi, lseq, nxt_Ex, xxtemp1, temp2_, temp3_, 
                        temp4, exlsq, callStmt, prcd, svoci, temp, res_S, 
                        rprcd, rpvi, rpctemp, res_R, vrs, addExpr, pvexpr, pvi, 
                        stk, test, sst, primedVars, localSub_, temp1, temp2, 
                        temp3, lsstsq, localSub, defSub, nxt, lsstqi, lsstemp, 
                        disjs, defs >>

XSt11 == /\ pc = "XSt11"
         /\ IF xlssi \leq Len(sst.ass)
               THEN /\ /\ expr' = sst.ass[xlssi].lhs.sub
                       /\ primeVars' = primedVars
                       /\ stack' = << [ procedure |->  "PrimeAndAddSub",
                                        pc        |->  "XSt12",
                                        primeVars |->  primeVars,
                                        sub       |->  sub,
                                        expr      |->  expr ] >>
                                    \o stack
                       /\ sub' = localSub_
                    /\ pc' = "PAAS1"
                    /\ UNCHANGED xlssi
               ELSE /\ xlssi' = 1
                    /\ pc' = "XSt14"
                    /\ UNCHANGED << stack, primeVars, sub, expr >>
         /\ UNCHANGED << i, j, gtemp1, gtemp2, gtemp3, gtemp4, result, rVal, 
                         pMap, prcdVars, procSeq, globalVars, nonGlobalVars, 
                         allVarSeq, localVars, A, res_, ia, prcdr, ipr, proc, 
                         ip, lsseq, ilss, lstmt, whl, ls, ils, ilLast, ili, le, 
                         ile, fs, fi, ifi, ifLast, fe, ife, ife2, feSeq, 
                         feSeqLast, fw, ifw, fwLast, cr, icr, gt, sss, isss, 
                         ss, asg, ias, ifst, estmt, iee, wi, iw, vdcl, pvdcl, 
                         exp, ie, elseq, nxt_, ixs, res_E, lst, nxt_E, temp_, 
                         flseq, temp_I, ifsqi, lseq, nxt_Ex, xxtemp1, temp2_, 
                         temp3_, temp4, exlsq, callStmt, prcd, svoci, temp, 
                         res_S, rprcd, rpvi, rpctemp, res_R, vrs, addExpr, 
                         pvexpr, pvi, stk, test, sst, primedVars, localSub_, 
                         xltemp1, temp1, temp2, temp3, res_X, sstsq, 
                         xprimedVars, localSub_X, res, xlsssqi, lsstsq, 
                         localSub, defSub, nxt, lsstqi, lsstemp, disjs, defs, 
                         str >>

XSt12 == /\ pc = "XSt12"
         /\ temp2' = rVal
         /\ /\ expr' = sst.ass[xlssi].rhs
            /\ primeVars' = primedVars
            /\ stack' = << [ procedure |->  "PrimeAndAddSub",
                             pc        |->  "XSt13",
                             primeVars |->  primeVars,
                             sub       |->  sub,
                             expr      |->  expr ] >>
                         \o stack
            /\ sub' = localSub_
         /\ pc' = "PAAS1"
         /\ UNCHANGED << i, j, gtemp1, gtemp2, gtemp3, gtemp4, result, rVal, 
                         pMap, prcdVars, procSeq, globalVars, nonGlobalVars, 
                         allVarSeq, localVars, A, res_, ia, prcdr, ipr, proc, 
                         ip, lsseq, ilss, lstmt, whl, ls, ils, ilLast, ili, le, 
                         ile, fs, fi, ifi, ifLast, fe, ife, ife2, feSeq, 
                         feSeqLast, fw, ifw, fwLast, cr, icr, gt, sss, isss, 
                         ss, asg, ias, ifst, estmt, iee, wi, iw, vdcl, pvdcl, 
                         exp, ie, elseq, nxt_, ixs, res_E, lst, nxt_E, temp_, 
                         flseq, temp_I, ifsqi, lseq, nxt_Ex, xxtemp1, temp2_, 
                         temp3_, temp4, exlsq, callStmt, prcd, svoci, temp, 
                         res_S, rprcd, rpvi, rpctemp, res_R, vrs, addExpr, 
                         pvexpr, pvi, stk, test, sst, primedVars, localSub_, 
                         xlssi, xltemp1, temp1, temp3, res_X, sstsq, 
                         xprimedVars, localSub_X, res, xlsssqi, lsstsq, 
                         localSub, defSub, nxt, lsstqi, lsstemp, disjs, defs, 
                         str >>

XSt13 == /\ pc = "XSt13"
         /\ LET newElt == << [sub |-> temp2, rhs |-> rVal] >> IN
              IF \E x \in 1..Len(xltemp1) :
                     xltemp1[x].var = sst.ass[xlssi].lhs.var
                 THEN /\ LET y == CHOOSE x \in 1..Len(xltemp1) :
                                    xltemp1[x].var = sst.ass[xlssi].lhs.var IN
                           xltemp1' = [xltemp1 EXCEPT ![y].assign = xltemp1[y].assign \o newElt]
                 ELSE /\ xltemp1' = xltemp1 \o <<[var    |-> sst.ass[xlssi].lhs.var,
                                                  assign |-> newElt] >>
         /\ xlssi' = xlssi + 1
         /\ pc' = "XSt11"
         /\ UNCHANGED << i, j, gtemp1, gtemp2, gtemp3, gtemp4, result, rVal, 
                         pMap, prcdVars, procSeq, globalVars, nonGlobalVars, 
                         allVarSeq, localVars, stack, A, res_, ia, prcdr, ipr, 
                         proc, ip, lsseq, ilss, lstmt, whl, ls, ils, ilLast, 
                         ili, le, ile, fs, fi, ifi, ifLast, fe, ife, ife2, 
                         feSeq, feSeqLast, fw, ifw, fwLast, cr, icr, gt, sss, 
                         isss, ss, asg, ias, ifst, estmt, iee, wi, iw, vdcl, 
                         pvdcl, exp, ie, elseq, nxt_, ixs, res_E, lst, nxt_E, 
                         temp_, flseq, temp_I, ifsqi, lseq, nxt_Ex, xxtemp1, 
                         temp2_, temp3_, temp4, exlsq, callStmt, prcd, svoci, 
                         temp, res_S, rprcd, rpvi, rpctemp, res_R, vrs, 
                         addExpr, pvexpr, pvi, stk, test, primeVars, sub, expr, 
                         sst, primedVars, localSub_, temp1, temp2, temp3, 
                         res_X, sstsq, xprimedVars, localSub_X, res, xlsssqi, 
                         lsstsq, localSub, defSub, nxt, lsstqi, lsstemp, disjs, 
                         defs, str >>

XSt14 == /\ pc = "XSt14"
         /\ IF xlssi \leq Len(xltemp1)
               THEN /\ IF \/ xltemp1[xlssi].var \in primedVars
                          \/ /\ Len(xltemp1[xlssi].assign) > 1
                             /\ \E x \in 1..Len(xltemp1[xlssi].assign) :
                                    xltemp1[xlssi].assign[x].sub = << >>
                          THEN /\ /\ stack' = << [ procedure |->  "Error",
                                                   pc        |->  "XSt15",
                                                   str       |->  str ] >>
                                               \o stack
                                  /\ str' = "12: Multiple assignment to  " \o
                                              xltemp1[xlssi].var
                               /\ pc' = "Error1"
                          ELSE /\ pc' = "XSt15"
                               /\ UNCHANGED << stack, str >>
               ELSE /\ pc' = "XSt99"
                    /\ UNCHANGED << stack, str >>
         /\ UNCHANGED << i, j, gtemp1, gtemp2, gtemp3, gtemp4, result, rVal, 
                         pMap, prcdVars, procSeq, globalVars, nonGlobalVars, 
                         allVarSeq, localVars, A, res_, ia, prcdr, ipr, proc, 
                         ip, lsseq, ilss, lstmt, whl, ls, ils, ilLast, ili, le, 
                         ile, fs, fi, ifi, ifLast, fe, ife, ife2, feSeq, 
                         feSeqLast, fw, ifw, fwLast, cr, icr, gt, sss, isss, 
                         ss, asg, ias, ifst, estmt, iee, wi, iw, vdcl, pvdcl, 
                         exp, ie, elseq, nxt_, ixs, res_E, lst, nxt_E, temp_, 
                         flseq, temp_I, ifsqi, lseq, nxt_Ex, xxtemp1, temp2_, 
                         temp3_, temp4, exlsq, callStmt, prcd, svoci, temp, 
                         res_S, rprcd, rpvi, rpctemp, res_R, vrs, addExpr, 
                         pvexpr, pvi, stk, test, primeVars, sub, expr, sst, 
                         primedVars, localSub_, xlssi, xltemp1, temp1, temp2, 
                         temp3, res_X, sstsq, xprimedVars, localSub_X, res, 
                         xlsssqi, lsstsq, localSub, defSub, nxt, lsstqi, 
                         lsstemp, disjs, defs >>

XSt15 == /\ pc = "XSt15"
         /\ temp2' = IF xltemp1[xlssi].var \in localVars
                     THEN localSub_
                     ELSE << >>
         /\ IF temp2' \o xltemp1[xlssi].assign[1].sub = << >>
               THEN /\ temp3' = xltemp1[xlssi].assign[1].rhs
               ELSE /\ temp3' = <<"[", xltemp1[xlssi].var, "EXCEPT">>
                                  \o
                                SeqConcat([x \in 1..Len(xltemp1[xlssi].assign) |->
                                            << "!" >> \o temp2' \o
                                             xltemp1[xlssi].assign[x].sub \o
                                            <<"=">> \o xltemp1[xlssi].assign[x].rhs
                                            \o IF x = Len(xltemp1[xlssi].assign)
                                                 THEN << >>
                                                 ELSE << "," >>])
                                    \o <<"]">>
         /\ res_X' =                       [action |-> res_X.action
                                                        \o << <<  xltemp1[xlssi].var, "'", "=">>
                                                        \o temp3' >>
                     ,
                                            pVars  |-> res_X.pVars \cup {xltemp1[xlssi].var}]
         /\ xlssi' = xlssi + 1
         /\ pc' = "XSt14"
         /\ UNCHANGED << i, j, gtemp1, gtemp2, gtemp3, gtemp4, result, rVal, 
                         pMap, prcdVars, procSeq, globalVars, nonGlobalVars, 
                         allVarSeq, localVars, stack, A, res_, ia, prcdr, ipr, 
                         proc, ip, lsseq, ilss, lstmt, whl, ls, ils, ilLast, 
                         ili, le, ile, fs, fi, ifi, ifLast, fe, ife, ife2, 
                         feSeq, feSeqLast, fw, ifw, fwLast, cr, icr, gt, sss, 
                         isss, ss, asg, ias, ifst, estmt, iee, wi, iw, vdcl, 
                         pvdcl, exp, ie, elseq, nxt_, ixs, res_E, lst, nxt_E, 
                         temp_, flseq, temp_I, ifsqi, lseq, nxt_Ex, xxtemp1, 
                         temp2_, temp3_, temp4, exlsq, callStmt, prcd, svoci, 
                         temp, res_S, rprcd, rpvi, rpctemp, res_R, vrs, 
                         addExpr, pvexpr, pvi, stk, test, primeVars, sub, expr, 
                         sst, primedVars, localSub_, xltemp1, temp1, sstsq, 
                         xprimedVars, localSub_X, res, xlsssqi, lsstsq, 
                         localSub, defSub, nxt, lsstqi, lsstemp, disjs, defs, 
                         str >>

XSt21 == /\ pc = "XSt21"
         /\ temp1' = rVal
         /\ /\ localSub_X' = localSub_
            /\ sstsq' = sst.else
            /\ stack' = << [ procedure |->  "XlateSStmtSeq",
                             pc        |->  "XSt22",
                             res       |->  res,
                             xlsssqi   |->  xlsssqi,
                             sstsq     |->  sstsq,
                             xprimedVars |->  xprimedVars,
                             localSub_X |->  localSub_X ] >>
                         \o stack
            /\ xprimedVars' = primedVars
         /\ res' = {}
         /\ xlsssqi' = 1
         /\ pc' = "XStSq1"
         /\ UNCHANGED << i, j, gtemp1, gtemp2, gtemp3, gtemp4, result, rVal, 
                         pMap, prcdVars, procSeq, globalVars, nonGlobalVars, 
                         allVarSeq, localVars, A, res_, ia, prcdr, ipr, proc, 
                         ip, lsseq, ilss, lstmt, whl, ls, ils, ilLast, ili, le, 
                         ile, fs, fi, ifi, ifLast, fe, ife, ife2, feSeq, 
                         feSeqLast, fw, ifw, fwLast, cr, icr, gt, sss, isss, 
                         ss, asg, ias, ifst, estmt, iee, wi, iw, vdcl, pvdcl, 
                         exp, ie, elseq, nxt_, ixs, res_E, lst, nxt_E, temp_, 
                         flseq, temp_I, ifsqi, lseq, nxt_Ex, xxtemp1, temp2_, 
                         temp3_, temp4, exlsq, callStmt, prcd, svoci, temp, 
                         res_S, rprcd, rpvi, rpctemp, res_R, vrs, addExpr, 
                         pvexpr, pvi, stk, test, primeVars, sub, expr, sst, 
                         primedVars, localSub_, xlssi, xltemp1, temp2, temp3, 
                         res_X, lsstsq, localSub, defSub, nxt, lsstqi, lsstemp, 
                         disjs, defs, str >>

XSt22 == /\ pc = "XSt22"
         /\ temp2' = rVal
         /\ /\ expr' = sst.test
            /\ primeVars' = primedVars
            /\ stack' = << [ procedure |->  "PrimeAndAddSub",
                             pc        |->  "XSt23",
                             primeVars |->  primeVars,
                             sub       |->  sub,
                             expr      |->  expr ] >>
                         \o stack
            /\ sub' = localSub_
         /\ pc' = "PAAS1"
         /\ UNCHANGED << i, j, gtemp1, gtemp2, gtemp3, gtemp4, result, rVal, 
                         pMap, prcdVars, procSeq, globalVars, nonGlobalVars, 
                         allVarSeq, localVars, A, res_, ia, prcdr, ipr, proc, 
                         ip, lsseq, ilss, lstmt, whl, ls, ils, ilLast, ili, le, 
                         ile, fs, fi, ifi, ifLast, fe, ife, ife2, feSeq, 
                         feSeqLast, fw, ifw, fwLast, cr, icr, gt, sss, isss, 
                         ss, asg, ias, ifst, estmt, iee, wi, iw, vdcl, pvdcl, 
                         exp, ie, elseq, nxt_, ixs, res_E, lst, nxt_E, temp_, 
                         flseq, temp_I, ifsqi, lseq, nxt_Ex, xxtemp1, temp2_, 
                         temp3_, temp4, exlsq, callStmt, prcd, svoci, temp, 
                         res_S, rprcd, rpvi, rpctemp, res_R, vrs, addExpr, 
                         pvexpr, pvi, stk, test, sst, primedVars, localSub_, 
                         xlssi, xltemp1, temp1, temp3, res_X, sstsq, 
                         xprimedVars, localSub_X, res, xlsssqi, lsstsq, 
                         localSub, defSub, nxt, lsstqi, lsstemp, disjs, defs, 
                         str >>

XSt23 == /\ pc = "XSt23"
         /\ temp3' = rVal
         /\ temp1' = [temp1 EXCEPT !.action = temp1.action \o
                                               MakeUnchanged(
                                                    CompSetToSubseq(
                                                       temp1.pVars,
                                                       SetToSubseq(temp1.pVars \cup temp2.pVars,
                                                                allVarSeq)))]
         /\ temp2' = [temp2 EXCEPT !.action = temp2.action \o
                                                MakeUnchanged(
                                                    CompSetToSubseq(
                                                       temp2.pVars,
                                                       SetToSubseq(temp1'.pVars \cup temp2.pVars,
                                                                allVarSeq)))]
         /\ res_X' = [res_X EXCEPT !.action = << << "(", "IF">> \o temp3' \o <<"THEN">> \o
                                                           MakeConj(temp1'.action)
                                                  \o <<"ELSE">> \o MakeConj(temp2'.action) \o <<")">> >>,
                                   !.pVars = temp1'.pVars \cup temp2'.pVars]
         /\ pc' = "XSt99"
         /\ UNCHANGED << i, j, gtemp1, gtemp2, gtemp3, gtemp4, result, rVal, 
                         pMap, prcdVars, procSeq, globalVars, nonGlobalVars, 
                         allVarSeq, localVars, stack, A, res_, ia, prcdr, ipr, 
                         proc, ip, lsseq, ilss, lstmt, whl, ls, ils, ilLast, 
                         ili, le, ile, fs, fi, ifi, ifLast, fe, ife, ife2, 
                         feSeq, feSeqLast, fw, ifw, fwLast, cr, icr, gt, sss, 
                         isss, ss, asg, ias, ifst, estmt, iee, wi, iw, vdcl, 
                         pvdcl, exp, ie, elseq, nxt_, ixs, res_E, lst, nxt_E, 
                         temp_, flseq, temp_I, ifsqi, lseq, nxt_Ex, xxtemp1, 
                         temp2_, temp3_, temp4, exlsq, callStmt, prcd, svoci, 
                         temp, res_S, rprcd, rpvi, rpctemp, res_R, vrs, 
                         addExpr, pvexpr, pvi, stk, test, primeVars, sub, expr, 
                         sst, primedVars, localSub_, xlssi, xltemp1, sstsq, 
                         xprimedVars, localSub_X, res, xlsssqi, lsstsq, 
                         localSub, defSub, nxt, lsstqi, lsstemp, disjs, defs, 
                         str >>

XSt31 == /\ pc = "XSt31"
         /\ temp2' = {}
         /\ xlssi' = 1
         /\ pc' = "XSt32"
         /\ UNCHANGED << i, j, gtemp1, gtemp2, gtemp3, gtemp4, result, rVal, 
                         pMap, prcdVars, procSeq, globalVars, nonGlobalVars, 
                         allVarSeq, localVars, stack, A, res_, ia, prcdr, ipr, 
                         proc, ip, lsseq, ilss, lstmt, whl, ls, ils, ilLast, 
                         ili, le, ile, fs, fi, ifi, ifLast, fe, ife, ife2, 
                         feSeq, feSeqLast, fw, ifw, fwLast, cr, icr, gt, sss, 
                         isss, ss, asg, ias, ifst, estmt, iee, wi, iw, vdcl, 
                         pvdcl, exp, ie, elseq, nxt_, ixs, res_E, lst, nxt_E, 
                         temp_, flseq, temp_I, ifsqi, lseq, nxt_Ex, xxtemp1, 
                         temp2_, temp3_, temp4, exlsq, callStmt, prcd, svoci, 
                         temp, res_S, rprcd, rpvi, rpctemp, res_R, vrs, 
                         addExpr, pvexpr, pvi, stk, test, primeVars, sub, expr, 
                         sst, primedVars, localSub_, xltemp1, temp1, temp3, 
                         res_X, sstsq, xprimedVars, localSub_X, res, xlsssqi, 
                         lsstsq, localSub, defSub, nxt, lsstqi, lsstemp, disjs, 
                         defs, str >>

XSt32 == /\ pc = "XSt32"
         /\ IF xlssi \leq Len(sst.ors)
               THEN /\ pc' = "XSt33"
                    /\ UNCHANGED << temp3, res_X >>
               ELSE /\ temp3' = [x \in 1..Len(xltemp1) |->
                                  xltemp1[x].action \o
                                      MakeUnchanged(
                                             CompSetToSubseq(
                                                xltemp1[x].pVars,
                                                SetToSubseq(temp2 ,
                                                            allVarSeq))) ]
                    /\ res_X' = [action |-> MakeDisj([x \in 1..Len(temp3') |->
                                                        <<"(">> \o MakeConj(temp3'[x])
                                                           \o <<")">>]),
                                 pVars  |-> temp2]
                    /\ pc' = "XSt99"
         /\ UNCHANGED << i, j, gtemp1, gtemp2, gtemp3, gtemp4, result, rVal, 
                         pMap, prcdVars, procSeq, globalVars, nonGlobalVars, 
                         allVarSeq, localVars, stack, A, res_, ia, prcdr, ipr, 
                         proc, ip, lsseq, ilss, lstmt, whl, ls, ils, ilLast, 
                         ili, le, ile, fs, fi, ifi, ifLast, fe, ife, ife2, 
                         feSeq, feSeqLast, fw, ifw, fwLast, cr, icr, gt, sss, 
                         isss, ss, asg, ias, ifst, estmt, iee, wi, iw, vdcl, 
                         pvdcl, exp, ie, elseq, nxt_, ixs, res_E, lst, nxt_E, 
                         temp_, flseq, temp_I, ifsqi, lseq, nxt_Ex, xxtemp1, 
                         temp2_, temp3_, temp4, exlsq, callStmt, prcd, svoci, 
                         temp, res_S, rprcd, rpvi, rpctemp, res_R, vrs, 
                         addExpr, pvexpr, pvi, stk, test, primeVars, sub, expr, 
                         sst, primedVars, localSub_, xlssi, xltemp1, temp1, 
                         temp2, sstsq, xprimedVars, localSub_X, res, xlsssqi, 
                         lsstsq, localSub, defSub, nxt, lsstqi, lsstemp, disjs, 
                         defs, str >>

XSt33 == /\ pc = "XSt33"
         /\ /\ localSub_X' = localSub_
            /\ sstsq' = sst.ors[xlssi]
            /\ stack' = << [ procedure |->  "XlateSStmtSeq",
                             pc        |->  "XSt34",
                             res       |->  res,
                             xlsssqi   |->  xlsssqi,
                             sstsq     |->  sstsq,
                             xprimedVars |->  xprimedVars,
                             localSub_X |->  localSub_X ] >>
                         \o stack
            /\ xprimedVars' = primedVars
         /\ res' = {}
         /\ xlsssqi' = 1
         /\ pc' = "XStSq1"
         /\ UNCHANGED << i, j, gtemp1, gtemp2, gtemp3, gtemp4, result, rVal, 
                         pMap, prcdVars, procSeq, globalVars, nonGlobalVars, 
                         allVarSeq, localVars, A, res_, ia, prcdr, ipr, proc, 
                         ip, lsseq, ilss, lstmt, whl, ls, ils, ilLast, ili, le, 
                         ile, fs, fi, ifi, ifLast, fe, ife, ife2, feSeq, 
                         feSeqLast, fw, ifw, fwLast, cr, icr, gt, sss, isss, 
                         ss, asg, ias, ifst, estmt, iee, wi, iw, vdcl, pvdcl, 
                         exp, ie, elseq, nxt_, ixs, res_E, lst, nxt_E, temp_, 
                         flseq, temp_I, ifsqi, lseq, nxt_Ex, xxtemp1, temp2_, 
                         temp3_, temp4, exlsq, callStmt, prcd, svoci, temp, 
                         res_S, rprcd, rpvi, rpctemp, res_R, vrs, addExpr, 
                         pvexpr, pvi, stk, test, primeVars, sub, expr, sst, 
                         primedVars, localSub_, xlssi, xltemp1, temp1, temp2, 
                         temp3, res_X, lsstsq, localSub, defSub, nxt, lsstqi, 
                         lsstemp, disjs, defs, str >>

XSt34 == /\ pc = "XSt34"
         /\ xltemp1' = xltemp1 \o <<rVal>>
         /\ temp2' = temp2 \cup rVal.pVars
         /\ xlssi' = xlssi + 1
         /\ pc' = "XSt32"
         /\ UNCHANGED << i, j, gtemp1, gtemp2, gtemp3, gtemp4, result, rVal, 
                         pMap, prcdVars, procSeq, globalVars, nonGlobalVars, 
                         allVarSeq, localVars, stack, A, res_, ia, prcdr, ipr, 
                         proc, ip, lsseq, ilss, lstmt, whl, ls, ils, ilLast, 
                         ili, le, ile, fs, fi, ifi, ifLast, fe, ife, ife2, 
                         feSeq, feSeqLast, fw, ifw, fwLast, cr, icr, gt, sss, 
                         isss, ss, asg, ias, ifst, estmt, iee, wi, iw, vdcl, 
                         pvdcl, exp, ie, elseq, nxt_, ixs, res_E, lst, nxt_E, 
                         temp_, flseq, temp_I, ifsqi, lseq, nxt_Ex, xxtemp1, 
                         temp2_, temp3_, temp4, exlsq, callStmt, prcd, svoci, 
                         temp, res_S, rprcd, rpvi, rpctemp, res_R, vrs, 
                         addExpr, pvexpr, pvi, stk, test, primeVars, sub, expr, 
                         sst, primedVars, localSub_, temp1, temp3, res_X, 
                         sstsq, xprimedVars, localSub_X, res, xlsssqi, lsstsq, 
                         localSub, defSub, nxt, lsstqi, lsstemp, disjs, defs, 
                         str >>

XSt41 == /\ pc = "XSt41"
         /\ temp1' = rVal
         /\ /\ localSub_X' = localSub_
            /\ sstsq' = sst.do
            /\ stack' = << [ procedure |->  "XlateSStmtSeq",
                             pc        |->  "XSt42",
                             res       |->  res,
                             xlsssqi   |->  xlsssqi,
                             sstsq     |->  sstsq,
                             xprimedVars |->  xprimedVars,
                             localSub_X |->  localSub_X ] >>
                         \o stack
            /\ xprimedVars' = primedVars
         /\ res' = {}
         /\ xlsssqi' = 1
         /\ pc' = "XStSq1"
         /\ UNCHANGED << i, j, gtemp1, gtemp2, gtemp3, gtemp4, result, rVal, 
                         pMap, prcdVars, procSeq, globalVars, nonGlobalVars, 
                         allVarSeq, localVars, A, res_, ia, prcdr, ipr, proc, 
                         ip, lsseq, ilss, lstmt, whl, ls, ils, ilLast, ili, le, 
                         ile, fs, fi, ifi, ifLast, fe, ife, ife2, feSeq, 
                         feSeqLast, fw, ifw, fwLast, cr, icr, gt, sss, isss, 
                         ss, asg, ias, ifst, estmt, iee, wi, iw, vdcl, pvdcl, 
                         exp, ie, elseq, nxt_, ixs, res_E, lst, nxt_E, temp_, 
                         flseq, temp_I, ifsqi, lseq, nxt_Ex, xxtemp1, temp2_, 
                         temp3_, temp4, exlsq, callStmt, prcd, svoci, temp, 
                         res_S, rprcd, rpvi, rpctemp, res_R, vrs, addExpr, 
                         pvexpr, pvi, stk, test, primeVars, sub, expr, sst, 
                         primedVars, localSub_, xlssi, xltemp1, temp2, temp3, 
                         res_X, lsstsq, localSub, defSub, nxt, lsstqi, lsstemp, 
                         disjs, defs, str >>

XSt42 == /\ pc = "XSt42"
         /\ temp2' = MakeConj(rVal.action)
         /\ res_X' = [res_X EXCEPT !.pVars = rVal.pVars]
         /\ pc' = "XSt43"
         /\ UNCHANGED << i, j, gtemp1, gtemp2, gtemp3, gtemp4, result, rVal, 
                         pMap, prcdVars, procSeq, globalVars, nonGlobalVars, 
                         allVarSeq, localVars, stack, A, res_, ia, prcdr, ipr, 
                         proc, ip, lsseq, ilss, lstmt, whl, ls, ils, ilLast, 
                         ili, le, ile, fs, fi, ifi, ifLast, fe, ife, ife2, 
                         feSeq, feSeqLast, fw, ifw, fwLast, cr, icr, gt, sss, 
                         isss, ss, asg, ias, ifst, estmt, iee, wi, iw, vdcl, 
                         pvdcl, exp, ie, elseq, nxt_, ixs, res_E, lst, nxt_E, 
                         temp_, flseq, temp_I, ifsqi, lseq, nxt_Ex, xxtemp1, 
                         temp2_, temp3_, temp4, exlsq, callStmt, prcd, svoci, 
                         temp, res_S, rprcd, rpvi, rpctemp, res_R, vrs, 
                         addExpr, pvexpr, pvi, stk, test, primeVars, sub, expr, 
                         sst, primedVars, localSub_, xlssi, xltemp1, temp1, 
                         temp3, sstsq, xprimedVars, localSub_X, res, xlsssqi, 
                         lsstsq, localSub, defSub, nxt, lsstqi, lsstemp, disjs, 
                         defs, str >>

XSt43 == /\ pc = "XSt43"
         /\ IF sst.eqOrIn = "="
               THEN /\ res_X' = [res_X EXCEPT !.action = << <<"LET", sst.var, "==">> \o temp1 \o <<"IN">> \o
                                                              temp2 >>]
               ELSE /\ res_X' = [res_X EXCEPT !.action = << <<"\\E", sst.var, "\\in">> \o temp1 \o <<":">> \o
                                                              temp2 >>]
         /\ pc' = "XSt99"
         /\ UNCHANGED << i, j, gtemp1, gtemp2, gtemp3, gtemp4, result, rVal, 
                         pMap, prcdVars, procSeq, globalVars, nonGlobalVars, 
                         allVarSeq, localVars, stack, A, res_, ia, prcdr, ipr, 
                         proc, ip, lsseq, ilss, lstmt, whl, ls, ils, ilLast, 
                         ili, le, ile, fs, fi, ifi, ifLast, fe, ife, ife2, 
                         feSeq, feSeqLast, fw, ifw, fwLast, cr, icr, gt, sss, 
                         isss, ss, asg, ias, ifst, estmt, iee, wi, iw, vdcl, 
                         pvdcl, exp, ie, elseq, nxt_, ixs, res_E, lst, nxt_E, 
                         temp_, flseq, temp_I, ifsqi, lseq, nxt_Ex, xxtemp1, 
                         temp2_, temp3_, temp4, exlsq, callStmt, prcd, svoci, 
                         temp, res_S, rprcd, rpvi, rpctemp, res_R, vrs, 
                         addExpr, pvexpr, pvi, stk, test, primeVars, sub, expr, 
                         sst, primedVars, localSub_, xlssi, xltemp1, temp1, 
                         temp2, temp3, sstsq, xprimedVars, localSub_X, res, 
                         xlsssqi, lsstsq, localSub, defSub, nxt, lsstqi, 
                         lsstemp, disjs, defs, str >>

XSt6 == /\ pc = "XSt6"
        /\ res_X' = [res_X EXCEPT !.action = res_X.action \o  << rVal >>]
        /\ pc' = "XSt99"
        /\ UNCHANGED << i, j, gtemp1, gtemp2, gtemp3, gtemp4, result, rVal, 
                        pMap, prcdVars, procSeq, globalVars, nonGlobalVars, 
                        allVarSeq, localVars, stack, A, res_, ia, prcdr, ipr, 
                        proc, ip, lsseq, ilss, lstmt, whl, ls, ils, ilLast, 
                        ili, le, ile, fs, fi, ifi, ifLast, fe, ife, ife2, 
                        feSeq, feSeqLast, fw, ifw, fwLast, cr, icr, gt, sss, 
                        isss, ss, asg, ias, ifst, estmt, iee, wi, iw, vdcl, 
                        pvdcl, exp, ie, elseq, nxt_, ixs, res_E, lst, nxt_E, 
                        temp_, flseq, temp_I, ifsqi, lseq, nxt_Ex, xxtemp1, 
                        temp2_, temp3_, temp4, exlsq, callStmt, prcd, svoci, 
                        temp, res_S, rprcd, rpvi, rpctemp, res_R, vrs, addExpr, 
                        pvexpr, pvi, stk, test, primeVars, sub, expr, sst, 
                        primedVars, localSub_, xlssi, xltemp1, temp1, temp2, 
                        temp3, sstsq, xprimedVars, localSub_X, res, xlsssqi, 
                        lsstsq, localSub, defSub, nxt, lsstqi, lsstemp, disjs, 
                        defs, str >>

XSt7 == /\ pc = "XSt7"
        /\ res_X' = [res_X EXCEPT !.action = res_X.action \o
                                              << <<"PrintT", "(">> \o rVal \o <<")">> >>]
        /\ pc' = "XSt99"
        /\ UNCHANGED << i, j, gtemp1, gtemp2, gtemp3, gtemp4, result, rVal, 
                        pMap, prcdVars, procSeq, globalVars, nonGlobalVars, 
                        allVarSeq, localVars, stack, A, res_, ia, prcdr, ipr, 
                        proc, ip, lsseq, ilss, lstmt, whl, ls, ils, ilLast, 
                        ili, le, ile, fs, fi, ifi, ifLast, fe, ife, ife2, 
                        feSeq, feSeqLast, fw, ifw, fwLast, cr, icr, gt, sss, 
                        isss, ss, asg, ias, ifst, estmt, iee, wi, iw, vdcl, 
                        pvdcl, exp, ie, elseq, nxt_, ixs, res_E, lst, nxt_E, 
                        temp_, flseq, temp_I, ifsqi, lseq, nxt_Ex, xxtemp1, 
                        temp2_, temp3_, temp4, exlsq, callStmt, prcd, svoci, 
                        temp, res_S, rprcd, rpvi, rpctemp, res_R, vrs, addExpr, 
                        pvexpr, pvi, stk, test, primeVars, sub, expr, sst, 
                        primedVars, localSub_, xlssi, xltemp1, temp1, temp2, 
                        temp3, sstsq, xprimedVars, localSub_X, res, xlsssqi, 
                        lsstsq, localSub, defSub, nxt, lsstqi, lsstemp, disjs, 
                        defs, str >>

XSt8 == /\ pc = "XSt8"
        /\ res_X' = [res_X EXCEPT !.action = res_X.action \o
                                              << <<"Assert", "(">> \o rVal \o
                                                    <<",">> \o Quote("Failed assert") \o
                                                  << ")">> >>]
        /\ pc' = "XSt99"
        /\ UNCHANGED << i, j, gtemp1, gtemp2, gtemp3, gtemp4, result, rVal, 
                        pMap, prcdVars, procSeq, globalVars, nonGlobalVars, 
                        allVarSeq, localVars, stack, A, res_, ia, prcdr, ipr, 
                        proc, ip, lsseq, ilss, lstmt, whl, ls, ils, ilLast, 
                        ili, le, ile, fs, fi, ifi, ifLast, fe, ife, ife2, 
                        feSeq, feSeqLast, fw, ifw, fwLast, cr, icr, gt, sss, 
                        isss, ss, asg, ias, ifst, estmt, iee, wi, iw, vdcl, 
                        pvdcl, exp, ie, elseq, nxt_, ixs, res_E, lst, nxt_E, 
                        temp_, flseq, temp_I, ifsqi, lseq, nxt_Ex, xxtemp1, 
                        temp2_, temp3_, temp4, exlsq, callStmt, prcd, svoci, 
                        temp, res_S, rprcd, rpvi, rpctemp, res_R, vrs, addExpr, 
                        pvexpr, pvi, stk, test, primeVars, sub, expr, sst, 
                        primedVars, localSub_, xlssi, xltemp1, temp1, temp2, 
                        temp3, sstsq, xprimedVars, localSub_X, res, xlsssqi, 
                        lsstsq, localSub, defSub, nxt, lsstqi, lsstemp, disjs, 
                        defs, str >>

XSt99 == /\ pc = "XSt99"
         /\ rVal' = res_X
         /\ pc' = Head(stack).pc
         /\ xlssi' = Head(stack).xlssi
         /\ xltemp1' = Head(stack).xltemp1
         /\ temp1' = Head(stack).temp1
         /\ temp2' = Head(stack).temp2
         /\ temp3' = Head(stack).temp3
         /\ res_X' = Head(stack).res_X
         /\ sst' = Head(stack).sst
         /\ primedVars' = Head(stack).primedVars
         /\ localSub_' = Head(stack).localSub_
         /\ stack' = Tail(stack)
         /\ UNCHANGED << i, j, gtemp1, gtemp2, gtemp3, gtemp4, result, pMap, 
                         prcdVars, procSeq, globalVars, nonGlobalVars, 
                         allVarSeq, localVars, A, res_, ia, prcdr, ipr, proc, 
                         ip, lsseq, ilss, lstmt, whl, ls, ils, ilLast, ili, le, 
                         ile, fs, fi, ifi, ifLast, fe, ife, ife2, feSeq, 
                         feSeqLast, fw, ifw, fwLast, cr, icr, gt, sss, isss, 
                         ss, asg, ias, ifst, estmt, iee, wi, iw, vdcl, pvdcl, 
                         exp, ie, elseq, nxt_, ixs, res_E, lst, nxt_E, temp_, 
                         flseq, temp_I, ifsqi, lseq, nxt_Ex, xxtemp1, temp2_, 
                         temp3_, temp4, exlsq, callStmt, prcd, svoci, temp, 
                         res_S, rprcd, rpvi, rpctemp, res_R, vrs, addExpr, 
                         pvexpr, pvi, stk, test, primeVars, sub, expr, sstsq, 
                         xprimedVars, localSub_X, res, xlsssqi, lsstsq, 
                         localSub, defSub, nxt, lsstqi, lsstemp, disjs, defs, 
                         str >>

XlateSStmt == XSt1 \/ XSt11 \/ XSt12 \/ XSt13 \/ XSt14 \/ XSt15 \/ XSt21
                 \/ XSt22 \/ XSt23 \/ XSt31 \/ XSt32 \/ XSt33 \/ XSt34 \/ XSt41
                 \/ XSt42 \/ XSt43 \/ XSt6 \/ XSt7 \/ XSt8 \/ XSt99

XStSq1 == /\ pc = "XStSq1"
          /\ res' = [action |-> << >>, pVars  |-> xprimedVars]
          /\ pc' = "XStSq2"
          /\ UNCHANGED << i, j, gtemp1, gtemp2, gtemp3, gtemp4, result, rVal, 
                          pMap, prcdVars, procSeq, globalVars, nonGlobalVars, 
                          allVarSeq, localVars, stack, A, res_, ia, prcdr, ipr, 
                          proc, ip, lsseq, ilss, lstmt, whl, ls, ils, ilLast, 
                          ili, le, ile, fs, fi, ifi, ifLast, fe, ife, ife2, 
                          feSeq, feSeqLast, fw, ifw, fwLast, cr, icr, gt, sss, 
                          isss, ss, asg, ias, ifst, estmt, iee, wi, iw, vdcl, 
                          pvdcl, exp, ie, elseq, nxt_, ixs, res_E, lst, nxt_E, 
                          temp_, flseq, temp_I, ifsqi, lseq, nxt_Ex, xxtemp1, 
                          temp2_, temp3_, temp4, exlsq, callStmt, prcd, svoci, 
                          temp, res_S, rprcd, rpvi, rpctemp, res_R, vrs, 
                          addExpr, pvexpr, pvi, stk, test, primeVars, sub, 
                          expr, sst, primedVars, localSub_, xlssi, xltemp1, 
                          temp1, temp2, temp3, res_X, sstsq, xprimedVars, 
                          localSub_X, xlsssqi, lsstsq, localSub, defSub, nxt, 
                          lsstqi, lsstemp, disjs, defs, str >>

XStSq2 == /\ pc = "XStSq2"
          /\ IF xlsssqi \leq Len(sstsq)
                THEN /\ /\ localSub_' = localSub_X
                        /\ primedVars' = res.pVars
                        /\ sst' = sstsq[xlsssqi]
                        /\ stack' = << [ procedure |->  "XlateSStmt",
                                         pc        |->  "XStSq3",
                                         xlssi     |->  xlssi,
                                         xltemp1   |->  xltemp1,
                                         temp1     |->  temp1,
                                         temp2     |->  temp2,
                                         temp3     |->  temp3,
                                         res_X     |->  res_X,
                                         sst       |->  sst,
                                         primedVars |->  primedVars,
                                         localSub_ |->  localSub_ ] >>
                                     \o stack
                     /\ xlssi' = {}
                     /\ xltemp1' = {}
                     /\ temp1' = {}
                     /\ temp2' = {}
                     /\ temp3' = {}
                     /\ res_X' = [action |-> << >>,
                                  pVars  |-> primedVars' ]
                     /\ pc' = "XSt1"
                     /\ UNCHANGED << rVal, sstsq, xprimedVars, localSub_X, res, 
                                     xlsssqi >>
                ELSE /\ rVal' = res
                     /\ pc' = Head(stack).pc
                     /\ res' = Head(stack).res
                     /\ xlsssqi' = Head(stack).xlsssqi
                     /\ sstsq' = Head(stack).sstsq
                     /\ xprimedVars' = Head(stack).xprimedVars
                     /\ localSub_X' = Head(stack).localSub_X
                     /\ stack' = Tail(stack)
                     /\ UNCHANGED << sst, primedVars, localSub_, xlssi, 
                                     xltemp1, temp1, temp2, temp3, res_X >>
          /\ UNCHANGED << i, j, gtemp1, gtemp2, gtemp3, gtemp4, result, pMap, 
                          prcdVars, procSeq, globalVars, nonGlobalVars, 
                          allVarSeq, localVars, A, res_, ia, prcdr, ipr, proc, 
                          ip, lsseq, ilss, lstmt, whl, ls, ils, ilLast, ili, 
                          le, ile, fs, fi, ifi, ifLast, fe, ife, ife2, feSeq, 
                          feSeqLast, fw, ifw, fwLast, cr, icr, gt, sss, isss, 
                          ss, asg, ias, ifst, estmt, iee, wi, iw, vdcl, pvdcl, 
                          exp, ie, elseq, nxt_, ixs, res_E, lst, nxt_E, temp_, 
                          flseq, temp_I, ifsqi, lseq, nxt_Ex, xxtemp1, temp2_, 
                          temp3_, temp4, exlsq, callStmt, prcd, svoci, temp, 
                          res_S, rprcd, rpvi, rpctemp, res_R, vrs, addExpr, 
                          pvexpr, pvi, stk, test, primeVars, sub, expr, lsstsq, 
                          localSub, defSub, nxt, lsstqi, lsstemp, disjs, defs, 
                          str >>

XStSq3 == /\ pc = "XStSq3"
          /\ res' = [res EXCEPT !.action = res.action \o rVal.action,
                                !.pVars = rVal.pVars]
          /\ xlsssqi' = xlsssqi + 1
          /\ pc' = "XStSq2"
          /\ UNCHANGED << i, j, gtemp1, gtemp2, gtemp3, gtemp4, result, rVal, 
                          pMap, prcdVars, procSeq, globalVars, nonGlobalVars, 
                          allVarSeq, localVars, stack, A, res_, ia, prcdr, ipr, 
                          proc, ip, lsseq, ilss, lstmt, whl, ls, ils, ilLast, 
                          ili, le, ile, fs, fi, ifi, ifLast, fe, ife, ife2, 
                          feSeq, feSeqLast, fw, ifw, fwLast, cr, icr, gt, sss, 
                          isss, ss, asg, ias, ifst, estmt, iee, wi, iw, vdcl, 
                          pvdcl, exp, ie, elseq, nxt_, ixs, res_E, lst, nxt_E, 
                          temp_, flseq, temp_I, ifsqi, lseq, nxt_Ex, xxtemp1, 
                          temp2_, temp3_, temp4, exlsq, callStmt, prcd, svoci, 
                          temp, res_S, rprcd, rpvi, rpctemp, res_R, vrs, 
                          addExpr, pvexpr, pvi, stk, test, primeVars, sub, 
                          expr, sst, primedVars, localSub_, xlssi, xltemp1, 
                          temp1, temp2, temp3, res_X, sstsq, xprimedVars, 
                          localSub_X, lsstsq, localSub, defSub, nxt, lsstqi, 
                          lsstemp, disjs, defs, str >>

XlateSStmtSeq == XStSq1 \/ XStSq2 \/ XStSq3

XLS1 == /\ pc = "XLS1"
        /\ /\ elseq' = lsstsq
           /\ nxt_' = nxt
           /\ stack' = << [ procedure |->  "ExpandSeq",
                            pc        |->  "XLS2",
                            ixs       |->  ixs,
                            res_E     |->  res_E,
                            elseq     |->  elseq,
                            nxt_      |->  nxt_ ] >>
                        \o stack
        /\ ixs' = {}
        /\ res_E' = << >>
        /\ pc' = "EX1"
        /\ UNCHANGED << i, j, gtemp1, gtemp2, gtemp3, gtemp4, result, rVal, 
                        pMap, prcdVars, procSeq, globalVars, nonGlobalVars, 
                        allVarSeq, localVars, A, res_, ia, prcdr, ipr, proc, 
                        ip, lsseq, ilss, lstmt, whl, ls, ils, ilLast, ili, le, 
                        ile, fs, fi, ifi, ifLast, fe, ife, ife2, feSeq, 
                        feSeqLast, fw, ifw, fwLast, cr, icr, gt, sss, isss, ss, 
                        asg, ias, ifst, estmt, iee, wi, iw, vdcl, pvdcl, exp, 
                        ie, lst, nxt_E, temp_, flseq, temp_I, ifsqi, lseq, 
                        nxt_Ex, xxtemp1, temp2_, temp3_, temp4, exlsq, 
                        callStmt, prcd, svoci, temp, res_S, rprcd, rpvi, 
                        rpctemp, res_R, vrs, addExpr, pvexpr, pvi, stk, test, 
                        primeVars, sub, expr, sst, primedVars, localSub_, 
                        xlssi, xltemp1, temp1, temp2, temp3, res_X, sstsq, 
                        xprimedVars, localSub_X, res, xlsssqi, lsstsq, 
                        localSub, defSub, nxt, lsstqi, lsstemp, disjs, defs, 
                        str >>

XLS2 == /\ pc = "XLS2"
        /\ lsstemp' = rVal
        /\ pc' = "XLS3"
        /\ UNCHANGED << i, j, gtemp1, gtemp2, gtemp3, gtemp4, result, rVal, 
                        pMap, prcdVars, procSeq, globalVars, nonGlobalVars, 
                        allVarSeq, localVars, stack, A, res_, ia, prcdr, ipr, 
                        proc, ip, lsseq, ilss, lstmt, whl, ls, ils, ilLast, 
                        ili, le, ile, fs, fi, ifi, ifLast, fe, ife, ife2, 
                        feSeq, feSeqLast, fw, ifw, fwLast, cr, icr, gt, sss, 
                        isss, ss, asg, ias, ifst, estmt, iee, wi, iw, vdcl, 
                        pvdcl, exp, ie, elseq, nxt_, ixs, res_E, lst, nxt_E, 
                        temp_, flseq, temp_I, ifsqi, lseq, nxt_Ex, xxtemp1, 
                        temp2_, temp3_, temp4, exlsq, callStmt, prcd, svoci, 
                        temp, res_S, rprcd, rpvi, rpctemp, res_R, vrs, addExpr, 
                        pvexpr, pvi, stk, test, primeVars, sub, expr, sst, 
                        primedVars, localSub_, xlssi, xltemp1, temp1, temp2, 
                        temp3, res_X, sstsq, xprimedVars, localSub_X, res, 
                        xlsssqi, lsstsq, localSub, defSub, nxt, lsstqi, disjs, 
                        defs, str >>

XLS3 == /\ pc = "XLS3"
        /\ IF lsstqi \leq Len(lsstemp)
              THEN /\ /\ localSub_X' = localSub
                      /\ sstsq' = lsstemp[lsstqi].stmts
                      /\ stack' = << [ procedure |->  "XlateSStmtSeq",
                                       pc        |->  "XLS4",
                                       res       |->  res,
                                       xlsssqi   |->  xlsssqi,
                                       sstsq     |->  sstsq,
                                       xprimedVars |->  xprimedVars,
                                       localSub_X |->  localSub_X ] >>
                                   \o stack
                      /\ xprimedVars' = {}
                   /\ res' = {}
                   /\ xlsssqi' = 1
                   /\ pc' = "XStSq1"
                   /\ UNCHANGED << rVal, lsstsq, localSub, defSub, nxt, lsstqi, 
                                   lsstemp, disjs, defs >>
              ELSE /\ rVal' = [defs |-> defs, disj |-> MakeDisj(disjs)]
                   /\ pc' = Head(stack).pc
                   /\ lsstqi' = Head(stack).lsstqi
                   /\ lsstemp' = Head(stack).lsstemp
                   /\ disjs' = Head(stack).disjs
                   /\ defs' = Head(stack).defs
                   /\ lsstsq' = Head(stack).lsstsq
                   /\ localSub' = Head(stack).localSub
                   /\ defSub' = Head(stack).defSub
                   /\ nxt' = Head(stack).nxt
                   /\ stack' = Tail(stack)
                   /\ UNCHANGED << sstsq, xprimedVars, localSub_X, res, 
                                   xlsssqi >>
        /\ UNCHANGED << i, j, gtemp1, gtemp2, gtemp3, gtemp4, result, pMap, 
                        prcdVars, procSeq, globalVars, nonGlobalVars, 
                        allVarSeq, localVars, A, res_, ia, prcdr, ipr, proc, 
                        ip, lsseq, ilss, lstmt, whl, ls, ils, ilLast, ili, le, 
                        ile, fs, fi, ifi, ifLast, fe, ife, ife2, feSeq, 
                        feSeqLast, fw, ifw, fwLast, cr, icr, gt, sss, isss, ss, 
                        asg, ias, ifst, estmt, iee, wi, iw, vdcl, pvdcl, exp, 
                        ie, elseq, nxt_, ixs, res_E, lst, nxt_E, temp_, flseq, 
                        temp_I, ifsqi, lseq, nxt_Ex, xxtemp1, temp2_, temp3_, 
                        temp4, exlsq, callStmt, prcd, svoci, temp, res_S, 
                        rprcd, rpvi, rpctemp, res_R, vrs, addExpr, pvexpr, pvi, 
                        stk, test, primeVars, sub, expr, sst, primedVars, 
                        localSub_, xlssi, xltemp1, temp1, temp2, temp3, res_X, 
                        str >>

XLS4 == /\ pc = "XLS4"
        /\ defs' = defs \o
                           << lsstemp[lsstqi].label >>
                              \o defSub \o <<"==">>
                              \o MakeConj( << <<"@pc@">> \o localSub \o <<"=">>
                                                \o Quote(lsstemp[lsstqi].label)
                                            >> \o rVal.action \o
                                            MakeUnchanged(
                                             CompSetToSubseq(rVal.pVars,
                                                             allVarSeq)))
        /\ disjs' = Append(disjs, << lsstemp[lsstqi].label >> \o defSub)
        /\ lsstqi' = lsstqi + 1
        /\ pc' = "XLS3"
        /\ UNCHANGED << i, j, gtemp1, gtemp2, gtemp3, gtemp4, result, rVal, 
                        pMap, prcdVars, procSeq, globalVars, nonGlobalVars, 
                        allVarSeq, localVars, stack, A, res_, ia, prcdr, ipr, 
                        proc, ip, lsseq, ilss, lstmt, whl, ls, ils, ilLast, 
                        ili, le, ile, fs, fi, ifi, ifLast, fe, ife, ife2, 
                        feSeq, feSeqLast, fw, ifw, fwLast, cr, icr, gt, sss, 
                        isss, ss, asg, ias, ifst, estmt, iee, wi, iw, vdcl, 
                        pvdcl, exp, ie, elseq, nxt_, ixs, res_E, lst, nxt_E, 
                        temp_, flseq, temp_I, ifsqi, lseq, nxt_Ex, xxtemp1, 
                        temp2_, temp3_, temp4, exlsq, callStmt, prcd, svoci, 
                        temp, res_S, rprcd, rpvi, rpctemp, res_R, vrs, addExpr, 
                        pvexpr, pvi, stk, test, primeVars, sub, expr, sst, 
                        primedVars, localSub_, xlssi, xltemp1, temp1, temp2, 
                        temp3, res_X, sstsq, xprimedVars, localSub_X, res, 
                        xlsssqi, lsstsq, localSub, defSub, nxt, lsstemp, str >>

XlateLabStmtSeq == XLS1 \/ XLS2 \/ XLS3 \/ XLS4

Error1 == /\ pc = "Error1"
          /\ PrintT("<<@Error@" \o str \o "@EndError@")
          /\ pc' = "Done"
          /\ UNCHANGED << i, j, gtemp1, gtemp2, gtemp3, gtemp4, result, rVal, 
                          pMap, prcdVars, procSeq, globalVars, nonGlobalVars, 
                          allVarSeq, localVars, stack, A, res_, ia, prcdr, ipr, 
                          proc, ip, lsseq, ilss, lstmt, whl, ls, ils, ilLast, 
                          ili, le, ile, fs, fi, ifi, ifLast, fe, ife, ife2, 
                          feSeq, feSeqLast, fw, ifw, fwLast, cr, icr, gt, sss, 
                          isss, ss, asg, ias, ifst, estmt, iee, wi, iw, vdcl, 
                          pvdcl, exp, ie, elseq, nxt_, ixs, res_E, lst, nxt_E, 
                          temp_, flseq, temp_I, ifsqi, lseq, nxt_Ex, xxtemp1, 
                          temp2_, temp3_, temp4, exlsq, callStmt, prcd, svoci, 
                          temp, res_S, rprcd, rpvi, rpctemp, res_R, vrs, 
                          addExpr, pvexpr, pvi, stk, test, primeVars, sub, 
                          expr, sst, primedVars, localSub_, xlssi, xltemp1, 
                          temp1, temp2, temp3, res_X, sstsq, xprimedVars, 
                          localSub_X, res, xlsssqi, lsstsq, localSub, defSub, 
                          nxt, lsstqi, lsstemp, disjs, defs, str >>

Error2 == /\ pc = "Error2"
          /\ pc' = Head(stack).pc
          /\ str' = Head(stack).str
          /\ stack' = Tail(stack)
          /\ UNCHANGED << i, j, gtemp1, gtemp2, gtemp3, gtemp4, result, rVal, 
                          pMap, prcdVars, procSeq, globalVars, nonGlobalVars, 
                          allVarSeq, localVars, A, res_, ia, prcdr, ipr, proc, 
                          ip, lsseq, ilss, lstmt, whl, ls, ils, ilLast, ili, 
                          le, ile, fs, fi, ifi, ifLast, fe, ife, ife2, feSeq, 
                          feSeqLast, fw, ifw, fwLast, cr, icr, gt, sss, isss, 
                          ss, asg, ias, ifst, estmt, iee, wi, iw, vdcl, pvdcl, 
                          exp, ie, elseq, nxt_, ixs, res_E, lst, nxt_E, temp_, 
                          flseq, temp_I, ifsqi, lseq, nxt_Ex, xxtemp1, temp2_, 
                          temp3_, temp4, exlsq, callStmt, prcd, svoci, temp, 
                          res_S, rprcd, rpvi, rpctemp, res_R, vrs, addExpr, 
                          pvexpr, pvi, stk, test, primeVars, sub, expr, sst, 
                          primedVars, localSub_, xlssi, xltemp1, temp1, temp2, 
                          temp3, res_X, sstsq, xprimedVars, localSub_X, res, 
                          xlsssqi, lsstsq, localSub, defSub, nxt, lsstqi, 
                          lsstemp, disjs, defs >>

Error == Error1 \/ Error2

PC1 == /\ pc = "PC1"
       /\ /\ A' = ast
          /\ stack' = << [ procedure |->  "IsAlgorithm",
                           pc        |->  "PC2",
                           res_      |->  res_,
                           ia        |->  ia,
                           A         |->  A ] >>
                       \o stack
       /\ res_' = FALSE
       /\ ia' = 0
       /\ pc' = "IA1"
       /\ UNCHANGED << i, j, gtemp1, gtemp2, gtemp3, gtemp4, result, rVal, 
                       pMap, prcdVars, procSeq, globalVars, nonGlobalVars, 
                       allVarSeq, localVars, prcdr, ipr, proc, ip, lsseq, ilss, 
                       lstmt, whl, ls, ils, ilLast, ili, le, ile, fs, fi, ifi, 
                       ifLast, fe, ife, ife2, feSeq, feSeqLast, fw, ifw, 
                       fwLast, cr, icr, gt, sss, isss, ss, asg, ias, ifst, 
                       estmt, iee, wi, iw, vdcl, pvdcl, exp, ie, elseq, nxt_, 
                       ixs, res_E, lst, nxt_E, temp_, flseq, temp_I, ifsqi, 
                       lseq, nxt_Ex, xxtemp1, temp2_, temp3_, temp4, exlsq, 
                       callStmt, prcd, svoci, temp, res_S, rprcd, rpvi, 
                       rpctemp, res_R, vrs, addExpr, pvexpr, pvi, stk, test, 
                       primeVars, sub, expr, sst, primedVars, localSub_, xlssi, 
                       xltemp1, temp1, temp2, temp3, res_X, sstsq, xprimedVars, 
                       localSub_X, res, xlsssqi, lsstsq, localSub, defSub, nxt, 
                       lsstqi, lsstemp, disjs, defs, str >>

PC2 == /\ pc = "PC2"
       /\ PrintT(ast.name \o " is a legal Algorithm")
       /\ pMap' = << >>
       /\ i' = 1
       /\ pc' = "PC3"
       /\ UNCHANGED << j, gtemp1, gtemp2, gtemp3, gtemp4, result, rVal, 
                       prcdVars, procSeq, globalVars, nonGlobalVars, allVarSeq, 
                       localVars, stack, A, res_, ia, prcdr, ipr, proc, ip, 
                       lsseq, ilss, lstmt, whl, ls, ils, ilLast, ili, le, ile, 
                       fs, fi, ifi, ifLast, fe, ife, ife2, feSeq, feSeqLast, 
                       fw, ifw, fwLast, cr, icr, gt, sss, isss, ss, asg, ias, 
                       ifst, estmt, iee, wi, iw, vdcl, pvdcl, exp, ie, elseq, 
                       nxt_, ixs, res_E, lst, nxt_E, temp_, flseq, temp_I, 
                       ifsqi, lseq, nxt_Ex, xxtemp1, temp2_, temp3_, temp4, 
                       exlsq, callStmt, prcd, svoci, temp, res_S, rprcd, rpvi, 
                       rpctemp, res_R, vrs, addExpr, pvexpr, pvi, stk, test, 
                       primeVars, sub, expr, sst, primedVars, localSub_, xlssi, 
                       xltemp1, temp1, temp2, temp3, res_X, sstsq, xprimedVars, 
                       localSub_X, res, xlsssqi, lsstsq, localSub, defSub, nxt, 
                       lsstqi, lsstemp, disjs, defs, str >>

PC3 == /\ pc = "PC3"
       /\ IF i \leq Len(ast.prcds)
             THEN /\ pMap' = pMap @@
                               (ast.prcds[i].name :>
                                 [params  |-> [x \in 1..Len(ast.prcds[i].params) |->
                                                         ast.prcds[i].params[x].var],
                                  vars    |-> [x \in 1..Len(ast.prcds[i].decls) |->
                                                         ast.prcds[i].decls[x].var],
                                  vals    |-> [x \in 1..Len(ast.prcds[i].decls) |->
                                                         ast.prcds[i].decls[x].val],
                                  label   |-> ast.prcds[i].body[1].label,
                                  tlavars |-> {ast.prcds[i].params[y].var :
                                                  y \in 1..Len(ast.prcds[i].params)}
                                                \cup
                                              {ast.prcds[i].decls[y].var :
                                                  y \in 1..Len(ast.prcds[i].decls)}] )
                  /\ i' = i+1
                  /\ pc' = "PC3"
                  /\ UNCHANGED << prcdVars, procSeq, globalVars, allVarSeq >>
             ELSE /\ prcdVars' = UNION {SeqToSet(pMap[x].params) \cup
                                         SeqToSet(pMap[x].vars) : x \in DOMAIN pMap}
                  /\ IF ast.type = "multiprocess"
                        THEN /\ procSeq' = [y \in 1.. Len(ast.procs) |->
                                              [vars  |-> [x \in 1..Len(ast.procs[y].decls)
                                                             |-> ast.procs[y].decls[x].var],
                                               label |-> ast.procs[y].body[1].label] ]
                        ELSE /\ procSeq' = << >>
                  /\ allVarSeq' = [x \in 1..Len(ast.decls) |-> ast.decls[x].var]
                                    \o <<"@pc@">>
                  /\ globalVars' = SeqToSet(allVarSeq')
                  /\ pc' = "PC4"
                  /\ UNCHANGED << i, pMap >>
       /\ UNCHANGED << j, gtemp1, gtemp2, gtemp3, gtemp4, result, rVal, 
                       nonGlobalVars, localVars, stack, A, res_, ia, prcdr, 
                       ipr, proc, ip, lsseq, ilss, lstmt, whl, ls, ils, ilLast, 
                       ili, le, ile, fs, fi, ifi, ifLast, fe, ife, ife2, feSeq, 
                       feSeqLast, fw, ifw, fwLast, cr, icr, gt, sss, isss, ss, 
                       asg, ias, ifst, estmt, iee, wi, iw, vdcl, pvdcl, exp, 
                       ie, elseq, nxt_, ixs, res_E, lst, nxt_E, temp_, flseq, 
                       temp_I, ifsqi, lseq, nxt_Ex, xxtemp1, temp2_, temp3_, 
                       temp4, exlsq, callStmt, prcd, svoci, temp, res_S, rprcd, 
                       rpvi, rpctemp, res_R, vrs, addExpr, pvexpr, pvi, stk, 
                       test, primeVars, sub, expr, sst, primedVars, localSub_, 
                       xlssi, xltemp1, temp1, temp2, temp3, res_X, sstsq, 
                       xprimedVars, localSub_X, res, xlsssqi, lsstsq, localSub, 
                       defSub, nxt, lsstqi, lsstemp, disjs, defs, str >>

PC4 == /\ pc = "PC4"
       /\ IF ast.prcds # << >>
             THEN /\ allVarSeq' = allVarSeq \o <<"@stack@">> \o
                                  
                                  SeqConcat(
                                    [x \in 1..Len(ast.prcds) |->
                                      [y \in 1..Len(ast.prcds[x].decls) |->
                                         ast.prcds[x].decls[y].var]
                                      \o
                                      [y \in 1..Len(ast.prcds[x].params) |->
                                         ast.prcds[x].params[y].var] ])
                  /\ globalVars' = globalVars \cup {"@stack@"}
             ELSE /\ TRUE
                  /\ UNCHANGED << globalVars, allVarSeq >>
       /\ pc' = "PC5"
       /\ UNCHANGED << i, j, gtemp1, gtemp2, gtemp3, gtemp4, result, rVal, 
                       pMap, prcdVars, procSeq, nonGlobalVars, localVars, 
                       stack, A, res_, ia, prcdr, ipr, proc, ip, lsseq, ilss, 
                       lstmt, whl, ls, ils, ilLast, ili, le, ile, fs, fi, ifi, 
                       ifLast, fe, ife, ife2, feSeq, feSeqLast, fw, ifw, 
                       fwLast, cr, icr, gt, sss, isss, ss, asg, ias, ifst, 
                       estmt, iee, wi, iw, vdcl, pvdcl, exp, ie, elseq, nxt_, 
                       ixs, res_E, lst, nxt_E, temp_, flseq, temp_I, ifsqi, 
                       lseq, nxt_Ex, xxtemp1, temp2_, temp3_, temp4, exlsq, 
                       callStmt, prcd, svoci, temp, res_S, rprcd, rpvi, 
                       rpctemp, res_R, vrs, addExpr, pvexpr, pvi, stk, test, 
                       primeVars, sub, expr, sst, primedVars, localSub_, xlssi, 
                       xltemp1, temp1, temp2, temp3, res_X, sstsq, xprimedVars, 
                       localSub_X, res, xlsssqi, lsstsq, localSub, defSub, nxt, 
                       lsstqi, lsstemp, disjs, defs, str >>

PC5 == /\ pc = "PC5"
       /\ IF ast.type = "multiprocess"
             THEN /\ allVarSeq' = allVarSeq \o
                                     SeqConcat(
                                         [x \in 1..Len(ast.procs) |->
                                           [y \in 1..Len(ast.procs[x].decls) |->
                                              ast.procs[x].decls[y].var]])
             ELSE /\ TRUE
                  /\ UNCHANGED allVarSeq
       /\ nonGlobalVars' = SeqToSet(allVarSeq') \ globalVars
       /\ IF (ast.defs = << >>) \/ (globalVars = {})
             THEN /\ result' = ast.defs \o <<"VARIABLES">> \o CommaSeq(allVarSeq')
             ELSE /\ result' = <<"VARIABLES">> \o
                                  CommaSeq(SetToSubseq(globalVars, allVarSeq')) \o
                               ast.defs \o <<"VARIABLES">> \o
                                  CommaSeq(SetToSubseq(nonGlobalVars', allVarSeq'))
       /\ pc' = "PC6"
       /\ UNCHANGED << i, j, gtemp1, gtemp2, gtemp3, gtemp4, rVal, pMap, 
                       prcdVars, procSeq, globalVars, localVars, stack, A, 
                       res_, ia, prcdr, ipr, proc, ip, lsseq, ilss, lstmt, whl, 
                       ls, ils, ilLast, ili, le, ile, fs, fi, ifi, ifLast, fe, 
                       ife, ife2, feSeq, feSeqLast, fw, ifw, fwLast, cr, icr, 
                       gt, sss, isss, ss, asg, ias, ifst, estmt, iee, wi, iw, 
                       vdcl, pvdcl, exp, ie, elseq, nxt_, ixs, res_E, lst, 
                       nxt_E, temp_, flseq, temp_I, ifsqi, lseq, nxt_Ex, 
                       xxtemp1, temp2_, temp3_, temp4, exlsq, callStmt, prcd, 
                       svoci, temp, res_S, rprcd, rpvi, rpctemp, res_R, vrs, 
                       addExpr, pvexpr, pvi, stk, test, primeVars, sub, expr, 
                       sst, primedVars, localSub_, xlssi, xltemp1, temp1, 
                       temp2, temp3, res_X, sstsq, xprimedVars, localSub_X, 
                       res, xlsssqi, lsstsq, localSub, defSub, nxt, lsstqi, 
                       lsstemp, disjs, defs, str >>

PC6 == /\ pc = "PC6"
       /\ result' = result \o <<"vars", "==", "<<">> \o CommaSeq(allVarSeq)
                     \o <<">>">>
       /\ pc' = "PC7"
       /\ UNCHANGED << i, j, gtemp1, gtemp2, gtemp3, gtemp4, rVal, pMap, 
                       prcdVars, procSeq, globalVars, nonGlobalVars, allVarSeq, 
                       localVars, stack, A, res_, ia, prcdr, ipr, proc, ip, 
                       lsseq, ilss, lstmt, whl, ls, ils, ilLast, ili, le, ile, 
                       fs, fi, ifi, ifLast, fe, ife, ife2, feSeq, feSeqLast, 
                       fw, ifw, fwLast, cr, icr, gt, sss, isss, ss, asg, ias, 
                       ifst, estmt, iee, wi, iw, vdcl, pvdcl, exp, ie, elseq, 
                       nxt_, ixs, res_E, lst, nxt_E, temp_, flseq, temp_I, 
                       ifsqi, lseq, nxt_Ex, xxtemp1, temp2_, temp3_, temp4, 
                       exlsq, callStmt, prcd, svoci, temp, res_S, rprcd, rpvi, 
                       rpctemp, res_R, vrs, addExpr, pvexpr, pvi, stk, test, 
                       primeVars, sub, expr, sst, primedVars, localSub_, xlssi, 
                       xltemp1, temp1, temp2, temp3, res_X, sstsq, xprimedVars, 
                       localSub_X, res, xlsssqi, lsstsq, localSub, defSub, nxt, 
                       lsstqi, lsstemp, disjs, defs, str >>

PC7 == /\ pc = "PC7"
       /\ IF ast.type = "multiprocess"
             THEN /\ result' = result \o <<"ProcSet", "==">> \o
                                MakeUnion(SeqConcat([x \in 1..Len(ast.procs) |->
                                           IF ast.procs[x].eqOrIn = "\\in"
                                             THEN <<ast.procs[x].id>>
                                             ELSE << <<"{">> \o  ast.procs[x].id
                                                       \o << "}">>
                                                  >> ] ) )
             ELSE /\ TRUE
                  /\ UNCHANGED result
       /\ pc' = "PC8"
       /\ UNCHANGED << i, j, gtemp1, gtemp2, gtemp3, gtemp4, rVal, pMap, 
                       prcdVars, procSeq, globalVars, nonGlobalVars, allVarSeq, 
                       localVars, stack, A, res_, ia, prcdr, ipr, proc, ip, 
                       lsseq, ilss, lstmt, whl, ls, ils, ilLast, ili, le, ile, 
                       fs, fi, ifi, ifLast, fe, ife, ife2, feSeq, feSeqLast, 
                       fw, ifw, fwLast, cr, icr, gt, sss, isss, ss, asg, ias, 
                       ifst, estmt, iee, wi, iw, vdcl, pvdcl, exp, ie, elseq, 
                       nxt_, ixs, res_E, lst, nxt_E, temp_, flseq, temp_I, 
                       ifsqi, lseq, nxt_Ex, xxtemp1, temp2_, temp3_, temp4, 
                       exlsq, callStmt, prcd, svoci, temp, res_S, rprcd, rpvi, 
                       rpctemp, res_R, vrs, addExpr, pvexpr, pvi, stk, test, 
                       primeVars, sub, expr, sst, primedVars, localSub_, xlssi, 
                       xltemp1, temp1, temp2, temp3, res_X, sstsq, xprimedVars, 
                       localSub_X, res, xlsssqi, lsstsq, localSub, defSub, nxt, 
                       lsstqi, lsstemp, disjs, defs, str >>

PC8 == /\ pc = "PC8"
       /\ gtemp1' = << >>
       /\ i' = 1
       /\ pc' = "PC9"
       /\ UNCHANGED << j, gtemp2, gtemp3, gtemp4, result, rVal, pMap, prcdVars, 
                       procSeq, globalVars, nonGlobalVars, allVarSeq, 
                       localVars, stack, A, res_, ia, prcdr, ipr, proc, ip, 
                       lsseq, ilss, lstmt, whl, ls, ils, ilLast, ili, le, ile, 
                       fs, fi, ifi, ifLast, fe, ife, ife2, feSeq, feSeqLast, 
                       fw, ifw, fwLast, cr, icr, gt, sss, isss, ss, asg, ias, 
                       ifst, estmt, iee, wi, iw, vdcl, pvdcl, exp, ie, elseq, 
                       nxt_, ixs, res_E, lst, nxt_E, temp_, flseq, temp_I, 
                       ifsqi, lseq, nxt_Ex, xxtemp1, temp2_, temp3_, temp4, 
                       exlsq, callStmt, prcd, svoci, temp, res_S, rprcd, rpvi, 
                       rpctemp, res_R, vrs, addExpr, pvexpr, pvi, stk, test, 
                       primeVars, sub, expr, sst, primedVars, localSub_, xlssi, 
                       xltemp1, temp1, temp2, temp3, res_X, sstsq, xprimedVars, 
                       localSub_X, res, xlsssqi, lsstsq, localSub, defSub, nxt, 
                       lsstqi, lsstemp, disjs, defs, str >>

PC9 == /\ pc = "PC9"
       /\ IF i \leq Len(ast.decls)
             THEN /\ gtemp1' = gtemp1 \o << <<ast.decls[i].var, ast.decls[i].eqOrIn>>
                                \o ast.decls[i].val >>
                  /\ i' = i + 1
                  /\ pc' = "PC9"
             ELSE /\ i' = 1
                  /\ pc' = "PC10"
                  /\ UNCHANGED gtemp1
       /\ UNCHANGED << j, gtemp2, gtemp3, gtemp4, result, rVal, pMap, prcdVars, 
                       procSeq, globalVars, nonGlobalVars, allVarSeq, 
                       localVars, stack, A, res_, ia, prcdr, ipr, proc, ip, 
                       lsseq, ilss, lstmt, whl, ls, ils, ilLast, ili, le, ile, 
                       fs, fi, ifi, ifLast, fe, ife, ife2, feSeq, feSeqLast, 
                       fw, ifw, fwLast, cr, icr, gt, sss, isss, ss, asg, ias, 
                       ifst, estmt, iee, wi, iw, vdcl, pvdcl, exp, ie, elseq, 
                       nxt_, ixs, res_E, lst, nxt_E, temp_, flseq, temp_I, 
                       ifsqi, lseq, nxt_Ex, xxtemp1, temp2_, temp3_, temp4, 
                       exlsq, callStmt, prcd, svoci, temp, res_S, rprcd, rpvi, 
                       rpctemp, res_R, vrs, addExpr, pvexpr, pvi, stk, test, 
                       primeVars, sub, expr, sst, primedVars, localSub_, xlssi, 
                       xltemp1, temp1, temp2, temp3, res_X, sstsq, xprimedVars, 
                       localSub_X, res, xlsssqi, lsstsq, localSub, defSub, nxt, 
                       lsstqi, lsstemp, disjs, defs, str >>

PC10 == /\ pc = "PC10"
        /\ IF i \leq Len(ast.prcds)
              THEN /\ j' = 1
                   /\ pc' = "PC11"
                   /\ UNCHANGED i
              ELSE /\ IF ast.type = "multiprocess"
                         THEN /\ i' = 1
                              /\ pc' = "PC13"
                         ELSE /\ pc' = "PC15"
                              /\ UNCHANGED i
                   /\ UNCHANGED j
        /\ UNCHANGED << gtemp1, gtemp2, gtemp3, gtemp4, result, rVal, pMap, 
                        prcdVars, procSeq, globalVars, nonGlobalVars, 
                        allVarSeq, localVars, stack, A, res_, ia, prcdr, ipr, 
                        proc, ip, lsseq, ilss, lstmt, whl, ls, ils, ilLast, 
                        ili, le, ile, fs, fi, ifi, ifLast, fe, ife, ife2, 
                        feSeq, feSeqLast, fw, ifw, fwLast, cr, icr, gt, sss, 
                        isss, ss, asg, ias, ifst, estmt, iee, wi, iw, vdcl, 
                        pvdcl, exp, ie, elseq, nxt_, ixs, res_E, lst, nxt_E, 
                        temp_, flseq, temp_I, ifsqi, lseq, nxt_Ex, xxtemp1, 
                        temp2_, temp3_, temp4, exlsq, callStmt, prcd, svoci, 
                        temp, res_S, rprcd, rpvi, rpctemp, res_R, vrs, addExpr, 
                        pvexpr, pvi, stk, test, primeVars, sub, expr, sst, 
                        primedVars, localSub_, xlssi, xltemp1, temp1, temp2, 
                        temp3, res_X, sstsq, xprimedVars, localSub_X, res, 
                        xlsssqi, lsstsq, localSub, defSub, nxt, lsstqi, 
                        lsstemp, disjs, defs, str >>

PC11 == /\ pc = "PC11"
        /\ IF j \leq Len(ast.prcds[i].params)
              THEN /\ IF ast.type = "uniprocess"
                         THEN /\ gtemp1' = gtemp1 \o << <<ast.prcds[i].params[j].var, "=">>
                                             \o ast.prcds[i].params[j].val >>
                         ELSE /\ gtemp1' = gtemp1 \o
                                             << <<ast.prcds[i].params[j].var, "=", "[",
                                                "self", "\\in", "ProcSet", "|->">>
                                             \o ast.prcds[i].params[j].val \o <<"]">> >>
                   /\ j' = j + 1
                   /\ pc' = "PC11"
              ELSE /\ j' = 1
                   /\ pc' = "PC12"
                   /\ UNCHANGED gtemp1
        /\ UNCHANGED << i, gtemp2, gtemp3, gtemp4, result, rVal, pMap, 
                        prcdVars, procSeq, globalVars, nonGlobalVars, 
                        allVarSeq, localVars, stack, A, res_, ia, prcdr, ipr, 
                        proc, ip, lsseq, ilss, lstmt, whl, ls, ils, ilLast, 
                        ili, le, ile, fs, fi, ifi, ifLast, fe, ife, ife2, 
                        feSeq, feSeqLast, fw, ifw, fwLast, cr, icr, gt, sss, 
                        isss, ss, asg, ias, ifst, estmt, iee, wi, iw, vdcl, 
                        pvdcl, exp, ie, elseq, nxt_, ixs, res_E, lst, nxt_E, 
                        temp_, flseq, temp_I, ifsqi, lseq, nxt_Ex, xxtemp1, 
                        temp2_, temp3_, temp4, exlsq, callStmt, prcd, svoci, 
                        temp, res_S, rprcd, rpvi, rpctemp, res_R, vrs, addExpr, 
                        pvexpr, pvi, stk, test, primeVars, sub, expr, sst, 
                        primedVars, localSub_, xlssi, xltemp1, temp1, temp2, 
                        temp3, res_X, sstsq, xprimedVars, localSub_X, res, 
                        xlsssqi, lsstsq, localSub, defSub, nxt, lsstqi, 
                        lsstemp, disjs, defs, str >>

PC12 == /\ pc = "PC12"
        /\ IF j \leq Len(ast.prcds[i].decls)
              THEN /\ IF ast.type = "uniprocess"
                         THEN /\ gtemp1' = gtemp1 \o << <<ast.prcds[i].decls[j].var, "=">>
                                             \o ast.prcds[i].decls[j].val >>
                         ELSE /\ gtemp1' = gtemp1 \o
                                             << <<ast.prcds[i].decls[j].var, "=", "[",
                                                "self", "\\in", "ProcSet", "|->">>
                                             \o ast.prcds[i].decls[j].val \o <<"]">> >>
                   /\ j' = j + 1
                   /\ pc' = "PC12"
                   /\ UNCHANGED i
              ELSE /\ i' = i + 1
                   /\ pc' = "PC10"
                   /\ UNCHANGED << j, gtemp1 >>
        /\ UNCHANGED << gtemp2, gtemp3, gtemp4, result, rVal, pMap, prcdVars, 
                        procSeq, globalVars, nonGlobalVars, allVarSeq, 
                        localVars, stack, A, res_, ia, prcdr, ipr, proc, ip, 
                        lsseq, ilss, lstmt, whl, ls, ils, ilLast, ili, le, ile, 
                        fs, fi, ifi, ifLast, fe, ife, ife2, feSeq, feSeqLast, 
                        fw, ifw, fwLast, cr, icr, gt, sss, isss, ss, asg, ias, 
                        ifst, estmt, iee, wi, iw, vdcl, pvdcl, exp, ie, elseq, 
                        nxt_, ixs, res_E, lst, nxt_E, temp_, flseq, temp_I, 
                        ifsqi, lseq, nxt_Ex, xxtemp1, temp2_, temp3_, temp4, 
                        exlsq, callStmt, prcd, svoci, temp, res_S, rprcd, rpvi, 
                        rpctemp, res_R, vrs, addExpr, pvexpr, pvi, stk, test, 
                        primeVars, sub, expr, sst, primedVars, localSub_, 
                        xlssi, xltemp1, temp1, temp2, temp3, res_X, sstsq, 
                        xprimedVars, localSub_X, res, xlsssqi, lsstsq, 
                        localSub, defSub, nxt, lsstqi, lsstemp, disjs, defs, 
                        str >>

PC13 == /\ pc = "PC13"
        /\ IF i \leq Len(ast.procs)
              THEN /\ j' = 1
                   /\ pc' = "PC14"
              ELSE /\ pc' = "PC15"
                   /\ UNCHANGED j
        /\ UNCHANGED << i, gtemp1, gtemp2, gtemp3, gtemp4, result, rVal, pMap, 
                        prcdVars, procSeq, globalVars, nonGlobalVars, 
                        allVarSeq, localVars, stack, A, res_, ia, prcdr, ipr, 
                        proc, ip, lsseq, ilss, lstmt, whl, ls, ils, ilLast, 
                        ili, le, ile, fs, fi, ifi, ifLast, fe, ife, ife2, 
                        feSeq, feSeqLast, fw, ifw, fwLast, cr, icr, gt, sss, 
                        isss, ss, asg, ias, ifst, estmt, iee, wi, iw, vdcl, 
                        pvdcl, exp, ie, elseq, nxt_, ixs, res_E, lst, nxt_E, 
                        temp_, flseq, temp_I, ifsqi, lseq, nxt_Ex, xxtemp1, 
                        temp2_, temp3_, temp4, exlsq, callStmt, prcd, svoci, 
                        temp, res_S, rprcd, rpvi, rpctemp, res_R, vrs, addExpr, 
                        pvexpr, pvi, stk, test, primeVars, sub, expr, sst, 
                        primedVars, localSub_, xlssi, xltemp1, temp1, temp2, 
                        temp3, res_X, sstsq, xprimedVars, localSub_X, res, 
                        xlsssqi, lsstsq, localSub, defSub, nxt, lsstqi, 
                        lsstemp, disjs, defs, str >>

PC14 == /\ pc = "PC14"
        /\ IF j \leq Len(ast.procs[i].decls)
              THEN /\ IF ast.procs[i].eqOrIn = "="
                         THEN /\ gtemp1' = gtemp1 \o << <<ast.procs[i].decls[j].var,
                                                          ast.procs[i].decls[j].eqOrIn>>
                                                        \o ast.procs[i].decls[j].val >>
                         ELSE /\ IF ast.procs[i].decls[j].eqOrIn = "="
                                    THEN /\ gtemp1' = gtemp1 \o
                                                       << <<ast.procs[i].decls[j].var, "=",
                                                            "[", "self", "\\in">> \o
                                                            ast.procs[i].id \o <<"|->" >>
                                                            \o ast.procs[i].decls[j].val
                                                            \o <<"]">> >>
                                    ELSE /\ gtemp1' = gtemp1 \o
                                                       << <<ast.procs[i].decls[j].var, "\\in",
                                                            "[">> \o ast.procs[i].id \o <<"->">>
                                                            \o ast.procs[i].decls[j].val
                                                            \o <<"]">> >>
                   /\ j' = j + 1
                   /\ pc' = "PC14"
                   /\ UNCHANGED i
              ELSE /\ i' = i + 1
                   /\ pc' = "PC13"
                   /\ UNCHANGED << j, gtemp1 >>
        /\ UNCHANGED << gtemp2, gtemp3, gtemp4, result, rVal, pMap, prcdVars, 
                        procSeq, globalVars, nonGlobalVars, allVarSeq, 
                        localVars, stack, A, res_, ia, prcdr, ipr, proc, ip, 
                        lsseq, ilss, lstmt, whl, ls, ils, ilLast, ili, le, ile, 
                        fs, fi, ifi, ifLast, fe, ife, ife2, feSeq, feSeqLast, 
                        fw, ifw, fwLast, cr, icr, gt, sss, isss, ss, asg, ias, 
                        ifst, estmt, iee, wi, iw, vdcl, pvdcl, exp, ie, elseq, 
                        nxt_, ixs, res_E, lst, nxt_E, temp_, flseq, temp_I, 
                        ifsqi, lseq, nxt_Ex, xxtemp1, temp2_, temp3_, temp4, 
                        exlsq, callStmt, prcd, svoci, temp, res_S, rprcd, rpvi, 
                        rpctemp, res_R, vrs, addExpr, pvexpr, pvi, stk, test, 
                        primeVars, sub, expr, sst, primedVars, localSub_, 
                        xlssi, xltemp1, temp1, temp2, temp3, res_X, sstsq, 
                        xprimedVars, localSub_X, res, xlsssqi, lsstsq, 
                        localSub, defSub, nxt, lsstqi, lsstemp, disjs, defs, 
                        str >>

PC15 == /\ pc = "PC15"
        /\ IF ast.prcds # << >>
              THEN /\ IF ast.type = "uniprocess"
                         THEN /\ gtemp1' = gtemp1 \o << <<"@stack@", "=", "<<", ">>" >> >>
                         ELSE /\ gtemp1' = gtemp1 \o << <<"@stack@", "=", "[", "self", "\\in",
                                                          "ProcSet", "|->", "<<", ">>", "]" >> >>
              ELSE /\ TRUE
                   /\ UNCHANGED gtemp1
        /\ pc' = "PC16"
        /\ UNCHANGED << i, j, gtemp2, gtemp3, gtemp4, result, rVal, pMap, 
                        prcdVars, procSeq, globalVars, nonGlobalVars, 
                        allVarSeq, localVars, stack, A, res_, ia, prcdr, ipr, 
                        proc, ip, lsseq, ilss, lstmt, whl, ls, ils, ilLast, 
                        ili, le, ile, fs, fi, ifi, ifLast, fe, ife, ife2, 
                        feSeq, feSeqLast, fw, ifw, fwLast, cr, icr, gt, sss, 
                        isss, ss, asg, ias, ifst, estmt, iee, wi, iw, vdcl, 
                        pvdcl, exp, ie, elseq, nxt_, ixs, res_E, lst, nxt_E, 
                        temp_, flseq, temp_I, ifsqi, lseq, nxt_Ex, xxtemp1, 
                        temp2_, temp3_, temp4, exlsq, callStmt, prcd, svoci, 
                        temp, res_S, rprcd, rpvi, rpctemp, res_R, vrs, addExpr, 
                        pvexpr, pvi, stk, test, primeVars, sub, expr, sst, 
                        primedVars, localSub_, xlssi, xltemp1, temp1, temp2, 
                        temp3, res_X, sstsq, xprimedVars, localSub_X, res, 
                        xlsssqi, lsstsq, localSub, defSub, nxt, lsstqi, 
                        lsstemp, disjs, defs, str >>

PC16 == /\ pc = "PC16"
        /\ IF ast.type = "uniprocess"
              THEN /\ gtemp1' = gtemp1 \o << <<"@pc@", "=">> \o
                                         Quote(ast.body[1].label) >>
                   /\ pc' = "PC19"
                   /\ UNCHANGED << i, gtemp2 >>
              ELSE /\ gtemp2' = <<"@pc@", "=", "[", "self", "\\in", "ProcSet",
                                       "|->", "CASE">>
                   /\ i' = 1
                   /\ pc' = "PC17"
                   /\ UNCHANGED gtemp1
        /\ UNCHANGED << j, gtemp3, gtemp4, result, rVal, pMap, prcdVars, 
                        procSeq, globalVars, nonGlobalVars, allVarSeq, 
                        localVars, stack, A, res_, ia, prcdr, ipr, proc, ip, 
                        lsseq, ilss, lstmt, whl, ls, ils, ilLast, ili, le, ile, 
                        fs, fi, ifi, ifLast, fe, ife, ife2, feSeq, feSeqLast, 
                        fw, ifw, fwLast, cr, icr, gt, sss, isss, ss, asg, ias, 
                        ifst, estmt, iee, wi, iw, vdcl, pvdcl, exp, ie, elseq, 
                        nxt_, ixs, res_E, lst, nxt_E, temp_, flseq, temp_I, 
                        ifsqi, lseq, nxt_Ex, xxtemp1, temp2_, temp3_, temp4, 
                        exlsq, callStmt, prcd, svoci, temp, res_S, rprcd, rpvi, 
                        rpctemp, res_R, vrs, addExpr, pvexpr, pvi, stk, test, 
                        primeVars, sub, expr, sst, primedVars, localSub_, 
                        xlssi, xltemp1, temp1, temp2, temp3, res_X, sstsq, 
                        xprimedVars, localSub_X, res, xlsssqi, lsstsq, 
                        localSub, defSub, nxt, lsstqi, lsstemp, disjs, defs, 
                        str >>

PC17 == /\ pc = "PC17"
        /\ IF i \leq Len(ast.procs)
              THEN /\ IF i > 1
                         THEN /\ gtemp2' = gtemp2 \o <<"[]">>
                         ELSE /\ TRUE
                              /\ UNCHANGED gtemp2
                   /\ pc' = "PC18"
                   /\ UNCHANGED gtemp1
              ELSE /\ gtemp1' = gtemp1 \o <<gtemp2 \o <<"]">>>>
                   /\ pc' = "PC19"
                   /\ UNCHANGED gtemp2
        /\ UNCHANGED << i, j, gtemp3, gtemp4, result, rVal, pMap, prcdVars, 
                        procSeq, globalVars, nonGlobalVars, allVarSeq, 
                        localVars, stack, A, res_, ia, prcdr, ipr, proc, ip, 
                        lsseq, ilss, lstmt, whl, ls, ils, ilLast, ili, le, ile, 
                        fs, fi, ifi, ifLast, fe, ife, ife2, feSeq, feSeqLast, 
                        fw, ifw, fwLast, cr, icr, gt, sss, isss, ss, asg, ias, 
                        ifst, estmt, iee, wi, iw, vdcl, pvdcl, exp, ie, elseq, 
                        nxt_, ixs, res_E, lst, nxt_E, temp_, flseq, temp_I, 
                        ifsqi, lseq, nxt_Ex, xxtemp1, temp2_, temp3_, temp4, 
                        exlsq, callStmt, prcd, svoci, temp, res_S, rprcd, rpvi, 
                        rpctemp, res_R, vrs, addExpr, pvexpr, pvi, stk, test, 
                        primeVars, sub, expr, sst, primedVars, localSub_, 
                        xlssi, xltemp1, temp1, temp2, temp3, res_X, sstsq, 
                        xprimedVars, localSub_X, res, xlsssqi, lsstsq, 
                        localSub, defSub, nxt, lsstqi, lsstemp, disjs, defs, 
                        str >>

PC18 == /\ pc = "PC18"
        /\ gtemp2' = gtemp2 \o
                      <<"self", ast.procs[i].eqOrIn>> \o
                         ast.procs[i].id \o <<"->">> \o
                        Quote(ast.procs[i].body[1].label)
        /\ i' = i + 1
        /\ pc' = "PC17"
        /\ UNCHANGED << j, gtemp1, gtemp3, gtemp4, result, rVal, pMap, 
                        prcdVars, procSeq, globalVars, nonGlobalVars, 
                        allVarSeq, localVars, stack, A, res_, ia, prcdr, ipr, 
                        proc, ip, lsseq, ilss, lstmt, whl, ls, ils, ilLast, 
                        ili, le, ile, fs, fi, ifi, ifLast, fe, ife, ife2, 
                        feSeq, feSeqLast, fw, ifw, fwLast, cr, icr, gt, sss, 
                        isss, ss, asg, ias, ifst, estmt, iee, wi, iw, vdcl, 
                        pvdcl, exp, ie, elseq, nxt_, ixs, res_E, lst, nxt_E, 
                        temp_, flseq, temp_I, ifsqi, lseq, nxt_Ex, xxtemp1, 
                        temp2_, temp3_, temp4, exlsq, callStmt, prcd, svoci, 
                        temp, res_S, rprcd, rpvi, rpctemp, res_R, vrs, addExpr, 
                        pvexpr, pvi, stk, test, primeVars, sub, expr, sst, 
                        primedVars, localSub_, xlssi, xltemp1, temp1, temp2, 
                        temp3, res_X, sstsq, xprimedVars, localSub_X, res, 
                        xlsssqi, lsstsq, localSub, defSub, nxt, lsstqi, 
                        lsstemp, disjs, defs, str >>

PC19 == /\ pc = "PC19"
        /\ result' = result \o <<"Init", "==">> \o MakeConj(gtemp1)
        /\ IF ast.prcds # << >>
              THEN /\ i' = 1
                   /\ pc' = "PC20"
              ELSE /\ pc' = "PC29"
                   /\ UNCHANGED i
        /\ UNCHANGED << j, gtemp1, gtemp2, gtemp3, gtemp4, rVal, pMap, 
                        prcdVars, procSeq, globalVars, nonGlobalVars, 
                        allVarSeq, localVars, stack, A, res_, ia, prcdr, ipr, 
                        proc, ip, lsseq, ilss, lstmt, whl, ls, ils, ilLast, 
                        ili, le, ile, fs, fi, ifi, ifLast, fe, ife, ife2, 
                        feSeq, feSeqLast, fw, ifw, fwLast, cr, icr, gt, sss, 
                        isss, ss, asg, ias, ifst, estmt, iee, wi, iw, vdcl, 
                        pvdcl, exp, ie, elseq, nxt_, ixs, res_E, lst, nxt_E, 
                        temp_, flseq, temp_I, ifsqi, lseq, nxt_Ex, xxtemp1, 
                        temp2_, temp3_, temp4, exlsq, callStmt, prcd, svoci, 
                        temp, res_S, rprcd, rpvi, rpctemp, res_R, vrs, addExpr, 
                        pvexpr, pvi, stk, test, primeVars, sub, expr, sst, 
                        primedVars, localSub_, xlssi, xltemp1, temp1, temp2, 
                        temp3, res_X, sstsq, xprimedVars, localSub_X, res, 
                        xlsssqi, lsstsq, localSub, defSub, nxt, lsstqi, 
                        lsstemp, disjs, defs, str >>

PC20 == /\ pc = "PC20"
        /\ IF i \leq Len(ast.prcds)
              THEN /\ IF ast.type = "uniprocess"
                         THEN /\ localVars' = {}
                              /\ /\ defSub' = << >>
                                 /\ localSub' = << >>
                                 /\ lsstsq' = ast.prcds[i].body
                                 /\ nxt' = "Error"
                                 /\ stack' = << [ procedure |->  "XlateLabStmtSeq",
                                                  pc        |->  "PC21",
                                                  lsstqi    |->  lsstqi,
                                                  lsstemp   |->  lsstemp,
                                                  disjs     |->  disjs,
                                                  defs      |->  defs,
                                                  lsstsq    |->  lsstsq,
                                                  localSub  |->  localSub,
                                                  defSub    |->  defSub,
                                                  nxt       |->  nxt ] >>
                                              \o stack
                              /\ lsstqi' = 1
                              /\ lsstemp' = {}
                              /\ disjs' = << >>
                              /\ defs' = << >>
                              /\ pc' = "XLS1"
                         ELSE /\ localVars' = prcdVars \cup {"@pc@", "@stack@"}
                              /\ /\ defSub' = <<"(", "self", ")">>
                                 /\ localSub' = <<"[", "self", "]">>
                                 /\ lsstsq' = ast.prcds[i].body
                                 /\ nxt' = "Error"
                                 /\ stack' = << [ procedure |->  "XlateLabStmtSeq",
                                                  pc        |->  "PC21",
                                                  lsstqi    |->  lsstqi,
                                                  lsstemp   |->  lsstemp,
                                                  disjs     |->  disjs,
                                                  defs      |->  defs,
                                                  lsstsq    |->  lsstsq,
                                                  localSub  |->  localSub,
                                                  defSub    |->  defSub,
                                                  nxt       |->  nxt ] >>
                                              \o stack
                              /\ lsstqi' = 1
                              /\ lsstemp' = {}
                              /\ disjs' = << >>
                              /\ defs' = << >>
                              /\ pc' = "XLS1"
              ELSE /\ pc' = "PC29"
                   /\ UNCHANGED << localVars, stack, lsstsq, localSub, defSub, 
                                   nxt, lsstqi, lsstemp, disjs, defs >>
        /\ UNCHANGED << i, j, gtemp1, gtemp2, gtemp3, gtemp4, result, rVal, 
                        pMap, prcdVars, procSeq, globalVars, nonGlobalVars, 
                        allVarSeq, A, res_, ia, prcdr, ipr, proc, ip, lsseq, 
                        ilss, lstmt, whl, ls, ils, ilLast, ili, le, ile, fs, 
                        fi, ifi, ifLast, fe, ife, ife2, feSeq, feSeqLast, fw, 
                        ifw, fwLast, cr, icr, gt, sss, isss, ss, asg, ias, 
                        ifst, estmt, iee, wi, iw, vdcl, pvdcl, exp, ie, elseq, 
                        nxt_, ixs, res_E, lst, nxt_E, temp_, flseq, temp_I, 
                        ifsqi, lseq, nxt_Ex, xxtemp1, temp2_, temp3_, temp4, 
                        exlsq, callStmt, prcd, svoci, temp, res_S, rprcd, rpvi, 
                        rpctemp, res_R, vrs, addExpr, pvexpr, pvi, stk, test, 
                        primeVars, sub, expr, sst, primedVars, localSub_, 
                        xlssi, xltemp1, temp1, temp2, temp3, res_X, sstsq, 
                        xprimedVars, localSub_X, res, xlsssqi, str >>

PC21 == /\ pc = "PC21"
        /\ result' = result \o rVal.defs
                      \o <<ast.prcds[i].name>>
                      \o (IF ast.type = "uniprocess"
                            THEN << "==" >>
                            ELSE <<"(", "self", ")", "==">>)
                      \o rVal.disj
        /\ i' = i + 1
        /\ pc' = "PC20"
        /\ UNCHANGED << j, gtemp1, gtemp2, gtemp3, gtemp4, rVal, pMap, 
                        prcdVars, procSeq, globalVars, nonGlobalVars, 
                        allVarSeq, localVars, stack, A, res_, ia, prcdr, ipr, 
                        proc, ip, lsseq, ilss, lstmt, whl, ls, ils, ilLast, 
                        ili, le, ile, fs, fi, ifi, ifLast, fe, ife, ife2, 
                        feSeq, feSeqLast, fw, ifw, fwLast, cr, icr, gt, sss, 
                        isss, ss, asg, ias, ifst, estmt, iee, wi, iw, vdcl, 
                        pvdcl, exp, ie, elseq, nxt_, ixs, res_E, lst, nxt_E, 
                        temp_, flseq, temp_I, ifsqi, lseq, nxt_Ex, xxtemp1, 
                        temp2_, temp3_, temp4, exlsq, callStmt, prcd, svoci, 
                        temp, res_S, rprcd, rpvi, rpctemp, res_R, vrs, addExpr, 
                        pvexpr, pvi, stk, test, primeVars, sub, expr, sst, 
                        primedVars, localSub_, xlssi, xltemp1, temp1, temp2, 
                        temp3, res_X, sstsq, xprimedVars, localSub_X, res, 
                        xlsssqi, lsstsq, localSub, defSub, nxt, lsstqi, 
                        lsstemp, disjs, defs, str >>

PC29 == /\ pc = "PC29"
        /\ IF ast.type = "multiprocess"
              THEN /\ i' = 1
                   /\ pc' = "PC30"
              ELSE /\ pc' = "PC36"
                   /\ UNCHANGED i
        /\ UNCHANGED << j, gtemp1, gtemp2, gtemp3, gtemp4, result, rVal, pMap, 
                        prcdVars, procSeq, globalVars, nonGlobalVars, 
                        allVarSeq, localVars, stack, A, res_, ia, prcdr, ipr, 
                        proc, ip, lsseq, ilss, lstmt, whl, ls, ils, ilLast, 
                        ili, le, ile, fs, fi, ifi, ifLast, fe, ife, ife2, 
                        feSeq, feSeqLast, fw, ifw, fwLast, cr, icr, gt, sss, 
                        isss, ss, asg, ias, ifst, estmt, iee, wi, iw, vdcl, 
                        pvdcl, exp, ie, elseq, nxt_, ixs, res_E, lst, nxt_E, 
                        temp_, flseq, temp_I, ifsqi, lseq, nxt_Ex, xxtemp1, 
                        temp2_, temp3_, temp4, exlsq, callStmt, prcd, svoci, 
                        temp, res_S, rprcd, rpvi, rpctemp, res_R, vrs, addExpr, 
                        pvexpr, pvi, stk, test, primeVars, sub, expr, sst, 
                        primedVars, localSub_, xlssi, xltemp1, temp1, temp2, 
                        temp3, res_X, sstsq, xprimedVars, localSub_X, res, 
                        xlsssqi, lsstsq, localSub, defSub, nxt, lsstqi, 
                        lsstemp, disjs, defs, str >>

PC30 == /\ pc = "PC30"
        /\ IF i \leq Len(ast.procs)
              THEN /\ IF ast.procs[i].eqOrIn = "="
                         THEN /\ localVars' = {"@pc@", "@stack@"} \cup prcdVars
                              /\ /\ defSub' = << >>
                                 /\ localSub' = <<"[">> \o ast.procs[i].id \o <<"]">>
                                 /\ lsstsq' = ast.procs[i].body
                                 /\ nxt' = "Done"
                                 /\ stack' = << [ procedure |->  "XlateLabStmtSeq",
                                                  pc        |->  "PC31",
                                                  lsstqi    |->  lsstqi,
                                                  lsstemp   |->  lsstemp,
                                                  disjs     |->  disjs,
                                                  defs      |->  defs,
                                                  lsstsq    |->  lsstsq,
                                                  localSub  |->  localSub,
                                                  defSub    |->  defSub,
                                                  nxt       |->  nxt ] >>
                                              \o stack
                              /\ lsstqi' = 1
                              /\ lsstemp' = {}
                              /\ disjs' = << >>
                              /\ defs' = << >>
                              /\ pc' = "XLS1"
                         ELSE /\ localVars' = SeqToSet(procSeq[i].vars) \cup prcdVars \cup
                                                         {"@pc@", "@stack@"}
                              /\ /\ defSub' = <<"(", "self", ")">>
                                 /\ localSub' = <<"[", "self", "]">>
                                 /\ lsstsq' = ast.procs[i].body
                                 /\ nxt' = "Done"
                                 /\ stack' = << [ procedure |->  "XlateLabStmtSeq",
                                                  pc        |->  "PC31",
                                                  lsstqi    |->  lsstqi,
                                                  lsstemp   |->  lsstemp,
                                                  disjs     |->  disjs,
                                                  defs      |->  defs,
                                                  lsstsq    |->  lsstsq,
                                                  localSub  |->  localSub,
                                                  defSub    |->  defSub,
                                                  nxt       |->  nxt ] >>
                                              \o stack
                              /\ lsstqi' = 1
                              /\ lsstemp' = {}
                              /\ disjs' = << >>
                              /\ defs' = << >>
                              /\ pc' = "XLS1"
              ELSE /\ pc' = "PC33"
                   /\ UNCHANGED << localVars, stack, lsstsq, localSub, defSub, 
                                   nxt, lsstqi, lsstemp, disjs, defs >>
        /\ UNCHANGED << i, j, gtemp1, gtemp2, gtemp3, gtemp4, result, rVal, 
                        pMap, prcdVars, procSeq, globalVars, nonGlobalVars, 
                        allVarSeq, A, res_, ia, prcdr, ipr, proc, ip, lsseq, 
                        ilss, lstmt, whl, ls, ils, ilLast, ili, le, ile, fs, 
                        fi, ifi, ifLast, fe, ife, ife2, feSeq, feSeqLast, fw, 
                        ifw, fwLast, cr, icr, gt, sss, isss, ss, asg, ias, 
                        ifst, estmt, iee, wi, iw, vdcl, pvdcl, exp, ie, elseq, 
                        nxt_, ixs, res_E, lst, nxt_E, temp_, flseq, temp_I, 
                        ifsqi, lseq, nxt_Ex, xxtemp1, temp2_, temp3_, temp4, 
                        exlsq, callStmt, prcd, svoci, temp, res_S, rprcd, rpvi, 
                        rpctemp, res_R, vrs, addExpr, pvexpr, pvi, stk, test, 
                        primeVars, sub, expr, sst, primedVars, localSub_, 
                        xlssi, xltemp1, temp1, temp2, temp3, res_X, sstsq, 
                        xprimedVars, localSub_X, res, xlsssqi, str >>

PC31 == /\ pc = "PC31"
        /\ result' = result \o rVal.defs
        /\ IF ast.procs[i].eqOrIn = "="
              THEN /\ gtemp1' = <<ast.procs[i].name>>
              ELSE /\ gtemp1' = <<ast.procs[i].name, "(", "self", ")">>
        /\ pc' = "PC32"
        /\ UNCHANGED << i, j, gtemp2, gtemp3, gtemp4, rVal, pMap, prcdVars, 
                        procSeq, globalVars, nonGlobalVars, allVarSeq, 
                        localVars, stack, A, res_, ia, prcdr, ipr, proc, ip, 
                        lsseq, ilss, lstmt, whl, ls, ils, ilLast, ili, le, ile, 
                        fs, fi, ifi, ifLast, fe, ife, ife2, feSeq, feSeqLast, 
                        fw, ifw, fwLast, cr, icr, gt, sss, isss, ss, asg, ias, 
                        ifst, estmt, iee, wi, iw, vdcl, pvdcl, exp, ie, elseq, 
                        nxt_, ixs, res_E, lst, nxt_E, temp_, flseq, temp_I, 
                        ifsqi, lseq, nxt_Ex, xxtemp1, temp2_, temp3_, temp4, 
                        exlsq, callStmt, prcd, svoci, temp, res_S, rprcd, rpvi, 
                        rpctemp, res_R, vrs, addExpr, pvexpr, pvi, stk, test, 
                        primeVars, sub, expr, sst, primedVars, localSub_, 
                        xlssi, xltemp1, temp1, temp2, temp3, res_X, sstsq, 
                        xprimedVars, localSub_X, res, xlsssqi, lsstsq, 
                        localSub, defSub, nxt, lsstqi, lsstemp, disjs, defs, 
                        str >>

PC32 == /\ pc = "PC32"
        /\ result' = result \o gtemp1 \o <<"==">> \o rVal.disj
        /\ i' = i + 1
        /\ pc' = "PC30"
        /\ UNCHANGED << j, gtemp1, gtemp2, gtemp3, gtemp4, rVal, pMap, 
                        prcdVars, procSeq, globalVars, nonGlobalVars, 
                        allVarSeq, localVars, stack, A, res_, ia, prcdr, ipr, 
                        proc, ip, lsseq, ilss, lstmt, whl, ls, ils, ilLast, 
                        ili, le, ile, fs, fi, ifi, ifLast, fe, ife, ife2, 
                        feSeq, feSeqLast, fw, ifw, fwLast, cr, icr, gt, sss, 
                        isss, ss, asg, ias, ifst, estmt, iee, wi, iw, vdcl, 
                        pvdcl, exp, ie, elseq, nxt_, ixs, res_E, lst, nxt_E, 
                        temp_, flseq, temp_I, ifsqi, lseq, nxt_Ex, xxtemp1, 
                        temp2_, temp3_, temp4, exlsq, callStmt, prcd, svoci, 
                        temp, res_S, rprcd, rpvi, rpctemp, res_R, vrs, addExpr, 
                        pvexpr, pvi, stk, test, primeVars, sub, expr, sst, 
                        primedVars, localSub_, xlssi, xltemp1, temp1, temp2, 
                        temp3, res_X, sstsq, xprimedVars, localSub_X, res, 
                        xlsssqi, lsstsq, localSub, defSub, nxt, lsstqi, 
                        lsstemp, disjs, defs, str >>

PC33 == /\ pc = "PC33"
        /\ result' = result \o <<"Next", "==">> \o
                      MakeDisj([x \in 1..Len(ast.procs) |->
                                  IF ast.procs[x].eqOrIn = "="
                                      THEN << ast.procs[x].name >>
                                      ELSE <<"(", "\\E", "self" , "\\in">> \o
                                             ast.procs[x].id \o
                                           <<":", ast.procs[x].name, "(",
                                             "self", ")", ")">>
                                 ])
        /\ pc' = "PC34"
        /\ UNCHANGED << i, j, gtemp1, gtemp2, gtemp3, gtemp4, rVal, pMap, 
                        prcdVars, procSeq, globalVars, nonGlobalVars, 
                        allVarSeq, localVars, stack, A, res_, ia, prcdr, ipr, 
                        proc, ip, lsseq, ilss, lstmt, whl, ls, ils, ilLast, 
                        ili, le, ile, fs, fi, ifi, ifLast, fe, ife, ife2, 
                        feSeq, feSeqLast, fw, ifw, fwLast, cr, icr, gt, sss, 
                        isss, ss, asg, ias, ifst, estmt, iee, wi, iw, vdcl, 
                        pvdcl, exp, ie, elseq, nxt_, ixs, res_E, lst, nxt_E, 
                        temp_, flseq, temp_I, ifsqi, lseq, nxt_Ex, xxtemp1, 
                        temp2_, temp3_, temp4, exlsq, callStmt, prcd, svoci, 
                        temp, res_S, rprcd, rpvi, rpctemp, res_R, vrs, addExpr, 
                        pvexpr, pvi, stk, test, primeVars, sub, expr, sst, 
                        primedVars, localSub_, xlssi, xltemp1, temp1, temp2, 
                        temp3, res_X, sstsq, xprimedVars, localSub_X, res, 
                        xlsssqi, lsstsq, localSub, defSub, nxt, lsstqi, 
                        lsstemp, disjs, defs, str >>

PC34 == /\ pc = "PC34"
        /\ IF ast.prcds # << >>
              THEN /\ result' = result \o <<"\\/", "(", "\\E", "self", "\\in",
                                            "ProcSet", ":">> \o
                                  MakeDisj([x \in 1..Len(ast.prcds) |->
                                              << ast.prcds[x].name, "(", "self", ")">>
                                             ]) \o <<")">>
              ELSE /\ TRUE
                   /\ UNCHANGED result
        /\ pc' = "PC35"
        /\ UNCHANGED << i, j, gtemp1, gtemp2, gtemp3, gtemp4, rVal, pMap, 
                        prcdVars, procSeq, globalVars, nonGlobalVars, 
                        allVarSeq, localVars, stack, A, res_, ia, prcdr, ipr, 
                        proc, ip, lsseq, ilss, lstmt, whl, ls, ils, ilLast, 
                        ili, le, ile, fs, fi, ifi, ifLast, fe, ife, ife2, 
                        feSeq, feSeqLast, fw, ifw, fwLast, cr, icr, gt, sss, 
                        isss, ss, asg, ias, ifst, estmt, iee, wi, iw, vdcl, 
                        pvdcl, exp, ie, elseq, nxt_, ixs, res_E, lst, nxt_E, 
                        temp_, flseq, temp_I, ifsqi, lseq, nxt_Ex, xxtemp1, 
                        temp2_, temp3_, temp4, exlsq, callStmt, prcd, svoci, 
                        temp, res_S, rprcd, rpvi, rpctemp, res_R, vrs, addExpr, 
                        pvexpr, pvi, stk, test, primeVars, sub, expr, sst, 
                        primedVars, localSub_, xlssi, xltemp1, temp1, temp2, 
                        temp3, res_X, sstsq, xprimedVars, localSub_X, res, 
                        xlsssqi, lsstsq, localSub, defSub, nxt, lsstqi, 
                        lsstemp, disjs, defs, str >>

PC35 == /\ pc = "PC35"
        /\ result' = result \o
                       <<"\\/", "(", "(", "\\A", "self", "\\in", "ProcSet", ":",
                          "@pc@", "[", "self", "]", "=">> \o Quote("Done") \o
                       <<")", "/\\" , "(", "UNCHANGED", "vars", ")", ")" >>
        /\ pc' = "PC36"
        /\ UNCHANGED << i, j, gtemp1, gtemp2, gtemp3, gtemp4, rVal, pMap, 
                        prcdVars, procSeq, globalVars, nonGlobalVars, 
                        allVarSeq, localVars, stack, A, res_, ia, prcdr, ipr, 
                        proc, ip, lsseq, ilss, lstmt, whl, ls, ils, ilLast, 
                        ili, le, ile, fs, fi, ifi, ifLast, fe, ife, ife2, 
                        feSeq, feSeqLast, fw, ifw, fwLast, cr, icr, gt, sss, 
                        isss, ss, asg, ias, ifst, estmt, iee, wi, iw, vdcl, 
                        pvdcl, exp, ie, elseq, nxt_, ixs, res_E, lst, nxt_E, 
                        temp_, flseq, temp_I, ifsqi, lseq, nxt_Ex, xxtemp1, 
                        temp2_, temp3_, temp4, exlsq, callStmt, prcd, svoci, 
                        temp, res_S, rprcd, rpvi, rpctemp, res_R, vrs, addExpr, 
                        pvexpr, pvi, stk, test, primeVars, sub, expr, sst, 
                        primedVars, localSub_, xlssi, xltemp1, temp1, temp2, 
                        temp3, res_X, sstsq, xprimedVars, localSub_X, res, 
                        xlsssqi, lsstsq, localSub, defSub, nxt, lsstqi, 
                        lsstemp, disjs, defs, str >>

PC36 == /\ pc = "PC36"
        /\ IF ast.type = "uniprocess"
              THEN /\ localVars' = {}
                   /\ /\ defSub' = << >>
                      /\ localSub' = << >>
                      /\ lsstsq' = ast.body
                      /\ nxt' = "Done"
                      /\ stack' = << [ procedure |->  "XlateLabStmtSeq",
                                       pc        |->  "PC41",
                                       lsstqi    |->  lsstqi,
                                       lsstemp   |->  lsstemp,
                                       disjs     |->  disjs,
                                       defs      |->  defs,
                                       lsstsq    |->  lsstsq,
                                       localSub  |->  localSub,
                                       defSub    |->  defSub,
                                       nxt       |->  nxt ] >>
                                   \o stack
                   /\ lsstqi' = 1
                   /\ lsstemp' = {}
                   /\ disjs' = << >>
                   /\ defs' = << >>
                   /\ pc' = "XLS1"
              ELSE /\ pc' = "PC49"
                   /\ UNCHANGED << localVars, stack, lsstsq, localSub, defSub, 
                                   nxt, lsstqi, lsstemp, disjs, defs >>
        /\ UNCHANGED << i, j, gtemp1, gtemp2, gtemp3, gtemp4, result, rVal, 
                        pMap, prcdVars, procSeq, globalVars, nonGlobalVars, 
                        allVarSeq, A, res_, ia, prcdr, ipr, proc, ip, lsseq, 
                        ilss, lstmt, whl, ls, ils, ilLast, ili, le, ile, fs, 
                        fi, ifi, ifLast, fe, ife, ife2, feSeq, feSeqLast, fw, 
                        ifw, fwLast, cr, icr, gt, sss, isss, ss, asg, ias, 
                        ifst, estmt, iee, wi, iw, vdcl, pvdcl, exp, ie, elseq, 
                        nxt_, ixs, res_E, lst, nxt_E, temp_, flseq, temp_I, 
                        ifsqi, lseq, nxt_Ex, xxtemp1, temp2_, temp3_, temp4, 
                        exlsq, callStmt, prcd, svoci, temp, res_S, rprcd, rpvi, 
                        rpctemp, res_R, vrs, addExpr, pvexpr, pvi, stk, test, 
                        primeVars, sub, expr, sst, primedVars, localSub_, 
                        xlssi, xltemp1, temp1, temp2, temp3, res_X, sstsq, 
                        xprimedVars, localSub_X, res, xlsssqi, str >>

PC41 == /\ pc = "PC41"
        /\ result' = result \o rVal.defs \o <<"Next", "==" >> \o rVal.disj \o
                     (IF ast.prcds # << >>
                        THEN <<"\\/">> \o
                             MakeDisj([x \in 1..Len(ast.prcds) |->
                                     << ast.prcds[x].name>> ])
                        ELSE << >>) \o
                       <<"\\/", "(", "(", "@pc@", "=">> \o Quote("Done") \o
                       << ")", "/\\", "UNCHANGED", "vars", ")" >>
        /\ pc' = "PC49"
        /\ UNCHANGED << i, j, gtemp1, gtemp2, gtemp3, gtemp4, rVal, pMap, 
                        prcdVars, procSeq, globalVars, nonGlobalVars, 
                        allVarSeq, localVars, stack, A, res_, ia, prcdr, ipr, 
                        proc, ip, lsseq, ilss, lstmt, whl, ls, ils, ilLast, 
                        ili, le, ile, fs, fi, ifi, ifLast, fe, ife, ife2, 
                        feSeq, feSeqLast, fw, ifw, fwLast, cr, icr, gt, sss, 
                        isss, ss, asg, ias, ifst, estmt, iee, wi, iw, vdcl, 
                        pvdcl, exp, ie, elseq, nxt_, ixs, res_E, lst, nxt_E, 
                        temp_, flseq, temp_I, ifsqi, lseq, nxt_Ex, xxtemp1, 
                        temp2_, temp3_, temp4, exlsq, callStmt, prcd, svoci, 
                        temp, res_S, rprcd, rpvi, rpctemp, res_R, vrs, addExpr, 
                        pvexpr, pvi, stk, test, primeVars, sub, expr, sst, 
                        primedVars, localSub_, xlssi, xltemp1, temp1, temp2, 
                        temp3, res_X, sstsq, xprimedVars, localSub_X, res, 
                        xlsssqi, lsstsq, localSub, defSub, nxt, lsstqi, 
                        lsstemp, disjs, defs, str >>

PC49 == /\ pc = "PC49"
        /\ IF fairness = ""
              THEN /\ gtemp1' = << >>
                   /\ pc' = "PC52"
              ELSE /\ gtemp1' = << "/\\" >>
                   /\ pc' = "PC50"
        /\ UNCHANGED << i, j, gtemp2, gtemp3, gtemp4, result, rVal, pMap, 
                        prcdVars, procSeq, globalVars, nonGlobalVars, 
                        allVarSeq, localVars, stack, A, res_, ia, prcdr, ipr, 
                        proc, ip, lsseq, ilss, lstmt, whl, ls, ils, ilLast, 
                        ili, le, ile, fs, fi, ifi, ifLast, fe, ife, ife2, 
                        feSeq, feSeqLast, fw, ifw, fwLast, cr, icr, gt, sss, 
                        isss, ss, asg, ias, ifst, estmt, iee, wi, iw, vdcl, 
                        pvdcl, exp, ie, elseq, nxt_, ixs, res_E, lst, nxt_E, 
                        temp_, flseq, temp_I, ifsqi, lseq, nxt_Ex, xxtemp1, 
                        temp2_, temp3_, temp4, exlsq, callStmt, prcd, svoci, 
                        temp, res_S, rprcd, rpvi, rpctemp, res_R, vrs, addExpr, 
                        pvexpr, pvi, stk, test, primeVars, sub, expr, sst, 
                        primedVars, localSub_, xlssi, xltemp1, temp1, temp2, 
                        temp3, res_X, sstsq, xprimedVars, localSub_X, res, 
                        xlsssqi, lsstsq, localSub, defSub, nxt, lsstqi, 
                        lsstemp, disjs, defs, str >>

PC50 == /\ pc = "PC50"
        /\ IF (fairness \in {"wf", "sf"}) /\ (ast.type = "multiprocess")
              THEN /\ i' = 1
                   /\ gtemp2' = << (IF fairness = "wf"
                                    THEN "WF_" ELSE "SF_") \o "vars", "(">>
                   /\ gtemp3' = << >>
                   /\ pc' = "PC51"
                   /\ UNCHANGED gtemp1
              ELSE /\ gtemp1' = gtemp1 \o <<"WF_", "vars", "(", "Next", ")">>
                   /\ pc' = "PC52"
                   /\ UNCHANGED << i, gtemp2, gtemp3 >>
        /\ UNCHANGED << j, gtemp4, result, rVal, pMap, prcdVars, procSeq, 
                        globalVars, nonGlobalVars, allVarSeq, localVars, stack, 
                        A, res_, ia, prcdr, ipr, proc, ip, lsseq, ilss, lstmt, 
                        whl, ls, ils, ilLast, ili, le, ile, fs, fi, ifi, 
                        ifLast, fe, ife, ife2, feSeq, feSeqLast, fw, ifw, 
                        fwLast, cr, icr, gt, sss, isss, ss, asg, ias, ifst, 
                        estmt, iee, wi, iw, vdcl, pvdcl, exp, ie, elseq, nxt_, 
                        ixs, res_E, lst, nxt_E, temp_, flseq, temp_I, ifsqi, 
                        lseq, nxt_Ex, xxtemp1, temp2_, temp3_, temp4, exlsq, 
                        callStmt, prcd, svoci, temp, res_S, rprcd, rpvi, 
                        rpctemp, res_R, vrs, addExpr, pvexpr, pvi, stk, test, 
                        primeVars, sub, expr, sst, primedVars, localSub_, 
                        xlssi, xltemp1, temp1, temp2, temp3, res_X, sstsq, 
                        xprimedVars, localSub_X, res, xlsssqi, lsstsq, 
                        localSub, defSub, nxt, lsstqi, lsstemp, disjs, defs, 
                        str >>

PC51 == /\ pc = "PC51"
        /\ IF i \leq Len(ast.procs)
              THEN /\ IF ast.procs[i].eqOrIn = "="
                         THEN /\ gtemp3' = gtemp3 \o
                                            << gtemp2 \o
                                                  <<ast.procs[i].name, ")">> >>
                         ELSE /\ gtemp3' = gtemp3 \o
                                           <<  << "\\A", "self", "\\in">> \o
                                              ast.procs[i].id \o << ":" >> \o gtemp2 \o
                                           <<ast.procs[i].name, "(", "self", ")", ")">> >>
                   /\ i' = i + 1
                   /\ pc' = "PC51"
                   /\ UNCHANGED gtemp4
              ELSE /\ gtemp4' = << >>
                   /\ i' = 1
                   /\ pc' = "PC59"
                   /\ UNCHANGED gtemp3
        /\ UNCHANGED << j, gtemp1, gtemp2, result, rVal, pMap, prcdVars, 
                        procSeq, globalVars, nonGlobalVars, allVarSeq, 
                        localVars, stack, A, res_, ia, prcdr, ipr, proc, ip, 
                        lsseq, ilss, lstmt, whl, ls, ils, ilLast, ili, le, ile, 
                        fs, fi, ifi, ifLast, fe, ife, ife2, feSeq, feSeqLast, 
                        fw, ifw, fwLast, cr, icr, gt, sss, isss, ss, asg, ias, 
                        ifst, estmt, iee, wi, iw, vdcl, pvdcl, exp, ie, elseq, 
                        nxt_, ixs, res_E, lst, nxt_E, temp_, flseq, temp_I, 
                        ifsqi, lseq, nxt_Ex, xxtemp1, temp2_, temp3_, temp4, 
                        exlsq, callStmt, prcd, svoci, temp, res_S, rprcd, rpvi, 
                        rpctemp, res_R, vrs, addExpr, pvexpr, pvi, stk, test, 
                        primeVars, sub, expr, sst, primedVars, localSub_, 
                        xlssi, xltemp1, temp1, temp2, temp3, res_X, sstsq, 
                        xprimedVars, localSub_X, res, xlsssqi, lsstsq, 
                        localSub, defSub, nxt, lsstqi, lsstemp, disjs, defs, 
                        str >>

PC59 == /\ pc = "PC59"
        /\ IF i \leq Len(ast.prcds)
              THEN /\ gtemp4' = gtemp4 \o
                                 << gtemp2 \o
                                     <<ast.prcds[i].name, "(", "self",
                                         ")", ")">> >>
                   /\ i' = i + 1
                   /\ pc' = "PC59"
                   /\ UNCHANGED << gtemp1, gtemp3 >>
              ELSE /\ gtemp3' = gtemp3 \o
                                 <<  << "\\A", "self", "\\in", "ProcSet",
                                        ":" >> \o
                                       MakeConj(gtemp4) >>
                   /\ gtemp1' = gtemp1 \o MakeConj(gtemp3')
                   /\ pc' = "PC52"
                   /\ UNCHANGED << i, gtemp4 >>
        /\ UNCHANGED << j, gtemp2, result, rVal, pMap, prcdVars, procSeq, 
                        globalVars, nonGlobalVars, allVarSeq, localVars, stack, 
                        A, res_, ia, prcdr, ipr, proc, ip, lsseq, ilss, lstmt, 
                        whl, ls, ils, ilLast, ili, le, ile, fs, fi, ifi, 
                        ifLast, fe, ife, ife2, feSeq, feSeqLast, fw, ifw, 
                        fwLast, cr, icr, gt, sss, isss, ss, asg, ias, ifst, 
                        estmt, iee, wi, iw, vdcl, pvdcl, exp, ie, elseq, nxt_, 
                        ixs, res_E, lst, nxt_E, temp_, flseq, temp_I, ifsqi, 
                        lseq, nxt_Ex, xxtemp1, temp2_, temp3_, temp4, exlsq, 
                        callStmt, prcd, svoci, temp, res_S, rprcd, rpvi, 
                        rpctemp, res_R, vrs, addExpr, pvexpr, pvi, stk, test, 
                        primeVars, sub, expr, sst, primedVars, localSub_, 
                        xlssi, xltemp1, temp1, temp2, temp3, res_X, sstsq, 
                        xprimedVars, localSub_X, res, xlsssqi, lsstsq, 
                        localSub, defSub, nxt, lsstqi, lsstemp, disjs, defs, 
                        str >>

PC52 == /\ pc = "PC52"
        /\ result' = result \o
                      <<"Spec", "==", "Init", "/\\", "[]", "[", "Next", "]_",
                        "vars">> \o gtemp1
        /\ pc' = "PC53"
        /\ UNCHANGED << i, j, gtemp1, gtemp2, gtemp3, gtemp4, rVal, pMap, 
                        prcdVars, procSeq, globalVars, nonGlobalVars, 
                        allVarSeq, localVars, stack, A, res_, ia, prcdr, ipr, 
                        proc, ip, lsseq, ilss, lstmt, whl, ls, ils, ilLast, 
                        ili, le, ile, fs, fi, ifi, ifLast, fe, ife, ife2, 
                        feSeq, feSeqLast, fw, ifw, fwLast, cr, icr, gt, sss, 
                        isss, ss, asg, ias, ifst, estmt, iee, wi, iw, vdcl, 
                        pvdcl, exp, ie, elseq, nxt_, ixs, res_E, lst, nxt_E, 
                        temp_, flseq, temp_I, ifsqi, lseq, nxt_Ex, xxtemp1, 
                        temp2_, temp3_, temp4, exlsq, callStmt, prcd, svoci, 
                        temp, res_S, rprcd, rpvi, rpctemp, res_R, vrs, addExpr, 
                        pvexpr, pvi, stk, test, primeVars, sub, expr, sst, 
                        primedVars, localSub_, xlssi, xltemp1, temp1, temp2, 
                        temp3, res_X, sstsq, xprimedVars, localSub_X, res, 
                        xlsssqi, lsstsq, localSub, defSub, nxt, lsstqi, 
                        lsstemp, disjs, defs, str >>

PC53 == /\ pc = "PC53"
        /\ IF ast.type = "uniprocess"
              THEN /\ result' = result \o <<"Termination", "==", "<>", "(", "@pc@", "=">>
                                  \o Quote("Done") \o <<")">>
              ELSE /\ result' = result \o
                                  <<"Termination", "==", "<>", "(", "\\A", "self",
                                     "\\in", "ProcSet", ":", "@pc@", "[", "self", "]",
                                    "=">>
                                  \o Quote("Done") \o <<")">>
        /\ pc' = "PC999"
        /\ UNCHANGED << i, j, gtemp1, gtemp2, gtemp3, gtemp4, rVal, pMap, 
                        prcdVars, procSeq, globalVars, nonGlobalVars, 
                        allVarSeq, localVars, stack, A, res_, ia, prcdr, ipr, 
                        proc, ip, lsseq, ilss, lstmt, whl, ls, ils, ilLast, 
                        ili, le, ile, fs, fi, ifi, ifLast, fe, ife, ife2, 
                        feSeq, feSeqLast, fw, ifw, fwLast, cr, icr, gt, sss, 
                        isss, ss, asg, ias, ifst, estmt, iee, wi, iw, vdcl, 
                        pvdcl, exp, ie, elseq, nxt_, ixs, res_E, lst, nxt_E, 
                        temp_, flseq, temp_I, ifsqi, lseq, nxt_Ex, xxtemp1, 
                        temp2_, temp3_, temp4, exlsq, callStmt, prcd, svoci, 
                        temp, res_S, rprcd, rpvi, rpctemp, res_R, vrs, addExpr, 
                        pvexpr, pvi, stk, test, primeVars, sub, expr, sst, 
                        primedVars, localSub_, xlssi, xltemp1, temp1, temp2, 
                        temp3, res_X, sstsq, xprimedVars, localSub_X, res, 
                        xlsssqi, lsstsq, localSub, defSub, nxt, lsstqi, 
                        lsstemp, disjs, defs, str >>

PC999 == /\ pc = "PC999"
         /\ PrintT(FixPCandStack(result))
         /\ pc' = "Done"
         /\ UNCHANGED << i, j, gtemp1, gtemp2, gtemp3, gtemp4, result, rVal, 
                         pMap, prcdVars, procSeq, globalVars, nonGlobalVars, 
                         allVarSeq, localVars, stack, A, res_, ia, prcdr, ipr, 
                         proc, ip, lsseq, ilss, lstmt, whl, ls, ils, ilLast, 
                         ili, le, ile, fs, fi, ifi, ifLast, fe, ife, ife2, 
                         feSeq, feSeqLast, fw, ifw, fwLast, cr, icr, gt, sss, 
                         isss, ss, asg, ias, ifst, estmt, iee, wi, iw, vdcl, 
                         pvdcl, exp, ie, elseq, nxt_, ixs, res_E, lst, nxt_E, 
                         temp_, flseq, temp_I, ifsqi, lseq, nxt_Ex, xxtemp1, 
                         temp2_, temp3_, temp4, exlsq, callStmt, prcd, svoci, 
                         temp, res_S, rprcd, rpvi, rpctemp, res_R, vrs, 
                         addExpr, pvexpr, pvi, stk, test, primeVars, sub, expr, 
                         sst, primedVars, localSub_, xlssi, xltemp1, temp1, 
                         temp2, temp3, res_X, sstsq, xprimedVars, localSub_X, 
                         res, xlsssqi, lsstsq, localSub, defSub, nxt, lsstqi, 
                         lsstemp, disjs, defs, str >>

Next == IsAlgorithm \/ IsProcedure \/ IsProcess \/ IsLabeledStmtSeq
           \/ IsLabeledStmt \/ IsWhile \/ IsLabelSeq \/ IsLabelIf
           \/ IsLabelEither \/ IsFinalStmt \/ IsFinalIf \/ IsFinalEither
           \/ IsFinalWith \/ IsCallOrReturn \/ IsGoto \/ IsSimpleStmtSeq
           \/ IsSimpleStmt \/ IsAssign \/ IsIf \/ IsEither \/ IsWith \/ IsVarDecl
           \/ IsPVarDecl \/ IsExpr \/ ExpandSeq \/ ExpandLStmt \/ IsFinalSeq
           \/ ExpandLSeq \/ SetPrcdVarsOnCall \/ RestorePrcdVarsFrom
           \/ ProcessVars \/ PrimeAndAddSub \/ XlateSStmt \/ XlateSStmtSeq
           \/ XlateLabStmtSeq \/ Error \/ PC1 \/ PC2 \/ PC3 \/ PC4 \/ PC5 \/ PC6
           \/ PC7 \/ PC8 \/ PC9 \/ PC10 \/ PC11 \/ PC12 \/ PC13 \/ PC14 \/ PC15
           \/ PC16 \/ PC17 \/ PC18 \/ PC19 \/ PC20 \/ PC21 \/ PC29 \/ PC30
           \/ PC31 \/ PC32 \/ PC33 \/ PC34 \/ PC35 \/ PC36 \/ PC41 \/ PC49
           \/ PC50 \/ PC51 \/ PC59 \/ PC52 \/ PC53 \/ PC999
           \/ (* Disjunct to prevent deadlock on termination *)
              (pc = "Done" /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION
=============================================================================
