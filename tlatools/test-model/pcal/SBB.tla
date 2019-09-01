------------------------------- MODULE SBB -------------------------------

EXTENDS Naturals, Sequences, TLC


(**************************************************************************)
(* The StringBuilder bug.                                                 *)
(**************************************************************************)

CONSTANT Pid        \* set of process ids
NoPid == CHOOSE p : p \notin Pid

CONSTANT Buf        \* set of buffers
NoBuf == CHOOSE b : b \notin Buf



(*--algorithm sbb

    variables
        sb = [ owner |-> NoPid, buf |-> CHOOSE b \in Buf : TRUE ];
        availablebuffers = Buf \ {sb.buf};
        publishedbuffers = {};


    process work \in Pid
        variable
            buf = NoBuf;
	    op = {};
    begin
      Loop:
        while TRUE do
            with lop \in { "Publish", "Modify" } do
                op := lop;
            end with;

	    if (op = "Publish") then
                buf := sb.buf;		    
              Publish1:
                if sb.owner # self /\ sb.owner # NoPid then
                    buf := CHOOSE b \in availablebuffers : TRUE;
                    availablebuffers := availablebuffers \ {buf};
                else
                  Publish2:
                    sb.owner := NoPid;
                end if;
              Publish3:
                publishedbuffers := publishedbuffers \cup {buf};


            else
                buf := sb.buf;
              Modify1:
                if sb.owner # self then
                    buf := CHOOSE b \in availablebuffers : TRUE;
                    availablebuffers := availablebuffers \ {buf};
                end if;
              Modify2:
              \* assert buf \notin publishedbuffers;
                sb.owner := self;
              Modify3:
                sb.buf := buf;
            end if
        end while;
    end process;
end algorithm

*)    


\* BEGIN TRANSLATION PC-533b33c7746a172d777f80327880e4a57ff1d51f621fa5b1f725a48bfe250b61
VARIABLES sb, availablebuffers, publishedbuffers, pc, buf, op

vars == << sb, availablebuffers, publishedbuffers, pc, buf, op >>

ProcSet == (Pid)

Init == (* Global variables *)
        /\ sb = [ owner |-> NoPid, buf |-> CHOOSE b \in Buf : TRUE ]
        /\ availablebuffers = Buf \ {sb.buf}
        /\ publishedbuffers = {}
        (* Process work *)
        /\ buf = [self \in Pid |-> NoBuf]
        /\ op = [self \in Pid |-> {}]
        /\ pc = [self \in ProcSet |-> "Loop"]

Loop(self) == /\ pc[self] = "Loop"
              /\ \E lop \in { "Publish", "Modify" }:
                   op' = [op EXCEPT ![self] = lop]
              /\ IF (op'[self] = "Publish")
                    THEN /\ buf' = [buf EXCEPT ![self] = sb.buf]
                         /\ pc' = [pc EXCEPT ![self] = "Publish1"]
                    ELSE /\ buf' = [buf EXCEPT ![self] = sb.buf]
                         /\ pc' = [pc EXCEPT ![self] = "Modify1"]
              /\ UNCHANGED << sb, availablebuffers, publishedbuffers >>

Publish1(self) == /\ pc[self] = "Publish1"
                  /\ IF sb.owner # self /\ sb.owner # NoPid
                        THEN /\ buf' = [buf EXCEPT ![self] = CHOOSE b \in availablebuffers : TRUE]
                             /\ availablebuffers' = availablebuffers \ {buf'[self]}
                             /\ pc' = [pc EXCEPT ![self] = "Publish3"]
                        ELSE /\ pc' = [pc EXCEPT ![self] = "Publish2"]
                             /\ UNCHANGED << availablebuffers, buf >>
                  /\ UNCHANGED << sb, publishedbuffers, op >>

Publish2(self) == /\ pc[self] = "Publish2"
                  /\ sb' = [sb EXCEPT !.owner = NoPid]
                  /\ pc' = [pc EXCEPT ![self] = "Publish3"]
                  /\ UNCHANGED << availablebuffers, publishedbuffers, buf, op >>

Publish3(self) == /\ pc[self] = "Publish3"
                  /\ publishedbuffers' = (publishedbuffers \cup {buf[self]})
                  /\ pc' = [pc EXCEPT ![self] = "Loop"]
                  /\ UNCHANGED << sb, availablebuffers, buf, op >>

Modify1(self) == /\ pc[self] = "Modify1"
                 /\ IF sb.owner # self
                       THEN /\ buf' = [buf EXCEPT ![self] = CHOOSE b \in availablebuffers : TRUE]
                            /\ availablebuffers' = availablebuffers \ {buf'[self]}
                       ELSE /\ TRUE
                            /\ UNCHANGED << availablebuffers, buf >>
                 /\ pc' = [pc EXCEPT ![self] = "Modify2"]
                 /\ UNCHANGED << sb, publishedbuffers, op >>

Modify2(self) == /\ pc[self] = "Modify2"
                 /\ sb' = [sb EXCEPT !.owner = self]
                 /\ pc' = [pc EXCEPT ![self] = "Modify3"]
                 /\ UNCHANGED << availablebuffers, publishedbuffers, buf, op >>

Modify3(self) == /\ pc[self] = "Modify3"
                 /\ sb' = [sb EXCEPT !.buf = buf[self]]
                 /\ pc' = [pc EXCEPT ![self] = "Loop"]
                 /\ UNCHANGED << availablebuffers, publishedbuffers, buf, op >>

work(self) == Loop(self) \/ Publish1(self) \/ Publish2(self)
                 \/ Publish3(self) \/ Modify1(self) \/ Modify2(self)
                 \/ Modify3(self)

Next == (\E self \in Pid: work(self))

Spec == Init /\ [][Next]_vars

\* END TRANSLATION TPC-4eab0d144e170064e19bed8461e1a580302cc1181d4c4c81d6f234e83535d765


Immutability ==
    \A self \in ProcSet :
    pc[self] = "Modify2" => buf[self] \notin publishedbuffers

Constraint ==
    availablebuffers # {}


============================================================================
