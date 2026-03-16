---------------------- MODULE Playground ----------------------
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Node,
          SlushLoopProcess,
          SlushQueryProcess,
          HostMapping,
          SlushIterationCount,
          SampleSetSize,
          PickFlipThreshold

ASSUME /\ Cardinality(Node) = Cardinality(SlushLoopProcess)
       /\ Cardinality(Node) = Cardinality(SlushQueryProcess)
       /\ SlushIterationCount \in Nat
       /\ SampleSetSize \in Nat
       /\ PickFlipThreshold \in Nat

ASSUME HostMappingType == /\ Cardinality(Node) = Cardinality(HostMapping)
                          /\ \A mapping \in HostMapping:
                               /\ Cardinality(mapping) = 3
                               /\ \E e \in mapping: e \in Node
                               /\ \E e \in mapping: e \in SlushLoopProcess
                               /\ \E e \in mapping: e \in SlushQueryProcess

==============================================================
