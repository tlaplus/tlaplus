# PaxosMadeSimple
A TLA+ formalization of the algorithm described in "Paxos Made Simple"
There are two specification: SimplePaxos.tla and PaxosMadeSimple.tla.
The second one is a modification of a specification found here: 
research.microsoft.com/en-us/um/people/lamport/tla/PConProof.tla

Each spec can be model-checked by opening it in the TLA toolbox and instructing the toolbox to import the model named "Model_1", then running TLC.

Some people think that there is a problem in the algorithm as described in the paper:
http://stackoverflow.com/questions/29880949/contradiction-in-lamports-paxos-made-simple-paper.
However the accepted answer is plain wrong; there is no problem, as can be checked with TLC.
