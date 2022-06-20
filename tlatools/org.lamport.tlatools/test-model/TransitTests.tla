------------- CONFIG TransitTests ---------

CONSTANT ModelValueConstant = ModelValue
===================

----------------------------- MODULE TransitTests -----------------------------
EXTENDS Transit, Integers, Sequences, TLC, TLCExt

CONSTANT ModelValueConstant

\* Helper function which asserts round trip data
AssertSerDes(v, expected) ==
    LET output == v
    IN
       /\ TransitSerialize("target/transit/test.transit", output)
       /\ expected = TransitDeserialize("target/transit/test.transit")

\* Model value is converted to a string
ASSUME(AssertSerDes(ModelValueConstant, "ModelValue"))

\* Serializing and deserializing objects
ndTestObjects ==
    LET output == <<[a |-> 1, b |-> "a"], [a |-> 2, b |-> "b"], [a |-> 3, b |-> "c"]>>
    IN
       /\ ndTransitSerialize("target/transit/test.transit", output)
       /\ LET input == ndTransitDeserialize("target/transit/test.transit")
          IN
             /\ Len(input) = 3
             /\ input[1].a = 1
             /\ input[1].b = "a"
             /\ input[2].a = 2
             /\ input[2].b = "b"
             /\ input[3].a = 3
             /\ input[3].b = "c"
ASSUME(ndTestObjects)

\* Serializing and deserializing arrays
ndTestArrays ==
    LET output == << <<1, 2, 3>>, <<4, 5, 6>>, <<7, 8, 9>> >>
    IN
       /\ ndTransitSerialize("target/transit/test.transit", output)
       /\ LET input == ndTransitDeserialize("target/transit/test.transit")
          IN
             /\ Len(input) = 3
             /\ input[1][1] = 1
             /\ input[1][2] = 2
             /\ input[1][3] = 3
             /\ input[2][1] = 4
             /\ input[2][2] = 5
             /\ input[2][3] = 6
             /\ input[3][1] = 7
             /\ input[3][2] = 8
             /\ input[3][3] = 9
ASSUME(ndTestArrays)

\* Serializing and deserializing primitive values
ndTestPrimitives ==
    LET output == <<1, 2, 3, 4>>
    IN
       /\ ndTransitSerialize("target/transit/test.transit", output)
       /\ LET input == ndTransitDeserialize("target/transit/test.transit")
          IN
             /\ Len(input) = 4
             /\ input[1] = 1
             /\ input[2] = 2
             /\ input[3] = 3
             /\ input[4] = 4
ASSUME(ndTestPrimitives)

\* Serializing and deserializing objects
TestObjects ==
    LET output == <<[a |-> 1, b |-> "a"], [a |-> 2, b |-> "b"], [a |-> 3, b |-> "c"]>>
    IN
       /\ TransitSerialize("target/transit/test.transit", output)
       /\ LET input == TransitDeserialize("target/transit/test.transit")
          IN
             /\ Len(input) = 3
             /\ input[1].a = 1
             /\ input[1].b = "a"
             /\ input[2].a = 2
             /\ input[2].b = "b"
             /\ input[3].a = 3
             /\ input[3].b = "c"
ASSUME(TestObjects)

\* Serializing and deserializing arrays with sets
TestArrays ==
    LET output == << <<1, 2, 3>>, <<4, 5, 6>>, <<7, 8, 9>>, {10, 20, 30} >>
    IN
       /\ TransitSerialize("target/transit/test.transit", output)
       /\ LET input == TransitDeserialize("target/transit/test.transit")
          IN
             /\ Len(input) = 4
             /\ input[1][1] = 1
             /\ input[1][2] = 2
             /\ input[1][3] = 3
             /\ input[2][1] = 4
             /\ input[2][2] = 5
             /\ input[2][3] = 6
             /\ input[3][1] = 7
             /\ input[3][2] = 8
             /\ input[3][3] = 9
             /\ input[4] = {30, 10, 20}
ASSUME(TestArrays)

\* Serializing and deserializing primitive values
TestPrimitives ==
    LET output == <<1, 2, 3, 4>>
    IN
       /\ TransitSerialize("target/transit/test.transit", output)
       /\ LET input == TransitDeserialize("target/transit/test.transit")
          IN
             /\ Len(input) = 4
             /\ input[1] = 1
             /\ input[2] = 2
             /\ input[3] = 3
             /\ input[4] = 4
ASSUME(TestPrimitives)

\* Round trip with complex object
RoundTrip ==
    LET output == <<[a |-> 3], 2, <<<<1, 2>>, "look">>, <<<<<<[b |-> [c |-> <<4, 5, 6>>]]>>>>>>>>
    IN
       /\ TransitSerialize("target/transit/test.transit", output)
       /\ output = TransitDeserialize("target/transit/test.transit")
ASSUME(RoundTrip)
=============================================================================
