------------- CONFIG JsonTests ---------

CONSTANT ModelValueConstant = ModelValue
===================

----------------------------- MODULE JsonTests -----------------------------
EXTENDS Json, Integers, Sequences, TLC, TLCExt

CONSTANT ModelValueConstant

\* Empty values
ASSUME(AssertEq(ToJsonArray({}), "[]"))
ASSUME(AssertEq(ToJsonArray(<<>>), "[]"))

\* Primitive values
ASSUME(AssertEq(ToJson(FALSE), "false"))
ASSUME(AssertEq(ToJson(1), "1"))
ASSUME(AssertEq(ToJson("a"), "\"a\""))
ASSUME(AssertEq(ToJson(ModelValueConstant), "\"ModelValue\""))
ASSUME(AssertEq(ToJson({TRUE, FALSE}), "[false,true]"))
ASSUME(AssertEq(ToJson({1}), "[1]"))
ASSUME(AssertEq(ToJsonArray({TRUE, FALSE}), "[false,true]"))
ASSUME(AssertEq(ToJsonArray({1}), "[1]"))
ASSUME(AssertEq(ToJsonArray({"foo"}), "[\"foo\"]"))
ASSUME(AssertEq(ToJsonObject([a |-> TRUE, b |-> FALSE]), "{\"a\":true,\"b\":false}"))
ASSUME(AssertEq(ToJsonObject([a |-> 1]), "{\"a\":1}"))
ASSUME(AssertEq(ToJsonObject([a |-> "b"]), "{\"a\":\"b\"}"))

\* Structural values
ASSUME(AssertEq(ToJson({3, 2, 1}), "[1,2,3]"))
ASSUME(AssertEq(ToJson(<<3, 2, 1>>), "[3,2,1]"))
ASSUME(AssertEq(ToJson([x \in {3, 2, 1} |-> 2 * x + 1]), "[3,5,7]"))
ASSUME(AssertEq(ToJson(3 :> "c" @@ 2 :> "b" @@ 1 :> "a"), "[\"a\",\"b\",\"c\"]"))
ASSUME(AssertEq(ToJson([ {2, 1} -> {"a", "b"} ]), "[[\"a\",\"a\"],[\"a\",\"b\"],[\"b\",\"a\"],[\"b\",\"b\"]]"))
ASSUME(AssertEq(ToJson([ {1, 0} -> {"a", "b"} ]), "[{\"0\":\"a\",\"1\":\"a\"},{\"0\":\"a\",\"1\":\"b\"},{\"0\":\"b\",\"1\":\"a\"},{\"0\":\"b\",\"1\":\"b\"}]"))
ASSUME(AssertEq(ToJson([a: {2, 1}, b: {"a", "b"}]), "[{\"a\":1,\"b\":\"a\"},{\"a\":1,\"b\":\"b\"},{\"a\":2,\"b\":\"a\"},{\"a\":2,\"b\":\"b\"}]"))
ASSUME(AssertEq(ToJson({2, 1} \X {"b", "a"}), "[[1,\"a\"],[1,\"b\"],[2,\"a\"],[2,\"b\"]]"))
ASSUME(AssertEq(ToJson(SUBSET {2, 1}), "[[],[1],[2],[1,2]]"))
ASSUME(AssertEq(ToJson(1..3), "[1,2,3]"))
ASSUME(AssertEq(ToJsonArray({3, 2, 1}), "[1,2,3]"))
ASSUME(AssertEq(ToJsonArray(<<3, 2, 1>>), "[3,2,1]"))
ASSUME(AssertEq(ToJsonArray([x \in {3, 2, 1} |-> 2 * x + 1]), "[3,5,7]"))
ASSUME(AssertEq(ToJsonArray(3 :> "c" @@ 2 :> "b" @@ 1 :> "a"), "[\"a\",\"b\",\"c\"]"))
ASSUME(AssertEq(ToJsonArray([ {2, 1} -> {"a", "b"} ]), "[[\"a\",\"a\"],[\"a\",\"b\"],[\"b\",\"a\"],[\"b\",\"b\"]]"))
ASSUME(AssertEq(ToJsonArray([ {1, 0} -> {"a", "b"} ]), "[{\"0\":\"a\",\"1\":\"a\"},{\"0\":\"a\",\"1\":\"b\"},{\"0\":\"b\",\"1\":\"a\"},{\"0\":\"b\",\"1\":\"b\"}]"))
ASSUME(AssertEq(ToJsonArray([a: {2, 1}, b: {"a", "b"}]), "[{\"a\":1,\"b\":\"a\"},{\"a\":1,\"b\":\"b\"},{\"a\":2,\"b\":\"a\"},{\"a\":2,\"b\":\"b\"}]"))
ASSUME(AssertEq(ToJsonArray({2, 1} \X {"b", "a"}), "[[1,\"a\"],[1,\"b\"],[2,\"a\"],[2,\"b\"]]"))
ASSUME(AssertEq(ToJsonArray(SUBSET {2, 1}), "[[],[1],[2],[1,2]]"))
ASSUME(AssertEq(ToJsonArray(1..3), "[1,2,3]"))
ASSUME(AssertEq(ToJsonObject([a |-> FALSE, b |-> 1]), "{\"a\":false,\"b\":1}"))
ASSUME(AssertEq(ToJsonObject("a" :> 1 @@ "b" :> 2 @@ "c" :> 3), "{\"a\":1,\"b\":2,\"c\":3}"))
ASSUME(AssertEq(ToJsonObject(1 :> "b" @@ 0 :> "c"), "{\"0\":\"c\",\"1\":\"b\"}"))

\* Tests FcnRcdValue where the domain could be represented symbolically.
ASSUME(AssertEq(ToJsonObject([n \in 1..2 |-> "a"]), "[\"a\",\"a\"]"))

\* Nested values
ASSUME(AssertEq(ToJsonObject([a |-> {<<1, 2>>}, b |-> [c |-> 3]]), "{\"a\":[[1,2]],\"b\":{\"c\":3}}"))

\* Serializing and deserializing objects
ndTestObjects ==
    LET output == <<[a |-> 1, b |-> "a"], [a |-> 2, b |-> "b"], [a |-> 3, b |-> "c"]>>
    IN
       /\ ndJsonSerialize("target/json/test.json", output)
       /\ LET input == ndJsonDeserialize("target/json/test.json")
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
       /\ ndJsonSerialize("target/json/test.json", output)
       /\ LET input == ndJsonDeserialize("target/json/test.json")
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
       /\ ndJsonSerialize("target/json/test.json", output)
       /\ LET input == ndJsonDeserialize("target/json/test.json")
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
       /\ JsonSerialize("target/json/test.json", output)
       /\ LET input == JsonDeserialize("target/json/test.json")
          IN
             /\ Len(input) = 3
             /\ input[1].a = 1
             /\ input[1].b = "a"
             /\ input[2].a = 2
             /\ input[2].b = "b"
             /\ input[3].a = 3
             /\ input[3].b = "c"
ASSUME(TestObjects)

\* Serializing and deserializing arrays
TestArrays ==
    LET output == << <<1, 2, 3>>, <<4, 5, 6>>, <<7, 8, 9>> >>
    IN
       /\ JsonSerialize("target/json/test.json", output)
       /\ LET input == JsonDeserialize("target/json/test.json")
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
ASSUME(TestArrays)

\* Serializing and deserializing primitive values
TestPrimitives ==
    LET output == <<1, 2, 3, 4>>
    IN
       /\ JsonSerialize("target/json/test.json", output)
       /\ LET input == JsonDeserialize("target/json/test.json")
          IN
             /\ Len(input) = 4
             /\ input[1] = 1
             /\ input[2] = 2
             /\ input[3] = 3
             /\ input[4] = 4
ASSUME(TestPrimitives)

\* Round trip with complex object
\* There is no way to encode sets in json (like in XML or EDN), this is why we don't use it here
RoundTrip ==
    LET output == <<[a |-> 3], 2, <<<<1, 2>>, "look">>, <<<<<<[b |-> [c |-> <<4, 5, 6>>]]>>>>>>>>
    IN
       /\ JsonSerialize("target/json/test.json", output)
       /\ output = JsonDeserialize("target/json/test.json")
ASSUME(RoundTrip)
=============================================================================
