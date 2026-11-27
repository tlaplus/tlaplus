---
title: Proving Type Correctness (`TypeOK`) in TLA⁺ with TLAPS
description: Guidance for Proving Type Correctness in TLA⁺ with TLAPS
---
### 🔍 Guidance for Proving Type Correctness (`TypeOK`) in TLA⁺ with TLAPS

To formally prove type correctness using TLAPS, follow these steps.
All proofs must be placed in a separate file with the _proof.tla extension (e.g., MyModule_proof.tla).

---

#### 1. **Enable TLAPS Pragmas**

Before writing the proof, ensure that the TLAPS pragmas such as `PTL`, `SMT`, etc., are available by either:

* Adding `EXTENDS TLAPS`, or
* Using `INSTANCE TLAPS`.

This makes the necessary proof strategies accessible to the prover.

---

#### 2. **Referencing Assumptions**

If your specification includes assumptions using `ASSUME`, **name** the assumption and **explicitly refer to it** in your proof using the `BY` clause.

For example:

```tla
----- MODULE MyModule -----
CONSTANT S

ASSUME Assumption == S \subseteq Nat

VARIABLES x
vars == <<x>>

TypeOK == x \in Nat

Init == ...

A == ...
B == ...

Next == A \/ B

Spec == Init /\ [][Next]_vars
=====

----- MODULE MyModule_proof -----
EXTENDS MyModule

LEMMA TypeCorrect == Spec => []TypeOK
<1>1. Init => TypeOK BY Assumption DEF Init, TypeOK
<1>2. TypeOK /\ [Next]_vars => TypeOK' BY Assumption DEF TypeOK, Next, vars, A, B
<1>. QED BY Assumption, <1>1, <1>2, PTL DEF Spec, TypeOK, Init, Next, A, B
=====
```

> ✅ **Note**: Explicitly referencing `Assumption` ensures TLAPS is aware of it during the proof. Omitting this may result in unprovable steps or silent failures.

---

#### 3. **Invocation and Interpreting Feedback**

TLAPS **must be run**—either through the **TLA⁺ extension in VSCode** or via the **command line**.

**To check a proof in VSCode**:

* Open the `_proof.tla` file in VSCode.
* Right-click anywhere inside the proof and select **“TLA+: Check Prove Step in TLAPS”**, or use the command palette.

**To check a proof on the command line**:

* Run the following command:

  ```bash
  $ opam exec -- tlapm MyModule_proof
  ```

After running TLAPS, examine its output carefully. It will indicate whether each **proof obligation has been successfully discharged** or if **any have failed**. Use this feedback to guide your next steps—refining proof steps, adjusting assumptions, or structuring your arguments more clearly. TLAPS is not just a checker but a valuable source of insight into how your proof is interpreted and where it may need improvement.
