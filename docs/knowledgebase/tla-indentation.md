---
title: When Indentation Matters in TLA+: Aligning Junctor Lists Correctly
description: Indentation in TLA+ is usually ignored, but junctor lists such as disjunction and conjunction are a critical exception. Misaligned operators can cause syntax errors or change the meaning of your specification. This article explains what junctor lists are, shows examples of how indentation affects semantics, and provides best practices to keep your TLA+ specifications correct and readable.
---
### **When Indentation Matters in TLA+**

In TLA+, indentation is **syntactically insignificant**, except when writing **junctor lists**—multi-line expressions using logical operators like **conjunction** (`/\`, "and") and **disjunction** (`\/`, "or"). Improper indentation of these lists can lead to **syntax errors**—or worse, **logical misinterpretation**.

---

### **What Are Junctor Lists?**

A **junctor list** is a multi-line expression combining multiple boolean conditions using logical **conjunction** (`/\`) or **disjunction** (`\/`). They are typically written across multiple lines to enhance readability.

---

### **Proper Alignment of Junctor Lists**

All operators (`/\` or `\/`) in a junctor list must be **indented consistently** and aligned vertically. The example below illustrates how varying indentation can alter the semantic meaning of a formula.

```tla
LEMMA 
    /\ TRUE
      \/ TRUE
    /\ FALSE
<=>
    (TRUE \/ TRUE) /\ FALSE
OBVIOUS

LEMMA 
    /\ TRUE
      \/ TRUE
      \/ FALSE
<=>
    TRUE \/ TRUE \/ FALSE
OBVIOUS 

LEMMA 
    \/ TRUE
    \/ TRUE
      /\ FALSE
<=> 
    TRUE \/ (TRUE /\ FALSE)
OBVIOUS
```

---

### **Best Practices**

* Always **align each junctor (`/\` or `\/`) in a list at the same indentation level**.
* Avoid using tabs; use **spaces** (typically 4 per level) for consistency.
* Prefer vertical alignment for readability and structural clarity.

---

### **Conclusion**

In TLA+, **indentation of junctor lists is not optional**—it affects the correctness of your specification. When writing conjunctions and disjunctions across multiple lines, make sure to **align operators consistently** to ensure your specification behaves as intended.
