import Mathlib.Data.Nat.Notation
import Mathlib.Data.Real.Basic

import Verso
import VersoManual
import VersoBlueprint

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Basic Properties of Real Numbers" =>

:::source_document "addition-source"
%%%
title := "Starter Addition Notes"
kind := .pdf
pdf := "source/addition-source.pdf"
%%%
:::

:::group "addition_core-1"
Core statements about addition on real numbers.
:::

:::author "project_author-1" (name := "Daniel Birmajer")
:::

```lean "namespace"
namespace Section_1_2
```
We will begin with the basic properties of _addition_, which are four:

   * *Commutative property*

:::theorem "add_comm" (parent := "addition_core-1")(lean := "add_comm")
For any real numbers $`a` and $`b`, the following holds: $`a + b = b + a`
:::

```lean "add_comm"
example (a b : ℝ) : a + b = b + a := by
  exact add_comm a b
```

  * *Associative property*
:::theorem "add_assoc" (parent := "addition_core-1")(lean := "add_assoc")
For any real numbers `a`, `b` and `c`, the following holds:
$$`(a + b) + c = a + (b + c)`
:::

```lean "add_assoc"
example (a b c : ℝ) : (a + b) + c = a + (b + c) := by
  exact add_assoc a b c
```
```tex
--\begin{axiom}{my_axiom_name} \label{ax:my_axiom}
Let $X$ be a set with property $P$.
--\end{axiom}
```

* *Existence of the neutral element* There exists a real number called _zero_ that we denote as $`0` such that,
for every real number $`a`:
$$`a + 0 = 0 + a = a`

:::theorem "add_zero" (parent := "addition_core-1")(lean := "add_zero")
For all real number $`a`:
$`a + 0  = a`.
:::

```lean "add_zero"
example (a : Real) : a + 0 = a := by
  exact add_zero a
```

:::theorem "zero_add" (parent := "addition_core-1")(lean := "zero_add")
For all real number $`a`:
$`0 + a  = a`.
:::

```lean "zero_add"
example (x : Real) : 0 + x  = x := by
  exact zero_add x
```

  * *Existence of the additive inverse*
Given a real number $`a`, there exists a real number that we call the _additive inverse_ of $`a`, and we indicate as `-a`, such that:
$$`a + (-a) = (-a) + a = 0`

:::theorem "add_neg_cancel" (parent := "addition_core-1")(lean := "add_neg_cancel")
Given a real number $`a`, there exists a real number that we call the _additive inverse_ of $`a`, and we indicate as `-a`, such that:
$$`a + (-a) = 0`
:::

```lean "add_neg_cancel"
example (a : ℝ) : a + (-a) = 0 := by
  exact add_neg_cancel a
```

:::theorem "neg_add_cancel" (parent := "addition_core-1")(lean := "neg_add_cancel")
Given a real number $`a`, there exists a real number that we call the _additive inverse_ of $`a`, and we indicate as `-a`, such that:
$$`(- a) + a  = 0`
:::

```lean "neg_add_cancel"
example (a : ℝ) : (-a) + a = 0 := by
  exact neg_add_cancel a
```

The basic properties of the _product_ are also four and correspond exactly to those of addition:

:::group "product_core"
Core statements about multiplication on real numbers.
:::

   * *Commutative property*

:::theorem "mul_comm" (parent := "product_core")(lean := "mul_comm")
For any real numbers $`a` and $`b`, the following holds: $`a ·  b = b ·  a`
:::

```lean "mul_comm"
example (a b : ℝ) : a * b = b * a := by
  exact mul_comm a b
```

  * *Associative property*
:::theorem "mul_assoc"  (parent := "product_core")(lean := "mul_assoc")
  For any real numbers $`a, b`, and $`c`, the following holds
$$`a \cdot (b \cdot c) = (a \cdot b) \cdot c`
:::

```lean "mul_assoc"
example (a b c : ℝ) : (a * b) * c = a * (b * c):= by
  exact mul_assoc a b c
```
  * *Property of existence of the neutral element*
There exists a real number distinct from _zero_ that we call _one_ and denote
as $`1` such that, for every real number:
$$`a \cdot 1 = 1 \cdot 1 = a`

:::theorem "one_ne_zero" (parent := "product_core")(lean := "one_ne_zero")
$`1 ≠ 0`
:::

```lean "one_ne_zero"
example : (1 : ℝ) ≠ (0 : ℝ) := one_ne_zero
```

:::theorem "mul_one" (parent := "product_core")(lean := "mul_one")
For all real number $`a`:
$`a · 1  = a`.
:::

```lean "add_zero"
example (a : Real) : a * 1 = a := by
  exact mul_one a
```

:::theorem "one_mul" (parent := "product_core")(lean := "one_mul")
For all real number $`a`:
$`1 · a  = a`.
:::

```lean "one_mul"
example (a : Real) : 1 * a  = a := by
  exact one_mul a
```

  * *Existence of the multiplicative inverse*
Given a real number $`a`, _distinct from zero_, there exists a real number
that we call the _multiplicative inverse of_ $`a`,
and we denote as $`a^{-1}`, such that:
$$`a \cdot a^{-1} = a^{-1} \cdot a = 1`


:::theorem "mul_inv_cancel" (parent := "product_core")(lean := "mul_inv_cancel₀")
For all real number $`a`, with $`a \ne 0`:
$`a · a^{-1}  = 1`.
:::

```lean "mul_inv_cancel"
example (a : ℝ) (hₐ : a ≠ 0)  : a * a⁻¹ = 1 := by
  exact mul_inv_cancel₀ hₐ
```
:::theorem "inv_mul_cancel" (parent := "product_core")(lean := "inv_mul_cancel₀")
For all real number $`a`, with $`a ≠ 0`:
$`a^{-1} · a  = 1`.
:::

```lean "inv_mul_cancel"
example (a : ℝ) (hₐ : a ≠ 0)  : a⁻¹ * a = 1 := by
  exact inv_mul_cancel₀ hₐ
```

We now include a property that links addition with with the product:

  *Distributive property*
:::theorem "mul_add" (parent := "order_core")(lean := "mul_add")
For any real numbers $`a, b`, and $`c`, the following holds:
$$`a \cdot (b + c) = a \cdot b + a \cdot c`
:::
```lean "mul_add"
example (a b c : ℝ) : a * (b + c) = a * b + a * c := by
  exact mul_add a b c
```

:::theorem "add_mul" (parent := "product_core")(lean := "add_mul")
For any real numbers $`a, b`, and $`c`, the following holds:
$$`(a + b) \cdot c = a \cdot c + b \cdot c`
:::

```lean "add_mul"
example (a b c : ℝ) : (a + b) * c = a * c + b * c := by
  exact add_mul a b c
```

The final properties we indicate now refer to the order relation that exists
between real numbers.

:::group "order_core"
Core statements about the order on real numbers.
:::

The notation $`a < b` means $`a` _is less than_ $`b` and is exactly the same as
$`b > a` ($`b` _is greater than_ $`a`).

  * *Property of trichotomy*
:::theorem "trichotomy" (parent := "order_core")(lean := "lt_trichotomy")
If $`a` and $`b` are two real numbers, _one, and only one_,
of the following possibilities holds:

    - $$`a < b`

    - $$`a = b`

    - $$`a > b`
:::

```lean "trichotomy"
example (a b : ℝ) : a < b ∨ a = b ∨ b < a :=
  lt_trichotomy a b
```

  * *Transitive property*

:::theorem "lt_trans" (parent := "order_core")(lean := "lt_trans")
If $`a`, $`b`, and $`c` are real numbers that satisfy $`a < b` and $`b < c`,
then it necessarily must be: $`a < c`
:::

```lean "lt_trans"
example (a b c : ℝ) (ha : a < b) (hb : b < c ) : a < c := by
  exact lt_trans ha hb
```
  *  *Monotonicity of addition*
:::theorem "add_lt_add_left" (parent := "order_core")(lean := "add_lt_add_left")
If $`a` and $`b` are real numbers that satisfy $`a < b`, then for any real
number $`c`, the following holds:
$$`a + c < b + c`
:::

```lean "add_lt_add_left"
example (a b c : ℝ) (hab : a < b) : a + c <  b + c :=
  add_lt_add_left hab c
```

  * *Monotonicity of the product*
:::theorem "mul_lt_mul_of_pos_right" (parent := "order_core")(lean := "mul_lt_mul_of_pos_right")
If $`a` and $`b` are real numbers that satisfy $`a < b`,
then for any real number $`c > 0`, the following holds:
$$`c \cdot a < b \cdot c`
:::

```lean "mul_lt_mul_of_pos_right"
example
  (a b c : ℝ)
  (h_a : a < b)
  (h_c : 0 < c) : a * c <  b * c := by
    exact mul_lt_mul_of_pos_right h_a h_c
```
                                                        ◇◇◇◇◇◇
We are now going to deduce some elementary properties of real numbers using
only the properties just listed.
The attentive reader will have noticed that we promised a list of 14 properties
and only 13 have appeared;
the remaining one we will not need for now and will be the subject of study in
a future paragraph.

:::group "properties_core"
Core statements about multiplication on real numbers.
:::

We begin by proving the _cancellation property_ which is stated as follows:
If $`a, b`, and $`c` are real numbers such that:
$$`a + c = b + c`
then:
$$`a = b`
(in other words, a term that appears added to both sides can be canceled).

:::theorem "add_right_cancel" (parent := "properties_core")(lean := "add_right_cancel")
If $`a, b`, and $`c` are real numbers such that:
$`\; a + c = b + c\;`
then:
$`\; a = b`
(in other words, a term that appears added to both sides can be canceled).
:::

```lean "add_right_cancel"
example {a b c : ℝ}
  (h : a + c = b + c) : a = b := by
    exact add_right_cancel h
```

:::proof "add_right_cancel"
*Explanation of the Lean-specific ingredients.*

  * The `calc` environment allows a proof to be written as a chain of
equalities (or inequalities).
Each line proves that the current expression is equal to the next one,
so the entire chain establishes the desired result by transitivity.

  * The theorem `add_zero a` states that $`a + 0 = a.`
  When the equality is needed in the opposite direction,
  Lean uses `Eq.symm (add_zero a)` $`a = a + 0.`

  * The theorem `add_neg_cancel c` states that $`c + (-c) = 0.`
  Again, if the reverse equality is required, Lean applies `Eq.symm`

  * The associativity theorem `add_assoc a b c` states that
    $$`(a + b) + c = a + (b + c).`
  Since associativity is an equality, Lean can use either
  `add_assoc a b c` or `Eq.symm (add_assoc a b c)` depending on the
  desired direction.

  * The theorem `Eq.symm` reverses an equality. If
  `h : x = y`, then `Eq.symm h : y = x`. This is useful whenever a
  previously established equality must be applied in the opposite direction.

  * The theorem `congrArg` expresses the principle that equal quantities
  remain equal after applying the same function to both sides.
  If `h : x = y` and `f` is a function, then `congrArg f h` produces
  the equality `f(x) = f(y).`

  For example, `congrArg (λ x => x + (-c)) h`
  transforms the hypothesis
  $$`a + c = b + c`
  into
  $$`(a + c) + (-c) = (b + c) + (-c),`
  while `congrArg (λ x => a + x) h` adds the same quantity `a` to
  both sides of an equality.

The Lean proof is
:::

```lean "add_right_cancel"
example
  (a b c : ℝ) (h : a + c = b + c) : a = b := by
  calc
    a = a + 0 := Eq.symm (add_zero a)
    _ = a + (c + (-c)) :=
      congrArg (λ x => a + x) (Eq.symm (add_neg_cancel c))
    _ = (a + c) + (-c) := Eq.symm (add_assoc a c (-c))
    _ = (b + c) + (-c) := congrArg (λ x => x + (-c)) h
    _ = b + (c + (-c)) := add_assoc b c (-c)
    _ = b + 0 := congrArg (λ  x => b + x) (add_neg_cancel c)
    _ = b := add_zero b
```

  * Exercise: Prove the following lemma in Lean 4:
:::theorem "add_left_cancel" (parent := "properties_core")(lean := "add_left_cancel")
If $`a, b`, and $`c` are real numbers such that:
$`\; a + b = a + c\;`
then:
$`\; b = c`
:::

```lean "add_left_cancel"
example {a b c : ℝ}
  (h : a + b = a + c) : b = c := by
    exact add_left_cancel h
```

Another property we demonstrate is the _uniqueness of zero_ which is stated
as follows:

:::lemma_ "add_right_eq_self" (parent := "properties_core")
If $`a` and $`b` are real numbers such that: $`a + b = a` then it must be:
$`b = 0`.
:::

This his demonstration is simple:

```lean "add_right_eq_self"
lemma add_right_eq_self {a b : ℝ}
  (h : a + b = a) : b = 0 := by
  have h' : a + b = a + 0 := by
    calc a + b
    _ = a := by exact h
    _ = a + 0 := by exact Eq.symm (add_zero a)
  exact add_left_cancel h'
```
We are now in a position to prove :

:::theorem "mul_zero" (parent := "properties_core")(lean := "mul_zero")
$$`a \cdot 0 =0` whatever the real number $`a` may be.
:::

```lean "mul_zero"
example (a : ℝ) : a * 0 = 0 :=
  mul_zero a
```

:::proof "mul_zero"
Explanation of the Lean-specific ingredients.

* The proof begins by introducing an intermediate equality with `have`.
    This allows us to prove the statement
    $`a \cdot 0 = a \cdot 0 + a \cdot 0`,
    which will later be simplified to conclude that $`a \cdot 0 = 0`.

* The `calc` environment writes the argument as a chain of equalities.
    Each line establishes that the current expression equals the next one,
    so the desired equality follows by transitivity.

* The theorem `add_zero 0` states that $`0 + 0 = 0`.
    Since the proof needs the equality in the opposite direction,
    Lean uses `Eq.symm (add_zero 0)`, which gives $`0 = 0 + 0`.

* The theorem `congrArg` applies the same function to both sides of an
    equality. Here the function is $`x \mapsto a \cdot x`,
    so `congrArg (λ x => a * x) (Eq.symm (add_zero 0))`
    transforms $`0 = 0 + 0` into $`a \cdot 0 = a \cdot (0 + 0).`

* The distributive law is provided by the theorem
    `mul_add a 0 0`, which states that
    $$`a \cdot (0 + 0) = a \cdot 0 + a \cdot 0`.
    This completes the chain of equalities proving the intermediate result.

* The theorem `add_right_eq_self` expresses the cancellation principle
    $`x = x + y \;\Longrightarrow\; y = 0`.
    Since the intermediate equality is stored in the opposite direction,
    the proof first applies `Eq.symm` to obtain
    $$`a \cdot 0 + a \cdot 0 = a \cdot 0.`
    Then `add_right_eq_self`
    concludes that the extra summand must be zero: $`a \cdot 0 = 0.`
    This is exactly the desired result.

The Lean proof is
:::

```lean "mul_zero"
example (a : ℝ) : a * 0 = 0 := by
  have : a * 0 = a * 0 + a * 0 :=
  calc
    a * 0 = a * (0 + 0) := by
      exact congrArg (λ x => a * x) (Eq.symm (add_zero 0))
    _     = a * 0 + a * 0 := by
      exact mul_add a 0 0
  exact (add_right_eq_self (Eq.symm this))
```

(Indeed, in the lemma `add_right_eq_self` one must take as parameters
$`a\cdot 0` as $`a` and also $`a\cdot 0` as $`b`)

This last demonstration illustrates the following fact:
once a property has been demonstrated starting from basic properties,
then said property can be used as a starting point to prove new properties.

It is clear that in this way, in the last instance, we only use the properties
from the given list.


```lean "end namespace"
end Section_1_2
```
