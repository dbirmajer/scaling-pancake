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
Given a real number $`a`, there exists a real number that we call the _opposite_ of $`a`, and we indicate as `-a`, such that:
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
In particular, if a real number $`a` is _different from 0_, it must be either
$`a < 0` or $`a > 0`.

:::theorem "lt_or_gt_of_ne" (parent := "order_core")(lean := "lt_or_gt_of_ne")
if a real number $`a` is _different from 0_, it must be either
$`a < 0` or $`a > 0`.
:::

```lean "lt_or_gt_of_ne"
example {a b : ℝ} (h : a ≠ 0) : a < 0 ∨ 0 < a := by
  exact lt_or_gt_of_ne h
```

:::definition "positive and negative" (parent := "order_core")
Postive and negative numbers
:::
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
$$`a + c = b + c` then:
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

A Lean proof:

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
:::


  * Exercise: Prove the following theorem in Lean 4:
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

```lean "add_left_cancel_ex"
example {a b c : ℝ}
  (h : a + b = a + c) : b = c := by
    sorry
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

A Lean proof is:

```lean "mul_zero"
example (a : ℝ) : a * 0 = 0 := by
  have : a * 0 = a * 0 + a * 0 :=
  calc
    a * 0 = a * (0 + 0) := by
      exact congrArg (λ x => a * x) ((add_zero 0).symm)
    _     = a * 0 + a * 0 := by
      exact mul_add a 0 0
  exact (add_right_eq_self (this.symm))
```
(Indeed, in the lemma `add_right_eq_self` one must take as parameters
$`a\cdot 0` as $`a` and also $`a\cdot 0` as $`b`)

:::proof "mul_zero"
Explanation of the Lean-specific ingredients.

* The proof begins by introducing an intermediate equality with `have`.
    This allows us to prove the statement
    $`a \cdot 0 = a \cdot 0 + a \cdot 0`,
    which will later be simplified to conclude that $`a \cdot 0 = 0`.

* The `have` tactic introduces an intermediate result that will be used
  later in the proof. It creates a new local hypothesis whose proof
  follows immediately after the `:=`.
  In this example, `have : a * 0 = a * 0 + a * 0 := ...`
  tells Lean that we will first prove the equality
  $$`a \cdot 0 = a \cdot 0 + a \cdot 0.`
  Once this proof is complete, the resulting equality becomes a local
  hypothesis (named `this` by default) that is available for the remainder
  of the proof. The final line uses this intermediate result to deduce
  that $`a \cdot 0 = 0.`

* The `calc` environment writes the argument as a chain of equalities.
    Each line establishes that the current expression equals the next one,
    so the desired equality follows by transitivity.

* The theorem `add_zero 0` states that $`0 + 0 = 0`.
    Since the proof needs the equality in the opposite direction,
    Lean uses `Eq.symm (add_zero 0)`, which gives $`0 = 0 + 0`.
    Equivalently, every equality has a `.symm` method, so the same result can be written more concisely as `(add_zero 0).symm`.

* The theorem `congrArg` applies the same function to both sides of an
    equality. Here the function is $`x \mapsto a \cdot x`,
    so `congrArg (λ x => a * x) (Eq.symm (add_zero 0))`
    transforms $`0 = 0 + 0` into $`a \cdot 0 = a \cdot (0 + 0)`.

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
:::


This last demonstration illustrates the following fact:
once a property has been demonstrated starting from basic properties,
then said property can be used as a starting point to prove new properties.

It is clear that in this way, in the last instance, we only use the properties
from the given list.

The product also has its cancellation law:


:::theorem "mul_left_cancel" (parent := "properties_core")(lean := "mul_left_cancel₀")
If $`a\cdot b = a\cdot c` and $`a \ne 0`, then $`b = c`.
:::

```lean "mul_left_cancel"
example (a b c : ℝ)
    (ha : a ≠ 0) (h : a * b = a * c) : b = c := by
  exact mul_left_cancel₀ ha h
```
A Lean proof is:

```lean "mul_left_cancel"
example (a b c : ℝ)
  (h : a * b = a * c)
  (hₐ : a ≠ 0) : b = c := by
  calc
    b = 1 * b := by rw [one_mul b]
    _ = (a⁻¹ * a) * b := by rw [inv_mul_cancel₀ hₐ]
    _ = a⁻¹ * (a * b) := by exact mul_assoc   a⁻¹ a b
    _ = a⁻¹ * (a * c) := by rw [h]
    _ = (a⁻¹ * a) * c := by rw [mul_assoc   a⁻¹ a c]
    _= 1 * c := by rw [inv_mul_cancel₀ hₐ]
    _= c := by exact one_mul c
```

:::proof "mul_left_cancel"
*Explanation of the Lean-specific ingredients.*

* The proof is written as a chain of equalities using the `calc`
  environment. Each line establishes that the current expression is equal
  to the next one, so the desired equality follows by transitivity.

* The main new ingredient in this proof is the tactic `rw`
  (short for *rewrite*). The command
  `rw [h]` tells Lean to replace an occurrence of one side of the equality
  `h` by the other side. Thus, if
  `h : x = y`, then `rw [h]` rewrites `x` as `y`,
  while `rw [← h]` rewrites `y` as `x`.
  In many situations, `rw` automatically performs the work that would
  otherwise require an explicit application of `Eq.symm` and `congrArg`.

* The first rewrite, `rw [one_mul b]`,
  uses the theorem $`1 \cdot b = b` in the reverse direction,
  changing $`b` into $`1 \cdot b.`
  Notice that although `one_mul b` is stated as $`1 \cdot b = b,`
  the `rw` tactic automatically recognizes that the opposite direction is
  needed and performs the reverse rewrite.

* The second rewrite, `rw [inv_mul_cancel₀ hₐ]`,
  replaces the factor $`1`
  by $`a^{-1}\cdot a,`
  since the theorem $`a^{-1}\cdot a = 1` holds whenever $`a \neq 0`.
  Again, `rw` automatically applies the equality in the required direction.

* The theorem `mul_assoc` states that
  $$`(x \cdot y)\cdot z = x\cdot(y\cdot z).`
  It is used to reassociate the factors so that the hypothesis
  `h : a \cdot b = a \cdot c` appears as a subexpression.

* The rewrite `rw [h]` replaces the subexpression
  $`a \cdot b` by $`a \cdot c` inside the larger expression
  $`a^{-1}\cdot(a\cdot b).`
  Earlier proofs required an explicit use of `congrArg` to rewrite inside a
  function, but the `rw` tactic performs this substitution automatically.

* The remaining rewrites undo the previous steps.
  Another application of `mul_assoc` groups the factors as
  $$`(a^{-1}\cdot a)\cdot c,`
  the theorem `inv_mul_cancel₀ hₐ` rewrites this as
  $`1\cdot c,`
  and finally `one_mul c` simplifies the expression to
  $`c.`

This proof illustrates one of the main advantages of the `rw` tactic:
instead of explicitly applying `Eq.symm` to reverse equalities and
`congrArg` to rewrite inside larger expressions, `rw` searches for matching
subexpressions and performs the necessary substitutions automatically,
using either direction of an equality whenever appropriate.
:::


We now proceed to prove the _rule of signs_. In the first place, it holds:
:::theorem "neg_neg" (parent := "properties_core")(lean := "neg_neg")
for every real number $`a`, $`−(−a) = a`.
:::

```lean "neg_neg"
theorem neg_neg_eq (a : ℝ) : - (-a) = a := by
  exact neg_neg a
```
Indeed, by definition $`−(−a)` is the additive inverse of $`−a`, that is:

```lean "neg_neg"
example {a : ℝ} : -(-a) = a := by
  have h : -(-a) + (-a) = a + (-a) := by
    calc
    -(-a) + (-a) = 0 := by exact neg_add_cancel (-a)
    _ = a + (-a) := by rw [add_neg_cancel a]
  exact add_right_cancel h
```

We continue proving:
:::theorem "neg_mul" (parent := "properties_core")(lean := "neg_mul")
$$`(−a) \cdot b = −(a \cdot b)`
for any real numbers $`a` and $`b`.
:::

```lean "neg_mul"
example (a b : ℝ) : (-a) * b = -(a * b) := by
  exact neg_mul a b
```
A Lean proof:

```lean "neg_mul"
example (a b : ℝ) : (-a) * b = -(a * b) := by
  have : (-a) * b + a * b = 0 := by
    calc
    (-a) * b + a * b = ((-a) + a) * b := by
      rw [add_mul (-a) a b]
    _ = 0 := by
      rw [neg_add_cancel a, mul_comm 0 b, mul_zero]
  have this : (-a) * b + a * b = -(a * b) + a * b := by
    calc
    (-a) * b + a * b = 0 := this
    _ =  -(a * b) + a * b := by rw [neg_add_cancel (a * b)]
  exact (add_right_cancel  this)
```
:::proof "neg_mul"
*Explanation of the Lean-specific ingredients.*

* As in previous examples, the proof begins with a `have` statement,
  introducing an intermediate result that will be used later.
  The first intermediate goal is
  $$`(-a)\cdot b + a\cdot b = 0.`
  Once this has been established, it becomes available as a local
  hypothesis (named `this` by default).

* The `calc` environment organizes the proof as a chain of equalities.
  Each line proves that the current expression is equal to the next one,
  and the entire chain is justified by transitivity.

* The first equality uses the distributive law
  `add_mul (-a) a b`, which states that
  $$`((-a) + a) \cdot b = (-a) \cdot b + a \cdot b.`
  Since the proof requires the equality in the opposite direction,
  the command `rw [add_mul (-a) a b]`
  automatically rewrites
  $$`(-a) \cdot b + a\cdot b`
  as
  $$`((-a) + a) \cdot b.`

* The next step illustrates an important feature of the `rw` tactic:
  *several rewrites can be performed with a single command.*

  The line `rw [neg_add_cancel a, mul_comm 0 b, mul_zero]`

  applies three theorems consecutively.

  * First, `neg_add_cancel a` rewrites
    $$`(-a) + a`
    as $`0`, producing $`0\cdot b.`

  * Next, `mul_comm 0 b` uses the commutativity of multiplication to
    rewrite $`0\cdot b` as $`b\cdot0.`

  * Finally, `mul_zero` rewrites $`b\cdot0` as $`0.`

  Thus a single `rw` command performs three successive substitutions,
  each using the result of the previous one.

* A second `have` statement introduces another intermediate equality:
  $$`(-a)\cdot b+a\cdot b=-(a\cdot b)+a\cdot b.`
  Its first step simply reuses the equality proved previously.

* The next rewrite,
  `rw [neg_add_cancel (a * b)]`,
  again uses an equality in the reverse direction.
  Since
  $$`-(a \cdot b)+(a \cdot b) = 0,`
  the tactic rewrites $`0` as $`-(a\cdot b)+(a\cdot b).`

* The proof concludes with the cancellation theorem
  `add_right_cancel`.
  Since both sides of the equality have the same term
  $$`a\cdot b`
  added to them, cancellation yields
  $$`(-a)\cdot b = -(a\cdot b),`
  which is exactly the desired result.

This proof demonstrates two important aspects of the `rw` tactic.

* First, `rw` automatically determines whether an equality should be used
  in its forward or reverse direction.

* Second, a single command may contain *a list of theorems*. Lean applies
  these rewrites from left to right, updating the goal after each one.
  This often produces short, readable proofs that would otherwise require
  several separate rewrite commands or explicit uses of `Eq.symm` and
  `congrArg`.
:::

  * Exercise: Prove the following theorem in Lean 4:
:::theorem "neg_mul_neg"
$$`(−a) \cdot (-b) = a \cdot b`
for any real numbers $`a` and $`b`.
:::

```lean "neg_mul_neg"
theorem neg_mul_neg_eq (a b : ℝ) : (-a) * (-b) = a * b := by
  exact neg_mul_neg a b
```

```lean "neg_mul_neg_exercise"
example (a b : ℝ) : (-a) * (-b) = a * b := by
  sorry
```

The following theorem states that the opposite of a number has the opposite sign:
:::theorem "neg_neg_iff_pos" (parent := "properties_core")(lean := "neg_neg_iff_pos")
For any real number $`a`, negative $`a` is less than zero if and only if
 $`a` is greater than zero.
:::

```lean "neg_neg_iff_pos"
theorem neg_lt_zero {a : ℝ} :
  (- a < 0) ↔ (0 < a) := by
  exact neg_neg_iff_pos
```

A Lean 4 proof:

```lean "neg_neg_iff_pos_proof"
example {a : ℝ} :
  (-a < 0) ↔ (0 < a) := by
  constructor
  · intro h
    calc 0
      = (-a) + a := by rw [neg_add_cancel]
    _ < 0 + a := by  exact add_lt_add_left h a
    _ = a := by exact zero_add a
  · intro h
    calc 0
      = a + (-a) := by rw [add_neg_cancel]
    _ > 0 + (-a) := by  exact (add_lt_add_left h (-a))
    _ = -a := by exact zero_add (-a)
```

:::proof "neg_neg_iff_pos"
*Explanation of the Lean-specific ingredients.*

* The statement to be proved is a *biconditional*
  $$`(-a < 0) \iff (0 < a).`
  A biconditional consists of two implications:
  $$`(-a < 0) \Longrightarrow (0 < a)`
  and
  $$`(0 < a) \Longrightarrow (-a < 0).`

* The tactic `constructor` tells Lean to prove each implication
  separately. After the command

  `constructor`

  the original goal is replaced by two subgoals:

  1. $$`(-a < 0)\rightarrow (0 < a),`
  2. $$`(0 < a) \rightarrow (-a < 0).`

  Once both implications have been established, Lean concludes the
  biconditional.

* The bullets `·` simply separate the proofs of the two subgoals.
  The first bullet proves the forward implication, while the second
  proves the reverse implication.

* The tactic `intro` introduces the assumption of an implication into the
  local context.

  For example, in the first subgoal the command `intro h`
  assumes the hypothesis `h : -a < 0` and changes the goal from
  $$`(-a < 0) \rightarrow (0 < a)`
  to $`0 < a.`

  Likewise, in the second subgoal, `intro h` assumes `h : 0 < a`
  and changes the goal from
  $$`(0<a)\rightarrow(-a<0)` to $`-a < 0.`

* Each implication is then proved using a `calc` block.
  In the forward direction, the proof begins with the identity
  $$`0 = (-a) + a,`
  obtained by rewriting the theorem `neg_add_cancel` in the reverse direction.

* The theorem `add_lt_add_left h a`
  expresses the monotonicity of addition.
  Since $`-a < 0,` adding the same number $`a`$ to both sides gives
  $$`(-a) + a < 0 + a.`

* Finally, `zero_add a` rewrites $`0+a` as $`a,` yielding $`0<a.`

* The reverse implication follows the same pattern.
  The identity $`0 = a + (-a)`. comes from the theorem
  `add_neg_cancel` rewritten in the opposite direction.

* Applying `add_lt_add_left h (-a)` to the hypothesis $`0<a`
  adds $`-a`$ to both sides, producing $`0+(-a)<a+(-a).`

  Since the `calc` proof is written from top to bottom, this inequality
  appears as $`a + (-a) > 0 + (-a),`
  which is mathematically equivalent.

* Finally, `zero_add (-a)` simplifies $`0+(-a)` to $`-a,`
  giving $`-a < 0.`

This proof illustrates two of Lean's most common logical tactics.

* The tactic `constructor` decomposes a conjunction or biconditional into
  its component parts, creating one goal for each part.

* The tactic `intro` introduces the assumption of an implication (or a
  universally quantified variable) into the local context, allowing it to
  be referred to by name in the remainder of the proof.
:::


:::definition "square"
If $a$ is a real number, then the square of $a$ is the product of $`a` with
itself: $`a^2 = a \cdot a`.
:::

We will. now prove the following fact:
:::theorem "todo"
Let $`a` be a real number. if $`a ≠ 0`, then $`a^2 > 0`
:::


```lean "todo"
example : ∀ a : ℝ, (a ≠ 0) → a^2 > 0 := by
  intro a h
  sorry
--  exact mul_self_pos.2 h
```

```lean "todo"
example (a : ℝ): (a ≠ 0) → a^2 > 0 := by
  intro h
  have h' : a < 0 ∨ 0 < a := by
    exact lt_or_gt_of_ne h
  rcases h' with hNeg | hPos
  . sorry
  . sorry
--  exact mul_self_pos.2 h
```

To finish this section, we are going to prove the following fact:
```lean "end namespace"
end Section_1_2
```
