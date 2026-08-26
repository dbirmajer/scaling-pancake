import Mathlib.Data.Nat.Notation
import Mathlib.Data.Real.Basic

import Verso
import VersoManual
import VersoBlueprint

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Basic Properties of Real Numbers" =>


# Basic Properties of Addition

:::group "addition_core-1"
Core statements about addition on real numbers.
:::

We will begin with the basic properties of _addition_, which are four:

```lean "open BasicProperties"
namespace BasicProperties
```

:::theorem "add_comm" (parent := "addition_core-1")(lean := "add_comm")(tags := "Commutative property")
For any real numbers $`a` and $`b`, the following holds: $`a + b = b + a`
:::

```lean "add_comm"
example (a b : ℝ) : a + b = b + a := by
  exact add_comm a b
```

:::theorem "add_assoc" (parent := "addition_core-1")(lean := "add_assoc")(tags := "Associative property")
For any real numbers $`a, b` and $`c`, the following holds:
$$`(a + b) + c = a + (b + c)`
:::

```lean "add_assoc"
example (a b c : ℝ) : (a + b) + c = a + (b + c) := by
  exact add_assoc a b c
```

:::theorem "S3" (parent := "addition_core-1")(tags := "Existence of 0")
There exists a real number called _zero_ that we denote as
$`0` such that, for every real number $`a`:
$$`a + 0 = 0 + a = a`
:::

The corresponding _theorems_ in `Lean` are:

:::theorem "add_zero" (parent := "addition_core-1")(lean := "add_zero")
For all real number $`a`: $`\; a + 0  = a`.
:::

```lean "add_zero"
example (a : Real) : a + 0 = a := by
  exact add_zero a
```

:::theorem "zero_add" (parent := "addition_core-1")(lean := "zero_add")
For all real number $`a`: $`\; 0 + a  = a`.
:::

```lean "zero_add"
example (a : Real) : 0 + a  = a := by
  exact zero_add a
```

:::theorem "S4" (parent := "addition_core-1")(tags := "Existence of the opposite")
Given a real number $`a`, there exists a real number that we call the
_opposite_ of $`a`, and we indicate as $`-a`, such that:
$$`a + (-a) = (-a) + a = 0`
:::

The corresponding _theorems_ in `Lean` are:

:::theorem "add_neg_cancel" (parent := "addition_core-1")(lean := "add_neg_cancel")
Given a real number $`a`, $`\; a + (-a) = 0`
:::

```lean "add_neg_cancel"
example (a : ℝ) : a + (-a) = 0 := by
  exact add_neg_cancel a
```

:::theorem "neg_add_cancel" (parent := "addition_core-1")(lean := "neg_add_cancel")
Given a real number $`a`, $`(- a) + a  = 0`
:::

```lean "neg_add_cancel"
example (a : ℝ) : (-a) + a = 0 := by
  exact neg_add_cancel a
```

# Basic Properties of Multiplication

The basic properties of the _product_ are also four and correspond exactly to
those of addition:

:::group "product_core"
Core statements about multiplication on real numbers.
:::



:::theorem "mul_comm" (parent := "product_core")(lean := "mul_comm")(tags := "Commutative property")
For any real numbers $`a` and $`b`, the following holds: $`a ·  b = b ·  a`
:::

```lean "mul_comm"
example (a b : ℝ) : a * b = b * a := by
  exact mul_comm a b
```

:::theorem "mul_assoc"  (parent := "product_core")(lean := "mul_assoc")(tags := "Associative property")
  For any real numbers $`a, b`, and $`c`, the following holds
$$`a \cdot (b \cdot c) = (a \cdot b) \cdot c`
:::

```lean "mul_assoc"
example (a b c : ℝ) : (a * b) * c = a * (b * c):= by
  exact mul_assoc a b c
```
:::theorem "P3" (parent := "product_core")(tags := "Existence of 1")
There exists a real number distinct from $`0` that we call _one_ and denote
as $`1` such that, for every real number:
$$`a \cdot 1 = 1 \cdot a = a`
:::

The corresponding _theorems_ in `Lean` are:

:::theorem "one_ne_zero" (parent := "product_core")(lean := "one_ne_zero")
$`1 ≠ 0`
:::

```lean "one_ne_zero"
example : (1 : ℝ) ≠ (0 : ℝ) := by
  exact one_ne_zero
```

:::theorem "mul_one" (parent := "product_core")(lean := "mul_one")
For all real number $`a`: $`a · 1  = a`.
:::

```lean "mul_one"
example (a : Real) : a * 1 = a := by
  exact mul_one a
```

:::theorem "one_mul" (parent := "product_core")(lean := "one_mul")
For all real number $`a`: $`1 · a  = a`.
:::

```lean "one_mul"
example (a : Real) : 1 * a  = a := by
  exact one_mul a
```

:::theorem "P4" (parent := "product_core")(lean := "one_mul")(tags := "Existence of the multiplicative inverse")
Given a real number $`a`, _distinct from zero_, there exists a real number
that we call the _multiplicative inverse of_ $`a`,
and we denote as $`a^{-1}`, such that:
$$`a \cdot a^{-1} = a^{-1} \cdot a = 1`
:::

The corresponding _theorems_ in `Lean` are:

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

# Distributive property

We now include a property that links addition with with the product:

:::theorem "mul_add" (parent := "order_core")(lean := "mul_add")(tags := "Distributive Property
")
For any real numbers $`a, b`, and $`c`, the following holds:
$$`a \cdot (b + c) = a \cdot b + a \cdot c`
:::

```lean "mul_add"
example (a b c : ℝ) : a * (b + c) = a * b + a * c := by
  exact mul_add a b c
```
:::theorem "add_mul" (parent := "product_core")(lean := "add_mul")(tags := "Distributive Property
")
For any real numbers $`a, b`, and $`c`, the following holds:
$$`(a + b) \cdot c = a \cdot c + b \cdot c`
:::

```lean "add_mul"
example (a b c : ℝ) : (a + b) * c = a * c + b * c := by
  exact add_mul a b c
```

# Order Relation

The final properties we indicate now refer to the order relation that exists
between real numbers.

:::group "order_core"
Core statements about the order on real numbers.
:::

The notation $`a < b` means $`a` _is less than_ $`b` and is exactly the same as
$`b > a` ($`b` _is greater than_ $`a`).

:::theorem "trichotomy" (parent := "order_core")(lean := "lt_trichotomy")(tags := "Trichotomy")
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
example {a : ℝ} (h : a ≠ 0) : a < 0 ∨ 0 < a := by
  exact lt_or_gt_of_ne h
```

:::definition "positive and negative" (parent := "order_core")
A real number $`a`$ is called *positive* if $`0 < a.`

A real number $`a` is called *negative* if $`a < 0.`
:::


:::theorem "lt_trans" (parent := "order_core")(lean := "lt_trans")(tags := "Transitive property")
If $`a`, $`b`, and $`c` are real numbers that satisfy $`a < b` and $`b < c`,
then it necessarily must be: $`a < c`
:::

```lean "lt_trans"
example {a b c : ℝ} : a < b → b < c → a < c := by
  intro hab hbc
  exact lt_trans hab hbc
```

:::theorem "add_lt_add_left" (parent := "order_core")(lean := "add_lt_add_left")(tags := "Monotonicity of addition")
If $`a` and $`b` are real numbers that satisfy $`a < b`, then for any real
number $`c`, the following holds:
$$`a + c < b + c`
:::

```lean "add_lt_add_left"
example (a b c : ℝ) (hab : a < b) : a + c <  b + c :=
  add_lt_add_left hab c
```

:::theorem "mul_lt_mul_of_pos_right" (parent := "order_core")(lean := "mul_lt_mul_of_pos_right")(tags := "Monotonicity of the product")
If $`a` and $`b` are real numbers that satisfy $`a < b`,
then for any real number $`c > 0`, the following holds:
$$`c \cdot a < b \cdot c`
:::

```lean "mul_lt_mul_of_pos_right"
example
  {a b c : ℝ}
  (hbc : b < c)
  (ha : 0 < a) : b * a <  c * a := by
    exact mul_lt_mul_of_pos_right hbc ha
```

# Some Elementary Properties

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
theorem add_right_cancel
  {a b c : ℝ} (h : a + c = b + c) : a = b := by
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

* In this theorem the variables are declared as `{a b c : ℝ}`
  rather than `(a b c : ℝ)`.

  The parentheses declare *explicit arguments*, while the braces declare
  *implicit arguments*.

  An explicit argument must always be supplied when the theorem is used.
  For example, `add_comm a b` explicitly passes the values of `a` and `b` to the
  theorem `add_comm`.

  By contrast, an implicit argument is usually inferred automatically by
  `Lean` from the other arguments. In the theorem
  `theorem add_right_cancel {a b c : ℝ} (h : a + c = b + c) : a = b`
  the variables `a`, `b`, and `c` are implicit, while the hypothesis `h`
  is an explicit argument.

  Once `Lean` sees a proof of `h : a + c = b + c`
  it can determine the values of `a`, `b`, and `c` by inspecting the type
  of `h`. Therefore, when applying the theorem, we can simply write
  `add_right_cancel h` rather than `add_right_cancel a b c h`.

  Implicit arguments make theorem applications shorter and easier to read,
  while still allowing the arguments to be supplied explicitly if desired.

  For example, `@add_right_cancel ℝ a b c h`
  tells Lean to expose all implicit arguments and require them to be
  supplied manually.
:::


  * Exercise: Prove the following theorem in Lean 4:
:::theorem "add_left_cancel" (parent := "properties_core")(tags := "Exercise")(lean := "add_left_cancel")
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
theorem add_left_cancel {a b c : ℝ}
  (_ : a + b = a + c) : b = c := by
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
For every real number $`a`, $\;`a \cdot 0 =0`.
:::

Here is an example of using this theorem in Lean 4:

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
theorem mu_left_cancel₀ (a b c : ℝ)
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
example (a : ℝ) : - (-a) = a := by
  exact neg_neg a
```
Indeed, by definition $`−(−a)` is the additive inverse of $`−a`, that is:

```lean "neg_neg"
theorem neg_neg (a : ℝ) : -(-a) = a := by
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
theorem neg_mul (a b : ℝ) : (-a) * b = -(a * b) := by
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
    as $`0`, producing $`0 \cdot b.`

  * Next, `mul_comm 0 b` uses the commutativity of multiplication to
    rewrite $`0\cdot b` as $`b\cdot0.`

  * Finally, `mul_zero` rewrites $`b\cdot0` as $`0.`

  Thus a single `rw` command performs three successive substitutions,
  each using the result of the previous one.

* A second `have` statement introduces another intermediate equality:
  $$`(-a) \cdot b + a \cdot b = - (a \cdot b) + a \cdot b.`
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
:::theorem "neg_mul_neg" (parent := "properties_core")(tags := "Exercise")(lean := "neg_mul_neg")
$$`(−a) \cdot (-b) = a \cdot b`
for any real numbers $`a` and $`b`.
:::

```lean "neg_mul_neg"
 example (a b : ℝ) : (-a) * (-b) = a * b := by
  exact neg_mul_neg a b
```

```lean "neg_mul_neg_exercise"
theorem neg_mul_neg (a b : ℝ) : (-a) * (-b) = a * b := by
  sorry
```

The following theorem states that the opposite of a number has the opposite sign:
:::theorem "neg_neg_iff_pos" (parent := "properties_core")(lean := "neg_neg_iff_pos")
For any real number $`a`, negative $`a` is less than zero if and only if
 $`a` is greater than zero.
:::

```lean "neg_neg_iff_pos"
example {a : ℝ} :
  (- a < 0) ↔ (0 < a) := by
  exact neg_neg_iff_pos
```

A `Lean` proof:

```lean "neg_neg_iff_pos_proof"
theorem neg_neg_iff_pos {a : ℝ} :
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
  $$`-a < 0 \iff 0 < a.`
  A biconditional consists of two implications:
  $$`-a < 0 \Longrightarrow 0 < a`
  and
  $$`0 < a \Longrightarrow -a < 0.`

* The tactic `constructor` tells Lean to prove each implication
  separately.
  After the command `constructor`
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
  `- a < 0 → 0 < a` to `0 < a`.

  Likewise, in the second subgoal, `intro h` assumes `h : 0 < a`
  and changes the goal from `0 < a → - a < 0` to $`- a < 0`.

* Each implication is then proved using a `calc` block.
  In the forward direction, the proof begins with the identity
  `0 = (-a) + a`, obtained by rewriting the theorem `neg_add_cancel` in
  the reverse direction.

* The theorem `add_lt_add_left h a`
  expresses the monotonicity of addition.
  Since `- a < 0,` adding the same number `a` to both sides gives
  `(- a) + a < 0 + a.`

* Finally, `zero_add a` rewrites `0 + a` as `a`, yielding `0 < a`.

* The reverse implication follows the same pattern.
  The identity $`0 = a + (-a)`. comes from the theorem
  `add_neg_cancel` rewritten in the opposite direction.

* Applying `add_lt_add_left h (-a)` to the hypothesis $`0 < a`
  adds $`-a`$ to both sides, producing $`0 + (-a) < a + (-a).`

  Since the `calc` proof is written from top to bottom, this inequality
  appears as $`a + (-a) > 0 + (-a),`
  which is mathematically equivalent.

* Finally, `zero_add (-a)` simplifies $`0 + (-a)` to $`-a,`
  giving $`-a < 0.`

This proof illustrates two of Lean's most common logical tactics.

* The tactic `constructor` decomposes a conjunction or biconditional into
  its component parts, creating one goal for each part.

* The tactic `intro` introduces the assumption of an implication (or a
  universally quantified variable) into the local context, allowing it to
  be referred to by name in the remainder of the proof.
:::

:::theorem "mul_ne_zero" (parent := "properties_core")(lean := "mul_ne_zero")
For all $`a, b ∈ ℝ`, $`a · b = 0 ↔ a = 0 ∨ b = 0`
:::

Here is an example of using this theorem in `Lean`

```lean "mul_ne_zero"
example {a b : ℝ}
  (ha : a ≠ 0) (hb : b ≠ 0 ): a * b ≠ 0 := by
  exact mul_ne_zero ha hb
```

A `Lean` proof:

```lean "mul_ne_zero"
theorem mul_ne_zero {a b : ℝ}
  (ha : a ≠ 0) (hb : b ≠ 0 ): a * b ≠ 0 := by
  have ha' : 0 < a ∨ a < 0 := by
    exact (lt_or_gt_of_ne ha).symm
  have hb' : 0 < b ∨ b < 0 := by
    exact (lt_or_gt_of_ne hb).symm
  rcases ha' with aPos | aNeg
  . rcases hb' with bPos | bNeg
    .
      have : 0 < a * b :=
        calc
         0 = 0 * b := by rw [zero_mul]
         _ < a * b := by
          exact mul_lt_mul_of_pos_right aPos bPos
      exact this.ne.symm
    . have : a * b < 0 :=
        calc
        a * b = b * a := by rw [mul_comm]
        _ < 0 * a := by
          exact mul_lt_mul_of_pos_right bNeg aPos
        _ = 0 := by rw [zero_mul]
      exact this.ne
  . rcases hb' with bPos | bNeg
    . have : a * b < 0 :=
        calc
        a * b < 0 * b := by
          exact mul_lt_mul_of_pos_right aNeg bPos
        _ = 0 := by rw [zero_mul]
      exact this.ne
    . have : -(-a) < 0 := by
        calc
        - (- a) = a := by rw [neg_neg]
        _ < 0 := by exact aNeg
      have ha : 0 < (- a) := by
        exact neg_neg_iff_pos.mp this
      have : -(-b) < 0 := by
        calc
        - (- b) = b := by rw [neg_neg]
        _ < 0 := by exact bNeg
      have hb : 0 < (- b) := by
        exact neg_neg_iff_pos.mp this
      have : 0 * (- b)  < (- a) * (- b) := by
        exact mul_lt_mul_of_pos_right ha hb
      have : 0 < a * b :=
        calc
        0 = 0 * (- b) := by rw [zero_mul]
        _ < (- a) * (- b) := by exact this
        _ = a * b := by rw [neg_mul_neg]

      exact this.ne.symm
```

:::definition "sq" (parent := "properties_core")(lean := "sq")
If $`a` is a real number, then the square of $`a` is the product of $`a` with
itself: `square a = a \cdot a`.
:::

```lean "sq_nonneg"
def square (x : ℝ) := x * x

theorem sq_nonneg (x : ℝ) : 0 ≤ square x := by

  unfold square
  have hPos : ∀ {a : ℝ}, 0 < a → 0 < a * a := by
    intro a ha
    calc
    0 = 0 * a := by  rw [zero_mul]
    _ < a * a := by
        exact (mul_lt_mul_of_pos_right ha ha)

  by_cases hx : x = 0
  . -- x = 0
    subst x
    rw [mul_zero]
  . have : 0 < x ∨ x < 0 := by
      exact lt_or_gt_of_ne (Ne.symm hx)
    rcases this with xPos | xNeg
    . exact le_of_lt (hPos xPos)

    . have : (-x) * (-x) = x * x := by
        exact neg_mul_neg x x
      rw [← this]

      have : 0 < -x := by
        calc
        0 = x + (-x) := by rw [add_neg_cancel]
        _ < 0 + (-x) := by exact add_lt_add_left xNeg (-x)
        _ = -x := by rw [zero_add]

      exact le_of_lt (hPos this)
```

```lean "sq"
example (a : ℝ) : a ^ 2 = a * a := by
  exact sq a
```
We will now prove the following fact:
:::theorem "sq_pos_of_ne_zero" (parent := "properties_core")(lean := "sq_pos_of_ne_zero")
Let $`a` be a real number. if $`a ≠ 0`, then $`0 < a ^ 2`
:::

```lean "sq_pos_of_ne_zero"
example {a : ℝ} : a ≠ 0 → a ^ 2 > 0 := by
  intro h
  exact sq_pos_of_ne_zero h
```
```lean "sq_pos_of_ne_zero_proof"
theorem sq_pos_of_ne_zero {a : ℝ}:
  a ≠ 0 → 0 < a ^ 2  := by
  have hPos : ∀ a : ℝ, 0 < a → 0 < a ^ 2 := by
    intro a aPos
    calc 0
       = 0 * a := by  rw [zero_mul a]
     _ < a * a := by exact mul_lt_mul_of_pos_right aPos aPos
     _ = a ^ 2 := by rw [← sq]
  intro h
  have h' : a < 0 ∨  0 < a:= by
    exact lt_or_gt_of_ne h
  rcases h' with aNeg | aPos
  . -- a < 0
    have : - (- a) < 0 := by exact (neg_neg a).trans_lt aNeg
    have aOppPos : 0 < (- a) := by
      exact neg_neg_iff_pos.mp this
    have : 0 < (- a) ^ 2 := by
      exact hPos (-a) aOppPos
    calc 0

      < (- a) ^ 2 := by exact this
    _ = (- a) * (-a) := by exact sq (- a)
    _ = a * a := by exact neg_mul_neg a a
    _  = a ^ 2 := by exact (sq a).symm
  . -- 0 < a
    exact hPos a aPos
```

:::proof "sq_pos_of_ne_zero"
*Explanation of the Lean-specific ingredients.*

* The proof begins by establishing an auxiliary result with `have`:

  $$`\forall a \in \mathbb R, \; 0 < a \Longrightarrow 0 < a^2.`

  This lemma is named `hPos` and is used later in both cases of the proof.
  By proving it once, we avoid repeating the same argument.

* The tactic `intro` is used twice in this proof.
  * The first occurrence, `intro a` introduces the universally quantified
    variable in the proof of `hPos`.

  * The second occurrence, `intro h` introduces the assumption
    `h : a ≠ 0` of the implication `a ≠ 0 → 0 < a ^ 2`.
    After this command, the goal is simply `0 < a ^ 2`.

* From the hypothesis `h : a ≠ 0`, the theorem `lt_or_gt_of_ne h`
  produces the disjunction `a < 0 ∨ 0 < a.`
  Thus Lean has reduced the problem to the two possible signs of a
  nonzero real number.

* The command `rcases h` with `aNeg | aPos` performs *case analysis* on
  the disjunction.

  The hypothesis `h' : a < 0 ∨ 0 < a` has the logical form `P ∨ Q`.
  To prove a statement from a disjunction, one must show that it follows
  from either alternative.

  The command `rcases` therefore creates two separate goals.

    * In the first goal, Lean assumes the left-hand alternative
    `aNeg : a < 0`  and asks us to prove `0 < a ^ 2`.

    * In the second goal, Lean assumes the right-hand alternative
    `aPos : 0 < a` and again asks us to prove `0 < a ^ 2`.

  Once both cases have been completed, Lean concludes that the theorem
  holds regardless of which alternative of the disjunction is true.

  * The second case is immediate.
    Since we already proved the auxiliary lemma  `hPos`,
    the command `exact hPos a aPos` simply applies that lemma.

  *  The first case is more interesting.

    We know `a < 0`, but the auxiliary lemma requires a _positive_ number.
    The idea is therefore to apply the lemma to `-a`.

  * The line
    `have : -(-a) < 0 := by exact (neg_neg a).trans_lt aNega`
    uses the method `trans_lt`.
    If `h_1 : x = y` and `h_2 : y < z`, then `h1.trans_lt h2`
    produces the inequality `x < z`.

  In this proof, `neg_neg a : - (-a) = a` and `aNeg : a < 0`. Therefore
  `(neg_neg a).trans_lt aNeg` proves `-(-a) < 0`.


  This is simply the transitivity of equality and inequality: since
  `- (- a) = a` and `a < 0`, it follows that `- (-a) < 0`.

* The theorem `neg_neg_iff_pos` proved earlier states that
  `- x < 0 ↔ 0 < x`.


  The notation `neg_neg_iff_pos.mp` means "apply the forward implication" of
  this equivalence. Thus `neg_neg_iff_pos.mp this` transforms
  `- (- a) < 0` into `0 < - a`.


* Since `- a` is positive, the auxiliary lemma `hPos` immediately yields
  `0 < (-a) ^ 2`.


* The final `calc` block rewrites this square until it becomes `a ^ 2`.

  * The theorem `sq (- a)` rewrites `(-a) ^ 2` as `(-a) · (-a)`.

  * The theorem `neg_mul_neg` simplifies `(-a)(-a)=a \cdot a`.

  * Finally, `(sq a).symm` rewrites `a * a` as `a ^ 2`.

  Thus we conclude `0 < a ^ 2`, completing the negative case.

* This proof illustrates two important proof techniques.

  * The command `rcases` is used to eliminate a disjunction.
    A proof of `P ∨ Q` is handled by considering the two cases separately,
    one assuming `P` and the other assuming `Q`.

  * The method `trans_lt` combines an equality with a strict inequality.

    If `h₁ : x = y` and `h₂ : y < z`, then `h₁.trans_lt h₂` proves
    `x < z`.
:::


:::corollary "sq_nonneg" (parent := "properties_core")(lean := "sq_nonneg")
If $`a ∈ ℝ`, then $`0 ≤ a ^ 2`
:::


To finish this section, we are going to prove the following fact: `0 < 1`.

:::theorem "zero_lt_one" (parent := "properties_core")(lean := "zero_lt_one")
`(0 : ℝ) < (1 : ℝ)`.
:::

```lean "zero_lt_one"
example : (0 : ℝ) < (1 : ℝ) := by
  exact zero_lt_one
```

```lean "zero_lt_one"
theorem zero_lt_one  : (0 : ℝ)  < (1 : ℝ) := by
  calc (0 : ℝ)
    < 1 ^ 2 := by exact sq_pos_of_ne_zero (one_ne_zero)
  _ = 1 * 1 := by exact sq 1
  _ = 1 := by exact one_mul 1
```

We will leave the rest of the elementary properties of real numbers as an
exercise. Let us say from now on that $`a − b` means $`a + (−b)` and that,
for $`b ≠ 0`, $`a / b` means $`a ⋅ b^{−1}`.

Likewise, we will stop indicating the product with a dot,
so that $`a b` will signify $`a · b`.

## Exercises

1. Use Lean 4 to prove in detail the following properties derived from
addition and indicate at each step which basic or previously derived properties
are used:
  * a. If $`a` and $`b` are real numbers such that $`a + b = 0`,
  then $`b = −a` (Uniqueness of the additive inverse).
  * b. If $`a` is distinct from zero, then $`−a` is also distinct from zero.
  * c.  If $`a − b = b − a`, then `a = b`.

2. Prove the following properties derived from addition and the product
(with the same recommendations as in the previous exercise):
  * a.  If $`a b = 0`, then $`a = 0` or $`b = 0`.
  * b. $`(−1)⋅a = − a`.
  * c. $`(a + b)(a − b) = a ^ 2 - b ^ 2`

3. Prove the following properties derived from the product
  (same recommendations):
  * a. If `a b = a` and $`a ≠ 0`, then $`b = 1` (Uniqueness of the neutral element).
  * b. If $`a ≠ 0`, then $`a^{−1} ≠ 0`
  * c. If $`a ≠ 0`, then $`(a^{−1})^{-1} = a`.
  * d. If $`a ≠ 0` and $`b ≠ 0`, then $`(ab)^{−1} = b^{-1}a^{−1}`

4. Prove the following properties derived from addition,
the product, and order:
  * a. $`0 < a` if and only if $`−a < 0` (the _if and only if_
  signifies proving both implications: if $`0 < a`, then $`−a < 0`).
  * b. If $`a < b` and $`c < d`, then $`a + c < b + d`.
  * c. $`a < b` if and only if $`−b < −a`.
  * d. If $`0 < a` and $`0 < b`, then $`0 < ab`.
  * e. If $`a < 0` and $`b < 0`, then $`0 < ab`.
  * f. If $`a < 0` and $`0 < b`, then $`ab < 0`.
  * g. If $`0 < a`, `0 < b`, and $`a < `b, then `a² < b²`
  * i. If `a² + b² = 0`, then `a` and `b` are zero.

```lean "end BasicProperties"
end BasicProperties
```
