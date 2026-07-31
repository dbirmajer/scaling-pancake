import Mathlib.Data.Nat.Notation
import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Factorial.Basic

import Mathlib.Tactic

--import Mathlib.Tactic.Ring
--import Mathlib.Tactic.LinearCombination
import Mathlib.Data.Rat.Init


import Verso
import VersoManual
import VersoBlueprint

open Verso.Genre
open Verso.Genre.Manual
open Informal


#doc (Manual) "The Rational Numbers" =>

```lean "open Rationals"
namespace Rationals
```

:::definition "def_1.17"
A real number $`a` is said to be a rational number if there exist integers
$`p` and $`q ≠ 0` such that:
$`a = \frac{p}{q}, \; \text{ that is } a = p \cdot q^{-1}.`
:::

The set of rational numbers will be denoted by ℚ.

```lean "def_1.17 alt"
abbrev NonzeroInt := {q : ℤ // q ≠ 0}

def NonZ := { q : ℤ | q ≠ 0}

def isRational (x : ℝ) : Prop :=
  ∃ (p : ℤ) (q : NonZ),
    x = (p : ℝ) / (q : ℝ)
```
In another form, a real number is rational when it can be written as a
quotient of integers.

                                    ◇◇◇◇◇◇◇◇◇◇◇◇◇◇◇◇◇◇◇◇◇◇◇◇◇◇◇◇◇◇◇◇◇◇◇◇◇◇◇◇◇◇

The following Proposition proves an elementary property of operations between
rational numbers, showing at the same time how those operations are performed.



:::lemma_ "prop_1.18 sum"
Let $`x` and $`y` be rational numbers. Then $`x + y`
 is a rational number.
:::

Here is a Lean formalization of this statement using Lean’s built-in
rational-number type ℚ.

```lean "prop_1.18"
example (x y : ℚ) : ∃ r : ℚ, x + y = r := by
  use (x + y)
```

```lean "prop_1.18 sum"
theorem sum_of_rationals_is_rational
  {x y : ℝ}
  (hx : isRational x)
  (hy : isRational y) : isRational (x + y) := by

  -- Step 1: Extract the numerator, denominator,
  -- and properties for x
  rcases hx with ⟨p1, ⟨q1, q1_nz⟩, hx_eq⟩

  -- Step 2: Extract the numerator, denominator,
  -- and properties for y
  rcases hy with ⟨p2, ⟨q2, q2_nz⟩, hy_eq⟩

  -- Step 3: Provide the explicitly computed numerator
  -- and denominator witnesses for (x + y)
  -- The common denominator fraction template is:
  let q_prod : NonzeroInt :=
    ⟨q1 * q2, mul_ne_zero  q1_nz q2_nz⟩
  use (p1 * q2 + p2 * q1), q_prod
  rw [hx_eq, hy_eq]

  change
  (p1 : ℝ) / (q1 : ℝ) + (p2 : ℝ) / (q2 : ℝ) =
    ((p1 * q2 + p2 * q1 : ℤ) : ℝ) /
      ((q1 * q2 : ℤ) : ℝ)

  have hq1 : (q1 : ℝ) ≠ 0 := by
    exact_mod_cast q1_nz

  have hq2 : (q2 : ℝ) ≠ 0 := by
    exact_mod_cast q2_nz

  field_simp [hq1, hq2]
  push_cast
  ring
```

:::proof "prop_1.18 sum"
Explanation of the Lean-specific ingredients.

* The command `rcases hx with ⟨p1, ⟨q1, q1_nz⟩, hx_eq⟩` takes apart both
the existential proof `hx` and the `NonzeroInt` subtype witness at once.
It produces:

$$`p_1 : ℤ, q_1 :\ ℤ, q_1 ≠ 0, \text{ and }  x=\frac{p_1}{q_1}.`
The nested pattern `⟨q1, q1_nz⟩` extracts the integer stored in the subtype
and its proof that the integer is nonzero.

* The command `let` introduces a local definition. Thus `q1` is a readable
name for the integer inside `q1_st`, while `q1_nz` names its proof of
nonzeroness.

* The expression `⟨q1 * q2, mul_ne_zero q1_nz q2_nz⟩`
constructs a `NonzeroInt`.
Its value is $`q_1q_2`, and `mul_ne_zero q1_nz q2_nz` proves that this
product is nonzero. (See {uses "mul_ne_zero"}[])

* The command use supplies witnesses for the two existential quantifiers in Rational (x + y). The witnesses are the numerator
$`p_1q_2+p_2q_1` and the denominator $`q_1q_2`.

* The command `rw [hx_eq, hy_eq]` replaces $`x` and $`y` by their
rational-fraction expressions.

* The command `change` replaces the current goal with a definitionally
equal but clearer version. In particular, it unfolds the subtype
denominator and makes every integer-to-real coercion explicit.

* The command `exact_mod_cast q1_nz` converts the integer fact
$`q_1\ne 0` into the real-number fact
`(q_1:\mathbb{R})\ne 0`.

* The tactic `field_simp [hq1, hq2]` clears the nonzero denominators
$`q_1` and $`q_2`.
It reduces the fraction identity to an equality involving addition
and multiplication only.

* Finally, `push_cast` rewrites casts of integer sums and products into
sums and products of real casts, and ring proves the resulting
polynomial identity.
:::


:::lemma_ "prop_1.18 prod"
Let $`x` and $`y` be rational numbers. Then $` x · y`
 is a rational number.
:::

Here is a Lean formalization of this statement using Lean’s built-in
rational-number type ℚ.

```lean "prop_1.18"
example (x y : ℚ) : ∃ r : ℚ, x * y = r := by
  use (x * y)
```

:::proof "prop_1.18 prod"
Below ( (See {uses "prop_1.18 prod_proof"}[]) we give a `Lean` proof.
:::

```lean "prop_1.18 prod_proof"
theorem prod_of_rationals_is_rational
  {x y : ℝ}
  (hx : isRational x)
  (hy : isRational y) : isRational (x * y) := by

  -- Step 1: Extract the numerator, denominator,
  -- and properties for x
  rcases hx with ⟨p1, ⟨q1, q1_nz⟩, hx_eq⟩

  -- Step 2: Extract the numerator, denominator,
  -- and properties for y
  rcases hy with ⟨p2, ⟨q2, q2_nz⟩, hy_eq⟩

  -- Step 3: Provide the explicitly computed numerator
  -- and denominator witnesses for (x + y)
  -- The common denominator fraction template is:
  let q_prod : NonzeroInt :=
    ⟨q1 * q2, mul_ne_zero  q1_nz q2_nz⟩

  use (p1 * p2), q_prod

  rw [hx_eq, hy_eq]

  change
  ((p1 : ℝ) / (q1 : ℝ)) * ((p2 : ℝ) / (q2 : ℝ)) =
    ((p1 *  p2 : ℤ) : ℝ) / ((q1 * q2 : ℤ) : ℝ)

  push_cast
  ring
```


Naturally, every integer $`m` is a rational number since $`m = \frac{m}{1}`.
Then we have the inclusions:

$$`\mathbb{N} \subset \mathbb{Z} \subset \mathbb{Q} \subset \mathbb{R}`

The previous Propositions have a very simple consequence to demonstrate and it
is that between two rational numbers there is always another rational number.
More precisely:

:::lemma_ "prop_1.19"
If $`x` and $`y` are rational numbers such that $`x < y`,
then $`\frac{x+y}{2}` is also rational and furthermore:
$$`x < \frac{x+y}{2} < y`
:::

:::proof "prop_1.19"
We divide the proof in two components, firts we prove that $`\frac{x + y}{2}`
is a rational number, the we prove the inequality $`x < \frac{x + y}{2} < y`.
:::

```lean "prop_1.19 part1"
example (x y : ℝ)
  (hx : Rational x)
  (hy : Rational y) : Rational ((x + y) / 2) := by
  have h2 : Rational (1 / 2) := by
    unfold Rational
    use (1 : ℤ)
    use (⟨2, by norm_num⟩ : NonzeroInt)
    ring
  have hxy : Rational (x + y) := by
    exact sum_of_rationals_is_rational hx hy
  have : Rational ((1 / 2)  * (x + y)) := by
    exact prod_of_rationals_is_rational h2 hxy
  have :  (x + y) / 2 = (1 / 2)  * (x + y) := by ring
  rw [this]
  assumption
```

```lean "prop_1.19 part2"
example (x y : ℝ)
  (hxy : x < y):
    x < (x + y) / 2 ∧ (x + y) / 2 < y := by
    constructor
    . have : x + x < y + x := by
        exact add_lt_add_left hxy x
      have : (x + x) * (1 / 2) < (y + x) * (1 / 2) := by
        exact mul_lt_mul_of_pos_right this (by norm_num)
      calc
      x = (x + x) * (1 / 2) := by ring
       _ < (y + x) * (1 / 2) := by exact this
       _ = (x + y) / 2 := by ring
    . have : x + y < y + y := by
        exact add_lt_add_left hxy y
      have : (x + y) * (1 / 2) < (y + y) * (1 / 2) := by
        exact mul_lt_mul_of_pos_right this (by norm_num)
      calc (x + y) / 2
        = (x + y) * (1/2) := by ring
      _ < (y + y) * (1 / 2) := by exact this
      _ = y := by ring
```

It is easy to convince oneself, from this Proposition,
that between two rational numbers there are infinite rational numbers.

Since between $`a` and $`b` there is one which is $`\frac{a+b}{2}`,
between $`a` and $`\frac{a+b}{2}` there is another which is
$`\frac{1}{2} \left( a + \frac{a+b}{2} \right)`, etc.

Reiterating this procedure, we realize the truth of the affirmation made.

We are not asked here for a demonstration of this fact from basic properties,
since the concept of "infinite" used has been intuitive.

It is perhaps surprising the precision that can be given to that concept,
something we will do in the next chapter.

```lean "end Rationals"
end Rationals
```
# Exercises

1.
  * a) Prove that a rational number $`a = \frac{p}{q}` ($`p, q \in \mathbb{Z}`)
is an integer if and only if $` q ∣ p`.

  * b) State which of the following numbers are integers and which are not (and prove it):
    $$`\frac{1}{2};\; \frac{4}{2};\; \frac{3}{7};\; \frac{5}{3};\; \frac{3}{6}.`


2. Prove that if $`a \in \mathbb{Q}` and $`a \neq 0`,
then $`a^m \in \mathbb{Q}` for every $`m \in \mathbb{Z}`.
(Do it first for $`m \in \mathbb{N}` and then consider cases).


3.
  * $`\star a)` Prove that every rational number can be written as the quotient of
  an integer by a natural number
  * $`\star\; b)` Let $`a = \frac{p}{q}` and $`b = \frac{s}{t}` written according to a)
    (that is $`p, s \in \mathbb{Z}, \ q, t \in \mathbb{N}`).
    Prove that $`a < b` if and only if $`pt < qs`.
  *  $`\star c)` Give an example of rational numbers $`a = \frac{p}{q}`
    and $`b = \frac{s}{t}` (with $`p, q, s` and $`t \in \mathbb{Z}`)
    such that $`a < b` but $`pt > qs`.

4.
  * $`\bullet a)` Calculate:
  $$`\frac{2}{7} + \frac{3}{5}, \quad \frac{-1}{4} \cdot \left( \frac{-5}{3} \right),
   \quad \frac{2/5}{3/4} .`
  * $`\bullet\; b)` Prove that
  $`\frac{pt}{qt} = \frac{p}{q}` for any $`p, q, t \in \mathbb{Z}.`
