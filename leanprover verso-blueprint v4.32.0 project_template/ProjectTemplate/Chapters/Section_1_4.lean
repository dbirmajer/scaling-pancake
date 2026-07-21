import Mathlib.Data.Nat.Notation
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

import Verso
import VersoManual
import VersoBlueprint

open Verso.Genre
open Verso.Genre.Manual
open Informal


#doc (Manual) "Definitions by Induction" =>

-- import Mathlib.Data.Nat.Notation
-- import Mathlib.Data.Real.Basic

-- import VersoManual
-- import TextbookTemplate.Meta.Lean
-- import TextbookTemplate.Papers
-- import Mathlib.Tactic


#doc (Manual) "Definitions by Induction" =>

:::group "definitions_induction"
Core statements about addition on real numbers.
:::

```lean "open DefinitionsByInduction"
namespace DefinitionsByInduction
```
We are going to group in this paragraph certain definitions of concepts that
presuppose the notion of natural number and we will see how,
from the point of view we are developing,
certain logical difficulties appear in the elementary or "naive"
definitions of these concepts, difficulties that we will partially overcome
for now and definitively in the next chapter.

We will begin with the definition of powers with natural exponents.

_If $`a` is any real number and $`n` is a natural number,
we know that $`a ^ n` means the product of a by itself $`n` times._

But what does "$`n` times" mean if $`n` is any natural number?
This question can cause surprise; everyone knows what $`4` times,
$`5` times, etc., means.
But if we think about what our definition of natural number is,
the surprise may disappear.
For us, a natural number is (see *exercise 4* of the previous paragraph) a
real number that belongs to all inductive subsets of ℝ.

And that is all we know about the natural number (besides what we have
already proven in the previous paragraph).

Then, while it is clear what $`a^4` or $`a ^ {18}` is,
to be sure that we know what $`a^n` is for every natural $`n` we must look
for another way.

The way, as always, is the principle of induction.
If we want to define $`a^n` for every natural $`a`,
let's define it for $`n = 1` in the obvious way:
$$`a^1 = a (1)`
 and then, assuming that we have defined it for a certain natural $`n`,
 let's define it for $`n + 1` in the following, and also obvious, way:
$$`a^{n+1} = a^n · a  (2)`

In this way we fulfill having defined $`a^n` for all natural numbers.
More precisely, if $`P(n)` is the statement "$`a^n` is defined,"
then $`P(1)` is true by $`(1)` and, assuming $`P(n)` is true, $`P(n+1)`
results true by $`(2)`.

Then, by *Corollary 1.4.*, $`P(n)` is true for all natural $`n`,
which is what we wanted.

At the risk of wearying the reader, we are going to formulate again the
routine question: "what does it mean to be well-defined?"
We must confess that we cannot answer that question for now,
something we will do in the appendix of the next chapter.
Meanwhile, we appeal to your good will.
Having already defined the power with natural exponent,
we prove its main properties:

:::proposition "prop_1.11"
Let $`a` be any real number and let $`m` and $`n` be any natural numbers.
Then:
  * a) $`a^{m + n} = a^m ⋅ a^n`

  * b) $`(a^m)^n =a^{m⋅n}`
:::
■■■■■■■■■■■■■■■■■■■■■■■■■■■■■■■■

:::proof "prop_1.11"
* a) We consider the following statement:
$$`P(n) : a^{m + n} \text{ is equal to } a^m ⋅ a^n`
whatever the natural number $`m`"
:::

:::proposition  "prop_1.12" (tags := "Bernoulli's Inequality")(parent := "definitions_induction")(lean := "zero_lt_one")
If $`h` is a real number greater than $`−1`,
then for every natural number n it holds:
$$`(1 + h)^n ≥ 1 +nh`.
:::


:::proof "prop_1.12"
* *Explanation of the Lean-specific ingredients*

* The command by linarith proves goals that follow from linear equalities and inequalities. In this proof, the assumption is \(h > -1\), and we need to show
$$`0 \leq 1 + h.`
Mathematically, adding $`1` to both sides of $`h > -1` gives
$`h + 1 > 0`, hence $`0 \leq 1 + h`.

* This is linear arithmetic: \(h\) occurs only to the first power,
with no terms such as $`h^2` or products involving variables.
Therefore `Lean` can find this consequence automatically with by
`linarith`.

* The command `by positivity` proves that an expression is nonnegative
or positive by examining its structure. It is used to establish
$$`0 \leq n h^2`.
Lean knows that $`n \geq 0`, because $`n` is a natural number and is
coerced to a real number. It also knows that
$`h^2 \geq 0` because every square is nonnegative.
Since the product of two nonnegative real numbers is nonnegative,
it concludes \(0 \leq n h^2\). Thus by positivity avoids proving
these facts manually.

* The commands `rw [Nat.cast_add, Nat.cast_one]` handle the conversion
from natural numbers to real numbers. Lean distinguishes
$`\uparrow (n + 1)` from $`\uparrow n + 1`.

The lemma `Nat.cast_add` rewrites $`\uparrow (n + 1)` as
$`\uparrow n + \uparrow 1`, and `Nat.cast_one rewrites`
$`\uparrow 1` as $`1` in ℝ.
After these rewrites, Lean can see that the two sides of the
final equality are the same.                                                ■■■■■■■■■■■■■■■■■■■■■■■■■■■■■■■■
:::

```lean "prop_1.12"
lemma bernoulli_inequality (h : ℝ) (n : ℕ)
    (q : h > -1) :
    (1 + h) ^ n ≥ 1 + n * h := by
  induction n with
  | zero =>
      norm_num
  | succ n ih =>
      have hnonneg : 0 ≤ 1 + h := by
        linarith
      calc
        (1 + h) ^ (n + 1)
            = (1 + h) ^ n * (1 + h) := by
                rw [pow_succ]
        _ ≥ (1 + (n : ℝ) * h) * (1 + h) := by
              exact mul_le_mul_of_nonneg_right ih hnonneg
        _ = 1 + (n + 1) * h + n * h^2 := by
              ring
        _ ≥ 1 + (n + 1) * h := by
              have hsq : 0 ≤ n * h ^ 2 := by
                exact mul_nonneg
                  (Nat.cast_nonneg n) (sq_nonneg h)
              simpa [add_zero] using
              add_le_add_right hsq (1 + (n + 1) * h)
        _ = 1 + ↑(n + 1) * h := by
          rw [Nat.cast_add, Nat.cast_one]
```

(Question: where have we used the hypothesis $`h > −1`?)

We are now going to introduce a concept that we will return to in much more
detail in *Chapter 3* and it is that of sequence;
by a sequence we mean an assignment to each natural number $`n` of a real
number that we will indicate as $`a_n`. The sequence is usually written:
$$`a_1, a_2, a_3, … ,a_n, …`

 For example, if to each natural number $`n` we assign its square,
 we obtain the sequence given by $`a_n = n^2` and which is written:
$$`1, 4, 9, 16, 25,…,n^2`

As another example, let us consider the assignment to each natural $`n` of
the real number $`a_n = (−1)^n`. This gives us the sequence:
$$`1, −1 , 1, −1, 1, … ,(−1)^n,…`

As a final example, let us consider the assignment to each natural number
$`n` of the real number $`a_n = ⅟{n}`. This gives us the sequence:
$$`1, ⅟{2}, ⅟{3}, ⅟{4}, … , ⅟{n} ,…,`

If we now have a determined sequence $`a_0, a_1, a_2 ,…,a_n`,
we want to define the sum of the first $`n` terms of said sequence,
something we will indicate in the form:
$$`a_0 + a_1 + a_2 + ⋯ + a_n`
​or also, in the more compact and precise form:
$$`∑_{k=1}^n a_k`
 (read: "sum from $`k=1` to $`k=n` of the $`a_k`").

Since we want to define the sum of the first $`n` terms of the sequence and
as we want to do it for every natural $`n`, there is only one way to do it.
Yes, you guessed it, _induction_. We define first:
$$`∑_{k=0}^0 a_k = a_0`

(what else could it be?) and then, assuming that we have defined:

$$`∑_{k=0}^n a_k`

we define:
$$`∑_{k=0}^{n+1} a_k = (∑_{k=0}^n a_ k)+ a_{n+1}`
​and the principle of induction assures us that

$$`∑_{k=0}^n a_k`
​
 is defined for every natural $`n`. Thus, for example:

$$`∑_{k=0}^2 a_k = (∑_{k=0}^1 a_k) + a_2  = (∑_{k=0}^0 a_k + a_1) + a_2 = a_0 + a_1 + a_2.`
​
Once the concept of "sum of n terms" is defined for every natural number
$`n`, we can prove various formulas that are usually a typical application
of the principle of induction.
As an example, we consider the sequence given by $`a_n = n`.
In this case:
$$`∑_{k=0} a_k`
​is none other than:
$$`∑_{k = 0}^n k,`
or, if the reader prefers the other notation, $`0 + 1 + 2 + ⋯ + n`.

:::theorem "triangular_numbers"
We are going to prove that:
$$`∑_{k = 0}^n k = n(n+1)/2`
for every natural $`n`, that is, in the other notation,
$`1 + 2 + ⋯ + n = n(n+1)/2`.
:::

```lean "triangular_numbers"
theorem sum_eq_formula (n : Nat) :
   2 * (∑ i ∈ Finset.range (n + 1), i) = n * (n + 1) := by
  induction n with
  | zero => -- Base case: n = 0
    -- Goal reduces to: 2 * 0 = 0
    rfl
  | succ n ih =>
    -- Inductive step: P(n) => P(succ n)
    -- Lean gives us the induction hypothesis `ih` for `n`
    -- Apply `Finset.sum_range_succ` to pull off the last
    -- element
    -- Distribute multiplication over addition
    -- and apply the inductive hypothesis

    rw [Finset.sum_range_succ, Nat.mul_add, ih]
    -- Simplify
    ring
```
# Exercises

1. Prove that if $`a` and $`b` are any real numbers,
  then for every natural number $`n` it holds:
$$`(a⋅b)^n = a^n⋅b^n`
(Use induction and $`ℐr{P_1}`).

2. Prove that if $`0 < a < b`, then $`a ^ n < b ^ n`
  for every natural $`n ≥ 1`.

```lean "S_3_ex_2"
example (a : ℝ) (n : ℕ) (ha : 1 < a) (hn : 1 ≤ n) :
    ∀ s : ℝ, a ≤ s → a ≤ s ^ n := by
  intro s hs
  have hs1 : 1 ≤ s := by
    linarith
  have hpow : s ^ 1 ≤ s ^ n := by
    exact pow_le_pow_right₀ hs1 hn
  have hs_le : s ≤ s ^ n := by
    simpa using hpow
  linarith
```

3.
  * a) Prove that if $`a ≠ 0`, then $`a^n ≠ 0`
for every natural $`n` (Induction).
  * b) Prove that if $`a ≠ 0`, then $`(a^n)^{−1} = (a^{−1})^n`
  for every natural $`n` (Use *Exercise 1* to calculate
  $`(a^{−1})^n ⋅ a^n)`.

  * c) Prove that if $`a` and $`b` are any real numbers and $`b ≠ 0`,
  then:
$$`(a/b)^n = a^n/b^n`
 for every natural $`n`. (Use _a)_ and _b)_)
.

  * d) Prove that if $`a>1` and $`n ∈ N`, then $`a^n > 1`$.
  Deduce that if $`m` and $`n` are natural and $`n < m`, then
  $`a^n < a^m`.
  * e) What happens if $`0 < a <1`? (Use _d)_) and $`1/a > 1`)

4.
  * a) Let $`a_0, a_1, …, a_n,…` and $`b_0, b_1, …, b_n,…`
be any two sequences.
Prove that for every natural number $`n` it holds:
$$`∑_{k=0}^n(a_k+b_k) = ∑_{k=0}^n a_k + ∑_{k=0}^n b_k`
(Induction)

  * b) Prove that if $`c` is any real number,
  then for every natural number `n` it holds:
$$`∑_{k=0}^n ca_k = c∑_{k=0}^n a_k`
(Also by Induction)

5. Let `$n_0` be any natural number and
$`a_0, a_1,\dots,a_n,\dots` a sequence.
We define inductively:

$$`
\sum_{k=n_0}^{n} a_k \qquad (n \ge n_0)
`
in the following manner:

* (i)
$`
\sum_{k=n_0}^{n_0} a_k = a_{n_0}.
`

* (ii)
$$`
\sum_{k=n_0}^{n+1} a_k
 =
\left(\sum_{k=n_0}^{n} a_k\right)+a_{n+1}.
`
  * a) Show that: $`∑_{k=n_0}^n a_k`
  is defined for every natural $`n ≥ n_0` .
  (Use exercise 3 of paragraph 1.3)
  * b) Prove that if $`n > n_0`, then
$$`
\sum_{k=0}^{n} a_k = \sum_{k=1}^{n_0} a_k + \sum_{k=n_0+1}^{n} a_k .
`
(Induction on $`n`).

* c) Prove that if $`n > n_0`, then
$$`
\sum_{k=n_0}^{n} a_k
 =
\sum_{k=1}^{\,n-n_0+1} a_{k+n_0-1}.
`
(Induction on $`n`).

* d) For a sequence $`a_0, a_1, … ,a_n,…` define
$`\sum_{k=0}^{n} a_k` and prove
$$`
\sum_{k=1}^{n} a_k
 =
\sum_{k=0}^{n-1} a_{k+1}.
`

6. Prove by induction the following statements:
  * (a)
$`
\sum_{k=1}^{n} k^2
 =
\frac{n(n+1)(2n+1)}{6}.
`

  * (b)
$`
\sum_{k=0}^{n} r^k
 =
\frac{r^{\,n+1}-1}{r-1},
\qquad (r\ne 1).
`

  * (c)
$`2^n > n^2
\quad \text{for all } n\ge 4.
`

  * (d)
$`n^3 > 4n^2 + 3n + 1
\quad \text{for all } n\ge 5.
`
```lean "end DefinitionsByInduction"
end DefinitionsByInduction
```
