import Mathlib.Data.Nat.Notation
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring

import Verso
import VersoManual
import VersoBlueprint

open Verso.Genre
open Verso.Genre.Manual
open Informal


#doc (Manual) "The Natural Numbers" =>

:::group "natural_numbers"
Core statements about addition on real numbers.
:::

```lean "open NaturalNumbers"
namespace NaturalNumbers
```
We are now going to begin to distinguish certain subsets of real numbers.
 The first of them is that of the natural numbers,
 which we could define as those numbers we use for counting,
 $`0, 1, 2, 3, 4`, etc.

Therefore we can ask: What are $`2, 3` and $`4`?

With this spirit, so far we are only sure that there are two real numbers,
the $`0` and the $`1` (Observe that they are indeed two, property $`ℐrm{P3}`
explicitly says that 1 is distinct from zero).

The solution to this problem is simple; by definition $`2 = 1 + 1`
and this new number is distinct from the ones already known.

In effect, we already know that $`1 > 0`, then by $`\;\mathrm{O_3}`
​it is $`1 + 1 > 1 + 0`$, or what is the same according to our definition
 and $`\mathrm{S_3}: 2 > 1`.

Then, by $`\mathrm{O_1}` , $`2` is distinct from $`1`.
Now, since $`2 > 1` and $`1 > 0`, then by  $`\;\mathrm{O_2}`
​it is $`2 > 0` and then, by $`O_1`, 2 is distinct from 0.

Defining $`3 = 2 + 1` we can repeat the previous reasoning and see that
$`3` is a fourth real number distinct from $`0, 1` and $`2`.

We see that in this way we can define as many natural numbers as we want.

The second objection is more serious; our definition has remained as
follows:
the set of natural numbers is the set formed by the numbers
$`1, 1 + 1, 1 + 1 + 1, 1 + 1 + 1 + 1`, etc.
 Now then, what does "etc." mean?

For now let's return to natural numbers.

If we could find some property that characterized the natural numbers, that is,
a property that was satisfied by the natural numbers and only by them,
then we could take said property as the definition of the natural numbers.

There is a property that they evidently satisfy: if $`n` is a natural number,
then $`n + 1` is also a natural number.

But this property is not definitory, since the set of the numbers
$`2, 3, 4, 5,` etc. also satisfies it; we then add the property that
$`1` be a natural number. These two properties together also do not define
the natural numbers but rather broad sets of real numbers to which,
for brevity, we now give a name:


:::definition "def_1.1"
Observe that in the basic properties
of real numbers only the existence of two real numbers is stated,
the number $`0` and the number $`1`
(mentioned in {uses "S3"}[] and {uses "P3"}[] respectively).
From them we will contruct the Natural numbers

A subset $`A` of the real numbers is said to be inductive if it has the
following properties:

  * $`\textrm{I1.}` The number $`0` belongs to $`A` ($`0 ∈ A`).
  * $`\textrm{I2.}` If any real number $`x` belongs to $`A`, then the real number
  $`x + 1` also belongs to $`A`.
:::

```lean "def_1.1"
def Inductive (A : Set ℝ) : Prop :=
  (1 : ℝ) ∈ A ∧ (∀ {x : ℝ}, x ∈ A → (x + 1) ∈ A)
```
⋄⋄⋄⋄⋄⋄⋄⋄⋄⋄⋄⋄⋄⋄⋄⋄⋄⋄⋄⋄⋄⋄⋄⋄

:::definition "1.2"
We will call the set of natural numbers, and we will indicate it with ℕ,
the subset of real numbers characterized by the following properties:
  * $`\mathrm{N_1.}` ℕ is inductive.
  * $`\mathrm{N_2.}` If $`A` is any inductive subset of real numbers,
  then $`ℕ ⊆ A`.
:::

```lean "def_1.2"
def isNatural (x : ℝ) : Prop :=
  ∀ {A}, Inductive A → x ∈ A

def Natural : Set ℝ := {x | isNatural x}

--   For x : ℝ, x ∈ Natural is equivalent to isNatural x
example {x : ℝ} :
  x ∈ Natural ↔ isNatural x := by
  rfl

example {x : ℝ} :
  x ∈ Natural ↔ isNatural x := by
  constructor
  . intro hx
    exact hx
  . intro hx
    exact hx

-- By contrast, `n : Natural` means that `n` is an
-- element of the subtype determined by the set `Natural`:
-- n : {x : ℝ // x ∈ Natural}
-- So it packages both pieces together:
-- `n : ℝ`        -- the underlying real number
-- `n.property`        -- a proof that (n : ℝ) ∈ Natural

example {x} (hx : x ∈ Natural) : Natural :=
  by exact ⟨x, hx⟩

example (n : Natural) : (n : ℝ) ∈ Natural := by
  exact n.property
```
:::lemma_ "0 is Natural"
$`1 ∈ Natural`
:::
```lean "0 is Natural"
theorem one_is_natural : (1 : ℝ) ∈ Natural := by
  intro A hA
  exact hA.left
```

```lean "succ is Natural"
theorem succ_is_natural :
  ∀ {n : ℝ}, n ∈ Natural → (n + 1) ∈ Natural := by
    intro n hn A hA
    exact hA.right (hn hA)
```
◇◇◇◇◇◇◇◇◇◇◇◇◇◇◇◇◇◇◇◇◇

The first property is so easy to demonstrate that it may be hard to
understand why it is given a name (although we will soon see its enormous
utility):

:::theorem "thm_1.13" (tags := "Principle of Induction")
If $`H ⊆ ℝ` is inductive, then $`ℕ ⊆ H`.
If $`H` is an inductive subset of ℕ, then $`H = ℕ`.
:::

:::proof "thm_1.13"
By definition, ℕ is a subset of any inductive subset of ℝ.

That $`H` is a subset of ℕ means $`H ⊆ ℕ`.
But being $`H` inductive, then $`N ⊆ H` by $`ℐrm{N_2}`.
From the two inclusions $`H ⊆ N` and $`N ⊆ H` we conclude $`H = N`. $`□`
:::

```lean "thm_1.13_proof"
-- The set of natural numbers is a subset of every
-- inductive set.
theorem natural_subset_of_inductive
  (h : Inductive H) : Natural ⊆ H := by
  intro n hn
  exact hn h

-- iIf an inductive set `H` is contained in `Natural`,
-- then it equals `Natural`.
theorem eq_natural_of_subset_of_inductive {H}
  (hH : H ⊆ Natural)
  (hI : Inductive H) : H = Natural := by
    apply Set.Subset.antisymm
    . exact hH
    . exact natural_subset_of_inductive  hI
```

There is a popular form of the _principle of induction_ that we are going
to indicate now.

:::corollary "cor_1.4"(tags := "Induction Principle")
Suppose that for each natural number $`n` we have a statement $`P(n)` about it
in such a way that the two following conditions are verified:
* The statement $`P(1)` is true.
* For every natural number $`n` the following occurs: if we suppose that
$`P(n)` is true we can then deduce that $`P(n+1)` is also true.

In that case the statement $`P(n)` is true for every natural
number $`n`.
:::

:::proof "cor_1.4"
Proof: Consider the following set:

$$`H = {n ∈ N : P(n) \; \text{is true}}`
(read _$`H` equal to the set of the $`n` belonging to the naturals such
that $`P(n)` is true_).

In the first place, by its own construction, $`H` is a subset of ℕ;
in effect, the elements of $`H` are those natural numbers $`n` for which
$`P(n)` is true, that is, the elements of $`H` are all natural numbers.

 But furthermore $`H` is inductive; in effect, $`1 ∈ H` because by
 hypothesis $`P(1)` is true and, on the other hand,
 if $`n ∈ H` then $`P(n)` is true; by hypothesis,
 that implies that $`P(n + 1)` is true, or what is the same $`n + 1 ∈ H`.

Being $`H` an inductive subset of ℕ, *Theorem 1.3.* tells us that $`H = ℕ`.
But this last statement means exactly that $`P(n)` is true for all `n ∈ ℕ`.
:::

```lean "Principle of Induction"
#print Natural

theorem pple_of_induction {P : ℝ → Prop}
  (h1 : P 1)
  (hs : ∀ {x : ℝ}, P x → P (x + 1)) :
    Natural ⊆ {x | P x} := by
      let S := {x : ℝ | P x}
      have : Inductive S := by
        unfold Inductive
        constructor
        . exact h1
        . exact hs
      change Natural ⊆ S
      exact natural_subset_of_inductive this
```

We will now use the principle of induction to prove elementary properties of
natural numbers.

:::proposition "prop_1.5 sum"
If $`n` and $`m` are natural numbers, then $`m + n` and $`m ⋅ n` are also
natural numbers.
:::
■■■■■■■■■■■■■■■■■■■■■■■■■■■■■■■■

```lean "prop_1.5 sum"
-- theorem sum_of_naturals (hn : n ∈ Natural) :
--   ∀ m, m ∈ Natural → n + m ∈ Natural := by sorry

theorem sum_of_naturals (n : Natural) :
  ∀ m : Natural, (n : ℝ) + (m : ℝ) ∈ Natural := by
  let H := {x : ℝ | n + x ∈ Natural}
  have IH : Inductive H := by
    unfold Inductive
    constructor
    . -- 1 ∈ H
      change isNatural ((n : ℝ) +  1)
      intro A hA
      have : (n : ℝ) ∈ A := by exact n.property hA
      exact hA.right this
    . -- ∀ {x : ℝ}, x ∈ H → (x + 1) ∈ H
      intro x hx
      change ((n : ℝ) + (x + (1 : ℝ))) ∈ Natural
      change (n : ℝ) + x ∈ Natural at hx
      rw [← add_assoc]
      exact succ_is_natural hx
  intro m
  have : (m : ℝ) ∈ H := by exact m.property IH
  simpa [H]

example :
  ∀ n m : Natural, (n : ℝ ) + (m : ℝ) ∈ Natural := by
  intro n m
  exact sum_of_naturals n m

def addNatural (n m : Natural) : Natural :=
  ⟨(n : ℝ) + (m : ℝ), sum_of_naturals n m⟩
```

:::proposition "prop_1.5 prod"
If $`n` and $`m` are natural numbers, then $`m + n` and $`m ⋅ n` are also
natural numbers.
:::
■■■■■■■■■■■■■■■■■■■■■■■■■■■■■■■■

```lean "prop_1.5 prod"
theorem mul_of_naturals (n : Natural) :
  ∀ m : Natural, (n : ℝ) * (m : ℝ) ∈ Natural := by
  let H := {x : ℝ | n * x ∈ Natural}
  have IH : Inductive H := by
    unfold Inductive
    constructor
    . -- 1 ∈ H
      intro A hA
      rw [mul_one]
      exact n.property hA
    . -- ∀ {x : ℝ}, x ∈ H → (x + 1) ∈ H
      intro x hx
      change ((n : ℝ) * (x + (1 : ℝ))) ∈ Natural
      rw [mul_add, mul_one]
      let nx : Natural  := ⟨(n : ℝ) * x, hx⟩
      change (nx : ℝ) + (n : ℝ) ∈ Natural
      exact (sum_of_naturals nx n)
  intro m
  exact m.property IH

example :
  ∀ n m : Natural, (n : ℝ ) + (m : ℝ) ∈ Natural := by
  intro n m
  exact sum_of_naturals n m

def mulNatural (n m : Natural) : Natural :=
  ⟨(n : ℝ) * (m : ℝ), mul_of_naturals n m⟩
```

:::proof "prop_1.5 prod"
Having done in detail the demonstration of our first affirmation,
we do more briefly the demonstration of the second.
We consider the affirmation:
$$`P(n) = \text{For every natural number } m, m \cdot n
\text{ is a natural number}`

The affirmation $`P(1)` is true since $`m \cdot 1 = m`,
which by hypothesis is a natural number.
Suppose then that the affirmation $`P(n)` is true for a certain natural
number $`n` and let's see that it implies that the affirmation
$`P(n + 1)` is true.
For that, if $`m` is any natural number then, by *Property D:*
$$`m \cdot (n + 1) = m \cdot n + m \cdot 1 = m \cdot n + m`

In this sum, the first summand $`m \cdot n` is a natural number
because we are supposing $`P(n)` is true,
and the second summand $`m` is a natural number by hypothesis.
Since we already know that the sum of natural numbers is a natural
number (it is the first part of this Proposition),
then $`m \cdot n + m` is a natural number whatever the natural number
$`m` may be. But that is to say that $`P(n + 1)` is true.

Once again we have proven the truth of $`P(1)` and that from the truth of
$`P(n)` follows the truth of $`P(n + 1)`.
Then, by *Corollary 1.4.*, $`P(n)` is true for every natural number $`n`,
which is what we wanted to demonstrate.
:::


Before demonstrating more properties of the natural numbers,
we are going to introduce a new concept:

:::definition "ge"
Given real numbers $`a` and  $`b`, we say that $`a` is
_greater than or equal_ to $`b`,
and we write $`a \ge b`, if one of the two following possibilities occurs:

  * $`\star i)` $`a` is greater than $`b`;
  * $`\star ii)` $`a` is equal to $`b`.
:::

Then, for it to be true that $`a \ge b`, it is enough that one of the two
possibilities be true (the two together cannot be).

Thus, for example, it is true that $`2 \ge 1`
(because, although it is not $`2 = 1`, it is true that $`2 > 1`)
and it is true that $`3 \ge 3` (because $`3 = 3` although it is not $`3 > 3`)
but it is not true that $`1 \ge 3` (for it is neither...

This relation has the following properties):

:::lemma_ "ge-properties"
1. If $`a \ge b` and $`b \ge a`, then $`a = b`.
2. If $`a \ge b` and $`b \ge c`, then $`a \ge c`.
3. If $`a \ge b`, then $`a + c \ge b + c` for any real number $`c`.
4. If $`a \ge b` and $`c` is greater than zero,
then $`a \cdot c \ge b \cdot c`
:::
We demonstrate only the first two and leave the remaining two as an exercise.

:::proof "ge-properties"
*Demonstration of 1:* Let $`a \ge b` mean that either $`a > b` or $`a = b`.
Since we want to prove $`a = b`, let's see that it cannot be $`a > b`.
If it were so, then it could not be $`b > a` nor $`a = b`
(by trichotomy, *O₁*) and then it would be false that $`b \ge a`.

But this is one of our hypotheses; therefore it cannot be $`a > b` and then
necessarily $`a = b`.

*Demonstration of 2:* Since $`a \ge b`, then either $`a = b` or
$`a > b` and since
$`b \ge c`, then either $`b > c` or $`b = c`.

This leaves us with four possibilities:

  * *i)* $`a = b` and $`b > c`;
  * *iii)* $`a > b` and $`b > c`;
  * *ii)* $`a = b` and $`b = c`;
  * *iv)* $`a > b` and $`b = c`.

In case i), as $`a` is the same as $`b` and $`b` is greater than $`c`,
then $`a` is greater than $`c`, $`a > c`.
But if $`a > c`, then it is true that $`a \ge c` (1).
In case ii), $`a` is $`= c` and therefore it is true that
$`a \ge c` (see note (1)).

In case iii) it results by $`O₂` that $`a > c` and therefore $`a \ge c`.
Finally, in case iv) it results $`a > c` (since $`a` is greater than $`b` and
$`b` is the same as $`c`) and therefore $`a \ge c`.
In conclusion, in all cases it results $`a \ge c`.
:::

We return now to elementary properties of natural numbers.

:::theorem "one_le_natural" (parent := "natural-numbers")(lean := "Nat.zero_le")
If $`n` is a natural number, then $`1 ≤ n`
:::

```lean "one_le_natural"
theorem one_le_natural : ∀ n : Natural, 1 ≤ (n :ℝ) := by
  sorry
```

We want now to prove the fact, intuitively clear, that if a natural number is
subtracted from a smaller natural number, the result is a natural number.
As a preliminary step, we prove the following Proposition.

:::theorem "th_1.7."
If $`n` is a natural number then either $`n = 1` or $`n - 1` is a natural
number.
:::


```lean "thm_1.7_proof"
example (n : Natural)  :
  ((n : ℝ) = 1) ∨ ((n : ℝ) - 1 ∈ Natural) := by
  sorry
```

Now we are in a position to prove the announced result:

:::theorem "prop_1.8"
If $`m` and $`n` are natural numbers and $`n < m`,
then $`m - n` is also a natural number.
:::

```lean "prop_1.8_proof"
example (n : ℕ) : n < n + 1 := by
  exact Nat.lt_succ_self n

theorem Nat.lt_succ_self (n : Nat) :
  LT.lt n (Nat.succ n) := Nat.lt_add_one _

example (n : ℕ) : n < n + 1 := by
  calc n
  _ = 0 + n  := by rw [zero_add n]
  _ < 1 + n := by  exact (add_lt_add_left zero_lt_one n)
  _ = n + 1 := by exact add_comm 1 n

protected theorem sub_sub
  (n m k : Nat) : n - m - k = n - (m + k) := by
  induction k with
  | zero => simp
  | succ k ih => rw [Nat.add_succ, Nat.sub_succ,
      Nat.add_succ, Nat.sub_succ, ih]

theorem proposition_1_8 (n m : ℕ) (h : n < m)  :
  (∃ k : ℕ, k = m - n) := by
  induction n with
  | zero => use m; rw [Nat.sub_zero m]
  | succ n ih =>
    have h' : ∃ k, k = m - n := by
      exact (ih (lt_trans (Nat.lt_succ_self n) h))
    obtain ⟨k, hk⟩ := h'
    use (k - 1)
    rw [hk, Nat.sub_sub]
```

Until now we have used induction in all our proofs of elementary properties
of ℕ. That happens because ℕ is practically defined by the principle of
induction, the only instrument to prove its first derived properties.

But as soon as some of them are proven, other properties can be derived with
those results without using, perhaps, the principle of induction in the proof.

The following Proposition is an example of it:

:::theorem "prop_1.9"
If $`n` and $`m` are natural numbers and $`n < m`, then $`m - n ∈ ℕ`,
and $`m \ge n + 1`.
:::

:::proof "prop_1.9"
{uses "prop_1.6"}[]
{uses "prop_1.8"}[]
:::

```lean "prop_1.9"
example (n m : ℕ) (h : n < m) : n + 1 ≤ m := by
  have : (∃ k  : ℕ, k = m - n) := proposition_1_8 n m h
  obtain ⟨k, hk⟩ := this
  have : 0 < k := by omega
  have : 1 ≤ k  := by exact (Nat.succ_le_of_lt this)
  have : m - n ≥ 1 := by omega
  omega
```

This theorem is in Lean 4:
```lean "prop_1.9"
example (n m : ℕ) (h : n < m) : n + 1 ≤ m := by
  exact Nat.succ_le_of_lt h
```

We are now going to prove a very important property of ℕ.

Let us first say that if $A$ is any set of real numbers,
an element $`a` of $`A` is said to be the _minimum_ of $`A` if it is
smaller than all the other elements of $`A`.

Put in another form: if $`A` is a set of real numbers,
a real number $`a` is said to be the minimum of $`A` if the two
following conditions are met:

  * $`\star i)` $`a` belongs to $`A`;
  * $`\star ii)` if $`b \in A`, then $`a \le b`
  (we put $`\le` instead of $`<` because $`b` could be $`a` itself $`^{(1)}`).

Not every set $`A \subset` ℝ has a minimum (on this we will return later)
but if we suppose $`A \subset \mathbb{N}`, the thing changes:

:::theorem "thm_1.10"
(Principle of Well-Ordering of $`\mathbb{N}`)
If $`A` is a subset of $`\mathbb{N}` and $`A` is not the empty set
then $`A` has a minimum.
:::

:::proof "thm_1.10"
We are going to make this proof by induction
(that is, using Corollary 1.4.). In the previous proofs, it was very easy to
choose $`P(n)` since it was practically given by the statement of the
corresponding Proposition.
Here instead one has to manage to construct the $`P(n)` that leads us to a
good end. It is convenient to consider the following:

$$`P(n) = \text{Every set } A \subset \mathbb{N} \text{ that contains } n
\text{ has a minimum}`
:::

```lean "thm_1.10"
def P (n : ℕ) : Prop :=
  ∀ (A : Set ℕ), n ∈ A →
    ∃ m, IsLeast A m
```

```lean "thm_1.10_proof"
lemma well_ordering' : ∀ n : ℕ, P n := by
  -- Introduce the arbitrary natural number n.
  intro n

  -- Prove the statement by induction on n.
  induction n with

  ---------------------------------------------------------
  -- Base case: n = 0
  ---------------------------------------------------------
  | zero =>
      -- Expand the definition of P.
      unfold P

      -- Let A be a subset of ℕ containing 0.
      intro A zero_in_A

      -- We claim that 0 is the least element of A.
      use 0
      constructor

      -- Show that 0 belongs to A.
      case left =>
        exact zero_in_A

      -- Show that 0 is less than or equal to every element
      --  of A.
      case right =>
        intro n _
        exact zero_le n

  ---------------------------------------------------------
    -- Inductive step
  ---------------------------------------------------------
  | succ n ih =>

      -- Expand the definition of P.
      unfold P

      -- Let A be a subset of ℕ.
      intro A

      -- Split into two cases depending on whether n
      -- belongs to A.
      by_cases nA : n ∈ A

      -----------------------------------------------------
      -- Case 1: n ∈ A
      -----------------------------------------------------
      . -- By the induction hypothesis, every subset
        -- containing n has a least element.
        have : ∃ m, IsLeast A m := by
          exact ih A nA

        -- Obtain the least element m of A.
        obtain ⟨m, hm⟩ := this

        -- Introduce the assumption that n+1 belongs to A.
        -- (It is unused in this branch.)
        intro _

        -- The same least element works.
        use m

      ------------------------------------------------------
      -- Case 2: n ∉ A
      ------------------------------------------------------
      . -- Adjoin n to A.
        let A' := A ∪ {n}

        -- Every element of A also belongs to A'.
        have a_in_A' : ∀ a ∈ A, a ∈ A' := by
          intro a pa
          exact Set.subset_union_left pa

        -- n belongs to A' by construction.
        have n_in_A' : n ∈ A' := by
          exact Or.inr rfl

        -- Apply the induction hypothesis to A'.
        have : ∃ m, IsLeast A' m := by
          exact ih A' n_in_A'

        -- Let m be the least element of A'.
        obtain ⟨m, hm⟩ := this

        -- m belongs to A'.
        have m_in_A': m ∈ A' := by
          exact hm.left

        -- Now assume that n + 1 belongs to A.
        intro succ_n_in_A

        -- Every element of A is at least m.
        have m_le_a : ∀ a ∈ A, m ≤ a := by
          intro a pa
          have : a ∈ A' := by
            exact a_in_A' a pa
          exact hm.right this

        -- Since A' = A ∪ {n}, m is either in A or equals n.
        have : (m ∈ A) ∨ (m ∈ ({n} : Set ℕ)) := by
          exact Or.symm (by simpa [A'] using m_in_A')

        -- Rewrite membership in the singleton as equality.
        have : (m ∈ A) ∨ (m = n) := by
          rcases this with hA | hN
          · exact Or.inl hA
          · have : m = n := by
              simpa using hN
            exact Or.inr this

        -- Consider the two possibilities.
        rcases this with hA | n_eq_m

        ---------------------------------------------------
        -- Subcase 2a: m ∈ A
        ---------------------------------------------------
        . -- m is already the least element of A.
          have m_le_a : ∀ a ∈ A, m ≤ a := by
            intro a pa
            have : a ∈ A' := by
              exact a_in_A' a pa
            exact hm.right this

          use m
          exact ⟨hA, m_le_a⟩

        ---------------------------------------------------
        -- Subcase 2b: m = n
        ---------------------------------------------------
        . -- Since n was assumed not to belong to A,
          -- m cannot belong to A.
          have m_not_in_A : m ∉ A := by
            rw [n_eq_m]
            exact nA

          -- Therefore every element of A is strictly
          --larger than m.
          have : ∀ a ∈ A, m < a := by
            intro a a_in_A

            have : m ≤ a := by
              exact hm.right (a_in_A' a a_in_A)

            -- m and a cannot be equal,
            -- since m ∉ A but a ∈ A.
            have : m ≠ a := by
              rintro rfl
              exact m_not_in_A a_in_A

            exact lt_of_le_of_ne (m_le_a a a_in_A) this

          -- Hence every element of A is at least m+1.
          have : ∀ a ∈ A, m + 1 ≤ a := by
            intro a a_in_A
            exact Nat.succ_le_of_lt (this a a_in_A)

          -- Replace m by n using m = n.
          have : ∀ a ∈ A, n + 1 ≤ a := by
            rw [← n_eq_m]
            exact this

          -- Conclude that n+1 is the least element of A.
          use (n + 1)
          exact ⟨succ_n_in_A, this⟩
```

# Exercises
1. Demonstrate that if $n$ and $m$ are natural numbers and $m > n$,
then $m \ge n + 1$ using only the principle of induction.

2. Demonstrate the "strong" induction principle:
suppose that for each natural number $`n` we have a statement
$`P(n)` about it such that the two following conditions are met:

  *  $`\diamond i)` $`P(1)` is true;
  *  $`\diamond ii)` If $`P(k)` is true for all $`k \le n`,
  then $`P(n + 1)` is true.

Then $`P(n)` is true for all $`n \in \mathbb{N}`
(_Suggestion_: consider the statement
$`Q(n) = ` "$`P(k)` is true for natural numbers $`k` less than or
equal to $`n`")

3. Let $`n_0` be any natural number and suppose that for each natural number
$`n` we have a statement $`P(n)` about it such that the two following conditions
are met:
  * $`\bullet i)` $`P(n_0)` is true;
  * $`\bullet ii)` if $`P(k)` is true for a certain natural $`k`,
  then $`P(k + 1)` is also true.
  Prove that $`P(n)` is true for all $`n \ge n_0`
  (_Suggestion_: consider $`Q(n) = P(n - n_0 + 1)`)

4. We recall that the intersection of a family of sets is defined as the set
formed by the elements that belong to all the sets of the given family.
We define now $`\mathbb{N}`, the set of natural numbers, as the intersection
of all inductive subsets of ℝ.

Then a real number is a natural number if and only if that number belongs to all the
inductive subsets of ℝ. Prove:
  * $`a)` With this definition, ℕ satisfies $`N_1)` and $`N_2)`


```lean "end NaturalNumbers"
end NaturalNumbers
```
