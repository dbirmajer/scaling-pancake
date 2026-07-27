import Mathlib.Data.Nat.Notation
import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Mathlib.Order.SetNotation

import Verso
import VersoManual
import VersoBlueprint

open Verso.Genre
open Verso.Genre.Manual
open Informal


#doc (Manual) "Completeness Property" =>

:::group "completeness"
Core statements about addition on real numbers.
:::

```lean "open "
namespace Completeness
```


We remind the reader that in paragraph 1.2, we had given a list of 13 basic
properties of real numbers and we had said that one property was missing for
that list to be complete (that is, so that with only those properties we could
deduce all the others).
In this paragraph, we are going to indicate which is the remaining property,
for which we need to introduce some previous notions.

Before entering properly into the subject,
let's talk about the representation of real numbers on a line.

The reader will probably have seen at some time that if on a line we arbitrarily
fix a point as 0 and another as 1, this allows us to think of each real
number as a point on the line.
It is customary to take a horizontal line and fix the
1 to the right of the 0:


To know where a rational number $`\frac{m}{n}` is represented, the segment that goes
from 0 to 1 is divided into $`n` equal parts (of length $`\frac{1}{n}` each) and
then one moves forward, starting from 0, $`m` steps to the right and there the
number $`\frac{m}{n}` is fixed.
This is if $`m` and $`n` are positive.

If the rational number is negative, it can be written as $`-\frac{m}{n}` with $`m`
and $`n` natural and then the same procedure is repeated but advancing to the left.

To represent the remaining real numbers (those that are not rational),
an approximation procedure is used that we will not describe for now.

One might wonder if the fact of being able to represent real numbers on a line
in a way that covers it completely is a basic or derived property of the set of
real numbers.

The answer is very simple: neither one nor the other.
And this for two reasons: the first is that the concept of "line"
used has not been precise; everyone knows what a line is but no one
knows how to define it (which is not so strange: it is hard to define "bitter").

And by not being able to define a line, we will hardly be able to demonstrate,
in a rigorous way, that we can represent real numbers on it.
Therefore, this fact cannot be a derived property.

And the second reason is that, to demonstrate properties of real numbers,
we do not need to appeal to that fact, as we do not need it as a basic property.

Do we abandon it then? No, in the same way that we do not stop using the word
"bitter" because we do not know how to define it.
We are going to use said representation frequently;
it will illustrate the demonstration,
it will help to better understand the demonstration,
it will even be able to suggest a demonstration,
but the demonstration itself will only be based, in the last instance,
on the basic properties of real numbers and never on the possibility of
representing them on a line.

Once the helpful role of the representation of ℝ on a line is understood,
let's move on to the topic of this paragraph.
We begin by giving some definitions:

*Definition 1.20.*
Let $`A` be any set of real numbers, that is $`A \subseteq \mathbb{R}`
A real number $`c` is said to be an *upper bound* of $`A` if it satisfies the following property: For every $`a \in A$ it holds $a \le c`

That is, a real number is an upper bound of a set when it is greater than or equal to _all_ the elements of the set.

In terms of the representation of real numbers on a line just discussed,
for a number to be an upper bound of a set means that it is to the _right_ of the set.
For example, in the drawing below, $c$ and $e$ are upper bounds of $`A` while
$`d` and $`f` are not:


Let's see more examples; suppose that $`a` and $`b` are any real numbers
such that $`a < b` and we define:

$$`
    \begin{align*}
        (a, b) &= \{x \in ℝ : a < x < b\} \\
        & \textbf{(Open interval } (a, b)) \\
        [a, b] &= \{x \in ℝ : a \le x \le b\} \\
        & \textbf{(Closed interval } [a, b])
    \end{align*}
`
which we graphically represent in the following way:


Then, for example, $`b + 1` is an upper bound of these two sets.
Indeed, if $`x \in (a, b)`, then $`a < x < b` and since $`b < b+1`,
then $`x < b + 1`, therefore $`b+1` is greater than all the elements of
$`(a, b)`. Same reasoning if $`x \in [a, b]`.

Also $`b + 2, b + \frac{1}{2}, b + \frac{3}{7}`, etc. are upper bounds of the
two sets. But there is an upper bound of the two sets that has a very important
particularity; this upper bound is $`b` itself.

Effectively it is an upper bound: if $`x \in [a, b]`, for example,
then $`a \le x \le b`, in particular $`x \le b`;
and this is the condition for being an upper bound.
The particularity to which we refer is the following: if one takes a number
less than $`b`, then it is clear from the geometric representation that that
number cannot be an upper bound of $`[a, b]`.

To prove it, let $`c < b`. If $`c < a`, then $`c` is not an upper bound of
$`[a, b]` because it is not greater than or equal to $`a`;
if $`a \le c < b`, let us consider a real number $`d` that is between
$`c` and $`b` (there always exists one; for example $`d = \frac{c+b}{2}`).

Then $`a \le c < d < b`, so $`d \in [a, b]`.
If $`c` were an upper bound of $`[a, b]`,
$`c` would have to be greater than or equal to all the elements of $`[a, b]`,
in particular $c$ would have to be greater than or equal to $`d`,
which is not the case.

What is then the property that $`b` has as an upper bound?
Well, that there are no upper bounds less than $`b`.
Put another way, $`b` is the least upper bound.
This type of upper bounds is so important in Analysis that they are given a name:

:::definition "def_1.21" (parent := "completeness")(tags := "Supremum")
Let $`A \subseteq ℝ`;
a real number $`c` is said to be the _supremum_ of $`A` and is written
$`c = \sup A` if it has the following two properties:

    * *S₁* $`c` is an upper bound of $`A`.
    * *S₂* If $`d` is an upper bound of $`A`,
    then $`c \le d` (this expresses that $`c` is the least of the upper bounds).
:::


The discussion prior to the definition proves that $`b` is the supremum of
$`[a, b]`; an analogous discussion proves that $`b` is also the supremum of $`(a, b)`.

A natural question we can ask ourselves: will every subset $`A` of ℝ have a supremum?
The answer is negative: to have a supremum, in particular it must have an
upper bound (since the supremum is, in particular, an upper bound)
and there are sets in ℝ that do not have an upper bound.

For example, if we take $`A = \mathbb{R}` then $`A` has no upper bound,
because if $`c` were an upper bound of $`A = \mathbb{R}`,
it would be $`x \le c` for all $`x \in \mathbb{R}`,
that is, there would be no real numbers greater than the real number $`c`.

Thinking of the representation of the reals on a line,
it is obvious that there are points on the line to the right of $`c`,
whoever $`c` may be, but as we promised not to use said representation
in the proofs we observe that by *O₃* it is $`c < c + 1` (since $`0 < 1`)
and therefore it is not $`x \le c` for all $`x \in ℝ`
(at least for $`x = c + 1` it is false).

And what if $`A` has an upper bound, or as is usually said,
if $`A` is _bounded above_? Except for one case
(the case where $`A` is the empty set, $`A = \emptyset`),
it is true that $`A` has a supremum if $`A` is bounded above.

To convince ourselves of this, let us think that the fact that
$`A` is bounded above means that, on the line, $`A` is to the left of a
certain number $`c`. Now we make that number $c$ travel to the left until
it "stumbles" upon $`A`;
right where it stumbles will be the supremum (the line has no "holes"):

$$`
    \begin{picture}(200,40)
        \line(1,0){200}
        % Set A
        \put(40,20){\makebox(0,0){(}}
        \put(80,20){\makebox(0,0){)}}
        \put(60,10){\makebox(0,0){$\underbrace{\hspace{40pt}}_A$}}

        % Sup A
        \put(80,20){\circle*{2}}
        \put(80,25){\makebox(0,0){$\sup A$}}

        % Moving point c
        \put(150,20){\circle*{2}}
        \put(150,25){\makebox(0,0){c}}
        \put(145,20){\vector(-1,0){60}}
        \multiput(82,20)(5,0){13}{\circle*{1}}
    \end{picture}
`

This is not a proof, of course; nor are we going to give any other.
We will take this fact as a basic property of ℝ and it will be the
$`14^{th}` that we were missing:

:::theorem "thm_completeness" (tags := "Completeness property")(lean := "sSup")(parent := "completeness")
If $`A` is a set of real numbers, $`A \subset \mathbb{R}`,
non-empty and $`A` is bounded above, then there exists:
$$`c = \sup A`
:::

```lean "thm_completeness"
example
    (A : Set ℝ)
    (_ : A.Nonempty)
    (_ : BddAbove A) : ∃ c : ℝ, c = sSup A := by
  use sSup A
```

In an example we saw before, $`A = (a, b)`,
the supremum was $`b`, which does not belong to $`A`.
In the other example, $`A = [a, b]`,
the supremum was also $`b`, which _does_ belong to $`A`.

In general, then, the supremum may or may not belong to the set;
in the case where it belongs to the set, it is called the _maximum_
instead of the supremum.

All this time we have been talking about _the_ supremum,
which implies that a set $`A` cannot have more than one supremum.
Indeed, if $`c_1` and $`c_2` are suprema of $`A`,
then by $`c_1` being an upper bound and $`c_2` being the least upper bound,
$`c_2 \le c_1`, and by $`c_2` being an upper bound and $`c_1`
being the least upper bound, $`c_1 \le c_2`.
Therefore $`c_1 = c_2` and the supremum is unique.

There is a way to characterize the supremum of a set that is very useful:

:::lemma_ "prop_1.22"
Let $`A` be a set bounded above and non-empty.
Then a real number $`c` is the supremum of $`A` if and only if it
satisfies the two following conditions:

    * *$`S_1'`* $`c` is an upper bound of $`A`.
    * *$`S_2'`* if $\epsilon$ is any real number arbitrary greater than zero,
    then there exists $`a \in A` such that $`c - ε < a`.
:::

```lean "prop_1.22_mp"
open Set

example (A : Set ℝ)
    (_ : A.Nonempty)
    (hA : BddAbove A) : a ∈ A → a ≤ sSup A := by
    intro a
    exact le_csSup hA a

theorem prop_1_22_mp (A : Set ℝ)
    (hne : A.Nonempty)
    (_ : BddAbove A) :
        ∀ ε > 0, ∃ a ∈ A,  sSup A - ε < a := by
    intro ε hε
-- Since ε > 0, subtracting ε from sSup A
-- gives a smaller number.
    have : sSup A - ε < sSup A := by
        exact sub_lt_self (sSup A) hε
-- Because sSup A is the least upper bound of A,
-- every number strictly below it fails to be
-- an upper bound. Therefore there is some element of A
-- above sSup A - ε.
    exact exists_lt_of_lt_csSup  hne this
```
Conversely,


```lean "prop_1.22_mpr"
example
    (A : Set ℝ)
    (hnne : A.Nonempty)
    (c : ℝ)
    (hupper : ∀ a ∈ A, a ≤ c)
    (happrox : ∀ ε > 0, ∃ a ∈ A, c - ε < a) :
        sSup A = c := by
  -- Step 1: Prove A is bounded above by showing 'c' is
  -- an upper bound(needed for supremum properties).
  have hA : BddAbove A := by
    exact ⟨c, hupper⟩

  -- Step 2: Prove that the supremum of A is less than or
  -- equal to c.
  -- By definition, sSup A is the *least* upper bound,
  -- and 'c' is *an* upper bound.
  have hle : sSup A ≤ c := by
    exact csSup_le hnne hupper

  -- Step 3: Start a proof by contradiction to establish
  -- the reverse inequality (c ≤ sSup A).
  have hle' : c ≤ sSup A := by
    by_contra h -- Assume the negation: sSup A < c

    -- Step 4: If sSup A < c, then the distance
    -- (c - sSup A) must be strictly positive.
    have hε : 0 < c - sSup A := by
      linarith

    -- Step 5: Instatiate the hypothesis 'happrox' using
    -- (c - sSup A) as our positive epsilon (ε).
    -- This extracts an element 'a' in 'A' that is closer
    -- to 'c' than 'sSup A' is.
    obtain ⟨a, haA, ha⟩ := happrox (c - sSup A) hε

    -- Step 6: Since 'a' belongs to 'A',
    -- it must be less than or equal to the supremum of A.
    have hsup : a ≤ sSup A := by
      exact le_csSup hA haA

    -- Step 7: Derive a contradiction by showing that
    -- sSup A is strictly less than 'a'.
    have : sSup A < a := by
      -- Simplifies c - (c - sSup A) into just 'sSup A' to
      -- transform the inequality 'ha'.
      have : c - (c - sSup A) < a := ha
      simpa using this

    -- Step 8: 'linarith' finds a contradiction between
    -- (a ≤ sSup A) and (sSup A < a), closing this branch.
    linarith

  -- Step 9: Use anti-symmetry
  -- (if x ≤ y and y ≤ x, then x = y)
  -- to conclude that sSup A = c.
  exact le_antisymm hle hle'
```

By changing greater for lesser, we obtain analogous notions and properties:

:::definition "def_1.23"
Let $`A \subset \mathbb{R}`; a real number $`d` is said to be a _lower bound_
of $`A`, if it has the following property:

For every $`a \in A` it is $`d \le a`.

If $`A` has a lower bound, $`A` is said to be _bounded below_.
:::

:::definition "def_1.24"
Let $`A \subset \mathbb{R}`; a real number $`d` is said to be
_Infimum_ of $`A` (and is denoted $`d = \inf A`),
if it has the following two properties:

    * $`I_1)` $`d` is a lower bound of $`A`.
    * $`I_2)` if $`k` is a lower bound of $`A`,
    $`k \le d` (that is, $`d` is the greatest lower bound).
:::

:::lemma_ "prop_1.25" (lean := "sInf")(parent := "completeness")(tags := "Infimum")
Let $`A \subset \mathbb{R}` be bounded below and non-empty.
Then there exists
$$`d = \inf A`
:::

```lean "prop_1.25"
example
    (A : Set ℝ)
    (_ : A.Nonempty)
    (_ : BddBelow A) : ∃ c : ℝ, c = sInf A := by
  use sInf A
```

```lean "prop_1.25_proof"
lemma sub_epsilon_lt_lt
    (c a : ℝ)
    (hε : ∀ ε > 0, c - ε ≤ a) : c ≤ a := by
    -- Prove the contrapositive.
    contrapose! hε
    -- Choose ε to be half the distance between a and c.
    let ε := (c - a) / 2
    -- It suffices to exhibit a positive ε for
    -- which c - ε > a.
    use ε
    constructor
    · -- ε is positive because c > a.
      positivity
    · -- Rewrite c - ε as the midpoint of a and c.
      have : c - ε = (c + a) / 2 := by
        dsimp [ε]
        ring
      rw [this]
      -- The midpoint of a and c is strictly greater than a.
      linarith

/--
`IsLB A k` means that `k` is a lower bound of the set `A`.
-/
def IsLB (A : Set ℝ) (k : ℝ) : Prop :=
  ∀ a ∈ A, k ≤ a

/--

Proof of the existence of the infimum.
Given a nonempty set `A ⊆ ℝ` that is bounded below,
this proof constructs the infimum of `A`.
The argument proceeds as follows.

1. Define the set of all lower bounds of `A`.
2. Show that this set is bounded above by any
    element of `A`.
3. Let `s` be the supremum of the set of lower bounds.
4. Prove that `s` is itself a lower bound of `A`.
5. Show that every lower bound of `A` is less than or
    equal to `s`.
Thus `s` is the greatest lower bound (infimum) of `A`.
-/
example (A : Set ℝ)
        (A_nonempty : A.Nonempty)
        (hA : BddBelow A) :
            ∃ s : ℝ,
                IsLB A s ∧ (∀ k, IsLB A k → k ≤ s) := by
        -- Define the set of all lower bounds of A.
        let lowerBounds (A : Set ℝ) : Set ℝ :=
            {k | IsLB A k}
        -- The set of lower bounds is bounded above.
        have bdd_above_lB_A : BddAbove (lowerBounds A) := by
                -- Pick any element of A.
                obtain ⟨a, ha⟩ := A_nonempty
                -- Every lower bound is less than or
                -- equal to this element.
                use a
                intro b hb
                exact hb a ha
        -- Let s be the supremum of the set of lower bounds.
        let s : ℝ := sSup (lowerBounds A)
        -- Show that s is the greatest lower bound.
        use s
        constructor
        · -- First, prove that s is itself a lower bound.
          intro a ha
          -- By the approximation property of the supremum,
          -- every ε > 0 admits a lower bound b
          -- with s - ε < b.
          have : ∀ ε > 0,
              ∃ b ∈ lowerBounds A, s - ε < b := by
              exact prop_1_22_mp
                  (lowerBounds A)
                  hA
                  bdd_above_lB_A
          -- Since b is a lower bound, b ≤ a.
          -- Hence s - ε < a for every ε > 0.
          have : ∀ ε > 0, s - ε < a := by
              intro ε hε
              obtain ⟨b, hb⟩ := this ε hε
              have w'' : b ≤ a := by
                  exact hb.left a ha
              have : s - ε < b := by
                  exact hb.right
              exact lt_of_lt_of_le this w''
          -- Replace strict inequality by
          -- non-strict inequality.
          have : ∀ ε > 0, s - ε ≤ a := by
              intro ε hε
              exact le_of_lt (this ε hε)
          -- Apply the ε-lemma to conclude s ≤ a.
          exact sub_epsilon_lt_lt s a this
        · -- Finally, prove that every lower bound is
          -- at most s.
          intro k hk
          -- View k as an element of the set of
          -- lower bounds.
          have k_is_lb : k ∈ lowerBounds A := by
              exact mem_setOf.mpr hk
          -- Since s is the supremum of the lower bounds,
          -- every element of that set is at most s.
          exact le_csSup bdd_above_lB_A k_is_lb
```

Analogously to what we said for supremum and maximum, if $`A` has an infimum,
$`d = \inf A`, and if $`d \in A`, $`d` is called the _minimum_ of $`A`.

# Exercises

1. Let $`a` and $`b` be real numbers such that $`a < b`.
Prove that $`b = \sup(a, b)`, and that $`a = \inf(a, b) = \inf[a, b]`.

2. Prove that the empty set is bounded above and below but does not have an
infimum or a supremum (Suggestion: prove that every real number is an upper and lower bound of $`\emptyset)`.

3. State which of the following sets are bounded above,
which below, and which are their infimums and supremums if they exist
(proving everything):

    * a) ℕ
    * b) ℤ
    * c) ℚ
    * d) $`A = \{x \in \mathbb{Z} : -2 < x < 8\}`
    * e) $`A = \{x \in \mathbb{Q} : \frac{1}{2} < x < 3\}`
    * f) $`A = \{x \in \mathbb{N} : x < 10\}`

4. Let $A$ be a non-empty set bounded below. Prove that a real number $d$ is the infimum of $A$ if and only if it satisfies the following conditions:
    * $`I'_1)` $`d` is a lower bound of $`A`.
    * $`I'_2)` For every $`\epsilon > 0` there exists $`a \in A` such that
    $`a < d + \epsilon`.

5. Prove that if we accept Proposition 1.25 as a basic property,
then the Completeness Property is a derived property
(suggestion: imitate the proof of Proposition 1.25,
taking $`B = \{x \in \mathbb{R} : x \text{ is an upper bound of } A \})`.

6.
    * $`\star\; a)`  Prove that $`\inf A \le \sup A` in case both exist.
    * $`\star\; b)` Prove that $`\inf A = \sup A` if and only if
    $`A` is a set of a single element.

# 1.9. Consequences of the Completeness Property

In this paragraph we are going to see how the acceptance of the Completeness
Property has a series of implications.
The first of them is the intuitively obvious fact that natural numbers can be
as large as one wishes.

:::lemma_ "prop_1.26" (tags := "Archimedean Principle" )(lean := "exists_nat_gt")(parent := "completeness")
If $`a` is any real number then there exists a natural number
$`n` such that $`n > a`.
:::

This theorem is already part of the Lean mathlib library,
but we have included a proof here for completeness.

```lean "prop_1.26"
example : ∀ a : ℝ, a > 0 ->  ∃ n : ℕ, n > a := by
  intro a ha
  exact exists_nat_gt a
```

```lean "prop_1.26_proof"
example (a : ℝ) (ha : a > 0) : ∃ n : ℕ, (n : ℝ) > a := by

  -- Let `S` be the set of natural numbers less than or
  -- equal to `a`.
  let S := {n : ℕ | (n : ℝ) ≤ a}

  -- Since `a > 0`, the natural number `0` belongs to `S`,
  -- so `S` is nonempty.
  have : S.Nonempty := by
    use 0
    simp [S]
    exact le_of_lt ha

  -- View `S` as a subset of the real numbers.
  let T : Set ℝ := (Nat.cast : ℕ → ℝ) '' S

  -- The image of a nonempty set under a function
  -- is nonempty.
  have hne : T.Nonempty := by
    exact Nonempty.image Nat.cast this

  -- Every element of `T` is at most `a`,
  -- so `T` is bounded above.
  have hbdT : BddAbove T := by
    use a
    intro x hx
    rcases hx with ⟨n, hnS, rfl⟩
    exact hnS

  -- Let `s` denote the least upper bound of `T`.
  let s := sSup T

  -- Since `1 > 0`, we have `s - 1 < s`.
  have : s - 1 < s := by
    linarith

  -- By the defining property of the supremum,
  --there is an element of `T` strictly larger than `s - 1`.
  have : ∃ t ∈ T, s - 1 < t := by
    exact exists_lt_of_lt_csSup hne this

  -- Convert the element of `T` back into a natural number
  -- belonging to `S`.
  have : ∃ n ∈ S, s - 1 < (n : ℝ) := by
    rcases this with ⟨t, htT, ht⟩
    rcases htT with ⟨n, hnS, rfl⟩
    exact ⟨n, hnS, ht⟩

  -- Show that this natural number has the property that
  --its successor is greater than `a`.
  have : ∃ n : ℕ, s - 1 < (n : ℝ) ∧ (n + 1 : ℝ) > a := by
    obtain ⟨n, hnS, hs⟩ := this

    -- Since `n > s - 1`, adding `1` gives `n + 1 > s`.
    have hssuccn : (n + 1 : ℝ) > s := by
      linarith

    -- Therefore `n + 1` cannot belong to `T`, because
    -- every element of `T` is bounded above by
    -- the supremum.
    have hnotmem : (n + 1 : ℝ) ∉ T := by
      intro hmem
      have hle : (n + 1 : ℝ) ≤ s := by
        exact le_csSup hbdT hmem
      linarith

    -- If `n + 1 ≤ a`, then `n + 1` would belong to `S`,
    -- hence to `T`, contradicting the previous fact.
    have hgt : (n + 1 : ℝ) > a := by
      by_contra hle
      have hn1S : n + 1 ∈ S := by
        simpa [S] using hle
      have hmem : (n + 1 : ℝ) ∈ T := by
        refine ⟨n + 1, hn1S, by simp [Nat.cast_add]⟩
      exact hnotmem hmem

    exact ⟨n, hs, hgt⟩

  -- The required witness is the successor of the
  -- natural number found above.
  show ∃ m : ℕ, (m : ℝ) > a
  obtain ⟨n, _, hgt⟩ := this
  use n + 1
  simpa [Nat.cast_add] using hgt
```

:::lemma_ "cor_1.27"
Let $`a` and $`b` be real numbers such that $`0 < a < b`.
Then there exists a natural number $`n` such that $`na > b`.
:::

```lean "cor_1.27_proof"
theorem corollary_1_17
  (a b : ℝ)
  (ha : 0 < a)
  (_ : a < b): ∃ n : ℕ,  b < (n : ℝ) * a := by
    rcases exists_nat_gt (b * a⁻¹) with ⟨n, hn⟩
    use n
    calc b
      _ = b * (a⁻¹ * a) :=  by
        rw [mul_comm a⁻¹,
          mul_inv_cancel₀ (ne_of_gt ha), mul_one]
      _ = (b * a⁻¹) * a := by rw [mul_assoc]
      _ < (n : ℝ) * a := by
          exact mul_lt_mul_of_pos_right hn ha
```
```lean "cor_1.27_proof"
theorem corollary_1_17'
  (a b : ℝ)
  (ha : 0 < a) : ∃ n : ℕ,  b < (n : ℝ) * a := by
    rcases exists_nat_gt (b * a⁻¹) with ⟨n, hn⟩
    use n
    calc b
      _ = b * (a⁻¹ * a) :=  by
        rw [mul_comm a⁻¹,
          mul_inv_cancel₀ (ne_of_gt ha), mul_one]
      _ = (b * a⁻¹) * a := by rw [mul_assoc]
      _ < (n : ℝ) * a := by
          exact mul_lt_mul_of_pos_right hn ha
```


This Corollary is, in reality, the Archimedean Principle;
he supposed that if $`AB` has length $`a` and $`AC` has length $`b`
with $`a < b`, then by successive addition of segments
$`BD, DE`, etc., of length $`a`,
one eventually reaches a point that exceeds the length of $`AC`.

This is essentially the Archimedean property of the real numbers
In `Lean 4`, `exists_nat_mul_gt` is typically an `ENNReal`
(Extended Nonnegative Real) lemma (from `Mathlib.Data.ENNReal.Inv`)
that states for any non-zero element `a` and non-infinity element `b`,
there exists a natural number `n` such that $`b < n · a`⋅

```lean "arquimedean_pple"
open ENNReal

example (a b : ℝ≥0∞) (ha : a ≠ 0) (hb : b ≠ ⊤) :
  ∃ n : ℕ,  b < (↑n) * a := by
  exact exists_nat_mul_gt ha hb
```

:::lemma_ "cor_1.28"
If $`\epsilon` is a real number greater than 0,
then there exists a natural number $`n` such that:
$`\frac{1}{n} < \epsilon`.
:::

```lean "cor_1.28_proof"
example (ε : ℝ) (hε : ε > 0) :
  ∃ n : ℕ , (1 / n : ℝ) < ε := by
  have hne : ∃ n : ℕ, n  > (1 / ε) := by
      exact exists_nat_gt (1 / ε)
  obtain ⟨n, hn⟩ := hne
  use n
  have hn' : (n : ℝ) * ε > 1 := by
    calc (n : ℝ) * ε
    _ > (1 / ε) * ε :=  by
      exact mul_lt_mul_of_pos_right hn hε
    _ = 1 := by rw [one_div, inv_mul_cancel₀ hε.ne']
  have n_positive: (n : ℝ) > 0 := by
    calc 0
    _ < (1 / ε) := by exact div_pos zero_lt_one hε
    _ < n := by exact hn
  have hn : (1 / n : ℝ) > 0 := by
    exact div_pos zero_lt_one n_positive
  have hcancel : (1 / (n : ℝ)) * (n : ℝ) = 1 := by
    field_simp [ne_of_gt n_positive]
  calc 1 / (n : ℝ)
    _ = 1 *  (1 / n : ℝ) := by rw [one_mul]
    _ < ((n : ℝ) * ε) * (1 / (n : ℝ)) := by
       exact mul_lt_mul_of_pos_right hn' hn
    _ = ε * (1 / (n : ℝ) * (n : ℝ)) := by
          rw [mul_assoc, mul_comm, mul_assoc]
    _ = ε  := by rw [hcancel, mul_one]
```
The standard theorem in modern `Mathlib` for this exact property is
`exists_nat_one_div_lt`. It is defined using `1 / (n + 1)` precisely
to eliminate division-by-zero boundary problems.

```lean "exists_nat_one_div_lt"
example (ε : ℝ) (hε : ε > 0) :
 ∃ n : ℕ, (1 / (n + 1 : ℝ)) < ε := by
  exact exists_nat_one_div_lt hε
```

:::lemma_ "prop_1.29"
We have proven before {uses "prop_1.19"}[](Proposition 1.19) that between two rational numbers
there is always another rational number and we have said in passing that
between two real numbers there is always another real number
(in both cases $`\frac{a+b}{2}`).

The following Proposition proves that between two real numbers there is
always a rational number:


Let $`a` and $`b` be real numbers such that $`a < b`$.
There exists then a rational number $`t` such that $`a < t < b`.
:::

```lean "prop_1.29"
example (a b : ℝ) (ha : 0 < a) (hab: a < b) :
  ∃ q : ℚ, a < q ∧ q < b := by
  let ε := b - a
  have hε : 0 < ε := by linarith
  obtain ⟨n', hn'⟩ := exists_nat_one_div_lt hε
  let n := (n' + 1 : ℕ)
  have bpos : 0 < b := by exact lt_trans ha hab
  have npos : (0 : ℝ)  < n := by positivity
  have inpos : (0 : ℝ) < (1 / n : ℝ) := by
    positivity
  let A := {p : ℕ | a < (p / n : ℝ)}
  have : ∃ p : ℕ, a < (p / n : ℝ) := by
    have : ∃ p : ℕ, a < (p : ℝ) * (1 / n : ℝ) := by
      exact corollary_1_17' (1 / n : ℝ) a inpos
    obtain ⟨p, hp⟩ := this
    use p
    rw [← mul_one_div]
    exact hp
  have neA : A.Nonempty := by
    obtain ⟨p, hp⟩ := this
    exact ⟨p, hp⟩
  let m := sInf A
  have : m ∈ A := Nat.sInf_mem neA
  have hm : IsLeast A m := by
    (expose_names; exact isLeast_csInf this_1)
  have a_le_mn : a < (m / n : ℝ) := by exact this
  have : a * n < m := by
    calc a * n
    _ < (m / n : ℝ) * n := by
      exact mul_lt_mul_of_pos_right this npos
    _ = m := by field_simp
  have mpos : 0 < m := by
    have hpos : (0 : ℝ) < a * (n : ℝ) :=
      mul_pos ha npos
    have hmpos : (0 : ℝ) < (m : ℝ) :=
      lt_trans hpos this
    exact_mod_cast hmpos
  have : m - 1 < m := by exact Nat.sub_lt mpos (by decide)
  have : ((m - 1) : ℕ) ∉ A := by
    intro hqA
    have hle : m ≤ (m - 1):= hm.2 hqA
    linarith
  have hcast : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by
    simpa using (Nat.cast_sub (Nat.succ_le_of_lt mpos))
  have : ((m - 1): ℝ) / (n : ℝ) <= a := by
    simpa [A, hcast] using this
  have : (m / n : ℝ) < b := by
    calc (m / n : ℝ)
    _ = ((m - 1 + 1) / n) := by ring
    _ = ((m - 1 )/ n : ℝ) + (1 / n) := by
      field_simp
    _ <= a +  (1 / n) := by
      exact add_le_add_left this (1 / ↑n)
    _ = a + (1 / (n' + 1)) := by simp [n]
    _ < a  + ε := by
      exact add_lt_add_right hn' a
    _ = a + (b - a) := by simp [ε]
    _ = b := by simp
  use (m / n)
  constructor
  . simpa using a_le_mn
  . simpa using this
```

```lean "cor_1.17"
example
  (a b : ℝ)
  (ha : 0 < a)
  (hab : a < b): ∃ n : ℕ,  b < (n : ℝ) * a := by
    exact corollary_1_17 a b ha hab
```


*Dem.:* $`\star \textbf{i)}` Let us first consider the case where
$`0 < a < b`. Let us call:
$$`\epsilon = b - a`
and let $`n \in \mathbb{N}` be such that $`\frac{1}{n} < \epsilon`.

We consider the set:
$$`A = \left\{ p \in \mathbb{N} : \frac{p}{n} > a \right\}`
That is, $A$ is the set of natural numbers such that, by taking $`p`$
jumps of length $`\frac{1}{n}` each, we exceed $`a`.
Since we want to exceed $`a` but not $`b` (as we want a rational between
$`a` and $`b`), the $`p` we consider must not be very large.
More precisely, since $`A \subset \mathbb{N}` and $`A \neq \emptyset`
(by Corollary 1.27), there exists, by well-ordering:
$$`m = \min A`.

We claim that the number $`\frac{m}{n} = m \cdot \frac{1}{n}` is between
$`a` and $`b`. In effect, $`\frac{m}{n} > a` because $`m \in A`
(the first thing that must be fulfilled to be the minimum of $`A`:
belonging to $`A`).
Furthermore, $`\frac{m}{n} < b` because if it were $`\frac{m}{n} \ge b`,
then:

$$`
\begin{align*}
    (m - 1) \cdot \frac{1}{n} &=
    m \cdot \frac{1}{n} - \frac{1}{n} = \frac{m}{n} - \frac{1}{n} \ge \\
    &\ge b - \frac{1}{n} > b - (b - a) = a
\end{align*}
`

that is, $`(m-1) \cdot \frac{1}{n} > a`, so $`m - 1 \in A`.
This cannot be since $`m - 1 < m` and $`m = \min A`.
Ultimately: $`a < \frac{m}{n} < b`
and clearly $`\frac{m}{n}` is rational
(since $`m` and $`n` are natural numbers).


The above was for the case $`0 < a < b`. The remaining cases are simple:

  * $`\star\; \textbf{ii)}` $`a < 0 < b`.
    In this case, 0 is rational and is between $`a` and $`b`.

  * $`\star\; \textbf{iii)}` $`a = 0 < b`.
    In this case, there exists $`n \in \mathbb{N}` such that
    $`\frac{1}{n} < b`. Since $`\frac{1}{n} > 0 = a` and
    $`\frac{1}{n} \in \mathbb{Q}`, the claim is proven in this case.

  * $`\star\; \textbf{iv)}` $`a < b = 0`.
    Then $`0 = -b < -a`. By case _(iii)_ we have $`n \in \mathbb{N}`
    such that $`\frac{1}{n} < -a`.
    Then $`a < -\frac{1}{n} < 0 = b` and $`-\frac{1}{n} \in \mathbb{Q}`.

  * $`\star\; \textbf{v)}` $`a < b < 0`.
    Multiplying by $`-1`: $`0 < -b < -a`. By case _i)_ we can place
    $`\frac{m}{n}` between $`-b` and $`-a`: $`-b < \frac{m}{n} < -a`.
    Multiplying again by $`-1`:
    $$`a < -\frac{m}{n} < b`
    and since $`-\frac{m}{n} \in \mathbb{Q}`,
    this finishes proving the Proposition.

As a final consequence of the Completeness Property,
we are going to prove the existence of $`n`-th roots of any positive number
for every natural $`n`.

:::lemma_ "prop_1.30" (tags:= "Existence of $`n`th-root")
Let $`a` be a positive real number and $n$ be a natural number.
There exists then a unique positive number $`b` such that:
$$`b^n = a` .
Said $`b` will be indicated as $`\sqrt[n]{a}` and will be called
"n-th root of $`a`".
:::

:::proof "prop_1.30"
We divide the demonstration into three cases:
    * $`\bullet \textbf{i)}\;` $`a > 1`
:::

```lean "prop_1.30"
/--
If `0 < a < 1`, then every positive power of `a`
is at most `a` itself.
-/

lemma pow_le_self (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1) :
    ∀ n : ℕ, 1 ≤ n → a ^ n ≤ a := by
  intro n
  induction n with
  | zero =>
      -- The hypothesis `1 ≤ 0` is impossible.
      intro hn
      omega
  | succ n ih =>
      intro hn
      by_cases h : n = 0
      · -- When `n = 0`, the exponent is `1`.
        subst h
        simp
      · -- Otherwise, use the induction hypothesis.
        have hnpos : 1 ≤ n := by
          omega
        have hih : a ^ n ≤ a := ih hnpos
        calc
          a ^ (n + 1) = a ^ n * a := by
            rw [pow_succ]
          -- Multiply the induction hypothesis by the
          -- positive number `a`.
          _ ≤ a * a := by
            exact
              mul_le_mul_of_nonneg_right hih (le_of_lt ha0)
          -- Since `a < 1`, we have `a² ≤ a`.
          _ ≤ a := by
            nlinarith
```

```lean "pow_gt_self"
lemma pow_gt_self (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1) :
      ∀ k : ℕ, 1 ≤ k → (- a) ≤ (- a) ^ k  := by
      intro k kpos
      by_cases heven : Even k
      . -- k is even
        have hak0 : 0 < (- a) ^ k := by
          rcases heven with ⟨m, _⟩
          subst k
          rw [pow_add]
          have h : (-a) ^ m * (-a) ^ m =
            ((-a) ^ m ) ^ 2 := by ring
          rw [h]
          apply sq_pos_of_ne_zero
          apply pow_ne_zero
          linarith
        have : (- a) < 0 := by linarith
        exact le_of_lt (lt_trans this hak0)
      . -- k is odd
        have hodd : Odd k := by
          rcases Nat.even_or_odd k with he | ho
          · exact False.elim (heven he)
          · exact ho
        rcases hodd with ⟨m, _⟩
        subst k
        rw [pow_add, pow_one]
        have hpow : a ^ (2 * m) ≤ 1 := by
          by_cases hm : m = 0
          · subst hm
            simp
          · have hmpos : 1 ≤ 2 * m := by omega
            have hle : a ^ (2 * m) ≤ a := by
              exact pow_le_self a ha0 ha1 (2 * m) hmpos
            linarith
        have hmul :
          a ^ (2 * m) * (-a) ≥ 1 * (-a) := by
            exact mul_le_mul_of_nonpos_right
              hpow (by linarith)
        simpa [← pow_mul, neg_mul] using hmul
```
```lean "prop_1.30_proof"
/--
For positive `x` and sufficiently small positive `ε`,
the increase in `(x + ε) ^ n` is bounded above by
`ε (x + 1) ^ n`.

This estimate is the key ingredient used later to show
that points sufficiently close to `x` remain below a
prescribed bound.
-/
lemma pow_add_epsilon_lt_bound
  {n : ℕ} (x : ℝ) (hx : 0 < x)
  (ε : ℝ) (hε : 0 < ε )(hε' : ε < 1) :
  (x + ε) ^ n < x ^ n + ε * (x + 1) ^ n := by

  -- Every positive power of `ε` is at most `ε`,
  -- because `0 < ε < 1`.
  have hpow (k : ℕ) (hk' : k < n):
    ε ^ (n - k) ≤ ε := by
      have hnk : 1 ≤ n - k := by omega
      exact pow_le_self ε hε hε' (n - k) hnk

  -- Every power of the positive number `x` is positive.
  have xkpos : ∀ k : ℕ, 0 < x ^ k := by
    intro k
    positivity

  -- Replace each occurrence of `ε^(n-k)`
  -- by the larger value `ε`.
  have hterm (k : ℕ) (hk' : k < n):
     x ^ k * ε ^ (n - k) * n.choose k ≤
      x ^ k * ε  * n.choose k := by
    have choose : (0 : ℝ) ≤ (n.choose k : ℝ) := by
      positivity
    have : x ^ k * ε ^ (n - k) ≤  x ^ k * ε :=  by
      exact mul_le_mul_of_nonneg_left
        (hpow k hk') (le_of_lt (xkpos k))
    exact mul_le_mul_of_nonneg_right this choose

  calc (x + ε) ^ n
  -- Expand `(x + ε)^n` using the binomial theorem.
  _ = ∑ k ∈ Finset.range (n + 1),
         x ^ k * ε ^ (n - k) * n.choose k  := by
        exact add_pow x ε n

  -- Separate the final term (`k = n`)
  -- from the remaining sum.
  _ = ∑ k ∈ Finset.range n,
         x ^ k * ε ^ (n - k) * n.choose k + x ^ n := by
         rw [Finset.sum_range_succ]
         simp

  -- Bound every remaining summand.
  _ ≤ ∑ k ∈ Finset.range n,
         x ^ k * ε * n.choose k + x ^ n := by
          refine add_le_add ?_ le_rfl
          refine Finset.sum_le_sum ?_
          intro k hk
          exact hterm k (Finset.mem_range.mp hk)

  -- Factor the common factor `ε` from the sum.
  _ = ε * ∑ k ∈ Finset.range n,
         x ^ k * n.choose k + x ^ n := by
          have hsummand :
            ∀ k, x ^ k * ε * ↑(n.choose k) =
              ε * (x ^ k * ↑(n.choose k)) := by
                intro k
                ring
          simp_rw [hsummand]
          rw [← Finset.mul_sum]

  -- Compare the remaining sum with the
  -- full binomial expansion
  -- of `(x + 1)^n`.
  _ <  x ^ n + ε * (x + 1) ^ n := by
        have : ∑ k ∈ Finset.range n,
         x ^ k * n.choose k < (x + 1) ^ n := by
          rw [add_pow]
          rw [Finset.sum_range_succ]
          simp_rw [one_pow, mul_one, Nat.choose_self]
          simpa using xkpos n
        have hmul :
          ε * ∑ k ∈ Finset.range n, x ^ k * ↑(n.choose k)
          < ε * (x + 1) ^ n := by
            exact mul_lt_mul_of_pos_left this hε
        simpa [add_comm] using add_lt_add_right hmul (x ^ n)
```


```lean "pow_sub_epsilon_gt_bound"
lemma pow_sub_epsilon_gt_bound
  {n : ℕ} (x : ℝ) (hx : 0 < x)
  (ε : ℝ) (hε0 : 0 < ε )(hε1 : ε < 1) :
  (x - ε) ^ n > x ^ n - ε * (x + 1) ^ n := by

  have hpow (k : ℕ) (hk' : k < n):
    ε ^ (n - k) ≤ ε := by
      have hnk : 1 ≤ n - k := by omega
      exact pow_le_self ε hε0 hε1 (n - k) hnk
  have xkpos : ∀ k : ℕ, 0 < x ^ k := by
    intro k
    positivity

  have hterm (k : ℕ) (hk' : k < n):
     x ^ k * ε ^ (n - k) * n.choose k ≤
      x ^ k * ε  * n.choose k := by
    have choose : (0 : ℝ) ≤ (n.choose k : ℝ) := by
      positivity
    have : x ^ k * ε ^ (n - k) ≤  x ^ k * ε :=  by
      exact mul_le_mul_of_nonneg_left
        (hpow k hk') (le_of_lt (xkpos k))
    exact mul_le_mul_of_nonneg_right this choose

  calc (x - ε) ^ n
  _ = ∑ k ∈ Finset.range (n + 1),
         x ^ k * (-ε) ^ (n - k) * n.choose k  := by
        exact add_pow x (-ε) n
  _ = ∑ k ∈ Finset.range n,
          x ^ k * (-ε) ^ (n - k) * n.choose k + x ^ n := by
          rw [Finset.sum_range_succ]
          simp

  _ > x ^ n - ε * (x + 1) ^ n := by sorry
    -- _ ≤ ∑ k ∈ Finset.range n,
  --        x ^ k * ε * n.choose k + x ^ n := by
  --         refine add_le_add ?_ le_rfl
  --         refine Finset.sum_le_sum ?_
  --         intro k hk
  --         exact hterm k (Finset.mem_range.mp hk)
  -- _ = ε * ∑ k ∈ Finset.range n,
  --        x ^ k * n.choose k + x ^ n := by
  --         have hsummand :
  --           ∀ k, x ^ k * ε * ↑(n.choose k) =
  --             ε * (x ^ k * ↑(n.choose k)) := by
  --               intro k
  --               ring
  --         simp_rw [hsummand]
  --         rw [← Finset.mul_sum]
  -- _ <  x ^ n + ε * (x + 1) ^ n := by
  --       have : ∑ k ∈ Finset.range n,
  --        x ^ k * n.choose k < (x + 1) ^ n := by
  --         rw [add_pow]
  --         rw [Finset.sum_range_succ]
  --         simp_rw [one_pow, mul_one, Nat.choose_self]
  --         simpa using  xkpos n
  --       have hmul :
  --         ε * ∑ k ∈ Finset.range n, x ^ k * ↑(n.choose k)
  --         < ε * (x + 1) ^ n := by
  --           exact mul_lt_mul_of_pos_left this hε
  --       simpa [add_comm] using add_lt_add_right hmul (x ^ n)
```

```lean "prop_1.30_proof"
/--
If `x^n < a`, then there exists a positive increment `ε`
such that `(x + ε)^n` is still strictly less than `a`.

The proof chooses an explicit value of `ε` small enough to
control the increase given by the previous lemma.
-/
lemma epsilon_power_increment_bound
  (a : ℝ)
  (n : ℕ)
  (x : ℝ) (hx0 : 0 < x) (hxa : x ^ n < a)
  : ∃ ε > 0, (x + ε) ^ n < a := by

  -- Choose `ε` to be the smaller of the available margin
  -- and `1/2`, ensuring both positivity and `ε < 1`.
  let ε := min ((a - x ^ n) / (x + 1) ^ n) (1 / 2)

  use ε

  have hε0 : 0 < ε := by
    positivity

  constructor
  · exact hε0

  · calc
      (x + ε) ^ n
      -- Apply the previous estimate.
      _ < x ^ n + ε * (x + 1) ^ n := by
        have : ε < 1 := by
          calc
            ε ≤ (1 / 2) := by
              exact min_le_right _ (1 / 2)
            _ < 1 := by
              linarith
        exact pow_add_epsilon_lt_bound x hx0 ε hε0 this

      -- Replace `ε` by its defining upper bound.
      _ ≤ x ^ n +
        ((a - x ^ n) / (x + 1) ^ n) * (x + 1) ^ n := by
        have hεle :
          ε ≤ (a - x ^ n) / (x + 1) ^ n := by
          dsimp [ε]
          exact min_le_left _ _

        have hmul :
          ε * (x + 1) ^ n ≤
            ((a - x ^ n) / (x + 1) ^ n) * (x + 1) ^ n := by
          exact
            mul_le_mul_of_nonneg_right hεle (by positivity)

        simpa [add_comm] using add_le_add_left hmul (x ^ n)

      -- The right-hand side simplifies exactly to `a`.
      _ = a := by
        field_simp
        ring
```
```lean "prop_1.30_proof"
example
  (a : ℝ) (ha1 :  1 < a)
  (n : ℕ) (hn : 1 ≤ n) : ∃ b : ℝ, b ^ n = a := by

    -- Consider all real numbers whose `n`th power
    -- is below `a`.
    let A := {s : ℝ | s ^ n < a}

    -- Since `1^n = 1 < a`, the set is nonempty.
    have h1A : (1 : ℝ) ∈ A := by
      calc (1 : ℝ) ^ n
      _ = 1 := by exact one_pow n
      _ < a := by exact ha1

    have Ane : A.Nonempty := by
      use (1 : ℝ)

    -- Show that `a` is an upper bound of the set.
    have Abdd : BddAbove A := by
      have a_is_ub : a ∈ upperBounds A := by
        have sa : ∀ s : ℝ, a ≤ s -> a ≤ s ^ n := by
          intro s hs
          have hs1 : 1 ≤ s := by
            linarith
          have hpow : s ^ 1 ≤ s ^ n := by
            exact pow_le_pow_right₀ hs1 hn
          have hs_le : s ≤ s ^ n := by
            simpa using hpow
          linarith
        intro s hs
        have : s ^ n < a := by simpa [A]
        have : s < a := by
          exact lt_of_not_ge (mt (sa s) (not_le_of_gt this))
        exact le_of_lt this
      use a

    -- Let `b` be the least upper bound of `A`.
    let b := sSup A

    -- Since `1 ∈ A`, the supremum satisfies `b ≥ 1`.
    have : 1 ≤ b := by
      dsimp [b]
      exact le_csSup Abdd h1A

    -- Hence `b` is positive.
    have hb0 : 0 < b := by linarith

    -- First prove `a ≤ b^n`.
    -- Otherwise `b^n < a`, so we could move slightly to the
    -- right while remaining inside `A`, contradicting the
    -- defining property of the supremum.
    have a_le_bpow : a ≤ b ^ n := by
      by_contra a_le_bpow
      have hlt : b ^ n < a := lt_of_not_ge a_le_bpow
      obtain ⟨ε, hε⟩ :=
        epsilon_power_increment_bound a n b  hb0 hlt
      have : b + ε ∈ A := by
        dsimp [A]
        exact hε.right
      have : b + ε ≤ b := by
        exact le_csSup Abdd this
      linarith [hε.left, this]

    -- The reverse inequality will show that `b^n = a`.
    have bpow_le_a: b ^ n ≤ a := by sorry

    use b
    exact le_antisymm  bpow_le_a a_le_bpow
```

This eliminates the possibility $`b^n < a`.

Let us consider then the remaining possibility, $`b ^ n > a`.
Let then $`t = b ^ n - a > 0`. For $`0 < h < 1`:
$$`
\begin{align*}
    (b-h)^n &= \sum_{k=0}^{n} \binom{n}{k} b^{n-k} (-h)^k = \\
    &= b^n + \sum_{k=1}^{n} \binom{n}{k} b^{n-k} (-h)^k >
\end{align*}`
(since $(-h)^k \ge -h$ for $k \ge 1$ and $`0 < h < 1`)
$$`
\begin{align*}
    &> b^n + \sum_{k=1}^{n} \binom{n}{k} b^{n-k} (-h) = \\
    &= b^n - h \sum_{k=1}^{n} \binom{n}{k} b^{n-k} > \\
    &> b^n - h \sum_{k=0}^{n} \binom{n}{k} b^{n-k} = \\
    &= b^n - h (b+1)^n = \\
    &= a + t - h (b+1)^n
\end{align*}
`
Taking then $`h < \frac{t}{(b+1)^n}` (and $0 < h < 1$), it results:
$$`
\begin{align*}
    (b-h)^n &> a + t - h(b+1)^n > \\
    &> a + t - \frac{t}{(b+1)^n} (b+1)^n = \\
    &= a + t - t = a
\end{align*}
`
or rather, $`(b-h)^n > a`.
Now then, as $`b = \sup A`, there must exist $`d \in A`
such that $`b - h < d` *(Proposition 1.22)* and therefore:
$$`(b-h)^n < d^n < a`,
that is:
$$`(b-h)^n < a`,
contrary to what we have seen.
This discards the possibility $`b^n > a`.
As we had already discarded $b^n < a$, it is necessarily:
$$`b^n = a`.

This proves that there exists $b$ with that property;
that this $`b` is unique follows easily from Exercise 2 of paragraph 1.4.
(Do it).

  * $`\bullet \textbf{ii)}` $`0 < a < 1`.
    In this case it will be $`\frac{1}{a} > 1`.
    Then there exists $`b'` (by i) such that:
    $$`b'^n = \frac{1}{a}` ,
    from which:
    $$` \left( \frac{1}{b'} \right)^n = \frac{1}{b'^n} = \frac{1}{1/a} = a`,
    so it is enough to take $b = 1/b'$.
    Uniqueness is proven the same as before.

  * $`\bullet \textbf{iii)}` $`a = 1`.
    Trivial case; results in $`b = 1`.

We can now speak freely of square roots, cube roots, etc.,
of positive numbers.
In particular, we already know the existence of the (positive) real number
$`\sqrt{2}`.

This number is going to give us our first example of an
*irrational* number, that is, of _a real number that is not rational_.
Let us prove that, indeed, $`\sqrt{2}` is irrational.

```lean "end Completeness"
end Completeness
```
