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

# The Natural Numbers

```lean "open NaturalNumbers"
namespace NaturalNumbers
```
We now distinguish certain subsets of the real numbers, beginning with the
natural numbers—the numbers used for counting: $`1, 2, 3,\ldots`.
Starting from $`0` and $`1`, define $`2 = 1 + 1,\; 3 = 2 + 1`, and so on.
The property $`0 < 1` implies that each new number is greater than,
and therefore distinct from, those preceding it.

However, “and so on” is not a precise definition.
We therefore seek a property characterizing the natural numbers.

They contain $`1` and are closed under adding $`1`: if $`x` belongs to the set,
then so does $`x + 1`. These conditions alone do not uniquely determine the
natural numbers, since larger subsets of ℝ may also satisfy them.

For brevity, we now give such sets a name:

:::definition "inductive_set"(tags := "Inductive Set")
A subset $`A` of the real numbers is said to be _inductive_ if it has the
following properties:
  * The real number $`1` belongs to $`A`
  * If any real number $`x` belongs to $`A`,
  then the real number $`x + 1` also belongs to $`A`.
:::

```lean "inductive_set"
def Inductive (A : Set ℝ) : Prop :=
    1 ∈ A ∧
      ∀ {x : ℝ}, x ∈ A → (x + 1) ∈ A

example : Inductive {x : ℝ | 0 < x} := by
  sorry
```

⋄⋄⋄⋄⋄⋄⋄⋄⋄⋄⋄⋄⋄⋄⋄⋄⋄⋄⋄⋄⋄⋄⋄⋄
The set of natural numbers can be characterized as the _smallest_ of all
inductive subsets of ℝ.

:::definition "natural_number"
A real number $`x ∈ ℝ` is a natural number if $`x` belongs to all the
inductive subsets of ℝ. The set of natural numbers is denoted as `Natural`.
:::

```lean "natural_number"
def isNatural (x : ℝ) : Prop :=
  ∀ {A}, Inductive A → x ∈ A

-- The Set of Natural numbeers
def Natural : Set ℝ := {x | isNatural x}

-- ```lean "G set"
-- def G (a : ℝ) (step : ℝ → ℝ → ℝ ) :=
--   ⋂₀  {A : Set (ℝ × ℝ) | G_inductive a step A}
-- ```

-- For x : ℝ, x ∈ Natural is equivalent to isNatural x
example {x : ℝ} :
  x ∈ Natural ↔ isNatural x := by
  rfl
```

By contrast, `n : Natural` means that `n` is an
element of the _subtype_ determined by the set `Natural`:
`n : {x : ℝ // x ∈ Natural}`
So it packages both pieces together:
* `n : ℝ`  the underlying real number
* `n.property`  a proof that `(n : ℝ) ∈ Natural`

```lean "def_1.2_subtype"
example {x} (hx : x ∈ Natural) : Natural :=
  by exact ⟨x, hx⟩

example (n : Natural) : (n : ℝ) ∈ Natural := by
  exact n.property
```

:::lemma_ "inductive_natural"
The set of natural numbers `Natural` is inductive.
:::

:::proof "inductive_natural"
We prove that `1 ∈ Natural` and the inductive step,
`n ∈ Natural → n + 1 ∈ Natural`.
:::

```lean "inductive_natural_proof"
theorem inductive_natural : Inductive Natural := by
  constructor
  . show 1 ∈ Natural
    intro A hA
    exact hA.left
  . show ∀ n : ℝ, n ∈ Natural → (n + 1) ∈ Natural
    intro n hn A hA
    exact hA.right (hn hA)

theorem one_mem_Natural : 1 ∈ Natural := by
  exact inductive_natural.left --inductive_natural

def one : Natural := ⟨1, one_mem_Natural⟩

lemma succ_mem_Natural
  (hn : n ∈ Natural) : n + 1 ∈ Natural := by
    exact inductive_natural.right hn

def succ (n : Natural) : Natural :=
  ⟨n + 1, succ_mem_Natural n.property⟩
```
◇◇◇◇◇◇◇◇◇◇◇◇◇◇◇◇◇◇◇◇◇

:::theorem "Principle_of_Induction" (tags := "Principle of Induction")
If $`H ⊆ ℝ` is inductive, then $`ℕ ⊆ H`.
If $`H` is an inductive subset of ℕ, then $`H = ℕ`.
:::

:::proof "Principle_of_Induction"
By definition, `Natural` is a subset of any inductive subset of ℝ.

That $`H` is a subset of ℕ means $`H ⊆ ℕ`.
But being $`H` inductive, then $`N ⊆ H` by $`ℐrm{N_2}`.
From the two inclusions $`H ⊆ N` and $`N ⊆ H` we conclude $`H = N`. $`□`
:::

```lean "Principle_of_Induction_proof"
theorem natural_subset_of_inductive
  (IH : Inductive H) : Natural ⊆ H := by
  intro n hn
  exact hn IH

theorem eq_natural_of_subset_of_inductive {H}
  (hH : H ⊆ Natural)
  (IH : Inductive H) : H = Natural := by
    apply Set.Subset.antisymm
    . exact hH
    . exact natural_subset_of_inductive  IH
```

We will now use the principle of induction to prove elementary properties of
natural numbers.

:::proposition "sum_of_naturals"
If $`n` and $`m` are natural numbers, then $`m + n` and $`m ⋅ n` are also
natural numbers.
:::
■■■■■■■■■■■■■■■■■■■■■■■■■■■■■■■■

```lean "sum_of_naturals_proof"
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
      exact inductive_natural.right hx
  intro m
  have : (m : ℝ) ∈ H := by exact m.property IH
  simpa [H]

example :
  ∀ n m : Natural, (n : ℝ ) + (m : ℝ) ∈ Natural := by
  intro n m
  exact sum_of_naturals n m

def addNat (n m : Natural) : Natural :=
  ⟨(n : ℝ) + (m : ℝ), sum_of_naturals n m⟩

theorem add_succ (n m : Natural) :
  addNat n (succ m) = succ (addNat n m) := by sorry

theorem add_Natural {n m : ℝ}
  (hn : n ∈ Natural)
  (hm: m ∈ Natural) : n + m ∈ Natural := by
    exact sum_of_naturals ⟨n, hn⟩ ⟨m, hm⟩
```

:::proposition "mul_of_naturals"
If `n` and `m` are natural numbers, then `m ⋅ n` is also
natural numbers.
:::
■■■■■■■■■■■■■■■■■■■■■■■■■■■■■■■■

:::proof "mul_of_naturals"
Given $`n ∈ Natural` We consider the set:
$$`H(x) = { x ∈ ℝ :  n · x ∈ Natural}`
and prove that $`H` is inductive. Then, by the _Principle of Induction_
{uses "Principle_of_Induction"}[] we conclude that $`Natural ⊆ H`.
Below we give a `Lean` proof.
:::

```lean "mul_of_naturals_proof"
theorem mul_of_naturals (n : Natural) :
  ∀ m : Natural, (n : ℝ) * (m : ℝ) ∈ Natural := by
  let H := {x : ℝ | n * x ∈ Natural}
  have IH : Inductive H := by
    unfold Inductive
    constructor
    . show 1 ∈ H
      intro A hA
      rw [mul_one]
      exact n.property hA
    . show ∀ {x : ℝ}, x ∈ H → (x + 1) ∈ H
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

def mulNat (n m : Natural) : Natural :=
  ⟨(n : ℝ) * (m : ℝ), mul_of_naturals n m⟩

theorem mul_one (n : Natural) :
  mulNat n one = n := by sorry

theorem mul_succ (n m : Natural) :
  mulNat n (succ m) =
    addNat (mulNat n m) n := by sorry
```

# More Properties of the Natural Numbers

Before demonstrating more properties of the natural numbers,
we are going to introduce a new concept:

:::definition "ge"
Given real numbers $`a` and  $`b`, we say that $`a` is
_less or equal_ than  $`b`,
and we write $`a \le b`, if one of the two following possibilities occurs:

  * $`a` is less than $`b`;
  * $`a` is equal to $`b`.
:::

```lean "ge"
example : ∀ {a b : ℝ},
  a ≤ b ↔ a < b ∨ a  = b := by
    exact Std.le_iff_lt_or_eq

example {a b : ℝ} (hab : a < b) : a ≤ b := by
  exact le_of_lt hab

example {a b : ℝ} (hab : a = b) : a ≤ b := by
  exact le_of_eq hab
```
Then, for it to be true that $`a \le b`, it is enough that one of the two
possibilities be true (the two together cannot be).

This relation has the following properties:

:::lemma_ "le_antisymm"(parent := "natural_numbers")(lean := "le_antisymm")(tags := "(≤) Antisymmetric property")
For any real numbers $`a` and $`b`, the following holds:
If $`a \le b` and $`b \le a`, then $`a = b`.
:::

```lean "le_antisymm"
example {a b : ℝ}
  (hab : a ≤ b)(hba : b ≤ a) : a = b := by
    exact le_antisymm hab hba
```
:::proof "le_antisymm"
Below we give a `Lean` proof:
:::

```lean "le_antisymm_proof"
theorem le_antisymm {a b : ℝ}
  (hab : a ≤ b)(hba : b ≤ a) : a = b := by
    have hab': a < b ∨ a = b := by
      exact Std.le_iff_lt_or_eq.mp hab
    have hba' : b < a ∨ b = a := by
      exact Std.le_iff_lt_or_eq.mp hba
    rcases hab' with a_lt_b | a_eq_b
    . rcases hba' with b_lt_a | b_eq_a
      . false_or_by_contra
        -- explicar este thm in trichotomy
        exact (lt_asymm a_lt_b b_lt_a)
      . false_or_by_contra
        subst a
        -- explicar este thm in trichotomy
        exact (lt_irrefl b) a_lt_b
    . rcases hba' with b_lt_a | b_eq_a
      . false_or_by_contra
        subst a
        exact (lt_irrefl b) b_lt_a
      . subst a
        exact b_eq_a
```

:::lemma_ "le_trans"(parent := "natural_numbers")(lean := "le_trans")(tags := "(≤) Transitive property")
If $`a \le b` and $`b \le c`, then $`a \le c`.
:::
```lean "le_trans"
example {a b : ℝ}(hab : a ≤ b)(hbc : b ≤ c) : a ≤ c := by
  exact le_trans hab hbc
```
```lean "le_trans_proof"
example {a b : ℝ}(hab : a ≤ b)(hbc : b ≤ c) : a ≤ c := by
  have hab: a < b ∨ a = b := by
      exact Std.le_iff_lt_or_eq.mp hab
  have hbc : b < c ∨ b = c := by
      exact Std.le_iff_lt_or_eq.mp hbc
  rcases hab with a_lt_b | a_eq_b
  . rcases hbc with b_lt_c | b_eq_c
    . exact le_of_lt (lt_trans a_lt_b b_lt_c)
    . subst c
      exact le_of_lt a_lt_b
  . rcases hbc with b_lt_c | b_eq_c
    . subst a
      exact le_of_lt b_lt_c
    . subst a
      exact le_of_eq b_eq_c
```

  * *Exercise:* Prove the following assertions in Lean:
:::lemma_"le_properties"
  1. If $`a \le b`, then $`a + c \le b + c\;` for any real number $`c`.
  2. If $`a \le b\;` and $`0 < c\;`,
then $`a \cdot c \le b \cdot c`.
:::

```lean "le_trans"
example {a b c : ℝ}(hab : a ≤ b) : a + c ≤ b + c := by
   exact add_le_add_left hab c

example {a b c : ℝ}
  (hab : a ≤ b)(hc : 0 < c) : a * c ≤ b * c := by
   exact mul_le_mul_of_nonneg_right hab (le_of_lt hc)
```

We return now to elementary properties of natural numbers.

:::theorem "one_le_natural" (parent := "natural-numbers")
If $`n` is a natural number, then $`1 ≤ n`
:::

:::proof "one_le_natural"
Let's consider $`H = \lbrace x : ℝ | 1 ≤ x\rbrace`. We will prove that $`H`
is an inductive set, and conclude that `Natural ⊆ H`.
:::

```lean "one_le_natural"
theorem one_le_natural {n : ℝ}
  (hn : n ∈ Natural): 1 ≤ n := by
  let H := {x : ℝ | 1 ≤ x}
  have IH : Inductive H := by
    constructor
    . simp [H]
    . simp [H]
      intro x hx
      have : (0 : ℝ)  ≤ 1 := by exact le_of_lt zero_lt_one
      exact le_trans this hx
  exact hn IH
```

:::corollary "one_lt_succ"
For all `n ∈ Natural`, `1 < n + 1`.
:::

```lean "one_lt_succ"
lemma one_lt_succ {n : ℝ} :
  n ∈ Natural → 1 < n + 1 := by sorry

```
We want now to prove the fact, intuitively clear, that if a natural number is
subtracted from a smaller natural number, the result is a natural number.
As a preliminary step, we prove the following Proposition.

:::theorem "th_1.7."
If $`n` is a natural number then either $`n = 1` or $`n - 1` is a natural
number.
:::

```lean "thm_1.7_proof"
theorem pred_mem_Natural
  (n_mem_Natural : n ∈ Natural) (one_lt_n : 1 < n) :
    n - 1 ∈ Natural := by
  let H : Set ℝ :=
    {n ∈ Natural | n = 1 ∨ (1 < n ∧ n - 1 ∈ Natural)}
  have hH : H ⊆ Natural := by
    intro n hn
    exact hn.left
  have IH : Inductive H := by
    constructor
    . show 1 ∈ H
      change 1 ∈
        Natural ∧ (1 = 1 ∨ (1 < 1 ∧ 1 - 1 ∈ Natural))
      constructor
      . exact inductive_natural.left
      . exact Or.inl rfl
    . show ∀ {x : ℝ}, x ∈ H → x + 1 ∈ H
      intro x hx
      have x_is_natural : x ∈ Natural := by exact hH hx
      have one_le_x : 1 ≤ x := by
        exact (one_le_natural x_is_natural)

      have e1 : 1 < x + 1 := by
            calc
            1 =  1 + 0 := by rw [add_zero]
            _ < x + 1 := by exact
              add_lt_add_of_le_of_lt one_le_x zero_lt_one
      change x + 1 ∈ Natural
          ∧ (x + 1 = 1 ∨
              (1 < x + 1 ∧ x + 1 - 1 ∈ Natural))
      constructor
      . exact succ_mem_Natural x_is_natural
      . have e1 : 1 < x + 1 := by
          calc
            1 =  1 + 0 := by rw [add_zero]
            _ < x + 1 := by exact
              add_lt_add_of_le_of_lt one_le_x zero_lt_one
        have e2 : x + 1 - 1 ∈ Natural := by
          norm_num
          exact x_is_natural
        exact Or.inr ⟨e1, e2⟩
  have H_eq_Natural : H = Natural := by
    exact eq_natural_of_subset_of_inductive hH IH
  have n_mem_H : n  ∈ H := by
    have : Natural ⊆ H := by rw [H_eq_Natural]
    exact this n_mem_Natural
  rcases n_mem_H.right with  one_eq_n | one_lt_n
  . false_or_by_contra
    exact ne_of_lt one_lt_n one_eq_n.symm
  . show (n : ℝ) - 1 ∈ Natural
    exact one_lt_n.right
```


:::lemma_ "natural_add_one_le_of_lt"
Let `n, m ∈ Natural`. If  `n < m`, then `n + 1 ≤ m`.
:::

```lean "natural_add_one_le_of_lt"
theorem natural_add_one_le_of_lt
  (n_mem_Natural : n ∈ Natural)
  (m_mem_Natural : m ∈ Natural)
  (n_lt_m : n < m) : n + 1 ≤ m := by
  let H := {k ∈ Natural | ∀ q ∈ Natural, k < q → k + 1 ≤ q}
  have IH : Inductive H := by
    constructor
    . show 1 ∈ H
      change 1 ∈ Natural ∧ ∀ q ∈ Natural, 1 < q → 1 + 1 ≤ q
      constructor
      . exact one_mem_Natural
      . rw [one_add_one_eq_two]
        intro q q_mem_Natural one_lt_q
        have pred_q_mem_Natural : q - 1 ∈ Natural := by
          exact pred_mem_Natural q_mem_Natural one_lt_q
        have one_le_pred_q : 1 ≤ q - 1 := by
          exact one_le_natural (pred_q_mem_Natural)
        calc
        2 = 1 + 1 := by rw [one_add_one_eq_two]
        _ ≤  (q - 1) + 1 := by
          exact add_le_add_left one_le_pred_q 1
        _ = q := by ring

    . show ∀ {x : ℝ}, x ∈ H → x + 1 ∈ H
      intro k k_mem_H
      change k + 1 ∈ Natural ∧
        ∀ q ∈ Natural, (k + 1 < q → k + 1 + 1 ≤ q)
      have k_mem_Natural : k ∈ Natural := by
        exact k_mem_H.left
      constructor
      . exact succ_mem_Natural k_mem_Natural
      . intro q q_mem_Natural succ_k_lt_q

        have one_lt_q : 1 < q := by
          calc (1 : ℝ)
          _  = 0 + 1 := by rw [zero_add]
          _ < 1 + 1 := by
            exact add_lt_add_left zero_lt_one 1
          _ ≤ k + 1 := by
            exact add_le_add_left
              (one_le_natural k_mem_Natural) 1
          _ < q := by exact succ_k_lt_q

        have pred_q_mem_Natural : q - 1 ∈ Natural := by
          exact pred_mem_Natural q_mem_Natural one_lt_q

        have k_lt_pred_q : k < q - 1 := by
          calc
          k = k + 1 - 1 := by ring
          _ < q - 1 := by
            exact add_lt_add_left succ_k_lt_q (-1)

        have : k + 1 ≤ q - 1 := by
          exact k_mem_H.right (q - 1)
            pred_q_mem_Natural  k_lt_pred_q

        calc k + 1 + 1
        _ ≤ q - 1 + 1 := by
          exact add_le_add_left this 1
        _ = q := by ring

  have n_mem_H : n ∈ H := by
    exact n_mem_Natural IH

  exact n_mem_H.right m m_mem_Natural n_lt_m
```
:::corollary "natural_le_of_lt_succ"
Let `n, m ∈ Natural`. If  `n < m + 1`, then `n ≤ m`.
:::

```lean "natural_le_of_lt_succ_proof"
theorem natural_le_of_lt_succ {n m : ℝ}
  (n_mem_Natural : n ∈ Natural)
  (m_mem_Natural : m ∈ Natural)
  (n_lt_succ_m : n < m + 1) : n ≤ m := by
  have : n + 1 ≤ m + 1 := by
    exact natural_add_one_le_of_lt
      n_mem_Natural
      (succ_mem_Natural m_mem_Natural)
      n_lt_succ_m
  calc
    n =  n + 1 - 1 := by ring
    _ ≤ m + 1 - 1 := by
      exact  add_le_add_left this (-1)
    _ = m := by ring
```

Now we are in a position to prove the announced result:

:::theorem "natural_sub_of_lt"
If $`m` and $`n` are natural numbers and $`n < m`,
then $`m - n` is also a natural number.
:::

```lean "natural_sub_of_lt_proof"
theorem natural_sub_of_lt
  (n_mem_Natural : n ∈ Natural)
  (m_mem_Natural : m ∈ Natural)
  (n_lt_m : n < m)  :m - n ∈ Natural := by
  let H : Set ℝ :=
    {m ∈ Natural |
      ∀ k ∈ Natural, k < m → m - k ∈ Natural}
  have IH : Inductive H := by
    constructor
    . show 1 ∈ H
      change 1 ∈ Natural ∧
        (∀ k ∈ Natural, k < 1 → 1 - k ∈ Natural)
      constructor
      . exact one_mem_Natural
      intro n n_is_natural hn
      false_or_by_contra
      exact not_le_of_gt hn
        (one_le_natural n_is_natural)
    . show ∀ {x : ℝ}, x ∈ H → x + 1 ∈ H
      intro x x_mem_H
      have x_mem_Natural : x ∈ Natural := by
        exact x_mem_H.left
      change (x + 1) ∈ Natural ∧
        ∀ k ∈ Natural, k < x + 1 → (x + 1) - k  ∈ Natural
      constructor
      . exact (succ_mem_Natural x_mem_Natural)
      . show ∀ k ∈ Natural, k < x + 1 → x + 1 - k ∈ Natural
        intro k k_mem_Natural k_lt_succ_x
        have : k < x ∨ k = x := by
          exact lt_or_eq_of_le (natural_le_of_lt_succ
            k_mem_Natural x_mem_Natural k_lt_succ_x)
        rcases this with k_lt_x | k_eq_x
        . show x + 1 - k ∈ Natural
          have x_sub_n_mem_Natural : x - k ∈ Natural := by
            exact x_mem_H.right k k_mem_Natural k_lt_x
          have : x + 1 - k = x - k + 1 := by ring
          rw [this]
          exact (succ_mem_Natural
            x_sub_n_mem_Natural : x - k + 1 ∈ Natural)
        . show x + 1 - k ∈ Natural
          subst k
          have : x + 1 - x = 1 := by ring
          rw [this]
          exact (one_mem_Natural : 1 ∈ Natural)
  have : m ∈ H := by
    exact m_mem_Natural IH
  exact (this.right n n_mem_Natural n_lt_m
    : m - n ∈ Natural)
```


# The Well Ordering Principle

We are now going to prove a very important property of `Natural`.

:::definition "minimum" (tags := "Minimum of a set")
If $`A` is a set of real numbers, a real number $`a` is said to be the
minimum of $`A` if the two following conditions are met:
* `a ∈ A`;
* If `b ∈ A`, then `a ≤ b`
:::

Not every set `A ⊆ ℝ` has a minimum (on this we will return later)
but if we suppose `A ⊆ Natural`, then thing changes:

:::theorem "Well_Ordering"(tags := "Well-Ordering Principle")
If `A ⊆ Natural` and `A` is not the empty set
then `A` has a minimum.
:::

:::proof "Well_Ordering"
It is convenient to consider the following set: Let

`H :=  {
    n ∈ Natural |
    ∀ S ⊆ Natural, n ∈ S → ∃ m ∈ Natural, IsLeast S m
    }
`

We will prove that `H` is inductive. Then, by the _Principle of Induction_
{uses "Principle_of_Induction"}[] we conclude that $`Natural ⊆ H`.
Below we give a `Lean` proof.
:::


```lean "Well_Ordering_proof"
theorem well_ordering :
  ∀ A ⊆ Natural, A.Nonempty →
    ∃ m ∈ Natural, IsLeast A m := by
  let H :=  {
    n ∈ Natural |
    ∀ S ⊆ Natural, n ∈ S → ∃ m ∈ Natural, IsLeast S m
    }
  have H_subset_Natural : H ⊆ Natural := by
    intro n n_mem_H
    exact n_mem_H.left

  have IH : Inductive H := by
    constructor

    . show 1 ∈ H
      change 1 ∈ Natural ∧
        ∀ S ⊆ Natural, 1 ∈ S → ∃ m ∈ Natural, IsLeast S m
      constructor
      . show 1 ∈ Natural
        exact one_mem_Natural
      . show ∀ S ⊆ Natural,
          1 ∈ S → ∃ m ∈ Natural, IsLeast S m
        intro S S_subset_Natural one_mem_S
        use 1
        constructor
        . exact one_mem_Natural
        . show IsLeast S 1
          constructor
          . show 1 ∈ S
            exact one_mem_S
          . show 1 ∈ lowerBounds S
            intro s s_mem_S
            have s_mem_Natural : s ∈ Natural := by
              exact S_subset_Natural s_mem_S
            exact one_le_natural s_mem_Natural

    . show  ∀ {k : ℝ}, k ∈ H → k + 1 ∈ H
      intro k k_mem_H
      change k + 1 ∈ Natural ∧
        ∀ S ⊆ Natural,
          k + 1 ∈ S → ∃ m ∈ Natural, IsLeast S m

      have k_mem_Natural : k ∈ Natural := by
          exact k_mem_H.left

      have succ_k_mem_Natural : k + 1 ∈ Natural := by
        exact (succ_mem_Natural k_mem_Natural
                : k + 1 ∈ Natural)
      constructor

      . show k + 1 ∈ Natural
        exact succ_k_mem_Natural
      . show ∀ S ⊆ Natural, k + 1 ∈ S →
          ∃ m ∈ Natural, IsLeast S m
        intro S S_subset_Natural succ_k_mem_S
        by_cases k_mem_S : k ∈ S
        . show ∃ m ∈ Natural, IsLeast S m -- k ∈ S
          exact (k_mem_H.right S S_subset_Natural k_mem_S)
        . show ∃ m ∈ Natural, IsLeast S m -- k ∉ S
          let S' := S ∪ {k}

          have S_subset_Natural' : S' ⊆ Natural := by
            intro s s_mem_S'
            rcases s_mem_S' with s_mem_S | s_eq_k
            . show s ∈ Natural
              exact S_subset_Natural s_mem_S
            . show s ∈ Natural
              have : s = k := by
                exact s_eq_k
              subst s
              exact (k_mem_Natural : k ∈ Natural)

          have k_mem_S' : k ∈ S' := by
            exact Set.mem_union_right S rfl

          have S_subset_S' : S ⊆ S' := by
            intro x x_mem_S
            exact Set.mem_union_left {k} x_mem_S

          have : ∃ m ∈ Natural, IsLeast S' m := by
            exact
              (k_mem_H.right S' S_subset_Natural' k_mem_S')
          rcases this with ⟨m, m_mem_Natural, m_least_S'⟩
          by_cases hmS : m ∈ S

          . show ∃ m ∈ Natural, IsLeast S m -- m ∈ S

            have : m ∈ lowerBounds S := by
              intro s s_mem_S
              exact m_least_S'.right (S_subset_S' s_mem_S)
            use m
            exact ⟨m_mem_Natural, hmS, this⟩
          . show ∃ m ∈ Natural, IsLeast S m -- m ∉ S

            have m_eq_k : m = k := by
              rcases m_least_S'.left with m_mem_S | m_eq_k
              . false_or_by_contra
                exact hmS m_mem_S
              . exact m_eq_k

            have : ∀ s ∈ S, k + 1 ≤ s := by
              intro s s_mem_S
              have s_mem_S' : s ∈ S' := by
                exact Set.mem_union_left {k} s_mem_S

              have k_ne_s : k ≠ s := by
                intro k_eq_s
                subst k
                subst m
                exact hmS s_mem_S

              have k_le_s : k ≤ s := by
                subst m
                exact m_least_S'.right s_mem_S'

              have : k < s := by
                exact lt_of_le_of_ne k_le_s k_ne_s
              exact natural_add_one_le_of_lt
                k_mem_Natural
                (S_subset_Natural s_mem_S)
                this
            use k + 1
            constructor

            . show k + 1 ∈ Natural
              exact succ_k_mem_Natural

            . show IsLeast S (k + 1)
              constructor

              . show k + 1 ∈ S
                assumption

              . show k + 1 ∈ lowerBounds S
                assumption

  have H_eq_Natural : H = Natural := by
    exact eq_natural_of_subset_of_inductive
          H_subset_Natural -- H ⊆ Natural
          IH               -- Inductive H

  intro A A_subset_Natural A_nonempty
  rcases A_nonempty with ⟨n, n_mem_A⟩

  have n_mem_Natural : n ∈ Natural := by
    exact (A_subset_Natural n_mem_A)

  have : n ∈ H := by
    rw [H_eq_Natural]
    exact n_mem_Natural

  show  ∃ m ∈ Natural, IsLeast A m
  exact this.right A A_subset_Natural n_mem_A
```

# Exercises
1. Demonstrate the _strong_ induction principle:
Let `H ⊆ Natural` such that the two following conditions are met:
  * `1 ∈ H` ;
  *  If `k ∈ H` for all `k ≤ n`,  then `n + 1 ∈ H`.
Then `H = Natural`

2. Let $`n₀` be any natural number and let `H ⊆ Natural` such that the two
following conditions are met:
  * `n₀ ∈ H`;
  * If `k ∈ H` for a certain natural $`k`, then `k + 1 ∈ H`.
  Prove that `H = {n ∈ Natural : n₀ ≤ n}`
```lean "end NaturalNumbers"

end NaturalNumbers
```
