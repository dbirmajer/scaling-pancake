import Mathlib.Data.Nat.Notation
import Mathlib.Data.Real.Basic
--import Mathlib.Tactic.Ring
import Mathlib.Tactic

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

# The _less or equal_ Relation in ℝ

```lean "open LE"
namespace LE
```
:::definition "le"
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

```lean "end LE"
end LE
```
# The Natural Numbers

We now distinguish certain subsets of the real numbers, beginning with the
natural numbers—the numbers used for counting: $`0, 1, 2, 3,\ldots`.
Starting from $`0` and $`1`, define $`2 = 1 + 1,\; 3 = 2 + 1`, and so on.
The property $`0 < 1` implies that each new number is greater than,
and therefore distinct from, those preceding it.

However, “and so on” is not a precise definition.
We therefore seek a property characterizing the natural numbers.

They contain $`0` and are closed under adding $`1`: if $`x` belongs to the set,
then so does $`x + 1`. These conditions alone do not uniquely determine the
natural numbers, since larger subsets of ℝ may also satisfy them.

For brevity, we now give such sets a name:

:::definition "inductive_set"(tags := "Inductive Set")
A subset $`A` of the real numbers is said to be _inductive_ if it has the
following properties:
  * The real number $`0` belongs to $`A`
  * If any real number $`x` belongs to $`A`,
  then the real number $`x + 1` also belongs to $`A`.
:::

```lean "open NaturalNumbers"
namespace NaturalNumbers
```

```lean "inductive_set"
def Inductive (A : Set ℝ) : Prop :=
    0 ∈ A ∧
      ∀ {x : ℝ}, x ∈ A → x + 1 ∈ A
```

:::lemma_ "ℝ_{ ≥ 0} is inductive"
$`ℝ_{≥ 0}` is an inductive set.
:::

```lean "inductive_zero_le"
lemma inductive_zero_le : Inductive {x : ℝ | 0 ≤  x} := by
  constructor
  . show 0 ∈ {x : ℝ| 0 ≤ x}
    have : (0 : ℝ) = (0 : ℝ) := by rfl
    exact le_of_eq this
  . show ∀ {x : ℝ}, x ∈ {x | 0 ≤ x} → x + 1 ∈ {x | 0 ≤ x}
    intro x hx
    have : 0 < x + 1 := by
      calc
      0 ≤ x := by exact hx
      _ = 0 + x := by rw [zero_add]
      _ < 1 + x := by exact add_lt_add_left (zero_lt_one) x
      _ = x + 1 := by rw [add_comm]
    exact le_of_lt this
```
⋄⋄⋄⋄⋄⋄⋄⋄⋄⋄⋄⋄⋄⋄⋄⋄⋄⋄⋄⋄⋄⋄⋄⋄
The set of natural numbers can be characterized as the _smallest_ of all
inductive subsets of ℝ.

:::definition "natural_number"
A real number $`x ∈ ℝ` is a natural number if $`x` belongs to all the
inductive subsets of ℝ. The set of natural numbers is denoted as `Natural`.
:::

```lean "natural_number"
-- The Set of Natural numbeers
def Natural := ⋂₀ {A : Set ℝ | Inductive A}
```

Equivalently, `n : Natural` means that `n` is an
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

example (n m : Natural) : n = m ↔ (n : ℝ) = (m : ℝ) := by
  constructor
  . exact congrArg Subtype.val
  . apply Subtype.ext
```

:::corollary "natural_nonnegative"
`Natural ⊆ {x : ℝ | 0 ≤ x}`
:::

```lean "natural_nonnegative"
theorem natural_nonegative :
  Natural ⊆ {x : ℝ | 0 ≤ x} := by
    apply Set.sInter_subset_of_mem
    exact inductive_zero_le
```

:::lemma_ "inductive_natural"
The set of natural numbers `Natural` is inductive.
:::

:::proof "inductive_natural"
We prove that `0 ∈ Natural` and the inductive step,
`n ∈ Natural → n + 1 ∈ Natural`.
:::

```lean "inductive_natural_proof"
theorem inductive_natural : Inductive Natural := by
  constructor
  . show 0 ∈ Natural
    intro A hA
    exact hA.left
  . show ∀ n : ℝ, n ∈ Natural → (n + 1) ∈ Natural
    intro n hn A hA
    have : Natural ⊆ A := by
      exact Set.sInter_subset_of_mem hA
    have : n ∈ A := by
      exact this hn
    exact hA.right this

-- theorem zero_mem_Natural : 0 ∈ Natural := by
--   exact inductive_natural.left

def zero : Natural := ⟨0, inductive_natural.left⟩

-- It is useful to register coercion lemmas once:
@[simp]
theorem coe_zero :
    ((zero : Natural) : ℝ) = 0 := by
  rfl

theorem zero_le (n : Natural) : zero ≤ n := by
  change (0 : ℝ) ≤ (n : ℝ)
  exact natural_nonegative n.property

def succ (n : Natural) : Natural :=
  ⟨n + 1, inductive_natural.right n.property⟩

def one : Natural := succ zero

-- It is useful to register coercion lemmas once:
@[simp]
theorem coe_succ (n : Natural) :
    ((succ n : Natural) : ℝ) = (n : ℝ) + 1 := by
  rfl

theorem succ.inj {n m : Natural} :
  succ n = succ m → n = m := by
  simp [succ]
  apply Subtype.ext


theorem zero_lt_succ (n : Natural) :
  zero < succ n := by
  change (0 : ℝ) < (n : ℝ) + 1
  calc (0 : ℝ)
  _ ≤ (n : ℝ) := by exact zero_le n
  _ = (0 : ℝ) + (n : ℝ) := by rw [zero_add]
  _ < (1 : ℝ) + (n : ℝ) := by
    exact add_lt_add_left zero_lt_one (n : ℝ)
  _ = n + 1 := by rw [add_comm]
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
theorem eq_natural_of_subset_of_inductive {H}
  (hH : H ⊆ Natural)
  (IH : Inductive H) : H = Natural := by
    apply Set.Subset.antisymm
    . exact hH
    . exact Set.sInter_subset_of_mem IH
```
```lean "induction"
theorem induction
    {P : Natural → Prop}
    (zero_case : P zero)
    (succ_case : ∀ n : Natural, P n → P (succ n)) :
    ∀ n : Natural, P n := by
  intro n

  let H : Set Natural := {k | P k}
  let H' : Set ℝ := Subtype.val '' H

  have hH'_subset : H' ⊆ Natural := by
    intro x hx
    rcases hx with ⟨k, hk, rfl⟩
    exact k.property

  have hH'_inductive : Inductive H' := by
    constructor
    · -- zero case
      exact ⟨zero, zero_case, rfl⟩

    · -- successor case
      intro x hx
      rcases hx with ⟨k, hk, rfl⟩
      exact ⟨succ k, succ_case k hk, rfl⟩

  have hH'_eq : H' = Natural :=
    eq_natural_of_subset_of_inductive
      hH'_subset hH'_inductive

  have hnH' : (n : ℝ) ∈ H' := by
    rw [hH'_eq]
    exact n.property

  rcases hnH' with ⟨k, hkH, hk_eq_n⟩

  have hkP : P k := by
    change P k at hkH
    exact hkH

  have hkn : k = n :=
    Subtype.ext hk_eq_n

  subst n
  exact hkP
```

We will now use the principle of induction to prove elementary properties of
natural numbers.

:::proposition "add_natural"
If $`n` and $`m` are natural numbers, then $`m + n` and $`m ⋅ n` are also
natural numbers.
:::
■■■■■■■■■■■■■■■■■■■■■■■■■■■■■■■■

```lean "add"
def add (n m : Natural) : Natural :=
  have hnm: (n : ℝ) + (m : ℝ) ∈ Natural := by
    let H := {x : ℝ | n + x ∈ Natural}

    have IH : Inductive H := by
      unfold Inductive
      constructor

      . show 0 ∈ H
        change (n : ℝ) + 0 ∈ Natural
        --intro A hA
        have : (n : ℝ) + 0 = (n : ℝ) := by ring
        rw [this]
        exact n.property


      . show ∀ {x : ℝ}, x ∈ H → (x + 1) ∈ H
        intro x hx
        change ((n : ℝ) + (x + (1 : ℝ))) ∈ Natural
        rw [← add_assoc]
        exact inductive_natural.right hx

    change (m : ℝ) ∈ H
    have : Natural ⊆ H := by
      exact Set.sInter_subset_of_mem IH

    exact this m.property
  ⟨(n : ℝ) + (m : ℝ), hnm⟩


instance : Add Natural where
  add := add

@[simp]
theorem coe_add (n m : Natural) :
    ((n + m : Natural) : ℝ) =
      (n : ℝ) + (m : ℝ) := by
  rfl
```

```lean "add_succ"
theorem add_succ (n m : Natural) :
  add n (succ m) = succ (add n m) := by
  apply Subtype.ext
  change
    (n : ℝ) + ((m : ℝ) + 1) =
      (n : ℝ) + (m : ℝ) + 1
  rw [add_assoc]
```

```lean "Natural.add_zero"
theorem Nat_add_zero (n : Natural) :
  n + zero  = n := by

  apply Subtype.ext
  change (n : ℝ) + (0 : ℝ) = (n : ℝ)
  exact add_zero (n : ℝ)
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

```lean "mul"
def mul (n m : Natural) : Natural := by
  have hnm : (n : ℝ) * (m : ℝ) ∈ Natural := by
    let H := {x : ℝ | (n : ℝ) * x ∈ Natural}

    have IH : Inductive H := by
      unfold Inductive
      constructor

      . show 0 ∈ H
        intro A hA
        rw [mul_zero]
        exact hA.left

      . show ∀ {x : ℝ}, x ∈ H → (x + 1) ∈ H
        intro x hx
        change ((n : ℝ) * (x + (1 : ℝ))) ∈ Natural
        rw [mul_add, mul_one]
        let nx : Natural  := ⟨(n : ℝ) * x, hx⟩
        exact (nx + n).property

    change (m : ℝ) ∈ H
    exact Set.sInter_subset_of_mem IH m.property

  exact ⟨(n : ℝ) * (m : ℝ), hnm⟩


instance : Mul Natural where
  mul := mul

@[simp]
theorem coe_mul (n m : Natural) :
    ((n * m : Natural) : ℝ) =
      (n : ℝ) * (m : ℝ) := by
  rfl
```

```lean "Nat_mul_one"
@[simp]
theorem Nat_mul_one (n : Natural) :
    n * one = n := by
  change mul n one = n
  simp [mul, one]
```

```lean "mul_succ"
@[simp]
theorem mul_succ (n m : Natural) :
  n * (succ m) = (n * m) + n := by
  apply Subtype.ext
  simp only [coe_mul, coe_add, coe_succ]
  ring
```

# More Properties of the Natural Numbers

We want now to prove the fact, intuitively clear, that if a natural number is
subtracted from a smaller natural number, the result is a natural number.
As a preliminary step, we prove the following Proposition.

:::theorem "th_1.7."
If $`n` is a natural number then either $`n = 0` or $`n - 1` is a natural
number.
:::

```lean "thm_1.7_proof"
theorem sub_one_of_pos (n : Natural) (hn : zero < n) :
    (n : ℝ) - 1 ∈ Natural := by

  let H : Set ℝ :=
    {x ∈ Natural | x = 0 ∨ (0 < x ∧ x - 1 ∈ Natural)}

  have hH : H ⊆ Natural := by
    intro n hn
    exact hn.left

  have IH : Inductive H := by
    constructor
    . show 0 ∈ H
      change 0 ∈
        Natural ∧ (0 = 0 ∨ (0 < 0 ∧ 0 - 1 ∈ Natural))
      constructor
      . exact inductive_natural.left
      . exact Or.inl rfl

    . show ∀ {x : ℝ}, x ∈ H → x + 1 ∈ H
      intro x hx
      let nx : Natural := ⟨x,  hH hx⟩
      have x_is_natural : x ∈ Natural := by exact hH hx

      have e1 : 0 < x + 1 := by
        calc
        0 =  0 + 0 := by rw [add_zero]
        _ < x + 1 := by exact
            add_lt_add_of_le_of_lt (zero_le nx) zero_lt_one

      change x + 1 ∈ Natural
          ∧ (x + 1 = 0 ∨
              (0 < x + 1 ∧ x + 1 - 1 ∈ Natural))

      constructor

      . exact (succ nx).property

      . have e2 : x + 1 - 1 ∈ Natural := by
          norm_num
          exact hH hx
        exact Or.inr ⟨e1, e2⟩

  have HN : H = Natural := by
    exact eq_natural_of_subset_of_inductive hH IH

  have nH : (n : ℝ) ∈ H := by
    exact HN.symm.le n.property

  rcases nH.right with  zero_eq_n | zero_lt_n
  .
    false_or_by_contra
    have : zero = n := by
      apply Subtype.ext zero_eq_n.symm
    exact ne_of_lt hn this

  . show (n : ℝ) - 1 ∈ Natural
    exact zero_lt_n.right
```


:::lemma_ "succ_le_of_lt"
Let `n, m ∈ Natural`. If  `n < m`, then `n + 1 ≤ m`.
:::

```lean "succ_le_of_lt"
theorem succ_le_of_lt (n : Natural) :
  ∀ m : Natural, n < m → succ n ≤ m := by
  let P (k : Natural) : Prop :=
    ∀ m : Natural, k < m → succ k  ≤ m

  have zero_case : P zero := by
    intro m hm
    change 0 + 1 ≤ (m : ℝ)

    have : (0 : ℝ) + (1 : ℝ) = (1 : ℝ) := by ring
    rw [this]

    have : (m : ℝ) - 1 ∈ Natural := by
      exact sub_one_of_pos m hm

    have : 0 ≤ (m : ℝ) - 1 :=
      by exact zero_le ⟨(m : ℝ) - 1, this⟩

    calc
    1 = 0 + 1 := by rw [zero_add]
    _ ≤ (m : ℝ) - 1 + 1 := by exact add_le_add_left this 1
    _ = (m : ℝ) := by ring

  have succ_case : ∀ k : Natural, P k → P (succ k) := by

    intro k pk
    change ∀ m : Natural, succ k < m → succ (succ k) ≤ m
    intro m hm
    simp [succ] at hm
    simp [succ]

    have : (0 : ℝ) ≤ (k : ℝ) := by
      exact zero_le k

    have : 0 < (m : ℝ) := by
      calc (0 : ℝ)
      _ < 1 := by exact zero_lt_one
      _ = 0 + 1 := by rw [zero_add]
      _ ≤ (k : ℝ) + 1 := by
        exact add_le_add_left this 1
      _ < m := by exact hm

    have hm_sub_one : (m : ℝ) - 1 ∈ Natural := by
      exact sub_one_of_pos m this

    have : (k : ℝ) + 1 < (m : ℝ) := by
      exact hm

    have : (k : ℝ) < (m : ℝ) - 1 := by
      calc (k : ℝ)
      _ = k + 1 - 1 := by ring
      _ < (m : ℝ) - 1 := by
        exact add_lt_add_left this (-1)

    have : (k : ℝ) + 1 ≤ (m : ℝ) - 1 := by
      exact pk ⟨(m : ℝ) - 1, hm_sub_one⟩ this


    calc (k : ℝ) + 1 + 1
    _ ≤ (m : ℝ) - 1 + 1 := by
      exact add_le_add_left this 1
    _ = m := by ring

  exact induction zero_case  succ_case n
```
:::corollary "le_of_lt_succ"
Let `n, m ∈ Natural`. If  `n < m + 1`, then `n ≤ m`.
:::

```lean "le_of_lt_succ"

theorem le_of_lt_succ (n : Natural) :
  ∀ m : Natural, n < succ m → n ≤ m := by

  intro m hnm

  have hsucc : succ n ≤ succ m := by
     exact succ_le_of_lt n (succ m) hnm

  simp [succ] at hsucc
  exact hsucc
```

Now we are in a position to prove the announced result:

:::theorem "natural_sub_of_lt"
If $`m` and $`n` are natural numbers and $`n < m`,
then $`m - n` is also a natural number.
:::


```lean "sub_of_lt"
theorem sub_of_le (n : Natural) :
  ∀ m : Natural, n ≤ m → (m : ℝ) - (n : ℝ) ∈ Natural := by
  let P (k : Natural) :=
    ∀ m : Natural, k ≤ m → (m : ℝ) - (k : ℝ) ∈ Natural

  have zero_case : P zero := by
    unfold P
    intro m hm
    simp [zero]

  have succ_case : ∀ k : Natural, P k → P (succ k) := by
    unfold P
    intro k pk m hkm
    simp [succ]

    have k_lt_m : (k : ℝ) < (m : ℝ) :=
      calc (k : ℝ)
      _ = (0 : ℝ) + (k : ℝ)  := by rw [zero_add]
      _ < (1 : ℝ) + (k : ℝ)  := by
        exact add_lt_add_left zero_lt_one (k : ℝ)
      _ = (k : ℝ) + (1 : ℝ) := by rw [add_comm]
      _ ≤ (m : ℝ) := by exact hkm

    have : (m : ℝ) - (k : ℝ) ∈ Natural :=
      by exact pk m (le_of_lt k_lt_m)

    let nmk  : Natural := ⟨(m : ℝ) - (k : ℝ), this⟩

    have : (m : ℝ) - (k : ℝ) - 1  =
      (m : ℝ)  - ((k : ℝ) + 1) := by
      ring

    rw [← this]

    have : 0 < (m : ℝ) - (k : ℝ) := by
      calc
      0 = (k : ℝ) - (k : ℝ) := by ring
      _ < (m : ℝ) - (k : ℝ) := by
        exact add_lt_add_left k_lt_m (-k : ℝ)

    exact sub_one_of_pos nmk this

  exact induction zero_case succ_case n
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
If `A ⊆ Natural` and `A` is not the empty set then `A` has a minimum.
:::

:::proof "Well_Ordering"
It is convenient to consider the following proposition: Let

-- `H :=  {
--     n ∈ Natural |
--     ∀ S ⊆ Natural, n ∈ S → ∃ m ∈ Natural, IsLeast S m
--     }
-- `

`
P(n) := ∀ H ⊆ Natural, n ∈ H → ∃ m ∈ H, IsLeast H m
`
We will prove that `H` is inductive. Then, by the _Principle of Induction_
{uses "Principle_of_Induction"}[] we conclude that $`Natural ⊆ H`.
Below we give a `Lean` proof.
:::


```lean "Well_Ordering_proof"
theorem well_ordering :
  ∀ A ⊆ Natural, A.Nonempty →
    ∃ m, IsLeast A m := by
  let P (n : Natural) : Prop :=
    ∀ H ⊆ Natural, (n : ℝ) ∈ H → ∃ m, IsLeast H m

  have zero_case : P zero := by
    intro H hH hnH
    use 0
    unfold IsLeast
    constructor
    . exact hnH
    . unfold lowerBounds
      intro a haH
      exact zero_le ⟨a, hH haH⟩

  have succ_case : ∀ n : Natural,
    P n → P (succ n) := by
    intro n pn H hH succnH

    by_cases hnH : ↑n ∈ H

    . rcases pn H hH hnH with ⟨m, hm⟩ -- hnH : ↑n ∈ H
      use m

    . let H' := H ∪ {↑n}  -- ↑n ∉ H

      have hH' : H' ⊆ Natural := by
        apply Set.union_subset
        · exact hH
        · exact Set.singleton_subset_iff.mpr n.property

      have hnH' : ↑n ∈ H' := by
        exact Set.mem_union_right H
          (Set.mem_singleton (n : ℝ))

      rcases pn H' hH' hnH' with ⟨m, hm⟩

      by_cases hmH : m ∈ H
      . use m -- hmH : m ∈ H
        unfold IsLeast
        constructor
        . exact hmH
        . intro x hxH
          have : x ∈ H' := by
            exact Set.mem_union_left {↑n} hxH
          exact hm.right this

      . use (succ n) -- hmH : m ∉ H
        have : m = n := by
          rcases hm.left with hm_in_H  | hm_in_singleton
          . exact False.elim (hmH hm_in_H)
          . simpa using hm_in_singleton
        rw [this] at hm
        rw [this] at hmH

        constructor
        . exact succnH
        . intro x hxH

          have x_mem_Nat : x ∈ Natural := by
            exact hH hxH

          have hxH' : x ∈ H' := by
            exact Set.mem_union_left {↑n} hxH

          have : x ≠ n := by
            intro x_eq_n
            subst x
            exact hmH hxH

          have : n < x := by
            exact
              (lt_of_le_of_ne (hm.right hxH') this.symm )

          exact succ_le_of_lt n ⟨x, x_mem_Nat⟩ this

  intro A hA hA_nonempty
  rcases hA_nonempty with ⟨n, hnA⟩
  have : n ∈ Natural := by
    exact hA hnA
  exact (induction zero_case succ_case ⟨n, this⟩) A hA hnA
```

# Exercises
1. Demonstrate the _strong_ induction principle:
Let `H ⊆ Natural` such that the two following conditions are met:
  * `0 ∈ H` ;
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
