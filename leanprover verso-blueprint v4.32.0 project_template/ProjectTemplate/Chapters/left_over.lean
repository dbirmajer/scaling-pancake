import Mathlib.Data.Nat.Notation
import Mathlib.Data.Real.Basic

namespace Section_1_3_LO
def Inductive (A : Set ℝ) : Prop :=
  (1 : ℝ) ∈ A ∧ (∀ (x : ℝ),  x ∈ A → (x + 1) ∈ A)

def isNatural (x : ℝ) : Prop :=
  ∀ {A : Set ℝ}, Inductive A → x ∈ A

def Natural : Set ℝ := {x | isNatural x}

-- Lean abreviation for:
example {x : ℝ} :
  x ∈ Natural ↔ isNatural x := by
  rfl

theorem one_is_natural : (1 : ℝ) ∈ Natural := by
  change isNatural (1 : ℝ)
  intro A ⟨h1, _⟩
  exact h1

theorem succ_is_natural :
  ∀ {n : ℝ}, n ∈ Natural → (n + 1) ∈ Natural := by
    intro n hn
    have hn' : isNatural n :=
      by exact hn
    change isNatural (n + 1 : ℝ)
    unfold isNatural
    intro A hA
    have : n ∈ A := by
      exact hn' hA
    exact (hA.right n) this
--

def oneNatural : Natural :=
  ⟨1, one_is_natural⟩

def succNatural (n : Natural) : Natural :=
  ⟨n.val + 1, succ_is_natural n.property⟩

theorem induction_principle
    (P : Natural → Prop)
    (h_base : P oneNatural)
    (h_step : ∀ n : Natural, P n → P (succNatural n)) :
    ∀ n : Natural, P n := by
    let H := { n : Natural | P n}

    -- The notation '' means set image.
    let HReal : Set ℝ :=
      (fun n : Natural => (n : ℝ)) '' H

    let HReal' : Set ℝ :=
      {x : ℝ | ∃ n : Natural, P n ∧ (n : ℝ) = x}
    --have : Inductive (H : set ℝ) := by sorry
    sorry

-- `n ∈ Natural` is a proposition: it says that a real
-- number `n`  belongs to the set `Natural`.
-- `n : ℝ`
-- `hn : n ∈ Natural`
--Here `n` is an ordinary real number,
--and `hn` is separate evidence that it is natural.

-- By contrast, `n : Natural` means that `n` is an
-- element of the subtype determined by the set `Natural`:
-- n : {x : ℝ // x ∈ Natural}
-- So it packages both pieces together:
-- `n.val`        -- the underlying real number
-- `n.property`        -- a proof that n.1 ∈ Natural

example (n : ℝ) (hn : n ∈ Natural) : Natural :=
  by exact ⟨n, hn⟩

-- If `n : Natural`, then Lean treats `(n : ℝ)`
-- as the underlying real number stored in the subtype. So:
-- `(n : ℝ) ∈ Natural` and `n.val ∈ Natural` mean
-- the same thing.

example (n : Natural) : n.val ∈ Natural := by
  exact n.property

example (n : Natural) : (n : ℝ) ∈ Natural := by
  exact n.property

theorem induction' {P : ℝ → Prop}
  (h1 : P 1) (ih : ∀ n : ℝ, n ∈ Natural → P n → P (n + 1))
    : ∀ n : ℝ, n ∈ Natural → P n := by sorry

theorem induction_pple {P : ℝ → Prop}
  (h1 : P 1) (ih : ∀ n ∈ Natural,  P n → P (n + 1))
    : ∀ n ∈ Natural, P n := by sorry

theorem induction {P : ℝ → Prop}
  (h1 : P 1)
  (hs : ∀ x : ℝ, P x → P (x + 1)) :
    Natural ⊆ {x | P x} := by
      let S := {x : ℝ | P x}
      have : Inductive S := by
        unfold Inductive
        constructor
        . exact h1
        . exact hs
      intro x hx
      change x ∈ S
      change isNatural x at hx
      exact hx this


example (n : ℕ) : 0 ≤ n := by
  exact Nat.zero_le n

theorem zero_le (n : ℕ) : 0 ≤ n := by
  induction n with
  | zero => exact le_of_eq rfl
  | succ n ih =>
      calc 0
      ≤ n := by exact ih
      _ = n + 0 := by rw [add_zero]
      _ <= n + 1 := by exact
        add_le_add_right (le_of_lt zero_lt_one) n

-- :::corollary "Nat.cast_nonneg"(parent := "natural-numbers")(lean := "Nat.cast_nonneg")
-- This theorem in necessary in Lean 4 beacuse of the Type theory.
-- Write a Chat GPT explanation
-- If n ∈ ℕ, then $`0 ≤ (n : ℝ)`
-- :::

example (n : ℕ) : 0 ≤ (n : ℝ) := by
  exact Nat.cast_nonneg n



-- :::theorem "th_1.6" (parent := "natural-numbers")(lean := "Nat.succ_le_of_lt")
-- If $`n` is a natural number other than $`0`, then $`n \ge 1`
-- :::



example {n : ℕ} : n ≠ 0 → 0 < n := by
  intro h
  exact pos_of_ne_zero h

lemma pos_of_ne_zero {n : ℕ}: n ≠ 0 → 0 < n := by
  induction n with
  | zero =>
      intro h
      contradiction
  | succ n ih =>
      by_cases h' : n = 0
      . intro _
        subst h'
        rw [zero_add]
        exact zero_lt_one
      . intro _
        calc 0
          < n := by exact ih h'
          _ = n + 0 := by rw [add_zero n]
          _ <  n + 1 := by exact
            add_lt_add_right (zero_lt_one) n

example {n : ℕ} (h : 0 < n) : 1 ≤ n := by
  exact Nat.succ_le_of_lt h

example (h : 0 < n) : (1 ≤ n) := by
  induction n with
  | zero => contradiction
  | succ n ih =>
  by_cases h' : n = 0
  . rw [h']
  . -- case n ≠ 0
    have : 0 ≤ 1 := by exact (le_of_lt (zero_lt_one))
    calc n + 1
    _ ≥ 1 + 1 := by exact
        add_le_add_left (ih (pos_of_ne_zero h')) 1
    _ ≥ 0 + 1 := add_le_add_left this 1
    _ = 1 := by exact (zero_add (1 : ℕ))

example (n : ℕ)  :
  (n = 0) ∨ (∃ m : ℕ, m  = n - 1) := by
  cases n
  case zero => exact Or.inl rfl
  case succ n =>
      right
      use n
      exact Nat.add_succ_sub_one n 0


-- There is a popular form of the _principle of induction_ that we are going
-- to indicate now.

-- :::corollary "cor_1.4"(tags := "Induction Principle")
-- Suppose that for each natural number $`n` we have a statement $`P(n)` about it
-- in such a way that the two following conditions are verified:
-- * The statement $`P(1)` is true.
-- * For every natural number $`n` the following occurs: if we suppose that
-- $`P(n)` is true we can then deduce that $`P(n+1)` is also true.

-- In that case the statement $`P(n)` is true for every natural
-- number $`n`.
-- :::

-- :::proof "cor_1.4"
-- Proof: Consider the following set:

-- $$`H = {n ∈ N : P(n) \; \text{is true}}`
-- (read _$`H` equal to the set of the $`n` belonging to the naturals such
-- that $`P(n)` is true_).

-- In the first place, by its own construction, $`H` is a subset of ℕ;
-- in effect, the elements of $`H` are those natural numbers $`n` for which
-- $`P(n)` is true, that is, the elements of $`H` are all natural numbers.

--  But furthermore $`H` is inductive; in effect, $`1 ∈ H` because by
--  hypothesis $`P(1)` is true and, on the other hand,
--  if $`n ∈ H` then $`P(n)` is true; by hypothesis,
--  that implies that $`P(n + 1)` is true, or what is the same $`n + 1 ∈ H`.

-- Being $`H` an inductive subset of ℕ, *Theorem 1.3.* tells us that $`H = ℕ`.
-- But this last statement means exactly that $`P(n)` is true for all `n ∈ ℕ`.
-- :::

-- ```lean "Principle of Induction"
#print Natural

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


theorem pple_of_induction {P : ℝ → Prop}
  (h1 : P 1)
  (hs : ∀ {x : ℝ}, P x → P (x + 1)) :
    Natural ⊆ {x | P x} := by
      let S := {x : ℝ | P x}
      have : Inductive S := by
        unfold Inductive
        constructor
        . exact h1
        . intro x
          exact hs
      change Natural ⊆ S
      exact natural_subset_of_inductive this

example {x : ℝ} :
  x ∈ Natural ↔ isNatural x := by
  constructor
  . intro hx
    exact hx
  . intro hx
    exact hx

/-
:::definition "1.2"
We will call the set of natural numbers, and we will indicate it with
`Natural`, the subset of real numbers characterized by the following
properties:
  * $`\mathrm{N_1.}` `Natural` is inductive.
  * $`\mathrm{N_2.}` If $`A` is any inductive subset of real numbers,
  then $`Natural ⊆ A`. Equivalently, a real number $`x` is natural if
  $`x` belongs to all inductive subsets of $`ℝ`. In `Lean`:
:::
-/

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

theorem inductive_natural : Inductive Natural := by
  constructor
  .-- (1 : ℝ) ∈ Natural
    intro A hA
    exact hA.left
  .-- n ∈ Natural → (n + 1) ∈ Natural := by
    intro n hn A hA
    exact hA.right (hn hA)

example (n : Natural) (hn : 1  < (n : ℝ)) :
  (n : ℝ) - 1 ∈ Natural := by
  let H : Set ℝ :=
    {n ∈ Natural | n = 1 ∨ (1 < n ∧ n - 1 ∈ Natural)}
  have one_is_natural : 1 ∈ Natural := by exact
    inductive_natural.left
  have hH : H ⊆ Natural := by
    intro n hn
    exact hn.left
  have IH : Inductive H := by
    constructor
    . show 1 ∈ H
      change 1 ∈
        Natural ∧ (1 = 1 ∨ (1 < 1 ∧ 1 - 1 ∈ Natural))
      constructor
      . exact one_is_natural
      . exact Or.inl rfl
    . show ∀ {x : ℝ}, x ∈ H → x + 1 ∈ H
      intro x hx
      have x_is_natural : x ∈ Natural := by exact hH hx
      have succ_x_is_natural : x + 1 ∈ Natural := by
            exact inductive_natural.right x_is_natural
      have one_le_x : 1 ≤ x := by
        exact (one_le_natural ⟨x, x_is_natural⟩)
      have : 1 < x ∨ 1 = x := by
        exact Std.le_iff_lt_or_eq.mp one_le_x
      rcases this with one_lt_x | one_eq_x
      . change x + 1 ∈ Natural
          ∧ (x + 1 = 1 ∨ (1 < x + 1 ∧ x + 1 - 1 ∈ Natural))
        constructor
        . exact succ_x_is_natural
        . have e1 : 1 < x + 1 := by
            calc
            1 =  1 + 0 := by rw [add_zero]
            _ < x + 1 := by exact
              add_lt_add_of_le_of_lt one_le_x zero_lt_one
          have e2 : x + 1 - 1 ∈ Natural := by
            norm_num
            exact x_is_natural
          exact Or.inr ⟨e1, e2⟩
      . rw [← one_eq_x]
        have e1 : (1 : ℝ) < (1 : ℝ)+ (1 : ℝ) := by norm_num
        have e2 : 1 + 1 - 1 ∈ Natural := by
          norm_num
          exact one_is_natural
        change 1 + 1 ∈ Natural
          ∧ (1 + 1 = 1 ∨ (1 < 1 + 1 ∧ 1 + 1 - 1 ∈ Natural))
        constructor
        · exact inductive_natural.right one_is_natural
        · exact Or.inr ⟨e1, e2⟩
  have H_eq_Natural : H = Natural := by
    exact eq_natural_of_subset_of_inductive hH IH
  have hn : (n : ℝ) ∈ H := by
    have : Natural ⊆ H := by rw [H_eq_Natural] --rev
    exact this n.property
  rcases hn with ⟨hnNatural, hn_eq_one | hn_gt_one⟩
  . false_or_by_contra
    exact ne_of_lt hn hn_eq_one.symm
  . show (n : ℝ) - 1 ∈ Natural
    exact hn_gt_one.right

example (n m : ℕ) (h : n < m)  :
  (∃ k : ℕ, k = m - n) := by
  induction n with
  | zero => use m; rw [Nat.sub_zero m]
  | succ n ih =>
    have h' : ∃ k, k = m - n := by
      exact (ih (lt_trans (Nat.lt_succ_self n) h))
    obtain ⟨k, hk⟩ := h'
    use (k - 1)
    rw [hk, Nat.sub_sub]
end Section_1_3_LO
