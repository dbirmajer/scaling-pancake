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

end Section_1_3_LO
