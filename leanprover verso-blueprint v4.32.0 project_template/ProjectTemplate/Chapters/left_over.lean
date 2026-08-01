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

end Section_1_3_LO
