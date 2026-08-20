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

-- theorem one_le_natural : ∀ n : Natural, 1 ≤ (n : ℝ) := by
--   let H := {x : ℝ | 1 ≤ x}
--   have IH : Inductive H := by
--     constructor
--     . simp [H]
--     . simp [H]
--       intro x hx
--       have : (0 : ℝ)  ≤ 1 := by
--    exact le_of_lt zero_lt_one
--       exact le_trans this hx
--   intro n
--   exact n.property IH

theorem one_le_natural' (n : Natural): 1 ≤ (n : ℝ) := by
  let H := {x : ℝ | 1 ≤ x}
  have IH : Inductive H := by
    constructor
    . simp [H]
    . simp [H]
      intro x hx
      have : (0 : ℝ)  ≤ 1 := by exact le_of_lt zero_lt_one
      exact le_trans this hx
  exact n.property IH

theorem natural_lt_succ_iff :
    ∀ k ∈ Natural,
      k < x + 1 ↔ k < x ∨ k = x := by
  intro k hk
  constructor
  . show k < x + 1 → k < x ∨ k = x
    sorry
  . show k < x ∨ k = x → k < x + 1
    intro hk
    rcases hk with k_lt_x | k_eq_x
    . calc
      k < x := by exact k_lt_x
      _ = 0 + x := by rw [zero_add]
      _ < 1 + x := by exact
        add_lt_add_left  zero_lt_one x
      _ = x + 1 := by exact add_comm 1 x
    . sorry

example (n : Natural) (hn : 1  < (n : ℝ)) :
  (n : ℝ) - 1 ∈ Natural := by
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
      . exact succ_mem_natural x_is_natural
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
  have hn : (n : ℝ) ∈ H := by
    have : Natural ⊆ H := by rw [H_eq_Natural] --rev
    exact this n.property
  rcases hn with ⟨hnNatural, hn_eq_one | hn_gt_one⟩
  . false_or_by_contra
    exact ne_of_lt hn hn_eq_one.symm
  . show (n : ℝ) - 1 ∈ Natural
    exact hn_gt_one.right

theorem natural_lt_succ_iff {n} (hn : n ∈ Natural) :
    ∀ k ∈ Natural,
      k < n + 1 ↔ k ≤ n := by
  intro k hk
  constructor
  . show k < n + 1 → k ≤ n
    sorry
  . show k ≤ n → k < n + 1
    intro hk
    . calc
      k ≤ n := by exact hk
      _ = 0 + n := by rw [zero_add]
      _ < 1 + n := by exact
        add_lt_add_left  zero_lt_one n
      _ = n + 1 := by exact add_comm 1 n

def P (n : ℕ) : Prop :=
  ∀ A : Set ℕ, n ∈ A →
    ∃ m, IsLeast A m

lemma well_ordering : ∀ n : ℕ, P n  := by
  -- Introduce the arbitrary natural number n.
  intro n
  change ∀ A : Set ℕ,
    n ∈ A →
    ∃ m : ℕ, IsLeast A m

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
  --      exact zero_le n
        sorry
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
Until now we have used induction in all our proofs of elementary properties
of ℕ. That happens because ℕ is practically defined by the principle of
induction, the only instrument to prove its first derived properties.

But as soon as some of them are proven, other properties can be derived with
those results without using, perhaps, the principle of induction in the proof.

The following Proposition is an example of it:

:::theorem "prop_1.9"
If $`n` and $`m` are natural numbers and $`n < m`,
then $`m - n ∈ Natural`, and $`n + 1 ≤ m`.
:::

:::proof "prop_1.9"
{uses "prop_1.6"}[]
{uses "prop_1.8"}[]
:::

example
  (n m : Natural)
  (h : (n : ℝ) < (m : ℝ)) : (n + 1 : ℝ) ≤ (m : ℝ) := by
  sorry
  -- have : (∃ k  : ℕ, k = m - n) := proposition_1_8 n m h
  -- obtain ⟨k, hk⟩ := this
  -- have : 0 < k := by omega
  -- have : 1 ≤ k  := by exact (Nat.succ_le_of_lt this)
  -- have : m - n ≥ 1 := by omega
  -- omega

example (n m : ℕ) (h : n < m) : n + 1 ≤ m := by
  exact Nat.succ_le_of_lt h

end Section_1_3_LO

namespace Section_1_4
def PowerInductive'
    (a : ℝ)
    (H : Set (ℝ × ℝ)) : Prop :=
  H ⊆ Natural ×ˢ (Set.univ : Set ℝ) ∧
  (1, a) ∈ H ∧
  ∀ {x y : ℝ},
    (x, y) ∈ H → (x + 1, a * y) ∈ H

theorem inductive_A (a : ℝ) : Inductive (opA a) := by
  let A := opA a
  unfold Inductive
  constructor
  . show (1 ∈ A)
    change 1 ∈ Natural ∧  ∃ y : ℝ, (1, y) ∈ PowerGraph a
    constructor
    . show 1 ∈ Natural
      exact one_mem_Natural
    . show ∃ y : ℝ, (1, y) ∈ PowerGraph a
      use a
      intro H hH
      exact hH.left
  . show ∀ {x : ℝ}, x ∈ A → x + 1 ∈ A
    intro x x_mem_A
    change  x ∈ Natural ∧
       ∃ y : ℝ, (x, y) ∈ PowerGraph a at x_mem_A
    change x + 1 ∈ Natural ∧
       ∃ y : ℝ, (x + 1, y) ∈ PowerGraph a
    constructor
    . show x + 1 ∈ Natural
      exact succ_mem_Natural x_mem_A.left
    . show ∃ y, (x + 1, y) ∈ PowerGraph a
      rcases x_mem_A.right with ⟨y, pxy_mem_A⟩
      use a * y
      change ∀ {B : Set (ℝ × ℝ)},
        PowerInductive a B → (x + 1, a * y) ∈ B
      intro B hB
      have pxy_mem_B : (x, y) ∈ B := by
        exact  pxy_mem_A hB
      exact hB.right pxy_mem_B

theorem A_eq_Natural : (opA a) = Natural := by
  let A := {n ∈ Natural | ∃ y : ℝ, (n, y) ∈ PowerGraph a}
  have : A ⊆ Natural := by
    intro a a_mem_A
    exact a_mem_A.left
  exact eq_natural_of_subset_of_inductive
        this
        (inductive_A a : Inductive (opA a))
```lean "G a step is a function-proof"
lemma function_at_one {a : ℝ} {step : ℝ → ℝ → ℝ}:
  ∀ b : ℝ, (1, b) ∈ G a step → a = b := by
  let F := G a step
  have hF : G_inductive a step F := by
    exact G_set_G_inductive_G a step
  intro b b_mem_F
  change (1, b) ∈ F at b_mem_F
  by_cases hab : a = b
  . show a = b -- hab : a = b
    exact hab
  . show a = b -- hab : a ≠ b
    false_or_by_contra
    let F' := F \ {(1, b)}
    sorry
  -- by_cases hba : b = a
  -- . show b = a -- case hab : b = a
  --   exact hba
  -- . false_or_by_contra
  --   show False
  --   let A' := A \ {(1, b)}
  --   have : PowerInductive a A' := by
  --     constructor
  --     . show (1, a) ∈ A' -- case hba : b ≠ a
  --       constructor
  --       . exact one_a_mem_A
  --       . simpa using (Ne.symm hba) -- revisar
  --     . show ∀ {x y : ℝ}, (x, y) ∈ A' → (x + 1, a * y) ∈ A'
  --       -- va a salir xq x + 1 no es 1
  --       sorry
  --   sorry

lemma unique_at_x {a : ℝ} {step : ℝ → ℝ → ℝ}:
  ∀ {x y : ℝ} , (x, y) ∈ G a step →
    (x + 1, b) ∈ G a step → b = step x y := by
    intro x y hxy hy'
    let F := G a step
    let y' := step x y
    by_cases hby' : b = y'
    . show b = y' -- hby' : b = y'
      exact hby'
    . show b = y' -- hby' : b ≠ y'
      false_or_by_contra
      let S := F \ {(x + 1, b)}
      have IS : G_inductive a step S := by sorry
      have : F ⊆ S := by
         exact Set.sInter_subset_of_mem IS
      have : (x + 1, b) ∈ S := by
        exact this hy'
      rcases this with ⟨_, b_ne_b⟩
      exact b_ne_b (Set.mem_singleton (x + 1, b))

theorem inductive_A' (a : ℝ) : Inductive (opA' a) := by
  let A' := opA' a
  unfold Inductive
  constructor
  . show (1 ∈ A')
    change 1 ∈ Natural ∧  ∃! y : ℝ, (1, y) ∈ PowerGraph a
    constructor
    . show 1 ∈ Natural
      exact one_mem_Natural
    . show ∃! y : ℝ, (1, y) ∈ PowerGraph a
      use a
      constructor
      . intro H hH
        exact hH.left
      .
        sorry
  . show ∀ {x : ℝ}, x ∈ A' → x + 1 ∈ A'
    intro x x_mem_A'
    change  x ∈ Natural ∧
       ∃! y : ℝ, (x, y) ∈ PowerGraph a at x_mem_A'
    change x + 1 ∈ Natural ∧
       ∃! y : ℝ, (x + 1, y) ∈ PowerGraph a
    constructor
    . show x + 1 ∈ Natural
      exact succ_mem_Natural x_mem_A'.left
    . show ∃! y, (x + 1, y) ∈ PowerGraph a
      rcases x_mem_A'.right with ⟨y, pxy_mem_A⟩
      use a * y
--      change ∀ {B : Set (ℝ × ℝ)},
        PowerInductive a B → (x + 1, a * y) ∈ B
      intro B hB
      have pxy_mem_B : (x, y) ∈ B := by
        exact  pxy_mem_A hB
      exact hB.right pxy_mem_B

theorem remove_wrong_succ
  {a b x y : ℝ} {step : ℝ → ℝ → ℝ} {A : Set (ℝ × ℝ)}
  (hA : G_inductive a step A):
  ∀ {x y : ℝ},
    (x, y) ∈ A → x ∈ Natural →
      ∀ b : ℝ, b ≠ step x y →
        G_inductive a step (A \ {(x + 1, b)}) := by
  intro x y hxy x_mem_Natural b hb
  constructor
  . show (1, a) ∈ A \ {(x + 1, b)}
    have succ_x_mem_Nat : x + 1 ∈ Natural := by
       exact succ_mem_Natural x_mem_Natural
    have : 1 ≠ x + 1 := by
      exact ne_of_lt (one_lt_succ x_mem_Natural)
    have : (1, a) ≠ (x + 1, b) := by
      intro h
      exact this (congrArg Prod.fst h)
    exact ⟨hA.left, this⟩
  .
    show  ∀ {x₁ y₁ : ℝ}, (x₁, y₁) ∈ A \ {(x + 1, b)}
      → (x₁ + 1, step x₁ y₁) ∈ A \ {(x + 1, b)}
    intro x₁ y₁ hx₁y
    by_cases hxx₁ : x = x₁
    . show (x₁ + 1, step x₁ y₁) ∈
        A \ {(x + 1, b)} -- hxx₁ : x = x₁
      subst x₁
      by_cases hy₁y : y₁ = y
      . subst y₁
        sorry
      .
        sorry
    sorry
        -- have : (x + 1, step x y₁) ≠ (x + 1, b) := by
        --   intro h
        --   have : step x y = b := by
        --     exact congrArg Prod.snd h
        --   exact hb.symm this
  -- . show ∀ {x y : ℝ}, (x, y) ∈ S → (x + 1, step x y) ∈ S
  --   intro x y hxy
  --   change (x, y) ∈
  --     (Natural ×ˢ  (Set.univ : Set ℝ)) \ {(1, b)} at hxy
  --   have x_mem_Natural : x ∈ Natural := by
  --     exact hxy.left.left
  --   have : (x + 1, step x y) ≠ (1, b) := by
  --     intro h
  --     have : x + 1 = 1 := by
  --       exact congrArg Prod.fst h
  --     exact (ne_of_lt (one_lt_succ x_mem_Natural)) this.symm
  --   exact ⟨⟨succ_x_mem_Nat, Set.mem_univ (step x y) ⟩,
  --     this⟩

# Functional Induction

:::definition "F_induction"
A set `H ⊆ ℝ × ℝ` is `G`-inductive with _initial value_ `a ∈ ℝ` and
_inductive step_ `step : ℝ → ℝ → ℝ` if it  satisfies the following properties:
* `(1, a) ∈ H`
* For all `x, y ∈ ℝ`, `(x, y) ∈ H ↔ (x + 1, step x y) ∈ H`
In this case, we write `(a, step, H)` is `F`-inductive.
:::

```lean "F_induction"
-- def F_inductive (a : ℝ) (step : ℝ → ℝ → ℝ)
--   (H : Set (ℝ × ℝ)) : Prop :=
--     (1, a) ∈ H ∧
--       ∀ {x y : ℝ}, (x, y) ∈ H ↔ (x + 1, step x y) ∈ H

def F_inductive (a : ℝ) (step : ℝ → ℝ → ℝ)
  (H : Set (ℝ × ℝ)) : Prop :=
    (1, a) ∈ H ∧
      ∀ x ∈ Natural,
        ∀ y : ℝ, (x, y) ∈ H ↔ (x + 1, step x y) ∈ H

def F_inductive' (a : ℝ) (step : ℝ → ℝ → ℝ)
  (H : Set (ℝ × ℝ)) : Prop :=
    H ⊆ Natural ×ˢ (Set.univ : Set ℝ) ∧
    (1, a) ∈ H ∧
      ∀ {x y : ℝ}, (x, y) ∈ H ↔ (x + 1, step x y) ∈ H

-- Natural ×ˢ Set.univ
```
```lean "F_is_function"
def F
    (a : ℝ)
    (step : ℝ → ℝ → ℝ) : Set (ℝ × ℝ) :=
  ⋂₀ {H : Set (ℝ × ℝ) | F_inductive a step H}

theorem F_is_inductive (a : ℝ) (step : ℝ → ℝ → ℝ) :
    F_inductive a step (F a step) := by
  sorry

theorem F_is_function
    (a : ℝ)
    (step : ℝ → ℝ → ℝ) :
    ∀ n ∈ Natural,
      ∃! y : ℝ, (n, y) ∈ F a step := by
  let P : Set ℝ :=
    {n ∈ Natural | ∃! y : ℝ, (n, y) ∈ F a step}

  have hP : Inductive P := by
    constructor

    · -- Base case
      refine ⟨one_mem_Natural, a, ?_, ?_⟩
      · exact (F_is_inductive a step).2.1
      · intro b hb
        -- Prove that every value of F at 1 equals a.
        exact (unique_at_one a step b hb).symm

    · -- Successor case
      intro n hnP
      rcases hnP with ⟨hnNatural, y, hny, hy_unique⟩

      refine ⟨succ_mem_Natural hnNatural, step n y, ?_, ?_⟩

      · -- Existence at n + 1
        exact (F_is_inductive a step).2.2 hny

      · -- Uniqueness at n + 1
        intro b hnb
        by_contra hb
        -- Show that removing `(n + 1, b)` still leaves an
        -- F-inductive set.
        let B :=
          (Natural ×ˢ (Set.univ : Set ℝ)) \ {(n + 1, b)}

        have hB : F_inductive a step B := by
          constructor
          · exact Set.diff_subset.trans Set.prod_subset_preimage_fst
          · constructor
            · -- The base pair is not the removed pair.
              sorry
            · intro x z hxz
              constructor
              · exact succ_mem_Natural hxz.1.1
              · constructor
                · trivial
                · intro heq
                  -- If the new pair equals `(n+1,b)`, then `x=n`.
                  -- Since `(x,z) ∈ F`, uniqueness at n gives `z=y`,
                  -- contradicting `hb`.
                  sorry

        have hF_subset_B : F a step ⊆ B := by
          apply Set.sInter_subset_of_mem
          exact hB

        have : (n + 1, b) ∈ B :=
          hF_subset_B hnb

        exact this.2 (by simp)

  have hP_eq : P = Natural :=
    eq_natural_of_subset_of_inductive
      (by
        intro n hn
        exact hn.1)
      hP

  intro n hnNatural
  have hnP : n ∈ P := by
    rw [hP_eq]
    exact hnNatural
  exact hnP.2
```
:::lemma_ "Natural × ℝ is F-inductive" (tags := "Natural × ℝ is G-inductive")
For any `a ∈ ℝ` and step function `step : ℝ → ℝ → ℝ`,
`Natural × ℝ` is `F`-inductive.
:::

```lean "Natural × ℝ is F-inductive"
theorem N_times_R {a : ℝ} {step : ℝ → ℝ → ℝ} :
  F_inductive a step (Natural ×ˢ (Set.univ : Set ℝ)) := by
  let R := (Set.univ : Set ℝ)
  constructor
  . show (1, a) ∈ Natural ×ˢ R
    exact ⟨one_mem_Natural , Set.mem_univ a⟩
  . show ∀ x ∈ Natural, ∀ y : ℝ, (x, y) ∈ Natural ×ˢ R ↔
      (x + 1, step x y) ∈ Natural ×ˢ Set.univ
    intro x hx y
    constructor
    . intro hmp
      have hsucc : x + 1 ∈ Natural := by
        exact succ_mem_Natural hmp.1
      exact ⟨hsucc, Set.mem_univ (step x y)⟩
    . show (x + 1, step x y) ∈ Natural ×ˢ Set.univ →
        (x, y) ∈ Natural ×ˢ R
      intro hmpr
      exact ⟨hx, Set.mem_univ y⟩

:::definition "power_inductive"
Fix `a ∈ ℝ`. A set `H ⊆ ℝ × ℝ` is `a`-power-inductive if it
satisfies the following properties:
* `(1, a) ∈ H`
* If `(x, y) ∈ H`, then `(x + 1, a ·y) ∈ H`
:::

```lean "power_inductive"
def PowerInductive (a : ℝ) (H : Set (ℝ × ℝ)) : Prop :=
  (1, a) ∈ H ∧
    ∀ {x y : ℝ},
      (x, y) ∈ H → (x + 1, a * y) ∈ H
```

```lean "power_inductive_example"
example (a : ℝ) :
  PowerInductive a (Natural ×ˢ (Set.univ : Set ℝ)) := by
  sorry
```

```lean "power_inductive_prop"
def isPowerGenerated (a : ℝ) (p : ℝ × ℝ) : Prop :=
  ∀ {A : Set (ℝ × ℝ)},
    PowerInductive a A → p ∈ A

-- The smallest Power Inductive a set in ℝ × ℝ
def PowerGraph (a : ℝ) : Set (ℝ × ℝ) :=
  {p | isPowerGenerated a p}


def PowerDomain (a : ℝ) :=
  {x : ℝ | ∃ y : ℝ, (x, y) ∈ PowerGraph a }

def PowerDomain' (a : ℝ) : Set ℝ :=
  Prod.fst '' PowerGraph a

theorem domain_subset_natural (a : ℝ) :
  PowerDomain a ⊆ Natural := by sorry

-- just finish the example above

theorem power_inductive_PG (a : ℝ) :
  PowerInductive a (PowerGraph a) := by sorry

theorem function_at_one {a : ℝ} :
  ∀ b : ℝ, (1, b) ∈ PowerGraph a → b = a := by
  let A := PowerGraph a
  have IA : PowerInductive a A  := by
    exact power_inductive_PG a
  have one_a_mem_A : (1, a) ∈ A := by
    exact IA.left
  intro b hb
  change (1, b) ∈ A at hb
  by_cases hba : b = a
  . show b = a -- case hab : b = a
    exact hba
  . false_or_by_contra
    show False
    let A' := A \ {(1, b)}
    have : PowerInductive a A' := by
      constructor
      . show (1, a) ∈ A' -- case hba : b ≠ a
        constructor
        . exact one_a_mem_A
        . simpa using (Ne.symm hba) -- revisar
      . show ∀ {x y : ℝ}, (x, y) ∈ A' → (x + 1, a * y) ∈ A'
        -- va a salir xq x + 1 no es 1
        sorry
    sorry
```
:::theorem "power_function"
Let `A = {n ∈ Natural : (n, y) ∈ PowerGraph (a : ℝ) for some y ∈ ℝ}`. Then,
* `A = Natural`
* `PowerGraph (a : ℝ)` is a function with domain `Natural` and
    codomain ℝ
*  `(1, a) ∈ PowerGraph (a : ℝ)`
* If `(n , y) ∈ PowerGraph (a : ℝ)`,
    then `(n , a · y) ∈ PowerGraph (a : ℝ)`
:::

:::proof "power_function"
First we will show that `A` is an inductive set. Since `A ⊆ Natural`,
we conclude by ({uses "Principle_of_Induction"}[]) that `A = Natural`.
:::

```lean "A_is_inductive"
section
def opA (a : ℝ):=
  {n ∈ Natural | ∃ y : ℝ, (n, y) ∈ PowerGraph a}

-- Quizas se puede deducir de PowerGraph a is inductive

theorem inductive_A (a : ℝ) : Inductive (opA a) := by
  let A := opA a
  unfold Inductive
  constructor
  . show (1 ∈ A)
    change 1 ∈ Natural ∧  ∃ y : ℝ, (1, y) ∈ PowerGraph a
    constructor
    . show 1 ∈ Natural
      exact one_mem_Natural
    . show ∃ y : ℝ, (1, y) ∈ PowerGraph a
      use a
      intro H hH
      exact hH.left
  . show ∀ {x : ℝ}, x ∈ A → x + 1 ∈ A
    intro x x_mem_A
    change  x ∈ Natural ∧
       ∃ y : ℝ, (x, y) ∈ PowerGraph a at x_mem_A
    change x + 1 ∈ Natural ∧
       ∃ y : ℝ, (x + 1, y) ∈ PowerGraph a
    constructor
    . show x + 1 ∈ Natural
      exact succ_mem_Natural x_mem_A.left
    . show ∃ y, (x + 1, y) ∈ PowerGraph a
      rcases x_mem_A.right with ⟨y, pxy_mem_A⟩
      use a * y
      change ∀ {B : Set (ℝ × ℝ)},
        PowerInductive a B → (x + 1, a * y) ∈ B
      intro B hB
      have pxy_mem_B : (x, y) ∈ B := by
        exact  pxy_mem_A hB
      exact hB.right pxy_mem_B

theorem A_eq_Natural : (opA a) = Natural := by
  let A := {n ∈ Natural | ∃ y : ℝ, (n, y) ∈ PowerGraph a}
  have : A ⊆ Natural := by
    intro a a_mem_A
    exact a_mem_A.left
  exact eq_natural_of_subset_of_inductive
        this
        (inductive_A a : Inductive (opA a))

def opA' (a : ℝ):=
  {n ∈ Natural | ∃! y : ℝ, (n, y) ∈ PowerGraph a}


end
```
```lean "(opA a)  is a function"
section
variable (a : ℝ)

theorem function_f :
  ∀ n ∈ Natural,
    ∃! y : ℝ, (n, y) ∈ PowerGraph a := by
    intro n n_mem_Natural
    constructor
    . have : n ∈ (opA a) := by
        rw [A_eq_Natural]
        exact  n_mem_Natural
      sorry
    . sorry

end
```


end Section_1_4
