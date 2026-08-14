import Mathlib.Data.Nat.Notation
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

  import ProjectTemplate.Chapters.Section_1_3

import Verso
import VersoManual
import VersoBlueprint

open Verso.Genre
open Verso.Genre.Manual
open Informal


#doc (Manual) "Definitions by Induction" =>

:::group "definitions_induction"
Core statements about addition on real numbers.
:::

```lean "open DefinitionsByInduction"
namespace DefinitionsByInduction
open NaturalNumbers
```

# Generalized Induction

:::definition "general_induction"
A set `H ⊆ ℝ × ℝ` is `G`-inductive with _initial value_ `a ∈ ℝ` and
_inductive step_ `step : ℝ → ℝ → ℝ` if it  satisfies the following properties:
* `(1, a) ∈ H`
* If `(x, y) ∈ H`, then `(x + 1, step x y) ∈ H`
In this case, we write `(a, step, H)` is `G`-inductive.
:::

```lean "general_induction"
def G_inductive (a : ℝ) (step : ℝ → ℝ → ℝ)
  (H : Set (ℝ × ℝ)) : Prop :=
    (1, a) ∈ H ∧
      ∀ {x y : ℝ}, (x, y) ∈ H → (x + 1, step x y) ∈ H
```

:::lemma_ "Natural × ℝ is G-inductive" (tags := "Natural × ℝ is G-inductive")
For any `a ∈ ℝ` and step function `step : ℝ → ℝ → ℝ`,
`Natural × ℝ` is `G`-inductive.
:::

```lean "general_induction_example"
theorem natural_times_R {a : ℝ} {step : ℝ → ℝ → ℝ} :
  G_inductive a step (Natural ×ˢ (Set.univ : Set ℝ)) := by
  let R := (Set.univ : Set ℝ)
  constructor
  . show (1, a) ∈ Natural ×ˢ R
    exact ⟨one_mem_Natural , Set.mem_univ a⟩
  . show ∀ {x y : ℝ}, (x, y) ∈ Natural ×ˢ R →
      (x + 1, step x y) ∈ Natural ×ˢ Set.univ
    intro x y hp
    have : x + 1 ∈ Natural := by
        exact succ_mem_Natural hp.1
    exact ⟨this, Set.mem_univ (step x y)⟩

theorem remove_wrong_base
  {a b: ℝ} {step : ℝ → ℝ → ℝ} (hab : a ≠ b) :
    G_inductive a step
      ((Natural ×ˢ
        (Set.univ : Set ℝ)) \ {(1, b)}) := by
  let S := (Natural ×ˢ  (Set.univ : Set ℝ)) \ {(1, b)}
  constructor
  . show (1, a) ∈ S
    constructor
    . show (1, a) ∈ Natural ×ˢ (Set.univ : Set ℝ)
      exact ⟨one_mem_Natural, Set.mem_univ a⟩
    . show  (1, a) ∉ {(1, b)}
      intro h
      have : a = b := by
         exact congrArg Prod.snd h
      exact hab this
  . show ∀ {x y : ℝ}, (x, y) ∈ S → (x + 1, step x y) ∈ S
    intro x y hxy
    change (x, y) ∈
      (Natural ×ˢ  (Set.univ : Set ℝ)) \ {(1, b)} at hxy
    have x_mem_Natural : x ∈ Natural := by
      exact hxy.left.left
    have succ_x_mem_Nat : x + 1 ∈ Natural := by
      exact succ_mem_Natural x_mem_Natural
    have : (x + 1, step x y) ≠ (1, b) := by
      intro h
      have : x + 1 = 1 := by
        exact congrArg Prod.fst h
      exact (ne_of_lt (one_lt_succ x_mem_Natural)) this.symm
    exact ⟨⟨succ_x_mem_Nat, Set.mem_univ (step x y) ⟩,
      this⟩
```

:::definition "G set"
Given `a ∈ ℝ` and `step : ℝ → ℝ → ℝ`, the `G`-set `G` with
initial value `a` and  inductive step function `step` is the
_smallest_  `G`-inductive set with _initial value_
`a ∈ ℝ` and _inductive step_ `step : ℝ → ℝ → ℝ`. Precisely,

`G = ⋂₀ {A : (a, step, A) is `G`-inductive}`
:::

```lean "G set"
def G (a : ℝ) (step : ℝ → ℝ → ℝ ) :=
  ⋂₀  {A : Set (ℝ × ℝ) | G_inductive a step A}
```

:::lemma_ "G ⊆ Natural × ℝ"
`G (a : ℝ) (step : ℝ → ℝ → ℝ ) ⊆ Natural × R`
:::

```lean "G ⊆ Natural × ℝ"
theorem G_subset_Natural_times_R
  {a : ℝ} {step : ℝ → ℝ → ℝ} :
  G a step ⊆ Natural ×ˢ Set.univ:= by
  unfold G
  apply Set.sInter_subset_of_mem
  exact natural_times_R
```

:::corollary "π₁ G ⊆ Natural"
Let `G` be the `G`-set with _initial value_
`a ∈ ℝ` and _inductive step_ `step : ℝ → ℝ → ℝ`, and let
`G₁ = {x ∈ ℝ : ∃ y ∈ ℝ, (x, y) ∈ G}`. Then `G₁ ⊆ Natural`
:::

:::proof "π₁ G ⊆ Natural"
Since ... tbc
:::

```lean "π₁ G ⊆ Natural"
theorem fst_G_subset_natural {a : ℝ} {step : ℝ → ℝ → ℝ} :
  Prod.fst '' (G  a step) ⊆ Natural := by
  intro x hx
  change ∃ p, p ∈ (G  a step) ∧ Prod.fst p = x at hx
  rcases hx with ⟨p, hpG, rfl⟩
  exact (G_subset_Natural_times_R hpG).1
```
:::theorem "G set is G-inductive"
Let  Let `G` be the `G`-set with _initial value_
`a ∈ ℝ` and _inductive step_ `step : ℝ → ℝ → ℝ`, then
`(a, set, G)` is G-inductive.
:::

:::proof "G set is G-inductive"
tbc
:::

```lean "G set is G-inductive"
theorem G_set_inductive (a : ℝ) (step : ℝ → ℝ → ℝ)
   : G_inductive a step (G a step)   := by
  let F := G a step
  unfold G_inductive
  constructor
  . show (1, a) ∈ F
    change (1, a) ∈
      ⋂₀ {A : Set (ℝ × ℝ) | G_inductive a step A}
    rw [Set.mem_sInter]
    intro A hA
    exact hA.left
  . show ∀ {x y : ℝ}, (x, y) ∈ F → (x + 1, step x y) ∈ F
    intro x y pxy
    change (x + 1, step x y) ∈
      ⋂₀ {A : Set (ℝ × ℝ) | G_inductive a step A}
    rw [Set.mem_sInter]
    intro A hA
    have : (x, y) ∈ A := by
      exact pxy A hA
    exact hA.right this
```

:::corollary "π₁ G = Natural"
`π₁ G = Natural`
:::

:::proof "π₁ G = Natural"
Since `π₁ G ⊆ Natural`, by {uses "Principle_of_Induction"}[],
it is enough to show that `π₁ G ⊆ Natural` is inductive.
:::

```lean "π₁ G = Natural_proof"
theorem fst_G_eq_natural {a : ℝ} {step: ℝ → ℝ → ℝ} :
  Prod.fst '' (G  a step) = Natural  := by
  let F := G  a step
  have G_inductive_F : G_inductive a step F := by
    exact (G_set_inductive a step)
  let X := Prod.fst '' F
  have X_subset_Natural: X ⊆ Natural := by
    exact fst_G_subset_natural
  have IX : Inductive X := by
    constructor
    . show 1 ∈ X
      have : (1, a) ∈ F := by
        exact G_inductive_F.left
      exact ⟨(1, a), this, rfl⟩
    . show ∀ {x : ℝ}, x ∈ X → x + 1 ∈ X
      intro x hx
      change ∃ p, p ∈ F ∧ p.1 = x at hx
      rcases hx with ⟨p, p_mem_F, fst_p_eq_x⟩
      let y := p.2
      have : (x, y) = p := by
        subst x
        subst y
        exact Prod.eta p
      have : (x, y) ∈ F := by
        rw [this]
        exact p_mem_F
      have : (x + 1, step x y) ∈ F := by
        exact G_inductive_F.right this
      exact ⟨(x + 1, step x y), this, rfl⟩
  exact eq_natural_of_subset_of_inductive
    X_subset_Natural
    IX
```
:::theorem "G a step is a function"
`G a step` is a functiom
:::

```lean "G a step is a function"
theorem unique_at_one
  (a : ℝ) (step : ℝ → ℝ → ℝ) :
  ∀ b : ℝ, (1, b) ∈ G a step → a = b := by
  intro b hb
  by_cases hab : a = b
  . show a = b -- hab : a = b
    exact hab
  . show a = b -- hab : a ≠ b
    false_or_by_contra
    let S := ((Natural ×ˢ
        (Set.univ : Set ℝ)) \ {(1, b)})
    have IS : G_inductive a step S := by
        exact remove_wrong_base hab
    have : G a step ⊆ S := by
        exact Set.sInter_subset_of_mem IS
    have : (1, b) ∈ S := by
      exact this hb
    rcases this with ⟨_, b_ne_b⟩
    exact b_ne_b (Set.mem_singleton (1, b))

theorem G_is_function (a : ℝ) (step : ℝ → ℝ → ℝ) :
  ∀ n ∈ Natural, ∃! y : ℝ, (n, y) ∈  G a step := by
  let A := G a step

  have IA : G_inductive a step A :=
    by exact G_set_inductive a step

  let H := {n ∈ Natural | ∃! y : ℝ, (n, y) ∈  A}

  have H_substet_Nat : H ⊆ Natural := by
    intro x hx
    exact hx.left

  have IH : Inductive H := by
    constructor
    . show 1 ∈ H
      exact ⟨one_mem_Natural,
        ⟨a,
          ⟨IA.left, fun y hy =>
            (unique_at_one a step y hy).symm⟩ ⟩⟩
    . show ∀ {x : ℝ}, x ∈ H → x + 1 ∈ H
      intro n n_mem_H
      rcases n_mem_H with
        ⟨n_mem_Nat, y, ⟨pny_mem_A, y_unique⟩⟩

      change n + 1 ∈ Natural ∧
        (∃ y' : ℝ, (n + 1, y') ∈ A ∧
          ∀ b : ℝ, (n + 1, b) ∈ A → b = y')

      have succ_n_mem_Nat : n + 1 ∈ Natural :=
        by exact succ_mem_Natural n_mem_Nat

      let y' := step n y

      have ey' : (n + 1, y') ∈ A := by
        exact IA.right pny_mem_A

      have uy' : ∀ b : ℝ, (n + 1, b) ∈ A → b = y' := by
        intro b p_mem_A
        by_cases hb : b = y'
        . exact hb

        . let B := A \ {(n + 1, b)}

          have B_subset_A : B ⊆ A:= by
            exact Set.sdiff_subset

          have IB : G_inductive a step B := by
            constructor
            . show (1, a) ∈ B

              have : 1 ≠ n + 1 := by
                exact ne_of_lt (one_lt_succ n_mem_Nat)

              have : (1, a) ≠ (n + 1, b) := by
                intro h
                exact this (congrArg Prod.fst h)
              exact ⟨IA.left, this⟩

            . show ∀ {u v : ℝ}, (u, v) ∈ B →
                (u + 1, step u v) ∈ B
              intro u v puv_mem_B

              have puv_mem_A : (u , v) ∈ A := by
                  exact B_subset_A puv_mem_B

              have psucc_mem_A : (u + 1, step u v) ∈ A :=
                  by exact IA.right puv_mem_A

              by_cases hun : u = n
              . subst u -- hun : u = n
                show (n + 1, step n v) ∈ B

                have : v = y := by
                  exact y_unique  v puv_mem_A

                subst v
                change (n + 1, y') ∈ B

                have : (n + 1, b) ≠ (n + 1, y') := by
                  intro h
                  apply hb
                  exact congrArg Prod.snd h
                exact ⟨psucc_mem_A, this.symm⟩

              . show (u + 1, step u v) ∈ B -- hun : u ≠ n
                have hsucc_ne : u + 1 ≠ n + 1 := by
                  intro hsucc
                  apply hun
                  exact add_right_cancel hsucc

                have : (u + 1, step u v) ≠ (n + 1, b) := by
                  intro phsucc
                  apply hsucc_ne
                  exact congrArg Prod.fst phsucc
                exact ⟨psucc_mem_A, this⟩

          have : A ⊆ B := by
            unfold A
            apply Set.sInter_subset_of_mem
            exact IB

          have : (n + 1, b) ∈ B := by
            exact this p_mem_A

          have : (n + 1, b) ≠ (n + 1, b) := by
            rcases this with ⟨hB, hk⟩
            exact hk
          false_or_by_contra
          exact this rfl

      exact ⟨succ_n_mem_Nat, ⟨y', ⟨ey', uy'⟩⟩⟩

  have : H = Natural := by
    exact eq_natural_of_subset_of_inductive H_substet_Nat IH
  intro x hx

  have : x ∈ H := by
    rw [this]
    exact hx

  exact this.right
```

# Powers with Natural exponents

We will begin with the definition of powers with natural exponents.

Given a real number `a`, our goal is to define a function
`f: Natural → ℝ`  satisfying:

* `f(1) = a`
* `f (n + 1) = a · f(a)` for all `n ∈ Natural`

To that end, we start with the following definition:

`Power a = G a (fun x y => a * y)`
`a ** n = y ↔ (n, y) ∈ G a (fun _ y => a * y)`

```lean "power"
-- noncomputable def power'
--   (a : ℝ) (n : ℝ) (hn : n ∈ Natural)  : ℝ :=
--   Classical.choose
--     (G_is_function
--       a
--       (fun _ y => a * y : ℝ → ℝ → ℝ)
--       (n : ℝ)
--       hn
--       )

noncomputable def power
  (a : ℝ) (n : Natural)  : ℝ :=
  Classical.choose
    (G_is_function
      a
      (fun _ y => a * y : ℝ → ℝ → ℝ)
      (n : ℝ)
      n.property
      )

local infixr:80 " ** " => power

theorem power_mem_graph
    (a : ℝ) (n : Natural) :
    ((n : ℝ), power a n) ∈
      G a (fun _ y => a * y) := by
  unfold power
  exact
    (Classical.choose_spec
      (G_is_function
        (a := a)
        (step := fun _ y => a * y)
        (n : ℝ)
        n.property)).1

theorem power_eq_iff_mem_graph
    (a y : ℝ) (n : Natural) :
    a ** n = y ↔
      ((n : ℝ), y) ∈
        G a (fun _ y => a * y) := by
  constructor
  · intro h
    rw [← h]
    exact power_mem_graph a n
  · intro hy
    exact
      ((Classical.choose_spec
        (G_is_function
          (a := a)
          (step := fun _ y => a * y)
          (n : ℝ)
          n.property)).2 y hy).symm
```
Having already defined the power with natural exponent,
we prove its main properties:

:::proposition "sum_exponents"
Let $`a` be any real number and let $`m` and $`n` be any natural numbers.
Then, `a ** (m + n) = a ** m ⋅ a ** n`
:::

:::proposition "mul_exponents"
Let $`a` be any real number and let $`m` and $`n` be any natural numbers.
Then,  `(a ** m) ** n = a ** (m ⋅ n)`
:::
■■■■■■■■■■■■■■■■■■■■■■■■■■■■■■■■

:::proof "sum_exponents"
* a) We consider the following statement:
$$`P(n) : a^{m + n} \text{ is equal to } a^m ⋅ a^n`
whatever the natural number $`m`
:::

```lean "sum_exponents"
-- theorem power_add (a : ℝ) (n m : ℝ) (hn : n ∈ Natural)
--  (hm : m ∈ Natural):
--     power' a (n + m) (add_Nat hn hm) =
--        (power' a n hn) * (power' a  m hm) := by
--   let H := {k ∈ Natural |
--     power' a (n + k) (add_Nat hn }
--        sorry

-- @[simp]
-- theorem power_one (a : ℝ) :
--     a ** one = a := by
--   sorry

theorem power_one (a : ℝ) :
    a ** one = a := by
  apply
    (power_eq_iff_mem_graph a a one).mpr

  change
    ((1 : ℝ), a) ∈
      ⋂₀ {H : Set (ℝ × ℝ) |
        G_inductive a (fun _ y => a * y) H}

  intro H hH
  exact hH.left

-- @[simp]
theorem power_succ (a : ℝ) (n : Natural) :
    a ** succ n = a * (a ** n) := by
  apply
    (power_eq_iff_mem_graph
      a
      (a * (a ** n))
      (succ n)).mpr

  have hn :
      ((n : ℝ), a ** n) ∈
        G a (fun _ y => a * y) :=
    power_mem_graph a n

  have hsucc :
      ((n : ℝ) + 1, a * (a ** n)) ∈
        G a (fun _ y => a * y) :=
    (G_set_inductive
      a
      (fun _ y => a * y)).2 hn

  exact hsucc

theorem custom_power_add
    (a : ℝ) (n m : Natural) :
    power a (addNatural n m) = a ** n * a ** m := by
  let H := {k : Natural | power a (addNatural n k) =
    a ** n * a ** k}
  let H' : Set ℝ := Subtype.val '' H
  have IH' : Inductive H' := by
    constructor
    . show 1 ∈ H'
      have one_mem_H : one ∈ H := by
        change power a (succ n) =
          a ** n * a ** one
        have : a ** one = a := by
          exact power_one a
        rw [this]
        have : a ** n * a = a * a ** n := by ring
        rw [this]
        exact power_succ a n
      change (1 : ℝ) ∈ Subtype.val '' H
      exact ⟨one, one_mem_H, rfl⟩

    . show  ∀ {x : ℝ}, x ∈ H' → x + 1 ∈ H'
      intro k hk
      change k ∈ Subtype.val '' H at hk
      rcases hk with ⟨kN, kN_mem_H, rfl⟩

      have succ_kN_mem_H : succ kN ∈ H := by
        change power a (addNatural n (succ kN)) =
          a ** n * a ** (succ kN)
        rw [power_succ a kN]
        have : a ** n * (a * a ** kN) =
          a ** n * a ** kN * a := by ring
        rw [this]
        rw [← kN_mem_H]
        rw [add_succ n kN]
        have : a ** addNatural n kN * a =
           a * a ** addNatural n kN := by ring
        rw [this]
        exact power_succ a (addNatural n kN)

      change (kN : ℝ) + 1 ∈ Subtype.val '' H
      exact ⟨succ kN, succ_kN_mem_H, rfl⟩

  have hH' : H' ⊆ Natural := by
    intro x hx
    change x ∈ Subtype.val '' H at hx
    rcases hx with ⟨k, hkH, rfl⟩
    exact k.property
  have : H' = Natural := by
    exact eq_natural_of_subset_of_inductive  hH' IH'

  have hmH' : (m : ℝ) ∈ H' := by
    rw [this]
    exact m.property

  have hmH : m ∈ H := by
    rcases hmH' with ⟨k, hkH, hk_eq_m⟩

    have hkm : k = m := by
      exact Subtype.ext hk_eq_m

    simpa [hkm] using hkH
    -- subst m
    -- assumption

  exact hmH
```

```lean "custom_power_mul"
theorem custom_power_mul
    (a : ℝ) (n m : Natural) :
    power a (addNatural n m) = a ** n * a ** m := by
  let H := {k : Natural | power a (addNatural n k) =
    a ** n * a ** k}
  let H' : Set ℝ := Subtype.val '' H
  have IH' : Inductive H' := by
    constructor
    . show 1 ∈ H'
      have one_mem_H : one ∈ H := by
        change power a (succ n) =
          a ** n * a ** one
        have : a ** one = a := by
          exact power_one a
        rw [this]
        have : a ** n * a = a * a ** n := by ring
        rw [this]
        exact power_succ a n
      change (1 : ℝ) ∈ Subtype.val '' H
      exact ⟨one, one_mem_H, rfl⟩

    . show  ∀ {x : ℝ}, x ∈ H' → x + 1 ∈ H'
      intro k hk
      change k ∈ Subtype.val '' H at hk
      rcases hk with ⟨kN, kN_mem_H, rfl⟩

      have succ_kN_mem_H : succ kN ∈ H := by
        change power a (addNatural n (succ kN)) =
          a ** n * a ** (succ kN)
        rw [power_succ a kN]
        have : a ** n * (a * a ** kN) =
          a ** n * a ** kN * a := by ring
        rw [this]
        rw [← kN_mem_H]
        rw [add_succ n kN]
        have : a ** addNatural n kN * a =
           a * a ** addNatural n kN := by ring
        rw [this]
        exact power_succ a (addNatural n kN)

      change (kN : ℝ) + 1 ∈ Subtype.val '' H
      exact ⟨succ kN, succ_kN_mem_H, rfl⟩

  have hH' : H' ⊆ Natural := by
    intro x hx
    change x ∈ Subtype.val '' H at hx
    rcases hx with ⟨k, hkH, rfl⟩
    exact k.property
  have : H' = Natural := by
    exact eq_natural_of_subset_of_inductive  hH' IH'

  have hmH' : (m : ℝ) ∈ H' := by
    rw [this]
    exact m.property

  have hmH : m ∈ H := by
    rcases hmH' with ⟨k, hkH, hk_eq_m⟩

    have hkm : k = m := by
      exact Subtype.ext hk_eq_m

    simpa [hkm] using hkH
    -- subst m
    -- assumption

  exact hmH
```
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
