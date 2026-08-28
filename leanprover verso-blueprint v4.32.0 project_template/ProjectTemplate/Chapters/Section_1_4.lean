import Mathlib.Data.Nat.Notation
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

import ProjectTemplate.Chapters.Section_1_2
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
--open NaturalNumbers
open BasicProperties
```

# Generalized Induction


:::definition "general_induction"
A set `H ⊆ ℝ × ℝ` is RecInductive with _initial value_ `a ∈ ℝ` and
_inductive step_ `step : ℝ → ℝ → ℝ` if it  satisfies the following properties:
* `(0, a) ∈ H`
* If `(x, y) ∈ H`, then `(x + 1, step x y) ∈ H`
--In this case, we write `(a, step, H)` is `G`-inductive.
:::

```lean "RecInductive"
def RecInductive
    (initial : ℝ)
    (step : Natural → ℝ → ℝ)
    (H : Set (Natural × ℝ)) : Prop :=
  (Natural.zero, initial) ∈ H ∧
  ∀ {n : Natural} {x : ℝ},
    (n, x) ∈ H →
    (Natural.succ n, step n x) ∈ H
```


:::lemma_ "Natural × ℝ is RecInductive" (tags := "Natural × ℝ is RecInductive")
For any `a ∈ ℝ` and step function `step : ℝ → ℝ → ℝ`,
`Natural × ℝ` is RecInductive.
:::

```lean "general_induction_example"
theorem recInductive_univ {a : ℝ} {step : Natural → ℝ → ℝ} :
  RecInductive a step
    (Set.univ : Set (Natural × ℝ)) := by
  constructor

  . show (Natural.zero, a) ∈ Set.univ
    exact Set.mem_univ  (Natural.zero, a)

  . show ∀ {n : Natural} {x : ℝ}, (n, x) ∈ Set.univ →
      (Natural.succ n, step n x) ∈ Set.univ
    intro n x hp
    exact Set.mem_univ (Natural.succ n, step n x)
```

```lean "remove_wrong_base"
theorem remove_wrong_base
  {a b: ℝ} {step : Natural → ℝ → ℝ} (hab : a ≠ b) :
    RecInductive a step
    ((Set.univ : Set (Natural × ℝ)) \
      {(Natural.zero,  b)}) := by

  let U := (Set.univ : Set (Natural × ℝ))
  let S := U  \ {(Natural.zero,  b)}
  constructor
  . show (Natural.zero, a) ∈ S

    constructor
    . show (Natural.zero, a) ∈ U
      exact Set.mem_univ (Natural.zero,  a)

    . show  (Natural.zero, a) ∉ {(Natural.zero, b)}
      intro h
      exact hab (congrArg Prod.snd h)

  . show ∀ {n : Natural} {x : ℝ},
      (n, x) ∈ S → (Natural.succ n, step n x) ∈ S
    intro n x hpG
    change (Natural.succ n, step n x) ∈
      Set.univ \ {(Natural.zero, b)}
    constructor
    . show (Natural.succ n, step n x) ∈ Set.univ
      exact Set.mem_univ (Natural.succ n, step n x)

    . show (Natural.succ n, step n x) ∉
        {(Natural.zero, b)}
      intro h
      have : Natural.succ n = Natural.zero := by
        exact (congrArg Prod.fst h)
      exact ne_of_lt (Natural.zero_lt_succ n) this.symm
```

:::definition "RecGraph"
Given `intial ∈ ℝ` and `step : Natural → ℝ → ℝ`,
the `RecGraph` with initial value `initial` and  inductive step function
`step` is the _smallest_  RecInductive set with _initial value_
`initla ∈ ℝ` and _inductive step_ `step : Natural → ℝ → ℝ`. Precisely,

`RecGraph = ⋂₀ {H | RecInductive initial step H}`
:::


```lean "RecGraph"
def RecGraph
    (initial : ℝ)
    (step : Natural → ℝ → ℝ) :
    Set (Natural × ℝ) :=
  ⋂₀ {H | RecInductive initial step H}
```


:::theorem "ReGraph is RecInductive"
Let  `F` be the `RecInductive`-set with _initial value_
`a ∈ ℝ` and _inductive step_ `step : Natural → ℝ → ℝ`, then
`F` is `RecInductive`.
:::


```lean "RG-inductive"
theorem RG_inductive (a : ℝ) (step : Natural → ℝ → ℝ)
   : RecInductive a step (RecGraph a step)   := by
  let F := RecGraph a step
  constructor

  . show (Natural.zero, a) ∈ RecGraph a step
    change (Natural.zero, a) ∈
      ⋂₀ {A : Set (Natural × ℝ) | RecInductive a step A}
    apply Set.mem_sInter.mpr
    intro A hA
    exact hA.left

  . show ∀ {n : Natural} {x : ℝ}, (n, x) ∈ F →
      (Natural.succ n, step n x) ∈ F
    intro n x pnx A hA
    have : (n, x) ∈ A := by
      exact pnx A hA
    exact hA.right this
```


Our goal is to prove that `F = RecGraph a step ⊆ Natural × ℝ` is a function.
We start by proving the following lemma:
:::lemma_ "Unique at zero"
Let  `F` be the `RecInductive`-set with _initial value_
`a ∈ ℝ` and _inductive step_ `step : Natural → ℝ → ℝ`, then
`∀ b : ℝ, (zero, b) ∈ RecGraph a step → a = b`.
:::

```lean "unique_at_zero"
lemma unique_at_zero
  (a : ℝ) (step : Natural → ℝ → ℝ) :
  ∀ b : ℝ, (Natural.zero, b) ∈ RecGraph a step → a = b := by
  intro b hzb
  by_cases hab : a = b
  . show a = b -- hab : a = b
    exact hab
  . show a = b -- hab : a ≠ b
    false_or_by_contra

    let U := (Set.univ : Set (Natural × ℝ))
    let S := U  \ {(Natural.zero,  b)}

    have IS : RecInductive a step S := by
        exact remove_wrong_base hab

    have : (Natural.zero, b) ∈ S := by
      exact (Set.sInter_subset_of_mem IS) hzb

    rcases this with ⟨_, hb⟩

    exact hb (Set.mem_singleton (Natural.zero, b))
```

:::theorem "RecGraph a step is a function"
Let  `F` be the `RecInductive`-set with _initial value_
`a ∈ ℝ` and _inductive step_ `step : Natural → ℝ → ℝ`, then
`F` is a function.
:::

```lean "RecGraph is a function"
theorem RG_is_function (a : ℝ) (step : Natural → ℝ → ℝ) :
  ∀ n : Natural, ∃! x : ℝ, (n, x) ∈  RecGraph a step := by

  let P (n : Natural) :=
    ∃! x : ℝ, (n, x) ∈  RecGraph a step

  let F := RecGraph a step

  have F_inductive : RecInductive a step F := by
          exact RG_inductive a step

  have zaF : (Natural.zero, a) ∈ F := by
    exact F_inductive.left

  have zero_case : P Natural.zero := by
    use a
    constructor
    . exact zaF
    . intro y hy
      exact (unique_at_zero a step y hy).symm

  have succ_case : ∀ n : Natural,
    P n → P (Natural.succ n) := by
    intro n hn

    rcases hn with ⟨x, hnx, hux⟩
    use step n x
    constructor
    . exact F_inductive.right hnx
    .
      intro y hny
      by_contra hxy
      let B := F \ {(Natural.succ n, y)}

      have hsubset : B ⊆ F := by
        exact Set.sdiff_subset

      have hproper :B ≠ F := by
        intro hBF

        have hnyB : (Natural.succ n, y) ∈ B := by
          rw [hBF]
          exact hny

        rcases hnyB with ⟨_, hnot_mem⟩
        apply hnot_mem
        exact Set.mem_singleton (Natural.succ n, y)


      have : RecInductive a step B := by
        constructor
        . have : (Natural.zero, a) ≠
            (Natural.succ n, y) := by
            intro h
            have : Natural.zero = Natural.succ n :=
              congrArg Prod.fst h
            exact ne_of_lt (Natural.zero_lt_succ n) this

          exact ⟨zaF, this⟩

        . intro k z kzB

          have kzF : (Natural.succ k, step k z) ∈ F :=
            by exact F_inductive.right kzB.left

          have kzy : (Natural.succ k, step k z) ≠
            (Natural.succ n , y) := by
            intro h
            by_cases hkn : k = n
            . -- hkn : k = n
              rw [hkn] at kzB
              rw [hkn] at h
              have : z = x := by
                exact hux z kzB.left
              rw [this ]at h

              have : step n x = y := by
                exact congrArg Prod.snd h

              exact hxy this.symm

            . -- hkn : k ≠ n
              have : Natural.succ k = Natural.succ n := by
                exact  congrArg Prod.fst h

              exact hkn (Natural.succ.inj this)

          exact ⟨kzF, kzy⟩

      have : F ⊆ B := by
        exact Set.sInter_subset_of_mem this

      have : F = B := by
        exact Set.Subset.antisymm this hsubset

      exact hproper this.symm

  intro n
  exact Natural.induction zero_case succ_case n
```

```lean "recursion"
-- Induction defines proofs;
-- recursion defines functions.
theorem recursion
  (initial : ℝ)
  (step : Natural → ℝ → ℝ) : ∃! f : Natural → ℝ,
      f Natural.zero = initial ∧
        ∀ n : Natural,
          f (Natural.succ n) = step n (f n) := by

    let F := RecGraph initial step

    let f : Natural → ℝ :=
      fun n => Classical.choose
        (RG_is_function initial step n)

    have f_spec (n : Natural) :
      (n, f n) ∈ RecGraph initial step ∧
      ∀ y : ℝ,
        (n, y) ∈ RecGraph initial step →
        y = f n := by
      exact
      Classical.choose_spec
        (RG_is_function initial step n)

    have hRG :
      RecInductive initial step F := by
        exact RG_inductive initial step

    have f_zero : f Natural.zero = initial := by
      have hinitial : (Natural.zero, initial) ∈ F := by
        exact hRG.left
      exact ((f_spec Natural.zero).2 initial hinitial).symm

    have f_succ :
      ∀ n : Natural,
        f (Natural.succ n) = step n (f n) := by
      intro n

      have hstep :
        (Natural.succ n, step n (f n)) ∈
          RecGraph initial step := by
          exact hRG.2 (f_spec n).1

      exact ((f_spec (Natural.succ n)).right
        (step n (f n)) hstep).symm

    refine ⟨f, ⟨f_zero, f_succ⟩, ?_⟩

     -- Uniqueness
    intro g hg
    funext n

    apply Natural.induction (P := fun n => g n = f n)

    · calc
      g Natural.zero = initial := hg.1
      _ = f Natural.zero := f_zero.symm

    · intro n ih
      calc
      g (Natural.succ n) = step n (g n) := hg.2 n
      _ = step n (f n) := congrArg (step n) ih
      _ = f (Natural.succ n) := (f_succ n).symm


noncomputable def rec
    (initial : ℝ)
    (step : Natural → ℝ → ℝ) :
    Natural → ℝ :=
  Classical.choose (recursion initial step)

theorem Natural.rec_spec
    (initial : ℝ)
    (step : Natural → ℝ → ℝ) :
    rec initial step Natural.zero = initial ∧
    ∀ n : Natural,
      rec initial step (Natural.succ n) =
        step n (rec initial step n) := by
  exact
    (Classical.choose_spec
      (recursion initial step)).1
```

```lean "simplification theorems"
@[simp]
theorem rec_zero
    (initial : ℝ)
    (step : Natural → ℝ → ℝ) :
    rec initial step Natural.zero = initial := by
  exact (Natural.rec_spec initial step).left


@[simp]
theorem rec_succ
    (initial : ℝ)
    (step : Natural → ℝ → ℝ)
    (n : Natural) :
    rec initial step (Natural.succ n) =
      step n (rec initial step n) := by
  exact (Natural.rec_spec initial step).right n
```
# Powers with Natural exponents

We will begin with the definition of powers with natural exponents.

Given a real number `a`, our goal is to define a function
`f: Natural → ℝ`  satisfying:

* `f(0) = 1`
* `f (n + 1) = a · f(n)` for all `n ∈ Natural`

To that end, we start with the following definition:

```lean "exp"
noncomputable def exp (a : ℝ) :=
  rec 1 (fun _ x => a * x )

local infixr:80 " ^ " => exp
```

Having already defined the power with natural exponent,
we prove its main properties:

:::proposition "sum_exponents"
Let $`a` be any real number and let $`m` and $`n` be any natural numbers.
Then, `a ** (m + n) = a ** m ⋅ a ** n`
:::

■■■■■■■■■■■■■■■■■■■■■■■■■■■■■■■■

:::proof "sum_exponents"
We consider the following statement:
$$`P(n) : a^{m + n} \text{ is equal to } a^m ⋅ a^n`
whatever the natural number $`m`
:::

```lean "pow_zero"
theorem pow_zero (a : ℝ) :
    a ^ Natural.zero = 1 := by
    unfold exp
    exact rec_zero 1 (fun _ x => a * x)
```

```lean "pow_succ"
theorem pow_succ (a : ℝ) (n : Natural) :
    a ^ (Natural.succ n) = a * (a ^ n) := by
    unfold exp
    apply rec_succ 1 (fun _ x => a * x)
```

```lean "pow_add"
theorem pow_add
  (a : ℝ) (n m : Natural) :
      a ^ (n + m) = a ^ n * a ^ m := by
  let P (k : Natural) : Prop := a ^ (n + k) = a ^ n * a ^ k

  have zero_case : P Natural.zero := by
    change a ^ (n + Natural.zero) = a ^ n * a ^ Natural.zero
    unfold exp
    calc a ^ (n + Natural.zero)
    _ = a ^ n := by rw [Natural.add_zero]
    _ = a ^ n * 1 := by rw [mul_one]
    _ = a ^ n * a ^ Natural.zero := by rw [pow_zero]

  have succ_case : ∀ k : Natural, P k →
    P (Natural.succ k) := by
    intro k pk
    change a ^ (n + k) = a ^ n * a ^ k at pk
    change a ^ (n + Natural.succ k) =
      a ^ n * a ^ (Natural.succ k)
    have : n + Natural.succ k = Natural.succ (n + k) := by
      exact Natural.add_succ n k
    rw [this]
    have : a ^ Natural.succ (n + k) =  a * a ^ (n + k) :=
      by exact pow_succ a (n + k)
    rw [this]
    rw [pk]
    have : a * (a ^ n * a ^ k) = a ^ n * (a * a ^ k) :=
      by ring
    rw [this]
    have : a * a ^ k = a ^ (Natural.succ k) := by
      rw [pow_succ a k]
    rw [this]

  exact Natural.induction zero_case succ_case m
```

:::proposition "mul_exponents"
Let $`a` be any real number and let $`m` and $`n` be any natural numbers.
Then,  `(a ** m) ** n = a ** (m ⋅ n)`
:::

```lean "power_mul"
theorem pow_mul
  (a : ℝ) (n m : Natural) :
    a ^ (n * m) = (a ^ n) ^ m := by

  let P (k : Natural) := a ^ (n * k) = (a ^ n) ^ k

  have zero_case : P Natural.zero := by
    calc a ^ (n * Natural.zero)
    _ = a ^ Natural.zero := by rw [Natural.mul_zero n]
    _= 1 := by exact pow_zero a
    _ = (a ^ n) ^ Natural.zero := by
      rw [pow_zero (a ^ n)]

  have succ_case : ∀ k : Natural, P k →
    P (Natural.succ k) := by
    intro k pk
    change a ^ (n * Natural.succ k) =
      (a ^ n) ^ Natural.succ k
    calc a ^ (n * Natural.succ k)
    _ = a ^ (n * k + n) := by rw [Natural.mul_succ]
    _ = a ^ (n * k) * a ^ n := by rw [pow_add]
    _ = (a ^ n) ^ k * a ^ n := by rw [pk]
    _ =  a ^ n * (a ^ n) ^ k := by rw [mul_comm]
    _ = (a ^ n) ^ Natural.succ k :=
      by rw [pow_succ (a ^ n) k]

  exact Natural.induction zero_case succ_case m
```

```lean "square"
noncomputable def square (x : ℝ) := x ^ Natural.two


@[simp]
theorem coe_square (x : ℝ) : square x = x * x := by
  calc x ^ Natural.two
    _ = x ^ (Natural.succ Natural.one) :=
      by rw [Natural.two]
    _ = x * x ^ Natural.one := by rw [pow_succ]
    _ = x * (x ^ Natural.succ Natural.zero) :=
      by rw [Natural.one]
    _ = x * (x * x ^ Natural.zero) := by rw [pow_succ]
    _ = x * (x * 1) := by rw [pow_zero]
    _ = x * x := by ring
```
:::proposition  "prop_1.12" (tags := "Bernoulli's Inequality")(parent := "definitions_induction")(lean := "zero_lt_one")
If $`h` is a real number greater than $`−1`,
then for every natural number `n` it holds:
$$`(1 + h)^n ≥ 1 + n · h`.
:::

```lean "prop_1.12"
lemma bernoulli_inequality
  (x : ℝ)
  (hx : -1 < x)
  (n : Natural) : 1 + (n : ℝ) * x  ≤ (1 + x) ^ n := by

  have hx' : 0 < 1 + x := by
    calc
    0 = -1 + 1 := by ring
    _ < x + 1 := by
      exact add_lt_add_left hx 1
    _ = 1 + x := by rw [add_comm]

  let P (k : Natural) : Prop :=
    1 + (k : ℝ) * x  ≤ (1 + x) ^ k

  have zero_case : 1 + (Natural.zero : ℝ) * x ≤
    (1 + x) ^ Natural.zero := by
    calc 1 + (Natural.zero : ℝ) * x
    _ = 1 := by simp
    _ = (1 + x) ^ Natural.zero := by rw [pow_zero]
    _ ≤ (1 + x) ^ Natural.zero := by exact le_of_eq rfl

  have succ_case : ∀ k : Natural, P k →
    P (Natural.succ k) := by
    intro k pk
    change 1 + (k : ℝ) * x  ≤ (1 + x) ^ k at pk
    change 1 + (Natural.succ k : ℝ) * x  ≤
      (1 + x) ^ (Natural.succ k)

    have hkxsq : 0 ≤ (k : ℝ) * (x * x) := by
      exact mul_nonneg (Natural.nat_nonneg k) (sq_nonneg x)

    calc 1 + (Natural.succ k : ℝ) * x
    _ = 1 + ((k : ℝ) + 1) * x := by
      simp only [Natural.succ]
    _ = 1 + (k : ℝ) * x + x  + 0 := by ring
    _ ≤ 1 + (k : ℝ) * x + x + (k : ℝ) * (x * x) := by
      exact add_le_add_right hkxsq (1 + (k : ℝ) * x + x)
    _ = (1 + (k : ℝ) * x) + x * (1 + (k : ℝ) * x) := by ring
    _ = (1 + (k :ℝ) * x) * (1 + x) := by ring
    _ ≤ (1 + x) ^ k * (1 + x) := by
      exact mul_le_mul_of_nonneg_right
        pk (le_of_lt hx')
    _ = (1 + x) * (1 + x) ^ k := by
      rw [mul_comm]
    _ = (1 + x) ^ (Natural.succ k) := by
        rw  [pow_succ (1 + x) k]

  exact Natural.induction zero_case succ_case n
```

(Question: where have we used the hypothesis $`x > −1`?)

We are now going to introduce a concept that we will return to in much more
detail in *Chapter 3* and it is that of sequence;

:::definition "Sequence"
A sequence we mean an assignment to each natural number $`n` of a real
number that we will indicate as $`a_n`. The sequence is usually written:
$$`a_0, a_1, a_2, … ,a_n, …`
:::

 For example, if to each natural number $`n` we assign its square,
 we obtain the sequence given by $`a_n = n ^ two` and which is written:
$$`0, 1, 4, 9, 16, 25, ...,n^2`

As another example, let us consider the assignment to each natural $`n` of
the real number $`a_n = (−1) ^ n`. This gives us the sequence:
$$`1, −1 , 1, −1, 1, … ,(−1)^n,…`

As a final example, let us consider the assignment to each natural number
$`1 ≤ n` of the real number $`a_n = ⅟{n}`. This gives us the sequence:
$$`1, ⅟{2}, ⅟{3}, ⅟{4}, … , ⅟{n} ,…,`

:::definition "Series"
If we now have a determined sequence $`a_0, a_1, a_2 ,…,a_n`,
we want to define the sum of the first $`n` terms of said sequence,
something we will indicate in the form:
$$`a_0 + a_1 + a_2 + ⋯ + a_n`
​or also, in the more compact and precise form:
$$`∑_{k=0}^n a_k`
 (read: "sum from $`k=1` to $`k=n` of the $`a_k`").
:::

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

```lean "series"
noncomputable def series (g : Natural → ℝ) : Natural → ℝ :=
  rec 0 (fun n x => g (Natural.succ n) + x)
```

```lean "sum_zero"
theorem sum_zero {g : Natural → ℝ}:
    series g Natural.zero = 0 := by
    unfold series
    exact rec_zero 0 (fun n x => g (Natural.succ n) + x)
```
```lean "sum_succ"
theorem sum_succ {g : Natural → ℝ}:
  series g (Natural.succ n) =
    g (Natural.succ n) + series g n := by
  unfold series
  apply rec_succ _ (fun n x => g (Natural.succ n) + x)
```

```lean "triangular"
noncomputable def triangular :=
  series (fun (n : Natural) => n )
```

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
$`0 + 1 + 2 + ⋯ + n = n(n+1)/2`.
:::

```lean "triangular numbers"
theorem sum_eq_formula (n : Natural) :
  2 * triangular n = (n : ℝ) * ((n : ℝ) + 1) := by

  let P (k : Natural) : Prop :=
    2 * triangular k = (k : ℝ) * ((k : ℝ) + 1)

  have zero_case : P Natural.zero := by

    change  2 * triangular Natural.zero =
      (Natural.zero : ℝ) * ((Natural.zero : ℝ) + 1)

    have : triangular Natural.zero = (0 : ℝ) :=
      by exact sum_zero
    simp [Natural.zero]

    exact sum_zero

  have succ_case : ∀ k : Natural, P k →
    P (Natural.succ k) := by
    intro k pk

    change 2 * triangular k = (k : ℝ) * ((k : ℝ) + 1) at pk
    change 2 * triangular (Natural.succ k) =
      (k + 1 : ℝ) * (k + 1 + 1 : ℝ)

    unfold triangular

    unfold triangular at pk

    rw [sum_succ]


    have : 2 * (↑(Natural.succ k) +
      series (fun n => ↑n) k) =
        2 * ↑(Natural.succ k) +
          2 * series (fun n => ↑n) k := by
      ring

    rw [this]
    rw [pk]
    simp [Natural.succ]


    calc 2 * ((k : ℝ) + 1) + ↑k * (↑k + 1)
    _ = (↑k + 1)  *(↑k + 1 + 1 ) := by ring

  exact Natural.induction zero_case succ_case n
```

# Exercises

1. Prove that if $`a` and $`b` are any real numbers,
  then for every natural number $`n` it holds:
$$`(a ⋅ b) ^ n = a ^ n ⋅ b ^ n`
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

  * d) Prove that if $`a>1` and $`n ∈ N`, then $`a^n > 1`.
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
\quad \text{for all } n\ge 5`.

```lean "end DefinitionsByInduction"
end DefinitionsByInduction
```
