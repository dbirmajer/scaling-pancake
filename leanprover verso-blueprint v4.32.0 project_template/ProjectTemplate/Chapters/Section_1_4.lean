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
theorem G_set_G_inductive_G (a : ℝ) (step : ℝ → ℝ → ℝ)
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
    exact (G_set_G_inductive_G a step)
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
  {a : ℝ} {step : ℝ → ℝ → ℝ} :
  ∀ b : ℝ, (1, b) ∈ G a step → a = b := by
  intro b hb
  by_cases hab : a = b
  . show a = b -- hab : a = b
    exact hab
  . show a = b -- hab : a ≠ b
    false_or_by_contra
    let S := ((Natural ×ˢ
        (Set.univ : Set ℝ)) \ {(1, b)})
    have : G_inductive a step S := by
        exact remove_wrong_base hab
    have : G a step ⊆ S := by
        apply Set.sInter_subset_of_mem this
    have : (1, b) ∈ S := by
      exact this hb
    rcases this with ⟨_, b_ne_b⟩
    exact b_ne_b (Set.mem_singleton (1, b))


lemma unique_at_x {a : ℝ} {step : ℝ → ℝ → ℝ}:
  ∀ {x y : ℝ} , (x, y) ∈ G a step ∧
    (x + 1, b) ∈ G a step → b = step x y := by sorry
```

# Powers with Natural exponents

We will begin with the definition of powers with natural exponents.

Given a real number `a`, our goal is to define a function
`f: Natural → ℝ`  satisfying:

* `f(1) = a`
* `f (n + 1) = a · f(a)` for all `n ∈ Natural`

To that end, we start with the following definition:

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
      change ∀ {B : Set (ℝ × ℝ)},
        PowerInductive a B → (x + 1, a * y) ∈ B
      intro B hB
      have pxy_mem_B : (x, y) ∈ B := by
        exact  pxy_mem_A hB
      exact hB.right pxy_mem_B

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


Having already defined the power with natural exponent,
we prove its main properties:

:::proposition "prop_1.11"
Let $`a` be any real number and let $`m` and $`n` be any natural numbers.
Then:
  * a) $`a^{m + n} = a^m ⋅ a^n`

  * b) $`(a^m)^n =a^{m⋅n}`
:::
■■■■■■■■■■■■■■■■■■■■■■■■■■■■■■■■

:::proof "prop_1.11"
* a) We consider the following statement:
$$`P(n) : a^{m + n} \text{ is equal to } a^m ⋅ a^n`
whatever the natural number $`m`"
:::

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
