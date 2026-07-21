import Mathlib.Data.Nat.Notation
import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.Choose.Basic

import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring


import Verso
import VersoManual
import VersoBlueprint

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "More Definitions by Induction and Newton's Formula" =>


:::group "more_definitions"
More definitions by Induction and Newton's formula
:::

Let us consider again any sequence $`a_0, ​a_1, …, a_n`.
We have already defined the sum of the first $`n` elements of this
sequence, whatever the natural number $`n` may be.
Similarly, we are going to define the product of the first $`n` terms of
said sequence, a product that we will indicate in any of the following
forms:

$$`\prod_{k=1}^{n} a_k
\qquad \text{o bien} \qquad
a_1 a_2 \cdots a_n.
`
As this must be done for every natural $`n`, the definition will naturally be
by induction. We define first for $`n = 1`:
$$`\prod_{k=1}^{1} a_k = a_1.`

and then, assuming that we already have it defined for a certain $`n`,
we define:
$$`
\prod_{k=0}^{n+1} a_k
=
\left(\prod_{k=1}^{n} a_k\right)a_{n+1}.
`

For example,

$$`
\prod_{k=0}^{1} a_k
=
\left(\prod_{k=0}^{1} a_k\right)a_1
= a_0 a_1,
`

$$`
\prod_{k=0}^{2} a_k
=
\left(\prod_{k=0}^{1} a_k\right)a_2
=
(a_0a_1)a_2 =a_0a_1a_2,
`

$$`\prod_{k=0}^{3} a_k
=
\left(\prod_{k=0}^{2} a_k\right)a_3
=
(a_0a_1a_2)a_3
=
a_0a_1a_2a_₃,
`and so on.

For example, if $`a_1, a_2, \ldots, a_n,\ldots`$ is the
_constant sequence_, that is, if $`a_n=b` for every natural
number $`n` (in which case the sequence is $`b, b, …, b, …`),
then
$$`
\prod_{k=1}^{n} a_k=b^n.
`

This recovers the original meaning of $`b^n`: the product of $`b`
by itself $`n` times. What we have done is give a precise meaning
to the expression "the product of $`n` numbers,'' regardless of
the natural number $`n`".


We now introduce two definitions that will be useful shortly.

:::definition "factorial"
The _factorial_ of a natural number $`n`,
which we denote by $`n!`. It is defined as the product of all
natural numbers from $`1` to $`n`:

$$`
\begin{align*}
0! &= 1;\
n! &= \prod_{k=1}^{n} k, \;   \text{ for } n ≥ 1.
\end{align*}
`

Or, if the reader prefers the more traditional notation,

$$`
\begin{align*}
0! &= 1;\
n! &= 1\cdot2\cdot3\cdots n, \quad µ{for } n ≥ 1.
\end{align*}
`
:::

For example,

$$`
\begin{align*}
1! &= 1,\\
2! &= 1 \cdot 2 = 2,\\
3! = 1 \cdot 2 \cdot 3 = 6,\\
4! = 1 \cdot 2 \cdot 3 \cdot 4 = 2,\
5! = 1 \cdot 2 \cdot 3 \cdot 4 \cdot 5 = 120,
\end{align*}
`
and so on.

It is very easy to prove the following property of factorials:

:::lemma_ "factorial_succ" (tags := "Factorial of Succ n")(parent := "more_definitions")(lean := "Nat.factorial_succ")
$$`(n+1)! = n!(n+1).`
:::

Indeed,

```lean "factorial"
example : Nat.factorial 0 = 1 := by
  exact Nat.factorial_zero

example (n : ℕ) :
  (n + 1).factorial = (n + 1) * n.factorial := by
    exact Nat.factorial_succ n
```


The second definition we wish to introduce is that of a
_binomial coefficient_.

:::definition "choose" (tags := "Binomial Coefficient")(parent := "more_definitions")(lean := "Nat.choose")
Given a natural number $`n` and a natural number $`k \le n`,
we define the binomial coefficient "$`n` choose $`k`" by

$$`
\binom{n}{k} =\frac{n!}{k!(n-k)!}.
`
:::

Why give a special name to this somewhat strange number?
The reason is the following. Suppose we have $`n` elements,

$$`a_1, a_2,\ldots, a_n,`

and we wish to form subsets consisting of $`k` of these
elements. For example,

$`\{a_1,a_2,\ldots,a_k\}`, or
$`\{a_2,a_3,\ldots,a_k,a_{k+1}\}`,
or
$`\{a_1,a_3,a_4,\ldots,a_k,a_{k+1}\}`, and so on.

How many of those sets can we form? Well, exactly $`\binom{n}{k}` sets,
as shown by the following argument: to choose the first element of the set,
we have $`n` possibilities; we can choose $`a_1` or $`a_2` or any other.

Once the first element is fixed, to fix the second element we have $`n - 1`
possibilities, all those that we have not already chosen.
Then to fix the first and second elements we have a total of $`n(n - 1)`
possibilities.

Now we have $`n - 2` possibilities to fix the third element,
so to fix the _three_ first we have $`n(n - 1)(n - 2)` possibilities.
Following this, when we reach the $`k-th` element,
$`n - (k - 1) = n - k + 1` possibilities will remain for us,
since up to that moment we fixed $`k - 1` of them.
Total number of possibilities: $`n(n - 1)(n - 2) \dots (n - k + 1)`.

But pay attention, we are counting each set several times.

For example, according to how we have counted, one possibility is to choose
first $`a_1`, then $`a_2`, then $`a_3`, etc., until reaching $`a_k`,
and another possibility is to choose first $`a_2`, then $`a_1`, then $`a_3`
and then continue in order until reaching $`a_k`.
The sets that remained in this example are:

$$`
\begin{align}
    \{a_1, a_2, a_3, \dots, a_k\} \quad (1) \\
    \{a_2, a_1, a_3, \dots, a_k\} \quad (2)
\end{align}
`

Now then, these two sets *as sets are equal*, they have the same elements;
it doesn't matter in what order we have placed them. This means that in our total number of possibilities, which was $`n(n - 1)(n - 2) \dots (n - k + 1)`,
we are counting too many; we are considering possibilities such as (1) and (2) as distinct, when they are the same.

The question is then, how many times have we counted each possibility?
Or put another way: in how many ways can we, for example, reorder the set (1)?

We apply an argument identical to the one already used: to decide which will be the first element we have $k$ possibilities, $`a_1` or $`a_2` or any up to $`a_k`.

Once the first one is chosen, to choose the second one we have $`k - 1` possibilities (all except the choice made for the first one).
Following this, we see that the set (1) can be ordered in
$`k(k - 1) \dots 2 \cdot 1` ways (here in the regressive product we reach up
to 1: if we choose $`k - 1`, the last element must be the only one left).

But that number is exactly what we had called $`k!`.
In summary, there were $`n(n - 1) \dots (n - k + 1)` possibilities,
but those possibilities we divide into groups of $`k!` possibilities in such a
way that in each group all the possibilities are only one.

The true number of possibilities is then:
$$`\frac{n(n - 1) \dots (n - k + 1)}{k!}`

This number does not change if we multiply numerator and denominator by
$`(n - k)!`. Let's do it:

```lean "choose"
example (n k : ℕ) : n.choose k =
  Nat.descFactorial n k / Nat.factorial k := by
    exact Nat.choose_eq_descFactorial_div_factorial n k

example (n k : ℕ) :
  Nat.choose n k =
     Nat.descFactorial n k / Nat.factorial k := by

  -- 1. Rewrite the descending factorial into its
  -- multiplicative form
  rw [Nat.descFactorial_eq_factorial_mul_choose]

  -- 2. Cancel out `Nat.factorial k` from the
  -- numerator and denominator
  rw [Nat.mul_div_cancel_left]

  -- 3. Ensure that k! is strictly greater than 0 so
  -- division by zero rules don't apply
  exact Nat.factorial_pos k
```

$$`
\begin{align}
    &\frac{n(n - 1) \dots (n - k + 1)(n - k)!}{k!(n - k)!} \\
    =& \frac{n(n - 1) \dots (n - k + 1)(n - k)(n - k - 1) \dots 2 \cdot 1}{k!(n - k)!} \\
    =& \frac{n!}{k!(n - k)!} = \binom{n}{k}
\end{align}
`
which is the promised result.

If the reader is not one of those who give up easily, they will wonder why
they want to know how many sets of $`k` elements they can form if they
choose those $`k` elements from among $`n` pre-fixed ones.
Which leads us straight to the last topic of this section, which is
*Newton's formula*.

The formula is well known:
$$`(a + b)^2 = a^2 + 2ab + b^2`
and the formula is also known:
$$`(a + b)^3 = a^3 + 3a^2b + 3ab^2 + b^3`

If one starts to work, they will find the formula for $`(a + b)^4`
(multiplying $`a + b` by itself 4 times), $`(a + b)^5`, etc.
But it would be good to have a formula that tells us the value of
$`(a + b)^n`$ for any natural number $`n`.
A bit of reasoning and we will have it:

To calculate $`(a + b)^n` we must multiply $`a + b` by itself $`n` times:
$$`
(a + b)^n = (a + b)(a + b) \dots (a + b) \quad (n \text{ times})
`
This product is carried out by applying the distributive property and grouping the factors that have the same power in $`a` and the same power in $`b`.
How many of these factors appear?

Of course, if $`a` appears raised to the $`k`, $`b` must appear raised to the
$`n - k` because each multiplication consists of $`n` factors.
Then each term that appears when distributing has the form:
$$`a^k b^{n-k}`
Again, how many of these terms are there? Let's number the factors:
$$`
\underbrace{(a + b)}_{F_1} \underbrace{(a + b)}_{F_2} \dots \underbrace{(a + b)}_{F_n}
`
By multiplying $`a` from $`F_1` by $`a` from $`F_2, \dots, a` from
$`F_k` and then by $`b` from $`F_{k+1}, b` from $`F_{k+2}, \dots, b` from
$`F_n`, we obtain $`a^k b^{n-k}`$.

We can see that it is enough to say from which $`k` factors the $`a`
was taken for multiplication, to know that from the remaining $`n - k` the
$`b` must be taken for multiplication;
we then focus on seeing from which of the factors the $`a` was taken to multiply.

There are several possibilities: taking it from $`F_1, F_2, \dots, F_k` as we indicated before, or from $`F_2, F_3, \dots, F_{k+1}`, etc.

Perhaps the reader is guessing that there are as many ways to get
$`a^k b^{n-k}` as there are ways to choose $k$ factors among
$`F_1, F_2, \dots, F_n`.
But it is exactly $`\binom{n}{k}` according to what we argued before.
Then when doing all the possible products we will get:
$$`\binom{n}{k} a^k b^{n-k}`

And this for all possible values of $`k`.
We are now in a position to conjecture the following formula:
$$`
(a+b)^n = \binom{n}{0} a^n b^0 + \binom{n}{1} a^{n-1} b^1 + \binom{n}{2} a^{n-2} b^2 + \dots + \binom{n}{n-1} a^1 b^{n-1} + \binom{n}{n} a^0 b^n
`
or, in a more compact and precise form:
$$`(a+b)^n = \sum_{k=0}^{n} \binom{n}{k} a^k b^{n-k}`
which is the famous Newton\'s formula. We have already conjectured it;
now let\'s prove it:

:::theorem "add_pow" (tags := "Newton's Formula")(parent := "more_definitions")(lean := "Finset.add_pow")
If $`a` and $`b` are any real numbers, then for every natural number $`n`:

$$`(a + b)^n = \sum_{k=0}^{n} \binom{n}{k} a^k b^{n-k}
`
:::

```lean "add_pow"
example (a b : ℝ) (n : ℕ) :
    (a + b) ^ n = ∑ k ∈ Finset.range (n + 1),
      a ^ k * b ^ (n - k) * n.choose k := by
  let t : ℕ → ℕ → ℝ :=
    fun n k ↦ a ^ k * b ^ (n - k) * n.choose k
  change (a + b) ^ n = ∑ k ∈ Finset.range (n + 1), t n k

  have h_first : ∀ n, t n 0 = b ^ n := fun n ↦ by
    unfold t
    rw [Nat.choose_zero_right,
        pow_zero,
        Nat.cast_one, mul_one,
        one_mul, Nat.sub_zero
        ]

  have h_last : ∀ n, t n n.succ = 0 := fun n ↦ by
    simp only [t,
              Nat.choose_succ_self,
              Nat.cast_zero,
              mul_zero]

  have h_middle :
      ∀ n i : ℕ,
        i ∈ Finset.range (n + 1) → (t (n + 1) (i + 1)) =
        a * t n i + b * t n (i + 1) := by
    intro n i h_mem
    have h_le : i ≤ n :=
      Nat.le_of_lt_succ (Finset.mem_range.mp h_mem)
    unfold t
    rw [Nat.choose_succ_succ, Nat.cast_add, mul_add]
    congr 1
    · rw [pow_succ' a,  Nat.succ_sub_succ, mul_assoc,
        mul_assoc, mul_assoc]
    · rw [← mul_assoc b, ← mul_assoc b]
      have h_cases := Nat.eq_or_lt_of_le h_le
      rcases h_cases with h_eq | h_lt
      . rw [h_eq, Nat.choose_succ_self, Nat.cast_zero,
          mul_zero, mul_zero]
      . rw [mul_comm b, mul_assoc, mul_assoc (a ^ (i + 1))]
        rw [mul_comm b, ←pow_succ b (n - (i +1))]
        rw [Nat.sub_add_eq, Nat.succ_sub h_le]
        rw [mul_assoc]
        congr 1; congr 1; congr 1
        omega

  induction n with
  | zero =>
      rw [pow_zero,
          Finset.sum_range_succ,
          Finset.range_zero,
        Finset.sum_empty, zero_add]
      rw [h_first 0, pow_zero]

  | succ n ih =>
      rw [Finset.sum_range_succ', h_first,
        Finset.sum_congr rfl (h_middle n)]
      rw [Finset.sum_add_distrib,
          add_assoc,
          pow_succ' (a + b),
          ih]
      rw [add_mul, Finset.mul_sum, Finset.mul_sum]
      congr 1
      rw [Finset.sum_range_succ', h_first, ← pow_succ' b,
        Finset.sum_range_succ]
      congr 1
      rw [h_last, mul_zero, add_zero]
```
then Newton's formula, assumed true for $`n`,
is true for $`n + 1`, which means it is true for every natural number. ///

# EXERCISES

1. Prove that if $`n` is natural and $`k` is natural, $`k \le n`, then:
$$`\binom{n}{k-1} + \binom{n}{k} = \binom{n+1}{k}`

2. Prove that $`\binom{n}{0} = \binom{n}{n} = 1`
for every natural number $`n`.

3. Prove that $`\binom{n}{k}` is always a natural number
(Use *Exercise 1* and the Principle of _strong induction_,
*Exercise 2 of paragraph 1.3*)

4. Expand $`(a + b)^3` and $`(a + b)^4` using Newton's formula.

5. Prove that
$$`\binom{n}{0} + \binom{n}{1} + \dots + \binom{n}{n} = 2^n`.

6. Prove that $`\binom{n}{k} = \binom{n}{n-k}` for natural
$`n` and $`k \le n`.
