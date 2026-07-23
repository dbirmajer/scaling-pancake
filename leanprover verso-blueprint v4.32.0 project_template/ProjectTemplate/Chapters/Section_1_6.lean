import Mathlib.Data.Nat.Notation
import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Sum

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

#doc (Manual) "The Integers" =>


```lean "open Integers"
namespace Integers
```
The *integers* are the natural numbers $`0, 1, 2, 3, 4`, etc.,
and also $`-1, -2, -3`, etc. More precisely:

:::definition "1.14."
A real number $`m` is said to be an integer if it satisfies one (and only one) of the
three following conditions:

* $`\mathrm{i)}\quad m \in \mathbb{N}` with $`m > 0`.
* $`\mathrm{ii)}\quad m = 0`.
* $`\mathrm{iii)}\quad m = -n`, for some natural number $`n > 0`.
:::

The set of integers will be denoted by ℤ.

In other words, the integers are the natural numbers along with their additive
inverses and $`0`.

:::lemma_ "prop_1.15"
If $`a` and $`b` are integers, then $`a + b`, $`ab`, and $`a - b` are also integers.
:::

:::proof "prop_1.15"
Let's see first that $`a + b` is an integer.
Since $`a` and $`b` have three possibilities each,
we have to consider nine possibilities for the sum.

We perform the proof in some of those cases and the
remaining ones will be left as exercises.

1. $`a \in \mathbb{N}`, $`b \in \mathbb{N}`.
   In this case $`a + b \in \mathbb{N}` by Proposition 1.5 of paragraph 1.2.
   Then $`a + b \in \mathbb{Z}`.

2. $`a \in \mathbb{N}`, $`b = 0`.
   In this case, $`a + b = a + 0 = a` $`\in \mathbb{N} \subseteq \mathbb{Z}`.

3. $`a \in \mathbb{N}`, $`b = -n` with $`n \in \mathbb{N}`.
   Then $`a + b = a - n`; there are three possibilities:

   * $`a > n`. Here $`a - n \in \mathbb{N}` by Proposition 1.8 of paragraph 1.2,
     then $`a - n \in \mathbb{Z}`.

   * $`a = n`. Here $`a - n = 0 \in \mathbb{Z}`.

   * $`a < n`. Here $`a - n = -(n - a)` and since $`n - a \in \mathbb{N}` by Proposition 1.8,
     then $`a - n` is the additive inverse of a natural number (of $`n - a`)
     and therefore $`a - n \in \mathbb{Z}`.

4. $`a = -n`, $`b = -m` for $`n` and $`m` natural (Exercise).

5. $`a = -n`, $`b \in \mathbb{N}` for $`n` natural (Similar to case 3).

6. $`a = -n`, $`b = 0` for $`n` natural (Exercise).

7. $`a = 0`, $`b \in \mathbb{N}` (Similar to case 2).

8. $`a = 0`, $`b = 0` (Exercise).

9. $`a = 0`, $`b = -n` for $`n` natural (Exercise).

The proofs of the other properties, $`ab \in \mathbb{Z}` and
$`a - b \in \mathbb{Z}`, are also left as an exercise.
:::

A notion that we will need in the following paragraph is divisibility,
which we proceed to define.

If $`a` and $`b` are integers, and $`a \neq 0`, we say that _$`a` divides $`b`_,
and we write $`a \mid b`, if there exists another integer $`m` such that:
$$`b = m \cdot a`

(In other words, $`a` divides $`b` if the division $`b \div a` is _exact_).

If $`a` and $`b` are natural numbers and $`a` divides $`b`,
then $`a \le b`. Indeed, since $`b = m \cdot a` for some integer $`m`,
and since $`a` and $`b` are positive, the same must happen for $`m`.
But a positive integer is a natural number;
then $`m \ge 1` by *prop 1.6*
and therefore:
$$`b = m \cdot a \ge 1 \cdot a = a`

Whether $`a` divides $`b` or not, the reader will have learned in their time the
"instructions" for performing the division between $`b` and $`a`,
which was equivalent to finding a quotient $`q` and a remainder $`r`.
This you will have seen written in the form:

$$`b = a \cdot q + r, \quad 0 \le r < a`

This arrangement means that $`a \cdot q + r = b`. But finding quotient and
remainder is not simply finding two numbers $`q` and $`r` that satisfy
$`a \cdot q + r = b`; for that is already achieved in the first step of the division,
and one continues dividing until reaching a remainder that _cannot_ be divided.
And this last part means that $`r` is less than $`a`.

The _instructions_ for dividing $`b` by $`a` allow us to guess that it is always
possible to find $`q` and $`r` with those two properties;
forgetting about the instructions, we now prove that this actually occurs:

:::theorem "division-algorithm"
If $`a` and $`b` are integers and $`a > 0` (that is, $`a` is a
non-zero natural number), then there exist unique integers $`q` and $`r` satisfying:
  * i) $`b = a \cdot q + r`
  * ii) $`0 \le r < a`
:::

:::proof "division-algorithm"
Note that this Theorem asserts two things: that there exist
$`q` and $`r` that satisfy i) and ii) and furthermore that they are unique.
We then divide the demonstration into two parts.

Consider the following set:
$$`H = \{ b - a \cdot q : q \in \mathbb{Z} \text{ and } b - a \cdot q \ge 0 \}
`
that is, let us form all possible numbers of the form $b - a q$ ($a$ and $b$ are fixed and all those numbers are obtained by giving various values to $q$) that are greater than or equal to zero. That set is not empty (for example, for $`q = -|b|`,
it results $`b - a \cdot q \in H`).

If $`0 \in H`, that is, if one of those combinations is zero, say $`b - a q = 0` for a certain $`q`, then that same $`q` and $`r = 0` satisfy i) and ii).

If $`0 \notin H`, then $`H \subset` ℕ because $`b - a q` is always an integer
(Proposition 1.15), it is $`> 0` and, since it is not 0, it is a positive integer,
that is, a natural number. Since $`H \subset \mathbb{N}`, by the Well-Ordering Principle (Theorem 1.10), $`H` has a minimum; let us call $r$ that minimum.
Since $`r` is an element of $`H` (by definition of minimum) then:
$$`r = b - a q`
for a certain $`q`. We then already have $`q` and $`r` that fulfill i).

Let us see that $`r` satisfies ii).
If it were not so, it would be $`r \ge a`. Then $`r - a \ge 0` and furthermore:
$$`r - a = b - a q - a = b - a(q + 1)`
Then $`r - a \in H` and furthermore $`r - a < r` (recall that $`a > 0`),
which contradicts the fact that $`r` is the minimum of $`H`.


In short, it results $`0 \le r < a`, that is, the $`q` and $`r` found satisfy i) and ii).

Let us now see the second part of the Theorem, that is,
that there are no other $`q` and $`r` that satisfy i) and ii).
Suppose then that $`q_1` and $`r_1` are integers such that:

$$`
\begin{align*}
    b &= a q_1 + r_1 \\
    0 &\le r_1 < a
\end{align*}
`

Then it is:
$$`a q + r = a q_1 + r_1`
from where:
$$`a(q - q_1) = r_1 - r`
This says that $a$ divides $`r_1 - r`. If we suppose $`r_1 > r`,
then according to what we saw, $`a \le r_1 - r`.
But since $`r \ge 0`, $`r_1 - r \le r_1 < a`, so it cannot be $`r_1 > r`.

Analogously we see that it cannot be $`r_1 < r`.
Then $`r_1 = r` and from $`a(q - q_1) = r_1 - r = 0`,
we obtain (since $`a` is not zero), $`q - q_1 = 0`, then $`q = q_1`.
This shows that $`q` and $`r` are unique and finishes proving the Theorem.
:::

As an application of this Theorem, let us see a fact that is of public domain.
An integer $`m` is said to be _even_ if it is divisible by 2, that is if $`2 ∣ m`,
and it is said to be _odd_ if it is not divisible by 2.
The form that even numbers have results immediately: if $`2 ∣  m`, then
$$`m = 2k, \quad \text{for some integer } k`,
and every number of the form $`2k` for $`k \in \mathbb{Z}` is an even number.

```lean "even"
def Even (n : Nat) : Prop :=
  ∃ k, n = 2 * k
```
What happens with the odd ones?
If $`m` is odd, by the previous Theorem we can write:
$$`m = 2k + r \quad \text{with } 0 \le r < 2`
Then it is $`m = 2k + 0` or $`m = 2k + 1`.
The first case cannot happen because it would imply that $`m` is divisible by 2.
It must then be $`m = 2k + 1` for some integer $`k`.

Conversely, if $`m` is of the form $`2k + 1`,
then it cannot be of the form $`2k'` for some other integer $`k'` due to the
uniqueness of the quotient and remainder just demonstrated.
Therefore $`m` is odd. In short:

: Even numbers

  $`n` is even $`\longleftrightarrow`  $`n = 2k` (for some $`k \in \mathbb{Z})`

: Odd numbers

  $`n` is odd $`\longleftrightarrow` $`n = 2k + 1` (for some $`k \in \mathbb{Z})`


Now let $`m` be an even number; then $`m = 2k`$ for a certain $`k \in \mathbb{Z}`.
If $`k` is also even, $`k = 2k'`, then $`m = 2^2 k'`.
If we continue analyzing $`k'`, etc., we realize that there will come a moment
when the factor in question ($`k', k'`,
or whichever it may be) will be odd and there the process stops.

Although realizing this is easy, proving this fact from the basic properties stated
at the beginning of this chapter requires a bit of work.

In the first place, by Bernoulli's inequality (Proposition 1.12) it is:
$$`2^m = (1 + 1)^m \ge 1 + m \cdot 1 = 1 + m > m`
whereby it cannot be that $`2^m | m` (in that case it would be $`2^m \le m` as we saw).
Let us then consider the set:
$$`A = \{ p \in \mathbb{N} : 2^p \text{ does not divide } m`
This set is included in ℕ by its definition and is non-empty (we have just seen that
$`m \in A`).
Then, by the Well-Ordering Principle (Theorem 1.10),
$`A` has a minimum. Let:
$$`q = \min A`
and let:
$$`t = q - 1`

Then $`2^q` does not divide $`m` but $`2^t` does (if it were not so,
then $`t \in A < \min A`, which is a contradiction).
Then it will be:
$$`m = 2^t k`
and $`k` must be odd:
if $`k = 2k'`, it will be
$$`m = 2^t \cdot 2k' = 2^{t+1} k' = 2^q k', \text { that is }, 2^q | m`.

In short, we have shown that if $m$ is even, there exists
$`t \in ℕ` and $`k` odd such that $`m = 2^t k`.
We will use this fact in the next paragraph.

To finish with the integers, let us see how the power of an integer exponent is
defined. The guide for our definition will be that Proposition 1.11 remains
valid when $`m` and $`n` are integers.

In the first place, we define $`a^0`.
If a) of 1.11 holds, then it will be:
$$`a^0 \cdot a^n = a^{0+n} = a^n`
and, if $`a \neq 0`, multiplying by $`(a^n)^{-1}` (which is also distinct from 0):
$$`a^0 = 1`.
Therefore we are forced to define $`a^0` as 1 for $`a \neq 0`.

We now define $`a^{-n}` for $`n \in \mathbb{N}`.
Always on the basis of a) of 1.11, it must be:
$$`a^{-n} \cdot a^n = a^{-n+n} = a^0 = 1`,
and therefore:
$$`a^{-n} = \frac{1}{a^n} = (a^n)^{-1}`.

Again, for Proposition 1.11 to hold when $`m` and $`n` are integers,
we are forced to define $`a^{-n}` as $`(a^n)^{-1}`.

```lean "end Integers"
end Integers
```
# Exercises

1. Prove in detail *Proposition 1.15.*
2. Prove that if $`m` is even, $`m^2` is even and that if $`m` is odd, $`m^2` is odd.
3. Prove that the remainder of dividing $`m^2` by 3 is always 0 or 1.

4. Prove that with the definitions $a`^0 = 1` and $`a^{-n} = (a^n)^{-1}`
it results:
  * a) $`a^{m+n} = a^m \cdot a^n` for all integers $`m, n\;  (a \neq 0)`.
  * b) $`(a^m)^n = a^{mn}` for all integers $`m, n\;  (a \neq 0)`.
    *HINT:* consider all possible cases for $`m` and $`n` as in 1.15.

5. If $`a` is a real number greater than 1,
prove that if $`m` and $`n` are integers and $`m < n`,
then $`a^m < a^n`.
What happens if $`0 < a < 1`? (Consider $`1/a` in this last case).

6. Prove that if $`m ∈ ℤ` and $`m \neq 0`,
then there exists $`t ∈ ℕ \cup \{0\}` such that
$`2^t` divides $`m` and $`2^{t+1}` does not divide $`m`.
