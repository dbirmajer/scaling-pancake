import Mathlib.Data.Nat.Notation
import Mathlib.Data.Real.Basic

import Verso
import VersoManual
import VersoBlueprint

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Basic and Derived Properties" =>

:::author "project_author-1" (name := "Daniel Birmajer")
:::

The [Lean website](https://lean-lang.org)

```tex
\begin{enumerate}
    \item \textbf{Basic properties and derived properties}
    \item \textbf{Basic properties of the real numbers}
    \item \textbf{Natural numbers}
    \item \textbf{Definitions by induction}
    \item \textbf{More definitions by induction and Newton's formula}
    \item \textbf{Integers}
    \item \textbf{Rational numbers}
    \item \textbf{Completeness property}
    \item \textbf{Consequences of the completeness property}
    \item \textbf{Powers with rational exponent}
    \item \textbf{Powers with real exponent}
    \item \textbf{Modulus or absolute value of a real number}
\end{enumerate}
```
What are the properties of real numbers?

At first, the many known—and yet undiscovered—properties of the real numbers may
make a complete account seem impossible.  A closer examination, however,
suggests otherwise.

Let us consider a few properties, for example:

  * $`\bigstar\; 1.` The sum of real numbers is commutative:
    $`a + b = b + a` for any real numbers $`a` and $`b`.

  * $`\bigstar\; 2.` Minus times minus is plus.

  * $`\bigstar\; 3.` The square of the sum of two real numbers is equal to the
  sum of their squares plus their double product:
  $`(a + b)^2 = a^2 + 2a \cdot b + b^2`.


The attitude towards each of these three properties is, without a doubt,
different. The first will seem natural, or you will have been convinced of it
by seeing some examples; the second you will remember as a "recipe"
of which you were informed at the time; and, if memory serves,
you will remember that the third has been _demonstrated_ to you in the
following way:

$$`
\begin{align*}
    (a + b)^2 &= (a + b) \cdot (a + b) = (a + b) \cdot a + (a + b) \cdot b = \\
    &= a \cdot a + b \cdot a + a \cdot b + b \cdot b = \\
    &= a^2 + 2a \cdot b + b^2
\end{align*}
`

This last observation suggests the following reflections:

* $`\bigstar\; \mathrm{i.}` In a list of the properties of real numbers it would not be
necessary to include property 3 since it can be deduced from other properties;
in particular, it would seem that we only need to know that
$`a \cdot b = b \cdot a` and to know how to multiply a sum of numbers by
another real number.

* $`\bigstar\; \mathrm{ii.}` If in this way we eliminate from our list those properties that
can be deduced from others more elementary, at some point we must arrive at
properties that cannot be demonstrated, which must serve as a starting point.

  At first glance, properties 1 and 2 should appear on that list since they
  do not seem susceptible to a demonstration.

* $`\bigstar\; \mathrm{iii.}` Once a list of properties is obtained that we can no longer
demonstrate but which serve as a starting point to demonstrate all the others,
that list could be considered to contain all the properties of real numbers,
at least potentially.
The properties enumerated in said list we could call *axioms* and all the
remaining properties, demonstrable from the basic ones,
we could call *derived*.

In the next paragraph we are going to present the list of basic properties of
real numbers; it may surprise you how low the number of them is;
_there are only 14_ and from them it is possible to derive all the study of
real numbers, in particular the content of this book.
