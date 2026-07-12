--import Mathlib.Data.Nat.Notation
import Mathlib.Data.Real.Basic

import Verso
import VersoManual
import VersoBlueprint

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Basic Properties of Real Numbers" =>

:::source_document "addition-source"
%%%
title := "Starter Addition Notes"
kind := .pdf
pdf := "source/addition-source.pdf"
%%%
:::

:::group "addition_core-1"
Core statements about addition on real numbers.
:::

:::author "project_author-1" (name := "Daniel Birmajer")
:::

```lean "namespace"
namespace Section_1_2
```
We will begin with the basic properties of _addition_, which are four:

   * *Commutative property*

:::theorem "add_comm" (parent := "addition_core-1")(lean := "add_comm")
For any real numbers $`a` and $`b`, the following holds:
$$`a + b = b + a`
This is another consequence of {uses "addition_spec"}[].
:::

```lean "add_comm"
example (a b : ℝ) : a + b = b + a := add_comm a b
```

:::definition "addition_spec-1" (parent := "addition_core-1")
We write $`a + b` for the result of adding $`b` to $`a`.
This starter Blueprint begins with the most basic sanity checks around that
operation.
:::

:::theorem "addition_right_identity-1" (parent := "addition_core-1") (owner := "project_author-1") (tags := "starter, arithmetic") (effort := "small") (priority := "high")
%%%
source := {
  document := "addition-source"
  spans := #[
    {
      page := "1"
      pdf := some {
        path := "source/addition-source.pdf"
      }
    }
  ]
}
%%%
For every natural number $`n`, adding zero on the right leaves it unchanged:
$`n + 0 = n`.
This is the first sanity check for {uses "addition_spec"}[].
:::


```tex
\begin{axiom}{my_axiom_name} \label{ax:my_axiom}
Let $X$ be a set with property $P$.
\end{axiom}
```
Axiom 2.1 (0 is a natural number)


* *Existence of the neutral element* There exists a real number called _zero_ that we denote as $`0` such that,
for every real number $`a`:
$$`a + 0 = 0 + a = a`

:::theorem "add_zero" (parent := "addition_core-1")(lean := "add_zero")
For all real number $`a`:
$`a + 0  = a`.
This is another consequence of {uses "addition_spec"}[].
:::

:::proof "add_zero"
Lean already provides this theorem as `add_zero`, so this Blueprint entry
links to an existing declaration instead of restating the code locally.
:::

```lean "add_zero"
example (a : Real) : a + 0 = a := by
  exact add_zero a
```

:::theorem "zero_add" (parent := "addition_core-1")(lean := "zero_add")
For all real number $`a`:
$`0 + a  = a`.
This is another consequence of {uses "addition_spec"}[].
:::

:::proof "zero_add"
Lean already provides this theorem as `zero_add`, so this Blueprint entry
links to an existing declaration instead of restating the code locally.
:::

```lean "zero_add"
example (x : Real) : 0 + x  = x := by
  exact zero_add x
```

:::theorem "add_assoc" (parent := "addition_core") (lean := "add_assoc")
For all natural numbers $`a`, $`b`, and $`c`, addition is associative:
$`(a + b) + c = a + (b + c)`.
This is another consequence of {uses "addition_spec"}[].
:::

:::proof "add_assoc"
Lean already provides this theorem as `add_assoc`, so this Blueprint entry
links to an existing declaration instead of restating the code locally.
:::

:::definition "addition_runtime_note-1" (parent := "addition_core")
Some projects keep implementation notes or helper snippets next to the informal
statement surface. Blueprint can attach a small Rust block for that purpose.
:::

```rust "addition_runtime_note-1"
pub fn add_preview(x: i32, y: i32) -> i32 {
    x + y
}
```
```lean "end namespace"
end Section_1_2
```
