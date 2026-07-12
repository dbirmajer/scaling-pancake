--import Mathlib.Data.Nat.Notation
import Mathlib.Data.Real.Basic

import Verso
import VersoManual
import VersoBlueprint

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Section_1_2" =>

:::source_document "addition-source"
%%%
title := "Starter Addition Notes"
kind := .pdf
pdf := "source/addition-source.pdf"
%%%
:::

:::group "addition_core"
Core statements about addition on real numbers.
:::

:::author "project_author" (name := "Daniel Birmajer")
:::

```lean "namespace"
namespace Section_1_2
```

:::definition "addition_spec" (parent := "addition_core")
We write $`a + b` for the result of adding $`b` to $`a`.
This starter Blueprint begins with the most basic sanity checks around that
operation.
:::

:::theorem "addition_right_identity" (parent := "addition_core") (owner := "project_author") (tags := "starter, arithmetic") (effort := "small") (priority := "high")
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

```lean "Existence of 0"
theorem nat_add_zero_right (n : Nat) : n + 0 = n := by
  simp
```

:::proof "addition_right_identity"
Induct on $`n`. The base case is immediate and the inductive step unfolds one
successor on each side.
:::

```tex
\begin{axiom}{existence of the neutral element} \label{ax:my_axiom}
There exists a real number called _zero_ that we denote as `0` such that,
for every real number `a`:
$$a + 0 = 0 + a = a$$
\end{axiom}
```

There exists a real number called _zero_ that we denote as `0` such that,
for every real number `a`:
$$`0 + a = a + 0 = a`

:::theorem "add_zero" (parent := "addition_core")(lean := "add_zero")
For all real number $`a`:
$`a + 0  = a`.
This is another consequence of {uses "addition_spec"}[].
:::

```lean "add_zero"
example (x : Real) : x + (0 : Real) = x := by
  exact add_zero x
```

:::proof "add_zero"
Lean already provides this theorem as `add_zero`, so this Blueprint entry
links to an existing declaration instead of restating the code locally.
:::

:::theorem "zero_add" (parent := "addition_core")(lean := "zero_add")
For all real number $`a`:
$`0 + a  = a`.
This is another consequence of {uses "addition_spec"}[].
:::

```lean "zero_add"
example (x : Real) : 0 + x  = x := by
  exact zero_add x
```

:::proof "zero_add"
Lean already provides this theorem as `add_zero`, so this Blueprint entry
links to an existing declaration instead of restating the code locally.
:::

:::theorem "add_assoc" (parent := "addition_core") (lean := "add_assoc")
For all natural numbers $`a`, $`b`, and $`c`, addition is associative:
$`(a + b) + c = a + (b + c)`.
This is another consequence of {uses "addition_spec"}[].
:::

:::proof "add_assoc"
Lean already provides this theorem as `add_assoc`, so this Blueprint entry
links to an existing declaration instead of restating the code locally.
:::

:::definition "addition_runtime_note" (parent := "addition_core")
Some projects keep implementation notes or helper snippets next to the informal
statement surface. Blueprint can attach a small Rust block for that purpose.
:::

```rust "addition_runtime_note"
pub fn add_preview(x: i32, y: i32) -> i32 {
    x + y
}
```
```lean "end namespace"
end Section_1_2
```
