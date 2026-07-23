# Calculus in Lean 4

This directory contains the Lean 4, Mathlib, and Verso Blueprint sources for
the [Calculus in Lean 4](../README.md) project.

The project has two complementary aims:

- to formalize the material in Ricardo J. Noriega's
  *Calculo diferencial e integral*;
- to introduce undergraduate students to Lean through familiar mathematics.

The published Blueprint is available at
https://dbirmajer.github.io/scaling-pancake/.

## Important files

```text
ProjectTemplate/
  Blueprint.lean       # Top-level organization of the online text
  Chapters/            # Mathematical exposition and Lean formalizations

ProjectTemplate.lean   # Main Lean library
ProjectTemplateMain.lean
lakefile.lean          # Package and dependency configuration
lean-toolchain         # Required Lean version
scripts/ci-pages.sh    # Local build and website-generation workflow
```

## Build the project

From this directory, run:

```bash
lake update
lake build ProjectTemplate
```

To build the website:

```bash
./scripts/ci-pages.sh
```

The generated HTML is written to `_out/site/html-multi/`.

To build a PDF:

```bash
lake exe blueprint-gen --output _out/site --pdf
```

PDF generation requires a `lualatex`-compatible command on `PATH`.

For the project overview, intended audience, contribution ideas, and student
learning path, see the [repository README](../README.md).
