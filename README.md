# Calculus in Lean 4

An undergraduate introduction to differential and integral calculus, developed
alongside a practical introduction to formal mathematics in Lean 4.

The project follows the mathematical development in Ricardo J. Noriega's
*Calculo diferencial e integral*. Its purpose is not merely to reproduce the
mathematics, but to express definitions, propositions, theorems, and proofs in
a form that can be checked by Lean.

## Project goals

This repository has two complementary aims:

1. **Develop calculus formally in Lean 4.** Present the main material from
   Noriega's text—including definitions, examples, propositions, and
   proofs—and formalize it using Lean 4 and Mathlib.
2. **Introduce undergraduates to Lean 4.** Use familiar undergraduate
   mathematics to teach precise definitions, theorem statements, proof
   structure, tactics, and interaction with a proof assistant.

The intended reader does not need previous experience with Lean. Some
mathematical maturity is helpful, but the material is designed to grow
gradually from elementary foundations toward differential and integral
calculus.

## Read the online Blueprint

The current web version is available at:

**https://dbirmajer.github.io/scaling-pancake/**

The Blueprint combines informal mathematical exposition with the corresponding
Lean declarations. It also includes a dependency graph and a summary of the
formalization's progress.

## Approach

Each section aims to contain three closely connected components:

- an informal explanation of the mathematics;
- a precise statement in Lean;
- a machine-checked proof, or a clear indication that the proof is still in
  progress.

This makes it possible to use the repository as a calculus text, a collection
of formalized results, a source of Lean exercises, or a companion for an
undergraduate course or independent study.

The development is incremental. Some chapters and proofs are incomplete, and
the organization may change as the project grows.

## Repository structure

The main Lean project is located in:

```text
leanprover verso-blueprint v4.32.0 project_template/
```

Important files include:

```text
ProjectTemplate/
  Blueprint.lean       # Organization of the online text
  Chapters/            # Exposition and formalized chapter material

ProjectTemplate.lean   # Main Lean library
ProjectTemplateMain.lean
lakefile.lean          # Lean and Mathlib dependencies
lean-toolchain         # Required Lean version
scripts/ci-pages.sh    # Builds the project and website
```

The `_out/` and `.lake/` directories are generated locally and are not part of
the mathematical source.

## Getting started

### 1. Install Lean

The recommended way to install Lean is through
[elan](https://github.com/leanprover/elan).

You may also want to use
[Visual Studio Code](https://code.visualstudio.com/) with the
[Lean 4 extension](https://marketplace.visualstudio.com/items?itemName=leanprover.lean4).

### 2. Clone the repository

```bash
git clone https://github.com/dbirmajer/scaling-pancake.git
cd scaling-pancake
cd "leanprover verso-blueprint v4.32.0 project_template"
```

### 3. Download the dependencies

```bash
lake update
```

### 4. Build the Lean project

```bash
lake build ProjectTemplate
```

### 5. Build the website locally

```bash
./scripts/ci-pages.sh
```

The generated website will be placed in:

```text
_out/site/html-multi/
```

Open `_out/site/html-multi/index.html` in a web browser to view it.

## Suggested path for students

If you are new to Lean:

1. Read the informal mathematical discussion first.
2. Examine the corresponding Lean statement.
3. Identify the hypotheses and conclusion.
4. Experiment with small changes in a separate file.
5. Try completing exercises or unfinished proofs.
6. Rebuild the project to let Lean check your work.

Do not worry if the formal version initially appears more complicated than the
paper proof. One purpose of the project is to explain why formal statements
require additional precision.

## Contributing

Contributions, corrections, and suggestions are welcome. Useful contributions
include:

- corrections to the mathematical exposition;
- improvements to Lean proofs;
- beginner-friendly explanations;
- new exercises and examples;
- documentation and website improvements;
- formalizations of results that are still incomplete.

Before submitting a change, verify that the project builds:

```bash
lake build ProjectTemplate
```

## Acknowledgments

The mathematical organization of this project is inspired by Ricardo J.
Noriega's *Calculo diferencial e integral*.

The formalization uses:

- [Lean 4](https://lean-lang.org/);
- [Mathlib](https://github.com/leanprover-community/mathlib4);
- [Verso](https://github.com/leanprover/verso);
- [Verso Blueprint](https://github.com/leanprover/verso-blueprint).

This is an independent educational formalization project and is not an official
edition or translation of Noriega's book.

## Project status

This repository is a work in progress. Definitions, proofs, chapter structure,
and explanatory material will continue to evolve.
