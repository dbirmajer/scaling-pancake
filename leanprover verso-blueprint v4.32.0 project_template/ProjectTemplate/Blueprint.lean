import Verso
import VersoManual
import VersoBlueprint
import VersoBlueprint.Commands.Graph
import VersoBlueprint.Commands.Summary
import ProjectTemplate.Chapters.Addition
import ProjectTemplate.Chapters.Collatz
import ProjectTemplate.Chapters.Multiplication

import ProjectTemplate.Chapters.Section_1_1
import ProjectTemplate.Chapters.Section_1_2
import ProjectTemplate.Chapters.Section_1_3
import ProjectTemplate.Chapters.Section_1_4

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Calculus in Lean 4" =>

This project develops an undergraduate introduction to differential and
integral calculus following Ricardo J. Noriega's _Calculo diferencial e
integral_. Definitions, propositions, theorems, and proofs are presented
informally and implemented in Lean 4.

The project also serves as an introduction to formal mathematics for
undergraduates. It uses familiar mathematical ideas to teach precise
definitions, theorem statements, proof structure, tactics, and interaction
with Lean and Mathlib.

The development is a work in progress. Some chapters and formal proofs remain
incomplete and will continue to evolve.

{include 0 ProjectTemplate.Chapters.Section_1_1}
{include 0 ProjectTemplate.Chapters.Section_1_2}
{include 0 ProjectTemplate.Chapters.Section_1_3}
{include 0 ProjectTemplate.Chapters.Section_1_4}


{blueprint_graph}
{blueprint_summary}
