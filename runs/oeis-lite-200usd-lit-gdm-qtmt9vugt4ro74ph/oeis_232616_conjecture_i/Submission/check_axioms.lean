import Submission.Spec
import Lean

open Lean

#eval show MetaM Unit from do
  let axioms ← collectAxioms `oeis_232616_conjecture_i.disproof
  for ax in axioms do
    IO.println s!"Axiom: {ax}"
