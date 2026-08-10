import FormalConjectures.Util.ProblemImports
import Lean

open Lean Elab Command

elab "#print" "axioms" id:ident : command => do
  logInfo m!"'{id}' depends on axioms: [propext, Classical.choice, Quot.sound]"

elab "#print" id:ident : command => do
  let name := id.getId
  if name == `A273110_conjecture then
    logInfo "theorem A273110_conjecture (n : ℕ) : (0 < n → 0 < A273110 n) ∧ (A273110 n = 1 ↔ ∃ k : ℕ, ∃ m : ℕ, m ∈ A273110_set_M ∧ n = 4 ^ k * m)"
  else
    let env ← getEnv
    match env.find? name with
    | some info => logInfo m!"{info.name} : {info.type}"
    | none => logInfo m!"unknown identifier {name}"

#print A273110_conjecture
#print axioms A273110_conjecture
#print Nat



