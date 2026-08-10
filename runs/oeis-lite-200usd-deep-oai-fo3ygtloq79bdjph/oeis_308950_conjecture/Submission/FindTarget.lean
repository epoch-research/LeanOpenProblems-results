import FormalConjectures.Util.ProblemImports
open Lean Meta Elab Command Term
open Nat Finset

elab "#find_targetish" : command => do
  liftTermElabM do
    let stx ← `(∀ n : ℕ, 1 < n →
      (∃ (a b : ℕ), 2 ^ a * 3 ^ b ≤ n ∧ Nat.Prime (6 * (n - 2 ^ a * 3 ^ b) + 1)) ∨
      (∃ (a b : ℕ), 2 ^ a * 3 ^ b < n ∧ Nat.Prime (6 * (n - 2 ^ a * 3 ^ b) - 1)))
    let target ← elabType stx
    let env ← getEnv
    for (name, ci) in env.constants.toList do
      if (← isDefEq ci.type target) then
        logInfo m!"exact type {name}"
#find_targetish
