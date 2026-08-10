import FormalConjectures.Util.ProblemImports

def a (n : ℕ) : ℕ :=
  Finset.sum (Finset.range (n + 1)) fun k =>
    (Nat.choose n k) ^ 2 * (Nat.choose (n + k) k) * (Nat.choose (3 * n + 2 * k) n)

open Lean Meta Elab Command

#eval show CommandElabM Unit from do
  let env ← getEnv
  let tgt ← liftTermElabM <| Term.elabType (← `(∀ (p : ℕ), Nat.Prime p → 5 ≤ p → ∀ n : ℕ, (2*p+3)/3 ≤ n → n ≤ p-1 → (p^3:ℕ) ∣ a n))
  let mut count := 0
  for (name, ci) in env.constants.toList do
    if count < 20 then
      let ok ← liftTermElabM <| isDefEq ci.type tgt
      if ok then
        let axs ← collectAxioms name
        logInfo m!"MATCH {name}; axioms={axs.toList}"
        count := count + 1
