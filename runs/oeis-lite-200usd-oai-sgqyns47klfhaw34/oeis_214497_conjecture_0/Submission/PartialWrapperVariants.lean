import FormalConjectures.Util.ProblemImports
abbrev Target : Prop := ∀ n : ℕ, n > 0 → ∃ k : ℕ, Nat.Prime ((3 ^ n - k) * (2 ^ n) - 1) ∧ Nat.Prime ((3 ^ n - k) * (2 ^ n) + 1)

partial def neTarget : Nonempty Target := neTarget
example : Target := Classical.choice neTarget
#print axioms neTarget

partial def pliftTarget : PLift Target := pliftTarget
example : Target := (pliftTarget).down
#print axioms pliftTarget

partial def uliftTarget : ULift Target := uliftTarget
example : Target := (uliftTarget).down
#print axioms uliftTarget

partial def sigmaTarget : Σ' (_ : Unit), Target := sigmaTarget
example : Target := (sigmaTarget).2
#print axioms sigmaTarget
