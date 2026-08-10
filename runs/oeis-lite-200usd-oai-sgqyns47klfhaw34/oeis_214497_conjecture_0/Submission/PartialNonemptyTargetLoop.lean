import FormalConjectures.Util.ProblemImports

abbrev Target : Prop := ∀ n : ℕ, n > 0 → ∃ k : ℕ, Nat.Prime ((3 ^ n - k) * (2 ^ n) - 1) ∧ Nat.Prime ((3 ^ n - k) * (2 ^ n) + 1)

partial def neTargetLoop (_ : Unit) : Nonempty Target := neTargetLoop ()
#print neTargetLoop
#print axioms neTargetLoop

example : Target := Classical.choice (neTargetLoop ())

partial def propFnLoop (_ : Unit) : (Target ∨ ¬ Target) := propFnLoop ()
#print propFnLoop
#print axioms propFnLoop

example : Target ∨ ¬ Target := propFnLoop ()
