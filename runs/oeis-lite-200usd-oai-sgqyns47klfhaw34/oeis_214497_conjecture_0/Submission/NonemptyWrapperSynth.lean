import FormalConjectures.Util.ProblemImports
abbrev Target : Prop := ∀ n : ℕ, n > 0 → ∃ k : ℕ, Nat.Prime ((3 ^ n - k) * (2 ^ n) - 1) ∧ Nat.Prime ((3 ^ n - k) * (2 ^ n) + 1)
#synth Nonempty (Nonempty Target)
#synth Nonempty (PLift Target)
#synth Nonempty (ULift Target)
#synth Nonempty (Σ' (_ : Unit), Target)
#synth Inhabited (Nonempty Target)
#synth Inhabited (PLift Target)
