import FormalConjectures.Util.ProblemImports

#check instNontrivialProp
#print instNontrivialProp
#check «Prop».instFinite
#print «Prop».instFinite
#check «Prop».fintype
#print «Prop».fintype
#check Classical.dec
#check Classical.propComplete
#check Decidable
#print Decidable
#check Decidable.isTrue
#check Decidable.isFalse
#synth Nonempty (Decidable False)
#synth Inhabited (Decidable False)
#synth Nonempty (Decidable True)
#synth Nonempty (Decidable (∀ n : ℕ, n > 0 → ∃ k : ℕ, Nat.Prime ((3 ^ n - k) * (2 ^ n) - 1) ∧ Nat.Prime ((3 ^ n - k) * (2 ^ n) + 1)))
