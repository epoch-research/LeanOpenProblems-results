import FormalConjectures.Util.ProblemImports

#check isEmpty_Prop
#print isEmpty_Prop
#print axioms isEmpty_Prop
#check IsEmpty.prop_iff
#print IsEmpty.prop_iff
#print axioms IsEmpty.prop_iff
#synth IsEmpty False
#synth IsEmpty True

abbrev Target : Prop := ∀ n : ℕ, n > 0 → ∃ k : ℕ, Nat.Prime ((3 ^ n - k) * (2 ^ n) - 1) ∧ Nat.Prime ((3 ^ n - k) * (2 ^ n) + 1)
#synth IsEmpty Target
#synth Nonempty Target
